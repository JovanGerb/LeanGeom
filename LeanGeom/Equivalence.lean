import LeanGeom.Abstraction

namespace LeanGeom

/-- A node in a union-find. -/
structure UFNode (α : Type) [Atomic α] [EqType α] (root : α) where
  val : α
  pf : EqProof root val

/-- The union-find state. -/
structure UnionFind (α : Type) [Atomic α] [EqType α] where
  map : Std.DHashMap α (UFNode α)
  deriving Inhabited

namespace UnionFind

variable {α : Type} [Atomic α] [EqType α]

partial def find (a : α) (uf : UnionFind α) : ((val : α) × EqProof a val) × UnionFind α :=
  match uf.map.get? a with
  | none => (⟨a, .refl a⟩, uf)
  | some { val := a', pf } =>
    if a' == a then
      (⟨a, .refl a⟩, uf)
    else
      let (⟨a', pf'⟩, uf) := find a' uf
      let pf := pf.trans pf'
      (⟨a', pf⟩, ⟨uf.map.insert a { val := a', pf } ⟩)

def union {a b : α} (pf : EqProof a b) (uf : UnionFind α) : UnionFind α :=
  let (⟨a, pfa⟩, uf) := uf.find a
  let (⟨b, pfb⟩, uf) := uf.find b
  if a == b then
    uf
  else
    ⟨uf.map.insert a ⟨b, (pfa.symm.trans pf).trans pfb⟩⟩

end UnionFind

section

def UF (α : Type) := α

structure UFObject (α : Type) [Object α] where
  orig : α
  atom : Atom α
  pf : EqProof (toAtom orig) atom

variable {α : Type} [Object α]

instance : Object (UFObject α) where
  Atom := Atom α
  instEqTypeAtom := unitEqType
  toAtom a := a.atom

variable {m : Type → Type} [Monad m] [MonadReaderOf (IO.Ref (UnionFind (Atom α))) m] [MonadLift IO m]

instance : Abstraction m α (UFObject α) where
  represent a := do
    let ref ← readThe (IO.Ref <| UnionFind (Atom α))
    let uf ← ref.get
    let (⟨a', pf⟩, uf) := uf.find (toAtom a)
    ref.set uf
    return ⟨a, a', pf⟩
  original a := a.orig
  proveEq
    | a, b, ⟨(pf : a.atom = b.atom)⟩ =>
      .mk fun _ => Object.of_atomEqProof <| (pf ▸ a.pf).trans b.pf.symm

end
