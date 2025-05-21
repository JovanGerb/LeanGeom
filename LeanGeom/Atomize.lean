import Std

structure Atomic (α : Type) where
  id : Nat
deriving Inhabited

variable {α : Type} [BEq α] [Hashable α]

instance : BEq (Atomic α) := ⟨(·.1 = ·.1)⟩
instance : Ord (Atomic α) := ⟨(compare ·.1 ·.1)⟩
instance : Hashable (Atomic α) := ⟨(hash ·.1)⟩

structure AtomContext (α : Type) [BEq α] [Hashable α] where
  encode : Std.HashMap α (Atomic α) := {}
  decode : Array α := #[]
deriving Inhabited


def atomize (ref : IO.Ref (AtomContext α)) (val : α) : IO (Atomic α) := do
  let { encode, .. } ← ref.get
  match encode[val]? with
  | some atom => return atom
  | none =>
    let atom := ⟨encode.size⟩
    ref.modify fun { encode, decode } => { encode := encode.insert val atom, decode := decode.push val }
    return atom

def deAtomize [Inhabited α] (ref : IO.Ref (AtomContext α)) (val : Atomic α) : IO α := do
  let { decode, .. } ← ref.get
  return decode[val.id]!
