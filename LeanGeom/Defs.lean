import LeanGeom.Util
import LeanGeom.LComb
import LeanGeom.Atomize

open Lean

structure Point where
  self : Expr
deriving Inhabited, BEq, Hashable
instance : ToMessageData Point := ⟨(m!"{·.1}")⟩

structure Equal (α : Type) where (lhs rhs : α)
structure NotEqual (α : Type) where (lhs rhs : α)

structure Ray where (A B : Point)
deriving Inhabited, BEq, Hashable
instance : ToMessageData Ray := ⟨fun r => m!"∠{r.A}{r.B}"⟩

structure AngleSum where
  sum : List (Int × Ray)
  θ : RatAngle
deriving Inhabited, BEq, Hashable
instance : ToMessageData AngleSum where
  toMessageData s :=
    let sum := s.sum.map fun (n, r) => m!"{n}*{r}"
    let sum := if sum.isEmpty then m!"0" else .joinSep sum " + "
    m!"{sum} + {s.θ}"

structure Segment where (A B : Point)

structure Ratio where
  prod : List (Segment × Int)
  l : PrimeProd

inductive Proposition where
| angleEqZero (angle : AngleSum)
| angleNeqZero (angle : AngleSum)
deriving Inhabited, BEq, Hashable
instance : ToMessageData Proposition where
  toMessageData
    | .angleEqZero angle => m!"{angle} = 0"
    | .angleNeqZero angle => m!"{angle} ≠ 0"

inductive Reason where
| app (lem : Name) (args : Array (Atomic Proposition))
| angleComb (comb : LSum Int (Atomic Proposition))
| given (pf : Expr)
deriving Inhabited, BEq

inductive CompleteProof where
| byContra (pos neg : Atomic Proposition)
| angleEqZero (comb : List (Int × Atomic Proposition))


structure Facts where
  angles : Array AngleSum := #[]
  nangles : Array AngleSum := #[]
instance : ToMessageData Facts where
  toMessageData facts := m!"{facts.angles}\n{facts.nangles}"



structure Ray' where (A B : Atomic Point)
  deriving Inhabited, BEq, Hashable, Repr

structure SolveCtx where
  point : AtomContext Point := {}
  ray : AtomContext Ray' := {}
  angle : IntCombContext (Atomic Ray') RatAngle (Atomic Proposition) := {}



structure GeomState where
  props : AtomContext Proposition := {}
  proofs : Std.HashMap (Atomic Proposition) Reason := {}
  result : Option CompleteProof := none
  facts : Facts := {}
  context : SolveCtx := {}


abbrev GeomM := StateRefT GeomState MetaM

def GeomM.run {α : Type} (x : GeomM α) : MetaM α := StateRefT'.run' x {}

instance : MonadAtom Proposition GeomM := ⟨return (← get).props, (modify fun s => { s with props := · s.props })⟩

instance : MonadAtom Point GeomM := ⟨return (← get).context.point, (modify fun s => { s with context.point := · s.context.point })⟩
instance : MonadAtom Ray'  GeomM := ⟨return (← get).context.ray  , (modify fun s => { s with context.ray   := · s.context.ray   })⟩

instance : MonadIntComb (Atomic Ray') RatAngle (Atomic Proposition) GeomM := ⟨modifyGet fun s => (s.context.angle, { s with context.angle := {} }), fun ctx => modify ({ · with context.angle := ctx })⟩

@[inline] def modifyFacts (f : Facts → Facts) : GeomM Unit :=
  modify fun s => { s with facts := f s.facts }

def addProof (prop : Atomic Proposition) (pf : Reason) : GeomM Unit := do
  if !(← get).proofs.contains prop then
    modify fun s => { s with proofs := s.proofs.insert prop pf }

def getProof (prop : Atomic Proposition) : GeomM Reason := do
  match (← get).proofs[prop]? with
  | some pf => return pf
  | none => throwError "proposition {← deAtomize prop} doesn't have a proof"

def addCompleteProof {α : Type} (pf : CompleteProof) : GeomM α := do
  modify fun s => { s with result := pf }
  throwError "the problem has been solved"
