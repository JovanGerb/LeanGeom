import Lean
import LeanGeom.Util
import LeanGeom.LComb
import LeanGeom.Atomize

structure Point where
  self : Lean.Expr
deriving Inhabited, BEq, Hashable

structure Equal (α : Type) where (lhs rhs : α)
structure NotEqual (α : Type) where (lhs rhs : α)

structure Ray where (A B : Point)
deriving Inhabited, BEq, Hashable

structure AngleSum where
  sum : List (Int × Ray)
  θ : RatAngle
deriving Inhabited, BEq, Hashable

structure Segment where (A B : Point)

structure Ratio where
  prod : List (Segment × Int)
  l : PrimeProd

inductive Proposition where
| angleEqZero (angle : AngleSum)
| angleNeqZero (angle : AngleSum)
deriving Inhabited, BEq, Hashable

initialize propositionState : IO.Ref (AtomContext Proposition) ← IO.mkRef {}

inductive Reason where
| app (lem : Lean.Name) (args : Array (Atomic Proposition))
| angleComb (comb : List (Int × Atomic Proposition))
| given (pf : Lean.Expr)
deriving Inhabited, BEq

initialize proofState : IO.Ref (Std.HashMap (Atomic Proposition) Reason) ← IO.mkRef {}
def getProof (prop : Atomic Proposition) : IO Reason := do
  match (← proofState.get)[prop]? with
  | some pf => return pf
  | none => throw (.userError "proposition doesn't have a proof")

inductive CompleteProof where
| byContra (pos neg : Atomic Proposition)
| angleEqZero (comb : List (Int × Atomic Proposition))

initialize completeProofState : IO.Ref (Option CompleteProof) ← IO.mkRef none


structure Facts where
  angles : Array AngleSum := #[]
  nangles : Array AngleSum := #[]
