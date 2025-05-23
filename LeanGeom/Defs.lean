import Lean
import LeanGeom.Util
import LeanGeom.LComb
import LeanGeom.Atomize

open Lean

structure Point where
  self : Lean.Expr
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

initialize propositionState : IO.Ref (AtomContext Proposition) ← IO.mkRef {}

inductive Reason where
| app (lem : Lean.Name) (args : Array (Atomic Proposition))
| angleComb (comb : LSum Int (Atomic Proposition))
| given (pf : Lean.Expr)
deriving Inhabited, BEq

initialize proofState : IO.Ref (Std.HashMap (Atomic Proposition) Reason) ← IO.mkRef {}

def addProof (prop : Atomic Proposition) (pf : Reason) : IO Unit := do
  if !(← proofState.get).contains prop then
    proofState.modify (·.insert prop pf)

def getProof (prop : Atomic Proposition) : MetaM Reason := do
  match (← proofState.get)[prop]? with
  | some pf => return pf
  | none => throwError "proposition {← deAtomize propositionState prop} doesn't have a proof"

inductive CompleteProof where
| byContra (pos neg : Atomic Proposition)
| angleEqZero (comb : List (Int × Atomic Proposition))

initialize completeProofState : IO.Ref (Option CompleteProof) ← IO.mkRef none


structure Facts where
  angles : Array AngleSum := #[]
  nangles : Array AngleSum := #[]
instance : ToMessageData Facts where
  toMessageData facts := m!"{facts.angles}\n{facts.nangles}"
