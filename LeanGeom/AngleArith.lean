import LeanGeom.Defs

open Lean

def solvedMsg : String := "the problem has been solved"
def unsolvedMsg : String := "the problem has not been solved"

structure Ray' where (A B : Atomic Point)
  deriving Inhabited, BEq, Hashable, Repr

initialize pointState : IO.Ref (AtomContext Point) ← IO.mkRef {}
initialize rayState : IO.Ref (AtomContext Ray') ← IO.mkRef {}
initialize angleState : IO.Ref (IntCombContext (Atomic Ray') RatAngle (Atomic Proposition)) ← IO.mkRef {}

def normalizeAngle (angle : AngleSum) (isTrue : Bool) : MetaM (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) := do
  let { sum, const, pf } ← ofAngleSum angle
  IntCombContext.simplify angleState sum const pf
where
  ofAngleSum (angle : AngleSum) : MetaM (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) := do
    let pf ← if isTrue then pure <| .single (← atomize propositionState (.angleEqZero angle)) else pure 0
    return {
      sum := ← angle.sum.foldlM (init := .nil) fun sum (n, ray) => do
        let ray := { A := ← atomize pointState ray.A, B := ← atomize pointState ray.B }
        let ray ← atomize rayState ray
        return sum.insert n ray
      const := angle.θ
      pf }

def noteAngle (angle : AngleSum) : MetaM Unit := do
  let intComb ← normalizeAngle angle true
  if let some comb ← IntCombContext.insert angleState intComb then
    let pf : CompleteProof := .angleEqZero <| comb.foldl (init := []) (fun list n pf => (n, pf) :: list)
    completeProofState.set pf
    throwError solvedMsg

def checkNonAngle (angle : AngleSum) : MetaM Unit := do
  let intComb ← normalizeAngle angle false
  if let some pf := intComb.isNil then
    let pos ← atomize propositionState <| .angleEqZero angle
    let neg ← atomize propositionState <| .angleNeqZero angle
    addProof pos (.angleComb (pf.map (-·)))
    let completePf : CompleteProof := .byContra pos neg
    completeProofState.set completePf
    throwError solvedMsg


def runSolver : StateRefT Facts MetaM Unit := do
  for angle in (← get).angles do
    noteAngle angle
  for angle in (← get).nangles do
    checkNonAngle angle


def getSolution (facts : Facts) : MetaM (Option CompleteProof) :=
  try
    runSolver.run' facts
    return none
  catch _ =>
    if let some pf ← completeProofState.get then
      return pf
    else
      return none
