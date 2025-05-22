import LeanGeom.Defs

def solvedMsg : String := "the problem has been solved"
def unsolvedMsg : String := "the problem has not been solved"

structure Ray' where (A B : Atomic Point)
  deriving Inhabited, BEq, Hashable

initialize pointState : IO.Ref (AtomContext Point) ← IO.mkRef {}
initialize rayState : IO.Ref (AtomContext Ray') ← IO.mkRef {}
initialize angleState : IO.Ref (IntCombContext (Atomic Ray') RatAngle (Atomic Proposition)) ← IO.mkRef {}

private def ofAngleSum (angle : AngleSum) : IO (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) :=
  return {
    sum := ← angle.sum.foldlM (init := .nil) fun sum (n, ray) => do
      let ray := { A := ← atomize pointState ray.A, B := ← atomize pointState ray.B }
      let ray ← atomize rayState ray
      return sum.insert n ray
    const := angle.θ
    pf := .single (← atomize propositionState (.angleEqZero angle)) }

def noteAngle (angle : AngleSum) : IO Unit := do
  let intComb ← ofAngleSum angle
  if let some comb ← IntCombContext.insert angleState intComb then
    let pf : CompleteProof := .angleEqZero <| comb.foldl (init := []) (fun list n pf => (n, pf) :: list)
    completeProofState.set pf
    throw (.userError solvedMsg)

def normalizeAngle (angle : AngleSum) : IO (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) := do
  let { sum, const, pf } ← ofAngleSum angle
  IntCombContext.simplify angleState sum const pf

def checkNonAngle (angle : AngleSum) : IO Unit := do
  let intComb ← ofAngleSum angle
  if intComb.isNil.isSome then
    let pos ← atomize propositionState <| .angleEqZero angle
    let neg ← atomize propositionState <| .angleNeqZero angle
    let pf : CompleteProof := .byContra pos neg
    completeProofState.set pf
    throw (.userError solvedMsg)


def runSolver : StateRefT Facts IO Unit := do
  for angle in (← get).angles do
    noteAngle angle
  for angle in (← get).nangles do
    checkNonAngle angle


def getSolution (facts : Facts) : IO CompleteProof :=
  try
    runSolver.run' facts
    throw (.userError unsolvedMsg)
  catch ex =>
    if let some pf ← completeProofState.get then
      return pf
    else
      throw ex
