import LeanGeom.Defs

open Lean

def normalizeAngle (angle : AngleSum) (isTrue : Bool) : GeomM (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) := do
  let lcomb ← ofAngleSum angle
  simplifyLComb lcomb
where
  ofAngleSum (angle : AngleSum) : GeomM (LComb ℤ (Atomic Ray') RatAngle (Atomic Proposition)) := do
    let pf ← if isTrue then pure <| .single (← atomize (.angleEqZero angle)) else pure 0
    return {
      sum := ← angle.sum.foldlM (init := .nil) fun sum (n, ray) => do
        let ray := { A := ← atomize ray.A, B := ← atomize ray.B }
        let ray ← atomize ray
        return sum.insert n ray
      const := angle.θ
      pf }

def noteAngle (angle : AngleSum) : GeomM Unit := do
  let intComb ← normalizeAngle angle true
  if let some comb ← insertLComb intComb then
    let pf : CompleteProof := .angleEqZero <| comb.foldl (init := []) (fun list n pf => (n, pf) :: list)
    addCompleteProof pf

def checkNonAngle (angle : AngleSum) : GeomM Unit := do
  let intComb ← normalizeAngle angle false
  if let some pf := intComb.isNil then
    let pos ← atomize (.angleEqZero angle)
    let neg ← atomize (.angleNeqZero angle)
    addProof pos (.angleComb (pf.map (-·)))
    let completePf : CompleteProof := .byContra pos neg
    addCompleteProof completePf

-- throws an exception if the problem is solved
def runSolver : GeomM Unit := do
  for angle in (← get).facts.angles do
    noteAngle angle
  for angle in (← get).facts.nangles do
    checkNonAngle angle


def getSolution : GeomM (Option CompleteProof) :=
  try
    runSolver
    return none
  catch _ =>
    return (← get).result
