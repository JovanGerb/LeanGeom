import LeanGeom.Defs


structure Ray' where (A B : Atomic Point)
  deriving Inhabited, BEq, Hashable

initialize pointState : IO.Ref (AtomContext Point) ← IO.mkRef {}
initialize rayState : IO.Ref (AtomContext Ray') ← IO.mkRef {}
initialize angleState : IO.Ref (IntCombContext (Atomic Ray') AddCircle (Atomic Proposition)) ← IO.mkRef {}

private def ofAngleSum (angle : AngleSum) : IO (LComb ℤ (Atomic Ray') AddCircle (Atomic Proposition)) :=
  return {
    sum := ← angle.sum.foldlM (init := .nil) fun sum (n, ray) => do
      let ray := { A := ← atomize pointState ray.A, B := ← atomize pointState ray.B }
      let ray ← atomize rayState ray
      return sum + (.cons n ray .nil)
    const := angle.θ
    pf := .single (← atomize propositionState (.angleEqZero angle)) }

def noteAngle (angle : AngleSum) : IO Unit := do
  let intComb ← ofAngleSum angle
  if let some comb ← IntCombContext.insert angleState intComb then
    let comb := comb.foldl (init := []) (fun list n pf => (n, pf) :: list)
    completeProofState.set (some (.angleEqZero comb))
    throw (.userError "the problem is solved")

def normalizeAngle (angle : AngleSum) : IO (LComb ℤ (Atomic Ray') AddCircle (Atomic Proposition)) := do
  let { sum, const, pf } ← ofAngleSum angle
  IntCombContext.simplify angleState sum const pf
