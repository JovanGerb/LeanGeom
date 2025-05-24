import LeanGeom.AngleArith
import LeanGeom.Delab
import Mathlib.Tactic.NormNum.Core


instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

open Qq Lean Elab Tactic Mathlib.Meta

instance : Neg AngleSum := ⟨fun { sum, θ } => { sum := sum.map fun (a, b) => (-a, b), θ := -θ }⟩
instance : SMul Int AngleSum := ⟨fun n { sum, θ } => { sum := sum.map fun (a, b) => (n * a, b), θ := n • θ }⟩
instance : Add AngleSum := ⟨fun a b => { sum := a.sum ++ b.sum, θ := a.θ + b.θ }⟩
instance : Sub AngleSum := ⟨fun a b => a + -b⟩

partial def obtainAngle (x : Q(Real.Angle)) : OptionT MetaM AngleSum := do
  match x with
  | ~q(∠ $A $B) => return { sum := [(1, ⟨⟨A⟩, ⟨B⟩⟩)], θ := 0 }
  | ~q(($n : Int) • $a) =>
    have : Q(Ring Int) := q(inferInstance)
    let ⟨n, _⟩ ← NormNum.deriveInt n
    let a ← obtainAngle a
    return (n.intLit! : Int) • a
  | ~q($a + $b) =>
    let a ← obtainAngle a
    let b ← obtainAngle b
    return a + b
  | ~q($a - $b) =>
    let a ← obtainAngle a
    let b ← obtainAngle b
    return a - b
  | ~q(-$a) =>
    let a ← obtainAngle a
    return -a
  | ~q(0) => return { sum := [], θ := 0}
  | _ => failure

def obtainFact (pf : Expr) : GeomM Unit := do
  let ⟨0, x, pf⟩ ← inferTypeQ pf | return
  match x with
  | ~q(($a : Real.Angle) = $b) =>
    let some a ← (obtainAngle a).run | return
    let some b ← (obtainAngle b).run | return
    modifyFacts fun facts => { facts with angles := facts.angles.push (a - b) }
    let prop ← atomize (.angleEqZero (a - b))
    addProof prop (.given pf)
  -- | ~q(($a : Real.Angle) ≠ $b)
  | ~q(¬($a : Real.Angle) = $b) =>
    let some a ← (obtainAngle a).run | return
    let some b ← (obtainAngle b).run | return
    modifyFacts fun facts => { facts with nangles := facts.nangles.push (a - b) }
    let prop ← atomize (.angleNeqZero (a - b))
    addProof prop (.given pf)
  | _ => return

def obtainFacts : GeomM Unit := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      obtainFact decl.toExpr




structure ProofState where
  names : Std.HashMap (Atomic Proposition) Ident := {}
  props : Array (Atomic Proposition) := #[]
  nameGen : NameGenerator := { namePrefix := `h }

abbrev PrintM := StateT ProofState GeomM

partial def nextName : PrintM Name := do
  let { nameGen, .. } ← get
  modify ({ · with nameGen := nameGen.next })
  let name := match nameGen.namePrefix with
    | .str p s => Name.mkStr p (s ++ "_" ++ toString nameGen.idx)
    | n       => Name.mkStr n ("_" ++ toString nameGen.idx)
  if (← getLCtx).findFromUserName? name |>.isSome then
    nextName
  else if (← getEnv).find? name |>.isSome then
    nextName
  else
    return name

def PrintM.insert (prop : Atomic Proposition) : PrintM Unit := do
  let name ← nextName
  modify fun s => { s with
    names := s.names.insert prop (mkIdent name)
    props := s.props.push prop
  }

partial def collectUsedPropsAux (prop : Atomic Proposition) : StateT (Std.HashSet (Atomic Proposition)) PrintM Unit := do
  let s ← get
  if s.contains prop then return
  modify (·.insert prop)
  match ← getProof prop with
  | .app _ args => args.forM collectUsedPropsAux
  | .angleComb comb => comb.forM (fun _ prop => collectUsedPropsAux prop)
  | .given _ => pure ()
  PrintM.insert prop

def collectUsedProps (pf : CompleteProof) : PrintM Unit := do
  match pf with
  | .byContra pos neg => (do collectUsedPropsAux pos; collectUsedPropsAux neg).run' {}
  | .angleEqZero comb => comb.forM (collectUsedPropsAux ·.2) |>.run' {}

def delabLine (prop : Atomic Proposition) : PrintM Lean.Syntax.Tactic := do
  let { names, .. } ← get
  let nameStx := names[prop]!
  let prop' ← deAtomize prop
  let propStx ← delabProposition prop'
  let pf ← getProof prop
  let pfStx ← delabReason pf prop' names
  `(tactic| have $nameStx : $propStx := $pfStx)


def delabCompleteProof (pf : CompleteProof) : PrintM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  collectUsedProps pf
  let mut lines ← (← get).props.mapM fun prop => delabLine prop
  match pf with
  | .byContra pos neg =>
    let pos := (← get).names[pos]!
    let neg := (← get).names[neg]!
    lines := lines.push (← `(tactic| absurd $pos))
    lines := lines.push (← `(tactic| exact $neg))
  | .angleEqZero _ => throwError "not yet implemented"
  `(tacticSeq| $[$lines]*)


elab "lean_geom" : tactic => withMainContext do
  let solution ← GeomM.run do
    obtainFacts
    let some proof ← getSolution | throwError "no solution was found"
    delabCompleteProof proof |>.run' {}
  logInfo m! "{solution}"
  Elab.Tactic.evalTactic solution

-- example : 0 = ((2 * (2 * Real.pi) : ℝ) : Real.Angle) := by
--   hint
--   abel

example (A B C D E F P : ℂ)
    (h₁ : ∠ A E - ∠ A F - ∠ P E + ∠ P F = 0)
    (h₂ : ∠ B F - ∠ B D - ∠ P F + ∠ P D = 0)
    (h₃ : ∠ C D + ∠ C E - ∠ P D + ∠ P E = 0)
    (l₁ : ∠ A E = -∠ C E) (l₂ : ∠ A F = ∠ B F)
    (nl₃ : ¬∠ B D = ∠ C D) : False := by
  lean_geom
--   have h_1 : ∠ B D = ∠ C D := by linear_combination (norm := abel) -h₁ - h₂ - h₃ + l₁ - l₂
--   absurd nl₃
--   exact h_1

-- #eval (-1:Int)/1

-- example (B C D : ℂ) (h : ∠ B D = ∠ C D) (g : ¬∠ B D = ∠ C D) : False := by
--   lean_geom
