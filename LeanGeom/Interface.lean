import LeanGeom.Defs
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Tactic.NormNum.Core

local notation "∠" A:max B:max => Complex.orientation.oangle A B
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
  | _ => failure

def obtainFact (pf : Expr) : StateT Facts MetaM Unit := do
  let ⟨0, x, pf⟩ ← inferTypeQ pf | return
  match x with
  | ~q(($a : Real.Angle) = $b) =>
    let some a ← (obtainAngle a).run | return
    let some b ← (obtainAngle b).run | return
    modify fun facts => { facts with angles := facts.angles.push (a - b) }
    let prop ← atomize propositionState (.angleEqZero (a - b))
    proofState.modify fun s => s.insert prop (.given pf)
  | _ => return

def obtainFacts : TacticM Facts := do
  withMainContext do
    let mut facts : Facts := {}
    for decl in (← getLCtx) do
      facts := (← (obtainFact decl.toExpr).run facts).2
    return facts




def delabInt (n : Int) : MetaM Term :=
  if n ≥ 0 then
    `($(Syntax.mkNatLit n.natAbs))
  else
    `(-$(Syntax.mkNatLit n.natAbs))

def delabRat (q : Rat) : MetaM Term := do
  if q.den = 1 then
    delabInt q.num
  else
    `($(← delabInt q.num) / $(Syntax.mkNatLit q.den))

def delabRatAngle (angle : RatAngle) : MetaM Term := do
  if angle = 0 then
    return Syntax.mkNatLit 0
  else
    let q ← delabRat (2 * angle.q)
    `($q * Real.pi)

def delabPoint : Point → MetaM Term
  | ⟨.fvar fvarId⟩ => do
    let name ← fvarId.getUserName
    `($(Syntax.mkNameLit name.toString))
  | ⟨point⟩ => throwError "don't know how to elaborate {point}"

def delabRay (r : Ray) : MetaM Term := do
  let A ← delabPoint r.A
  let B ← delabPoint r.B
  `(∠ $A $B)


def delabAngleSum (angle : AngleSum) : MetaM Term := do
  if angle.sum.isEmpty then
    delabRatAngle angle.θ
  else
    let sum ← delabSum angle.sum
    if angle.θ = 0 then
      return sum
    let θ ← delabRatAngle angle.θ
    `($sum + $θ)
where
  delabSum : List (Int × Ray) → MetaM Term
  | (n, r) :: s => do
    let r ← delabRay r
    let (n, n_pos) := (n.natAbs, (n ≥ 0 : Bool))
    let r ←
      if n = 1 then
        pure r
      else
        `($(Syntax.mkNatLit n) • $r)
    if s.isEmpty then
      if n_pos then
        return r
      else
        `(-$r)
    else
      let s ← delabSum s
      if n_pos then
        `($s + $r)
      else
        `($s - $r)
  | [] => unreachable!

def delabProposition (prop : Proposition) : MetaM Term := do
  match prop with
  | .angleEqZero angle => `($(← delabAngleSum angle) = 0)
  | .angleNeqZero angle => `($(← delabAngleSum angle) ≠ 0)





def delabLinearComb (names : Std.HashMap (Atomic Proposition) NameLit) : List (Int × (Atomic Proposition)) → MetaM Term
  | (n, prop) :: s => do
    let h : Term := names[prop]!
    let (n, n_pos) := (n.natAbs, (n ≥ 0 : Bool))
    let h ←
      if n = 1 then
        pure h
      else
        `($(Syntax.mkNatLit n) * $h)
    if s.isEmpty then
      if n_pos then
        return h
      else
        `(-$h)
    else
      let s ← delabLinearComb names s
      if n_pos then
        `($s + $h)
      else
        `($s - $h)
  | [] => unreachable!


def delabReason (reason : Reason) (names : Std.HashMap (Atomic Proposition) NameLit) : MetaM Term := do
  match reason with
  | .app lem args =>
    let lem := Syntax.mkNameLit lem.toString
    let argNames : Array NameLit := args.map (names[·]!)
    return Syntax.mkApp lem argNames
  | .angleComb comb => `(by linear_combination (norm := abel) $(← delabLinearComb names comb):term)
  | .given (.fvar fvarId) =>
    let name ← fvarId.getUserName
    `($(Syntax.mkNameLit name.toString))
  | .given pf => throwError "don't know how to elaborate proof {pf}"



structure ProofState where
  propMap : Std.HashMap (Atomic Proposition) NameLit
  props : Array (Atomic Proposition)
  nameGen : NameGenerator

partial def nextName (nameGen : NameGenerator) : MetaM (Name × NameGenerator) := do
  let name := match nameGen.namePrefix with
    | .str p s => Name.mkStr p (s ++ "_" ++ toString nameGen.idx)
    | n       => Name.mkStr n ("_" ++ toString nameGen.idx)
  if (← getLCtx).findFromUserName? name |>.isSome then
    nextName (nameGen.next)
  else if (← getEnv).find? name |>.isSome then
    nextName (nameGen.next)
  else
    return (name, nameGen.next)

def ProofState.insert (prop : Atomic Proposition) (s : ProofState) : MetaM ProofState := do
  let (name, nameGen) ← nextName s.nameGen
  return {
    propMap := s.propMap.insert prop (Syntax.mkNameLit name.toString)
    props := s.props.push prop
    nameGen
  }

partial def collectUsedPropsAux (prop : Atomic Proposition) : StateT ProofState MetaM Unit := do
  let s ← get
  if s.propMap.contains prop then return
  match ← getProof prop with
  | .app _ args => args.forM collectUsedPropsAux
  | .angleComb comb => comb.forM (collectUsedPropsAux ·.2)
  | .given _ => pure ()
  let s ← get
  set (← s.insert prop)

def collectUsedProps (pf : CompleteProof) : StateT ProofState MetaM Unit := do
  match pf with
  | .byContra pos neg => collectUsedPropsAux pos; collectUsedPropsAux neg
  | .angleEqZero comb => comb.forM (collectUsedPropsAux ·.2)

def delabLine (prop : Atomic Proposition) (names : Std.HashMap (Atomic Proposition) NameLit) : MetaM Lean.Syntax.Tactic := do
  let nameStx := names[prop]!
  let propStx ← delabProposition (← deAtomize propositionState prop)
  let pf ← getProof prop
  let pfStx ← delabReason pf names
  `(tactic| have $nameStx:name : $propStx := $pfStx)

def delabProof (props : Array (Atomic Proposition)) (names : Std.HashMap (Atomic Proposition) NameLit) : MetaM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let mut lines ← props.mapM fun prop => delabLine prop names

  `(tacticSeq| $[$lines]*)
