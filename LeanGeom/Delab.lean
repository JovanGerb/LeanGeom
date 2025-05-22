import Batteries
import LeanGeom.Defs
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

notation "∠" A:max B:max => Complex.orientation.oangle A B

open Lean

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
    `($(Syntax.mkNameLit name.toString):name)
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
    let lem ← `($(Syntax.mkNameLit lem.toString):name)
    let argNames : Array NameLit := args.map (names[·]!)
    return Syntax.mkApp lem argNames
  | .angleComb comb => `(by linear_combination (norm := abel) $(← delabLinearComb names comb):term)
  | .given (.fvar fvarId) =>
    let name ← fvarId.getUserName
    `($(Syntax.mkNameLit name.toString):name)
  | .given pf => throwError "don't know how to elaborate proof {pf}"
