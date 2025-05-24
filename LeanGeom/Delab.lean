import Batteries.Data.Rat.Basic
import LeanGeom.Defs
import LeanGeom.Tactics

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
  | ⟨.fvar fvarId⟩ => return mkIdent (← fvarId.getUserName)
  | ⟨point⟩ => throwError "don't know how to delaborate {point}"

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





def delabLinearComb (names : Std.HashMap (Atomic Proposition) Ident) : LSum Int (Atomic Proposition) → MetaM Term
  | .cons n prop s => do
    let h : Term := names[prop]!
    let (n, n_pos) := (n.natAbs, (n ≥ 0 : Bool))
    let h ←
      if n = 1 then
        pure h
      else
        `($(Syntax.mkNatLit n) * $h)
    if s.isNil then
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
  | .nil => unreachable!


def delabReason (reason : Reason) (prop : Proposition) (names : Std.HashMap (Atomic Proposition) Ident) : MetaM Term := do
  match reason with
  | .app lem args =>
    let argNames : Array Ident := args.map (names[·]!)
    return Syntax.mkApp (mkIdent lem) argNames
  | .angleComb comb => `(by linear_combination (norm := abel) $(← delabLinearComb names comb):term)
  | .given (.fvar fvarId) =>
    let h ← `(ident| $(mkIdent (← fvarId.getUserName)))
    match prop with
    | .angleEqZero _ => `(by linear_combination (norm := abel) $h:term)
    | .angleNeqZero _ => `(by contrapose! $h; linear_combination (norm := abel) $h:term)
  | .given pf => throwError "don't know how to delaborate proof {pf}"
