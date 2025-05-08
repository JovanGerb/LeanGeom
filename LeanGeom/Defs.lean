import LeanGeom.Util

namespace LeanGeom

local instance : Ord Lean.Name := ⟨Lean.Name.quickCmp⟩

inductive Point where
| free (p : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord

-- `Angle` lives in `(ℝ/2πℤ) ∪ ⊥`
inductive Angle where
| ray (A B : Point)
| const (θ : AddCircle)
| smul (n : Int) (a : Angle)
| add (a₁ a₂ : Angle)
| free (θ : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord


instance : Add Angle := ⟨.add⟩
instance : SMul Int Angle := ⟨.smul⟩
instance : Neg Angle := ⟨fun a => -1 • a⟩
instance : Sub Angle := ⟨fun a₁ a₂ => a₁ + -a₂⟩
scoped notation:max "∠" A:max B:max C:max => (2 : ℤ) • Angle.ray A B - (2 : ℤ) • Angle.ray B C

-- `Length` lives in `ℝ∞ ∪ ⊥`
inductive Length where
| segment (A B : Point)
| const (q : Rat)
| add (l₁ l₂ : Length)
| smul (n : Rat) (l : Length)
| mul (l₁ l₂ : Length)
| pow (l : Length) (n : Int)
| free (l : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord

instance : Add Length := ⟨.add⟩
instance : SMul Rat Length := ⟨.smul⟩
instance : Mul Length := ⟨.mul⟩
instance : Pow Length Int := ⟨.pow⟩
instance : Inv Length := ⟨fun l => l ^ (-1)⟩
instance : Div Length := ⟨fun l₁ l₂ => l₁ * l₂⁻¹⟩
scoped macro:max atomic("|" noWs) A:term:max B:term:max noWs "|" : term => `(Length.segment $A $B)

structure Triangle where
  A : Point
  B : Point
  C : Point
deriving Inhabited, DecidableEq, Hashable, Ord

scoped notation:max "△" A:max B:max C:max => Triangle.mk A B C

mutual

inductive PointEq : Point → Point → Type where
| refl (A) : PointEq A A
| symm {A B} : PointEq A B → PointEq B A
| trans {A B C} : PointEq A B → PointEq B C → PointEq A C
| given {A B} : Lean.Name → PointEq A B

inductive PointNEq : Point → Point → Type where
| symm {A B} : PointNEq A B → PointNEq B A
| congr {A B A' B'} : PointEq A A' → PointEq B B' → PointNEq A B → PointNEq A' B'
| given {A B} : Lean.Name → PointNEq A B

-- `AngleEq a θ` defaults to `True` in the case that `a` is `⊥`
inductive AngleEq : Angle → AddCircle → Type where
| const {θ} : AngleEq (.const θ) θ
| smul {a θ} {n : Int} : AngleEq a θ → AngleEq (n • a) (n • θ)
| add {a₁ a₂ θ₁ θ₂} : AngleEq a₁ θ₁ → AngleEq a₂ θ₂ → AngleEq (a₁ + a₂) (θ₁ + θ₂)
| coll {A B C} : Coll [A,B,C] → AngleEq (∠A B C) 0
| similar {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → AngleEq (∠A B C - s • ∠A₂ B₂ C₂) 0
| given {a θ} : Lean.Name → AngleEq a θ

inductive AngleNEq : Angle → AddCircle → Type where
| const {θ₁ θ₂} : θ₁ ≠ θ₂ → AngleNEq (.const θ₁) θ₂
| smul {a θ} {n : Int} : AngleNEq (n • a) (n • θ) → AngleNEq a θ
| add {a₁ a₂ θ₁ θ₂} : AngleEq a₁ θ₁ → AngleNEq a₂ θ₂ → AngleNEq (a₁ + a₂) (θ₁ + θ₂)
| ncoll {A B C} : NColl [A,B,C] → AngleNEq (∠A B C) 0
| given {a θ} : Lean.Name → AngleNEq a θ

inductive LengthEq : Length → Rat → Type where
| const {r} : LengthEq (.const r) r
| smul {l r} {r' : Rat} : LengthEq l r → LengthEq (r' • l) (r' * r)
| add {l₁ l₂ r₁ r₂} : LengthEq l₁ r₁ → LengthEq l₂ r₂ → LengthEq (l₁ + l₂) (r₁ + r₂)
| pow {l r} {n : Int} : LengthEq l r → LengthEq (l ^ n) (r ^ n)
| mul {l₁ l₂ r₁ r₂} : LengthEq l₁ r₁ → LengthEq l₂ r₂ → LengthEq (l₁ * l₂) (r₁ * r₂)
| similar {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → LengthEq ((|A B|/|B C|)/(|A₂ B₂|/|B₂ C₂|)) 1
| given {l r} : Lean.Name → LengthEq l r

-- TODO: LengthNe
-- TODO: LengthLe

inductive Similar : (T₁ T₂ : Triangle) → SignGroup → Type where
| swap₁ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △B A C △B₂ A₂ C₂ s
| swap₂ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △C B A △C₂ B₂ A₂ s
| swap₃ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △A C B △A₂ C₂ B₂ s
| swap₄ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △B C A △B₂ C₂ A₂ s
| swap₅ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △C A B △C₂ A₂ B₂ s
| refl (T) {s} : Similar T T s
| symm {T₁ T₂ s} : Similar T₁ T₂ s → Similar T₂ T₁ s
| trans {T₁ T₂ T₃ s₁ s₂} : Similar T₁ T₂ s₁ → Similar T₂ T₃ s₂ → Similar T₁ T₃ (s₁ * s₂)
| aa  {A B C A₂ B₂ C₂ s} : AngleEq (∠A B C - s • ∠A₂ B₂ C₂) 0 → AngleEq (∠C A B - s • ∠C₂ A₂ B₂) 0 → NColl [A,B,C] → Similar △A B C △A₂ B₂ C₂ s
| sas  {A B C A₂ B₂ C₂ s} : AngleEq (∠A B C - s • ∠A₂ B₂ C₂) 0 → LengthEq ((|A B|/|B C|)/(|A₂ B₂|/|B₂ C₂|)) 1 → Similar △A B C △A₂ B₂ C₂ s

inductive Coll : List Point → Type where
-- | two {A B} : Coll [A,B]
| subset {l₁ l₂} : l₂ ⊆ l₁ → Coll l₁ → Coll l₂
| para {A B C} : AngleEq (∠A B C) 0 → Coll [A, B, C]
| given {l} : Lean.Name → Coll l

inductive NColl : List Point → Type where
| para {A B C} : AngleNEq (∠A B C) 0 → NColl [A, B, C]
| subset {l₁ l₂} : l₁ ⊆ l₂ → NColl l₁ → NColl l₂
| given {l} : Lean.Name → NColl l


inductive Cyclic : List Point → Type where
-- | three {A B C} : Cyclic [A,B,C]
| subset {l₁ l₂} : l₂ ⊆ l₁ → Cyclic l₁ → Cyclic l₂
| quad {A B C D} : AngleEq (∠A B D - ∠ A C D) 0 → Cyclic [A,B,C,D]

end

inductive Proposition where
| pointEq : Point → Point → Proposition
| pointNEq : Point → Point → Proposition
| angleEq : Angle → AddCircle → Proposition
| AngleNEq : Angle → AddCircle → Proposition
| similar : Triangle → Triangle → SignGroup → Proposition
| coll : List Point → Proposition
| ncoll : List Point → Proposition
| cyclic : List Point → Proposition
deriving Inhabited, DecidableEq, Hashable, Ord

inductive Proof : Proposition → Type where
| pointEq {A B} : PointEq A B → Proof (.pointEq A B)
| pointNEq {A B} : PointNEq A B → Proof (.pointNEq A B)
| angleEq {a θ} : AngleEq a θ → Proof (.angleEq a θ)
| AngleNEq {a θ} : AngleNEq a θ → Proof (.AngleNEq a θ)
| similar {T₁ T₂ s} : Similar T₁ T₂ s → Proof (.similar T₁ T₂ s)
| coll {l} : Coll l → Proof (.coll l)
| ncoll {l} : NColl l → Proof (.ncoll l)
| cyclic {l} : Cyclic l → Proof (.cyclic l)




-- inductive Angle : (L : List (Int × Angle)) → (θ : AddCircle) → Type where
-- | perm {l₁ l₂ θ} : l₁.Perm l₂ → Angle l₁ θ → Angle l₂ θ
-- | nil : Angle [] 0
-- | append {l₁ l₂ θ₁ θ₂} : Angle l₁ θ₁ → Angle l₂ θ₂ → Angle (l₁ ++ l₂) (θ₁ + θ₂)
-- | zero {a} : Angle [(0, a)] 0
-- | add {n₁ n₂ a} : Angle [(n₁, a), (n₂, a), (-(n₁ + n₂), a)] 0
-- | smul {l θ} (n : Int) : Angle l θ → Angle (l.map fun x => (n * x.1, x.2)) (n • θ)
