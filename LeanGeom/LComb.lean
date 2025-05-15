import Std
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Rat.Defs

/-- keep the invariant that `a = a₁ * x + a₂ * y`, `b = b₁ * x + b₂ * y` -/
partial def Int.xgcdAux (a a₁ a₂ b b₁ b₂ : Int) (_ : b ≠ 0) : Int × Int × Int :=
  if h : a % b = 0 then
    (b, b₁, b₂)
  else
    Int.xgcdAux b b₁ b₂ (a % b) (a₁ - (a / b) * b₁) (a₂ - (a / b) * b₂) h

/-- returns `(gcd, a, b)` such that `gcd = a * x + b * y`. -/
def Int.xgcd (x y : Int) : Int × Int × Int :=
  if h : y = 0 then
    (x, 1, 0)
  else
    Int.xgcdAux x 1 0 y 0 1 h



inductive LSum (G α : Type) where
| cons : G → α → LSum G α → LSum G α
| nil : LSum G α

namespace LSum

attribute [local instance] ltOfOrd
variable {G H α β : Type} [Zero G] [One G] [Add G] [Neg G] [Sub G] [Mul G] [DecidableEq G] [Ord α]

def reverseAux (s acc : LSum G α) : LSum G α :=
  match s with
  | .nil => acc
  | .cons g a s => reverseAux s (.cons g a acc)

def reverse (s : LSum G α) : LSum G α := reverseAux s .nil

@[specialize]
def mapAux (f : G → H) (f' : α → β) : LSum G α → LSum H β → LSum H β
  | .nil => reverse
  | .cons g a s => (mapAux f f' s <| .cons (f g) (f' a) ·)

/-- Require that `f g = 0 → g = 0`. -/
@[specialize]
def map (f : G → H) (f' : α → β) (s : LSum G α) : LSum H β := mapAux f f' s .nil

@[specialize]
partial def addAux (s₁ s₂ acc : LSum G α) : LSum G α :=
  match s₁ with
  | .nil => reverseAux acc s₂
  | .cons g₁ a₁ t₁ =>
    match s₂ with
    | .nil => reverseAux acc s₁
    | .cons g₂ a₂ t₂ =>
      match compare a₁ a₂ with
      | .lt => addAux t₁ s₂ (.cons g₁ a₁ acc)
      | .eq =>
        if g₁ + g₂ = 0 then
          addAux t₁ t₂ (.cons (g₁ + g₂) a₁ acc)
        else
          addAux t₁ t₂ acc
      | .gt => addAux s₁ t₂ (.cons g₂ a₂ acc)

@[specialize]
partial def subAux (s₁ s₂ acc : LSum G α) : LSum G α :=
  match s₁ with
  | .nil => reverseAux acc s₂
  | .cons g₁ a₁ t₁ =>
    match s₂ with
    | .nil => reverseAux acc s₁
    | .cons g₂ a₂ t₂ =>
      match compare a₁ a₂ with
      | .lt => subAux t₁ s₂ (.cons g₁ a₁ acc)
      | .eq =>
        if g₁ = g₂ then
          subAux t₁ t₂ (.cons (g₁ - g₂) a₁ acc)
        else
          subAux t₁ t₂ acc
      | .gt => subAux s₁ t₂ (.cons g₂ a₂ acc)

instance : Zero (LSum G α) := ⟨.nil⟩

instance : Coe α (LSum G α) := ⟨fun a => .cons 1 a .nil⟩

@[inline] instance : Neg (LSum G α) := ⟨fun a => a.map (-·) id⟩

@[inline] instance : SMul G (LSum G α) := ⟨fun g a => a.map (g * ·) id⟩

@[inline] instance : Add (LSum G α) := ⟨fun a b => addAux a b .nil⟩

@[inline] instance : Sub (LSum G α) := ⟨fun a b => subAux a b .nil⟩

end LSum

structure LComb (G H α π : Type) where
  sum : LSum G α
  const : H
  pf : LSum G π

-- namespace LComb

-- variable {G H α : Type} [Zero G] [Add G] [Neg G] [Sub G] [Mul G] [DecidableEq G] [Ord α]

-- def nil [Zero H] : LComb G H α := ⟨.nil, 0⟩
-- def cons (g : G) (a : α) (comb : LComb G H α) : LComb G H α :=
--   match comb with
--   | ⟨s, c⟩ => ⟨.cons g a s, c⟩

-- instance [Zero H] : Zero (LComb G H α) := ⟨nil⟩

-- @[inline] instance [Neg H] : Neg (LComb G H α) := ⟨fun ⟨s, c⟩ => ⟨-s, -c⟩⟩

-- @[inline] instance [SMul G H] : SMul G (LComb G H α) := ⟨fun g ⟨s, c⟩ => ⟨g • s, g • c⟩⟩

-- @[inline] instance [Add H] : Add (LComb G H α) := ⟨fun ⟨s, c⟩ ⟨s', c'⟩ => ⟨s + s', c + c'⟩⟩

-- @[inline] instance [Sub H] : Sub (LComb G H α) := ⟨fun ⟨s, c⟩ ⟨s', c'⟩ => ⟨s - s', c - c'⟩⟩

-- end LComb

structure IntCombContext (G α π : Type) [BEq α] [Hashable α] where
  ctx : Std.HashMap α (Int × LComb Int G α π)

namespace IntCombContext

variable {G α π} [Add G] [Sub G] [SMul Int G] [BEq α] [Hashable α] [Ord α] [Ord π]

variable (ref : IO.Ref (IntCombContext G α π))

partial def simplifyAux (sum : LSum Int α) (g : G) (pf : LSum Int π) (acc : LSum Int α) : IO (LComb Int G α π) := do
  match sum with
  | .nil => return ⟨acc.reverse, g, pf⟩
  | .cons n a sum =>
    let ⟨ctx⟩ ← ref.get
    match ctx[a]? with
    | none => simplifyAux sum g pf (.cons n a acc)
    | some (a_n, ⟨a_sum, a_g, a_pf⟩) =>
      ref.modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
      let a_new@⟨a_sum, a_g, a_pf⟩ ← simplifyAux a_sum a_g a_pf .nil
      ref.modify fun ⟨ctx⟩ => ⟨ctx.insert a (a_n, a_new)⟩

      let div := n / a_n
      if div = 0 then
        simplifyAux sum g pf (.cons n a acc)
      else
        let n := n % a_n
        simplifyAux (sum - div • a_sum) (g - div • a_g) (pf - div • a_pf) (if n = 0 then acc else .cons n a acc)

def simplify (sum : LSum Int α) (g : G) (pf : LSum Int π) : IO (LComb Int G α π) :=
  simplifyAux ref sum g pf .nil

variable [Zero G] [DecidableEq G]

partial def insert (comb : LComb Int G α π) : IO (Option (LSum Int π)) := do
  match comb with
  | ⟨.nil, g, pf⟩ => if g = 0 then return none else return pf
  | ⟨.cons n a sum, g, pf⟩ =>
    let ⟨ctx⟩ ← ref.get
    match ctx[a]? with
    | none =>
      let red ← simplify ref sum g pf
      ref.modify fun ⟨ctx⟩ => ⟨ctx.insert a (n, red)⟩
      return none
    | some (a_n, ⟨a_sum, a_g, a_pf⟩) =>
      if n % a_n = 0 then
        insert ⟨sum - (n / a_n) • a_sum, g - (n / a_n) • a_g, pf - (n / a_n) • a_pf⟩
      else
        ref.modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
        let (gcd, x, y) := Int.xgcd n a_n
        let red ← simplify ref (x • sum + y • a_sum) (x • g + y • a_g) (x • pf + y • a_pf)
        ref.modify fun ⟨ctx⟩ => ⟨ctx.insert a (gcd, red)⟩
        insert ⟨sum - (n / gcd) • red.sum, g - (n / gcd) • red.const, pf - (n / gcd) • red.pf⟩

end IntCombContext


structure RatCombContext (G α π : Type) [BEq α] [Hashable α] where
  ctx : Std.HashMap α (LComb Rat G α π)

namespace RatCombContext

variable {G α π} [Add G] [Sub G] [SMul Rat G] [BEq α] [Hashable α] [Ord α] [Ord π]

variable (ref : IO.Ref (RatCombContext G α π))

partial def simplifyAux (sum : LSum Rat α) (g : G) (pf : LSum Rat π) (acc : LSum Rat α) : IO (LComb Rat G α π) := do
  match sum with
  | .nil => return ⟨acc.reverse, g, pf⟩
  | .cons n a sum =>
    let ⟨ctx⟩ ← ref.get
    match ctx[a]? with
    | none => simplifyAux sum g pf (.cons n a acc)
    | some ⟨a_sum, a_g, a_pf⟩ =>
      ref.modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
      let a_new@⟨a_sum, a_g, a_pf⟩ ← simplifyAux a_sum a_g a_pf .nil
      ref.modify fun ⟨ctx⟩ => ⟨ctx.insert a a_new⟩
      simplifyAux (sum - n • a_sum) (g - n • a_g) (pf - n • a_pf) acc

def simplify (sum : LSum Rat α) (g : G) (pf : LSum Rat π) : IO (LComb Rat G α π) :=
  simplifyAux ref sum g pf .nil

variable [Zero G] [DecidableEq G]

partial def insert (comb : LComb Rat G α π) : IO (Option (LSum Rat π)) := do
  match comb with
  | ⟨.nil, g, pf⟩ => if g = 0 then return none else return pf
  | ⟨.cons n a sum, g, pf⟩ =>
    let sum := n⁻¹ • sum
    let g := n⁻¹ • g
    let pf := n⁻¹ • pf
    let ⟨ctx⟩ ← ref.get
    match ctx[a]? with
    | none =>
      let red ← simplify ref sum g pf
      ref.modify fun ⟨ctx⟩ => ⟨ctx.insert a red⟩
      return none
    | some ⟨a_sum, a_g, a_pf⟩ =>
      insert ⟨sum - a_sum, g - a_g, pf - a_pf⟩

end RatCombContext
