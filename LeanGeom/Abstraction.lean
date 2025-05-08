import Mathlib.Logic.Equiv.Defs

namespace LeanGeom

class Atomic (α : Type) extends Inhabited α, BEq α, LawfulBEq α, Hashable α, Ord α where

class EqType (α : Type) where
  EqProof : α → α → Type
  refl (a) : EqProof a a
  symm {a b} : EqProof a b → EqProof b a
  trans {a b c} : EqProof a b → EqProof b c → EqProof a c
export EqType (EqProof)
alias EqType.EqProof.refl := EqType.refl
alias EqType.EqProof.symm := EqType.symm
alias EqType.EqProof.trans := EqType.trans

instance {α} [EqType α] (a : α) : Inhabited (Σ b, EqProof a b) := ⟨a, .refl a⟩


class HasAtom (α : Type) where
  Atom : Type
  instAtomic : Atomic Atom := by infer_instance
  toAtom : α → Atom
export HasAtom (Atom toAtom)
attribute [instance] HasAtom.instAtomic

instance instEqTypeOfAtom {α} [HasAtom α] [EqType (Atom α)] : EqType α where
  EqProof a b := EqProof (toAtom a) (toAtom b)
  refl a := .refl (toAtom a)
  symm   := .symm
  trans  := .trans

/-- An instance can also be constructed via `instObjectOfEqType`. -/
class Object (α : Type) extends HasAtom α where
  instEqTypeAtom : EqType Atom

  instEqType : EqType α := instEqTypeOfAtom
  of_atomEqProof {a b} : EqProof (toAtom a) (toAtom b) → EqProof a b := by exact id
  to_atomEqProof {a b} : EqProof a b → EqProof (toAtom a) (toAtom b) := by exact id

attribute [instance] Object.instEqTypeAtom Object.instEqType

inductive HasAtom.EqProof' {α} [HasAtom α] [EqType α] : (a b : Atom α) → Type where
| refl {a b} : a = b → HasAtom.EqProof' a b
| mk {a b} {left right : α} (h_left : toAtom left = a) (h_right : toAtom right = b)
    (h : EqProof left right) : HasAtom.EqProof' a b

/-
abbrev instEqTypeAtom' {α} [HasAtom α] [EqType α]
    (h_atom : ∀ {a b a' b' : α}, toAtom a = toAtom a' → toAtom b = toAtom b' → EqProof a b → EqProof a' b') : EqType (Atom α) where
  EqProof := HasAtom.EqProof'
  refl _ := .refl rfl
  symm
    | .refl h => .refl h.symm
    | .mk h_left h_right h => .mk h_right h_left h.symm
  trans
    | .refl h => fun eq => h ▸ eq
    | eq@(.mk h_left h_right h) => fun
      | .refl h => h ▸ eq
      | .mk h_left' h_right' h' => .mk h_left h_right' (h.trans (h_atom (h_left'.trans h_right.symm) rfl h'))

abbrev instObjectOfEqType {α} [HasAtom α] [EqType α]
    (h_atom : ∀ {a b a' b' : α}, toAtom a = toAtom a' → toAtom b = toAtom b' → EqProof a b → EqProof a' b') : Object α where
  instAtomEqType := instEqTypeAtom' h_atom
  instEqType := ‹_›
  of_atomEqProof i := by
    cases i with
    | refl h => exact h_atom h.symm rfl (.refl _)
    | mk h_left h_right h => exact h_atom h_left h_right h
  to_atomEqProof h := .mk rfl rfl h
-/

section Eq

abbrev unitEqType {α} : EqType α where
  EqProof a b := PLift (a = b)
  refl _ := ⟨rfl⟩
  symm | ⟨rfl⟩ => ⟨rfl⟩
  trans | ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

def EqAtom (α : Type) := α

instance {α} [Atomic α] : Object (EqAtom α) where
  Atom := α
  instEqTypeAtom := unitEqType
  toAtom := id

end Eq


class Abstraction (m : Type → Type) (α : outParam Type) (β : Type) [Object α] [Object β] where
  represent : α → m β
  original : β → α
  proveEq a b : EqProof a b → Thunk (EqProof (original a) (original b))

class AbstractionT (m : Type → Type) (α : semiOutParam Type) (β : Type) [Object α] [Object β] where
  represent : α → m β
  original : β → α
  proveEq a b : EqProof a b → Thunk (EqProof (original a) (original b))

section
variable {m : Type → Type} {α β γ : Type} [Monad m] [Object α] [Object β] [Object γ]

instance (priority := low) [BEq α] [Object α] : AbstractionT m α α where
  represent a := pure a
  original a := a
  proveEq _ _ := .pure

instance [AbstractionT m α β] [Abstraction m β γ] : AbstractionT m α γ where
  represent := AbstractionT.represent >=> Abstraction.represent
  original := AbstractionT.original m ∘ Abstraction.original m
  proveEq a b := have : Bind Thunk := ⟨.bind⟩; Abstraction.proveEq a b >=> AbstractionT.proveEq _ _
end

abbrev baseObject {α} [i : EqType α] [Atomic α] : Object α where
  Atom := α
  toAtom a := a
  instEqType := i
  instEqTypeAtom := i

class BaseObject (m : Type → Type) (α : Type) [Atomic α] [Object α] where
  Abstraction : Type
  inst₁ : Object Abstraction := by infer_instance
  inst₂ : AbstractionT m α Abstraction := by infer_instance

attribute [instance] BaseObject.inst₁

variable {m : Type → Type} {α : Type} [Monad m] [Atomic α] [Object α] [i : BaseObject m α]

def represent := i.inst₂.represent
def original := i.inst₂.original
def proveEq := i.inst₂.proveEq
