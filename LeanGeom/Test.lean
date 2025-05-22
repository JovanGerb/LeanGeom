import LeanGeom.AngleArith
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

open Orientation

local instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

noncomputable def o := Complex.orientation

local notation "∠" A:max B:max => Complex.orientation.oangle A B

example (A B C D E F P : ℂ)
    (h₁ : ∠ A E - ∠ A F - ∠ P E + ∠ P F = 0)
    (h₂ : ∠ B F - ∠ B D - ∠ P F + ∠ P D = 0)
    (h₃ : ∠ C D - ∠ C E - ∠ P D + ∠ P E = 0)
    (l₁ : ∠ A E = ∠ C E) (l₂ : ∠ A F = ∠ B F)
    (nl₃ : ¬∠ B D = ∠ C D) : False := by
  have h_1 : ∠ B D = ∠ C D := by linear_combination (norm := abel) -h₁ - h₂ - h₃ + l₁ - l₂
  absurd nl₃
  exact h_1

example (A B C D E F P : ℂ)
    (h : ∠ B D = ∠ C D) :
    ∠ B D = ∠ C D := by
  linear_combination (norm := abel) h
