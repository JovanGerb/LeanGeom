import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

notation "∠" A:max B:max => Complex.orientation.oangle A B


-- #check  AddCircle.equivAddCircle

/-
first use simp with `equivAddCircle` to cast into `AddCircle 1`, and push the cast.
then, use a simproc to swap rays to be sorted.
and, use simp to push `equivAddCircle` through casts from `ℝ` involving `π`.
And finally, call `abel`
-/

/-
For distances with multiplication, use `log` to cast it into something additive, and a positivity side goal.
-/
