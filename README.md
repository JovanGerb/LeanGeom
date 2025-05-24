# LeanGeom

This repository is an attempt at implementing a version of DDAR (as described in the Alpha Geometry paper), in the form of a Lean-tactic, fully implemented in Lean.

The tactic, `lean_geom`, produces the solution in the form of a tactic script, which is then run to solve the problem.

The tactic is meant to work with mathlib's conventions for how to state geometry problems, using a `NormedAddTorsor`. However, the first version of the tactic just works for points in the complex numbers.