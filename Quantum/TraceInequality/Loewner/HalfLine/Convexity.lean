import Quantum.TraceInequality.Loewner.HalfLine.ConvexRep
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Positive-ray operator convexity interfaces

This module provides theorem-facing names for the Loewner half-line layer.
The actual operator convexity and concavity predicates are the existing
`LownerHeinzCore` definitions; this file does not introduce a parallel notion.
-/

namespace Quantum.TraceInequality.Loewner

universe u

/--
The quotient transform appearing in Hiai Proposition 2.33.

Only values on `(0,∞)` are mathematically relevant in the operator monotonicity
statement; Lean's value at `0` is the ordinary real division value.
-/
noncomputable def positiveRayDivTransform (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x : ℝ => f x / x

end Quantum.TraceInequality.Loewner
