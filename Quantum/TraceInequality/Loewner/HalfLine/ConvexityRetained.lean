import Quantum.Analysis.Calculus.ClosedPositiveOperatorConvexity
import Quantum.TraceInequality.Loewner.HalfLine.ConvexRep
import Quantum.TraceInequality.LownerHeinzCore

/-!
# Positive-ray operator convexity interfaces

This module provides theorem-facing names for the Loewner half-line layer.
The actual operator convexity and concavity predicates are the existing
`LownerHeinzCore` definitions; this file does not introduce a parallel notion.
-/

namespace Quantum.TraceInequality.Loewner

universe u

/--
Theorem-facing operator convexity on the open positive half-line.

This is an alias for the existing `LownerHeinzCore` uniform CFC predicate,
not a new Loewner-specific definition.
-/
abbrev OperatorConvexOnPositive (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOnAll.{0} (Set.Ioi (0 : ℝ)) f

/--
Theorem-facing operator concavity on the open positive half-line.

This is an alias for the existing `LownerHeinzCore` uniform CFC predicate,
not a new Loewner-specific definition.
-/
abbrev OperatorConcaveOnPositive (h : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOnAll.{0} (Set.Ioi (0 : ℝ)) h

end Quantum.TraceInequality.Loewner
