import Quantum.TraceInequality.LownerHeinzCore

namespace Quantum.TraceInequality.Loewner

universe u

/--
Theorem-facing operator convexity on the closed positive half-line.

This is an alias for the existing `LownerHeinzCore` uniform CFC predicate,
not a new Loewner-specific definition.
-/
abbrev OperatorConvexOnClosedPositive (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOnAll.{0} (Set.Ici (0 : ℝ)) f

end Quantum.TraceInequality.Loewner
