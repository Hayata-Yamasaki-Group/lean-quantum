import ComparatorChallenges.Solution
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HiaiRegularity

/-!
# Paper 2 headline: the four equivalent Löwner conditions

An exact wrapper around the existing comparator and the reverse library root.
The three biconditionals connect all four predicates; they do not assert that
an arbitrary function satisfies any of them. The universe reduction in the
reverse direction is the same one used by the existing comparator.
-/

namespace ComparatorChallenges

open Quantum.TraceInequality.Loewner

universe u

/-- Löwner positivity, Pick extension, integral representation, and operator
monotonicity on the normalized interval are equivalent.
This formalization combines the three conditions of Simon, *Loewner's Theorem on
Monotone Matrix Functions* (2019), Theorem 1.3, with the characterization by
positive semidefinite Löwner matrices for C¹ functions in Theorem 5.1; the Lean condition
`LoewnerPosOnUnitInterval` assumes differentiability on (-1,1) instead. The four
characterizations are organized here, rather than stated as a single theorem in
Simon. Operator monotonicity is generalized from finite matrices to the
non-unital C*-algebra CFC formulation; the claim depends only on (-1,1). -/
theorem loewnerUnitIntervalFourConditions {f : ℝ → ℝ} :
    (LoewnerPosOnUnitInterval f ↔ Nonempty (PickExtensionOnUnitInterval f)) ∧
    (Nonempty (PickExtensionOnUnitInterval f) ↔ Nonempty (IntegralRepOnUnitInterval f)) ∧
    (Nonempty (IntegralRepOnUnitInterval f) ↔ OperatorMonotoneOnUnitInterval.{u} f) := by
  obtain ⟨hmono, hpick, hpos⟩ := loewnerUnitIntervalCharacterizations.{u} (f := f)
  refine ⟨⟨?_, ?_⟩, hpick, hmono.symm⟩
  · intro h
    exact hpick.mpr (hmono.mp (hpos h))
  · intro h
    exact loewnerPosOnUnitInterval_of_operatorMonotone
      (operatorMonotoneOnUnitInterval_toZero (hmono.mpr (hpick.mp h)))

end ComparatorChallenges
