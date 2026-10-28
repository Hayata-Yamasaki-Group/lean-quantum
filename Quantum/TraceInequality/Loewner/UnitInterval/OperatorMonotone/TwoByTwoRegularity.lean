import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.EntrywisePipeline
import Quantum.Analysis.Calculus.SharedSecantFilter
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 3 two-by-two regularity and secant inputs

This file contains the two-by-two CFC order comparison and the regularity
input `TwoByTwoRegularityInput`.  Differentiability itself is proved by a secant
squeeze in `twoByTwoRegularityInput_closed` (`HiaiRegularity.lean`).
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/--
Full `2×2` CFC order comparison obtained by specializing finite matrix
monotonicity.

This is not a one-parameter rank-one order ray.  It is the full `M₂` order
comparison used by the book regularity theorem that `2`-monotone functions are
differentiable on the open interval.
-/
theorem twoByTwo_cfc_orderComparison_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {A B : CStarMatrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ cStarFiniteMatrixDomain 2)
    (hB : B ∈ cStarFiniteMatrixDomain 2)
    (hAB : A ≤ B) :
    cfcₙ (fun t : ℝ => f t - f 0) A ≤
      cfcₙ (fun t : ℝ => f t - f 0) B := by
  exact hfinite.cfc_monotone_matrix 2 hA hB hAB

/--
Book-side `2×2` regularity input, in the normalized CFC form used in this file.

This is the Hiai Chapter 13 Proposition 1.16(1) statement: a function satisfying
full `2×2` matrix monotonicity on `(-1,1)` is differentiable on the open
interval.  The structure records that regularity theorem as an explicit input;
it is proved as `twoByTwoRegularityInput_closed` in `HiaiRegularity.lean`.
-/
structure TwoByTwoRegularityInput : Prop where
  differentiableOn_of_twoByTwo_cfc_order :
    ∀ {f : ℝ → ℝ},
      (∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B) →
        DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)

/--
The book `2×2` regularity theorem supplies the differentiability producer for
the operator-monotonicity-to-Löwner-positivity theorem.
-/
def operatorMonotoneDifferentiabilityInput_of_twoByTwoRegularityInput
    (input : TwoByTwoRegularityInput) :
    OperatorMonotoneDifferentiabilityInput where
  differentiable := by
    intro f h
    apply input.differentiableOn_of_twoByTwo_cfc_order
    intro A B hA hB hAB
    exact twoByTwo_cfc_orderComparison_of_finiteMatrixMonotone
      (unitIntervalMatrixMonotone_of_finiteMatrixMonotone
        (finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval h))
      hA hB hAB

end

end Quantum.TraceInequality.Loewner
