import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HiaiInterlacing
import Quantum.Analysis.Calculus.SharedSecantFilter

/-!
# Chapter 3 Hiai regularity closure

This file contains the final Hiai regularity closure of the Chapter 3 hard
direction: secant-limit packaging, the closed two-by-two regularity input, the
public `loewnerPosOnUnitInterval_of_operatorMonotone` wrapper, and the retained
one-sided secant diagnostic alternative.
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

lemma secant_tendsto_nhdsWithin_Ioo_punctured_of_left_right
    {f : ℝ → ℝ} {x D : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hleft :
      Filter.Tendsto (slope f x) (𝓝[Set.Ioo (-1 : ℝ) x] x) (𝓝 D))
    (hright :
      Filter.Tendsto (slope f x) (𝓝[Set.Ioo x (1 : ℝ)] x) (𝓝 D)) :
    Filter.Tendsto (slope f x)
      (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D) := by
  have hleftSet :
      Set.Ioo (-1 : ℝ) 1 ∩ Set.Iio x = Set.Ioo (-1 : ℝ) x := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      exact ⟨⟨hy.1, lt_trans hy.2 hx.2⟩, hy.2⟩
  have hrightSet :
      Set.Ioo (-1 : ℝ) 1 ∩ Set.Ioi x = Set.Ioo x (1 : ℝ) := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.2, hy.1.2⟩
    · intro hy
      exact ⟨⟨lt_trans hx.1 hy.1, hy.2⟩, hy.1⟩
  have hleft' :
      Filter.Tendsto (slope f x)
        (𝓝[Set.Ioo (-1 : ℝ) 1 ∩ Set.Iio x] x) (𝓝 D) := by
    simpa [hleftSet] using hleft
  have hright' :
      Filter.Tendsto (slope f x)
        (𝓝[Set.Ioo (-1 : ℝ) 1 ∩ Set.Ioi x] x) (𝓝 D) := by
    simpa [hrightSet] using hright
  rw [← nhdsWithinLT_sup_nhdsWithinGT (s := Set.Ioo (-1 : ℝ) 1) x]
  exact hleft'.sup hright'

/--
Matching one-sided secant limits give the punctured secant limit needed for
differentiability.
-/
theorem twoByTwo_cfc_order_secant_left_right_bound
    {f : ℝ → ℝ}
    {x D : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hleft :
      Filter.Tendsto (slope f x) (𝓝[Set.Ioo (-1 : ℝ) x] x) (𝓝 D))
    (hright :
      Filter.Tendsto (slope f x) (𝓝[Set.Ioo x (1 : ℝ)] x) (𝓝 D)) :
    Filter.Tendsto (slope f x)
      (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D) := by
  exact secant_tendsto_nhdsWithin_Ioo_punctured_of_left_right
    hx hleft hright

/--
Punctured secant limits at every interior point give differentiability on the
open interval.
-/
theorem twoByTwo_cfc_order_secant_tendsto
    {f : ℝ → ℝ}
    (hsec :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ D : ℝ,
          Filter.Tendsto (slope f x)
            (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D)) :
    DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  rcases hsec x hx with ⟨D, hD⟩
  exact (hasDerivWithinAt_iff_tendsto_slope.mpr hD).differentiableWithinAt

/--
Matching left and right secant limits at every interior point suffice.  This is
the scalar squeeze shape used by the closed Hiai `2`-monotone regularity theorem
after scalar continuity.
-/
theorem twoByTwo_cfc_order_secant_left_right_squeeze
    {f : ℝ → ℝ}
    (hsec :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ D : ℝ,
          Filter.Tendsto (slope f x) (𝓝[Set.Ioo (-1 : ℝ) x] x) (𝓝 D) ∧
            Filter.Tendsto (slope f x) (𝓝[Set.Ioo x (1 : ℝ)] x) (𝓝 D)) :
    DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1) := by
  refine twoByTwo_cfc_order_secant_tendsto ?_
  intro x hx
  rcases hsec x hx with ⟨D, hleft, hright⟩
  exact ⟨D,
    twoByTwo_cfc_order_secant_left_right_bound hx hleft hright⟩

/--
The Hiai cross-secant estimate supplies the punctured secant limit under full
`2×2` CFC order comparison.
-/
theorem twoByTwo_cfc_order_secant_tendsto_of_hiai_cross
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ D : ℝ,
      Filter.Tendsto (slope f x)
        (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D) :=
  secant_tendsto_of_localOscillation hx
    (twoByTwo_cfc_order_secant_localOscillation_of_hiai_cross h2 hx)

/--
The Hiai squeeze gives matching one-sided secant limits at every interior
point.  The common value is obtained from the punctured secant limit.
-/
theorem twoByTwo_cfc_order_secant_commonLimit_of_hiai_squeeze
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ D : ℝ,
        Filter.Tendsto (slope f x) (𝓝[Set.Ioo (-1 : ℝ) x] x) (𝓝 D) ∧
          Filter.Tendsto (slope f x) (𝓝[Set.Ioo x (1 : ℝ)] x) (𝓝 D) := by
  intro x hx
  rcases twoByTwo_cfc_order_secant_tendsto_of_hiai_cross h2 hx with
    ⟨D, hD⟩
  refine ⟨D, ?_, ?_⟩
  · have hsubset :
        Set.Ioo (-1 : ℝ) x ⊆ Set.Ioo (-1 : ℝ) 1 \ {x} := by
      intro y hy
      exact ⟨⟨hy.1, lt_trans hy.2 hx.2⟩, hy.2.ne⟩
    exact hD.mono_left (nhdsWithin_mono x hsubset)
  · have hsubset :
        Set.Ioo x (1 : ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 \ {x} := by
      intro y hy
      exact ⟨⟨lt_trans hx.1 hy.1, hy.2⟩, hy.1.ne'⟩
    exact hD.mono_left (nhdsWithin_mono x hsubset)

/--
Closed Hiai `2`-monotone regularity input in the normalized `2×2` CFC form.
-/
def twoByTwoRegularityInput_closed : TwoByTwoRegularityInput where
  differentiableOn_of_twoByTwo_cfc_order := by
    intro f h2
    exact twoByTwo_cfc_order_secant_left_right_squeeze
      (twoByTwo_cfc_order_secant_commonLimit_of_hiai_squeeze h2)

/-- Full finite-matrix monotonicity supplies differentiability on the open interval. -/
theorem differentiableOn_Ioo_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hmatrix : UnitIntervalMatrixMonotone f) :
    DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1) := by
  apply twoByTwoRegularityInput_closed.differentiableOn_of_twoByTwo_cfc_order
  intro A B hA hB hAB
  exact twoByTwo_cfc_orderComparison_of_finiteMatrixMonotone
    hmatrix hA hB hAB

/-- Full finite-matrix monotonicity supplies finite-dimensional Löwner positivity. -/
theorem loewnerPosOnUnitInterval_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hmatrix : UnitIntervalMatrixMonotone f) :
    LoewnerPosOnUnitInterval f := by
  let input :=
    quadraticFormMatrixInput_of_separatedEntrywiseVariationInput
      (separatedEntrywiseVariationInput_of_rawEntrywiseVariationInput
        (rawEntrywiseVariationInput_of_polynomialApproximationInput
          (polynomialApproximationInput_of_hermitePolynomialApproximationInput
            (hermitePolynomialApproximationInput_of_hermiteRemainderInput
              (hermiteRemainderInput_of_remainderEstimateInput
                (diagonalCFCHermiteRemainderEstimateInput_of_differentiable
                  (differentiableOn_Ioo_of_finiteMatrixMonotone hmatrix)))))))
  exact
    { differentiable := input.differentiable
      posSemidef := by
        intro n x hx hinj
        exact loewnerMatrix_posSemidef_of_quadratic_nonneg
          (input.quadratic_nonneg_of_matrixMonotone hmatrix n x hx hinj) }

/--
Public wrapper: operator monotonicity on the normalized interval implies
finite-dimensional Löwner positivity.
-/
theorem loewnerPosOnUnitInterval_of_operatorMonotone
    {f : ℝ → ℝ} (h : OperatorMonotoneOnUnitInterval.{0} f) :
    LoewnerPosOnUnitInterval f :=
  loewnerPosOnUnitInterval_of_finiteMatrixMonotone
    (unitIntervalMatrixMonotone_of_finiteMatrixMonotone
      (finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval h))
end

end Quantum.TraceInequality.Loewner
