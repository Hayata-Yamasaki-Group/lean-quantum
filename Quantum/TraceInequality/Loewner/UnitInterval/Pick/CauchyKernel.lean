import Quantum.TraceInequality.Loewner.UnitInterval.Pick.MeasureRecoveryDischarge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Distributions.Cauchy

/-!
# Chapter 3 concrete Cauchy-kernel inputs

This module supplies the concrete Cauchy-kernel domination estimates used by
the Proposition 3.5 discharge step.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Concrete Cauchy-kernel inputs -/

/--
The normalized Proposition 3.5 kernel is the Cauchy density at location `y`
and scale `ε`, multiplied by the book weight `(1 + y^2)/(1 + x^2)`.
-/
theorem unitIntervalHerglotzProp35TestKernel_eq_weighted_cauchyPDFReal
    {ε x y : ℝ} (hε : 0 ≤ ε) :
    unitIntervalHerglotzProp35TestKernel ε x y =
      ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹) *
        ProbabilityTheory.cauchyPDFReal y ⟨ε, hε⟩ x := by
  unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
  rw [ProbabilityTheory.cauchyPDFReal_def]
  simp
  ring_nf

/--
An elementary pointwise domination of the normalized Proposition 3.5 kernel by
the sum of a Cauchy density and the fixed integrable density `(1+x^2)^{-1}`.
-/
theorem unitIntervalHerglotzProp35TestKernel_norm_pointwise_bound
    {ε x y : ℝ} (hε : 0 < ε) :
    ‖unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      2 * ((Real.pi)⁻¹ * ε / ((x - y) ^ (2 : ℕ) + ε ^ (2 : ℕ))) +
        2 * ((Real.pi)⁻¹ * ε * (1 + x ^ (2 : ℕ))⁻¹) := by
  have hnonneg := unitIntervalHerglotzProp35TestKernel_nonneg hε (x := x) (y := y)
  rw [Real.norm_of_nonneg hnonneg]
  unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
  have hden1 : 0 < (x - y) ^ (2 : ℕ) + ε ^ (2 : ℕ) := by
    positivity
  have hden2 : 0 < 1 + x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg x]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hy :
      1 + y ^ (2 : ℕ) ≤
        2 * (1 + x ^ (2 : ℕ)) + 2 * ((x - y) ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg (y - 2 * x)]
  rw [div_eq_mul_inv]
  field_simp [hε.ne', hden1.ne', hden2.ne', hpi.ne']
  nlinarith [sq_nonneg ε, hy]

/--
Concrete Cauchy-kernel domination: for `0 < ε ≤ 1`, the `x`-integral of the
normalized Proposition 3.5 kernel is bounded uniformly in `y`.
-/
theorem unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_four
    {ε y : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) :
    (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 := by
  let A : ℝ → ℝ := fun x =>
    2 * ((Real.pi)⁻¹ * ε / ((x - y) ^ (2 : ℕ) + ε ^ (2 : ℕ)))
  let B : ℝ → ℝ := fun x =>
    2 * ((Real.pi)⁻¹ * ε * (1 + x ^ (2 : ℕ))⁻¹)
  have hA_int : Integrable A (volume : Measure ℝ) := by
    exact (ProbabilityTheory.integrable_cauchyPDFReal y (γ := ⟨ε, hε.le⟩)).const_mul 2
  have hB_int : Integrable B (volume : Measure ℝ) := by
    exact (integrable_inv_one_add_sq.const_mul ((Real.pi)⁻¹ * ε)).const_mul 2
  have hAB_int : Integrable (fun x : ℝ => A x + B x) (volume : Measure ℝ) :=
    hA_int.add hB_int
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
        (volume : Measure ℝ) := by
    have hm : Measurable
        (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖) := by
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound_all :
      ∀ x : ℝ,
        ‖unitIntervalHerglotzProp35TestKernel ε x y‖ ≤ A x + B x := by
    intro x
    dsimp [A, B]
    exact unitIntervalHerglotzProp35TestKernel_norm_pointwise_bound hε
  have hleft_int :
      Integrable
        (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
        (volume : Measure ℝ) := by
    refine hAB_int.mono' hmeas ?_
    filter_upwards with x
    simpa using hbound_all x
  have hA_int_eval : (∫ x : ℝ, A x) = 2 := by
    have hc :
        (∫ x : ℝ, (Real.pi)⁻¹ * ε / ((x - y) ^ (2 : ℕ) + ε ^ (2 : ℕ))) = 1 :=
      ProbabilityTheory.integral_cauchyPDFReal_eq_one y
        (γ := ⟨ε, hε.le⟩) (Subtype.ext_iff.not.mpr hε.ne')
    simp [A, integral_const_mul, hc]
  have hB_int_eval : (∫ x : ℝ, B x) = 2 * ε := by
    have hb :
        (∫ x : ℝ, (Real.pi)⁻¹ * ε * (1 + x ^ (2 : ℕ))⁻¹) = ε := by
      calc
        (∫ x : ℝ, (Real.pi)⁻¹ * ε * (1 + x ^ (2 : ℕ))⁻¹)
            = (Real.pi)⁻¹ * ε *
                (∫ x : ℝ, (1 + x ^ (2 : ℕ))⁻¹) := by
              rw [integral_const_mul]
        _ = ε := by
          rw [integral_univ_inv_one_add_sq]
          field_simp [Real.pi_ne_zero]
    simp [B, integral_const_mul, hb]
  calc
    (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
        ≤ ∫ x : ℝ, (A x + B x) := by
          exact integral_mono hleft_int hAB_int hbound_all
    _ = (∫ x : ℝ, A x) + ∫ x : ℝ, B x := by
          rw [integral_add hA_int hB_int]
    _ ≤ 4 := by
          rw [hA_int_eval, hB_int_eval]
          nlinarith

/-- Concrete supplier for the measure-recovery `x`-integral domination contract. -/
theorem unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete
    {ε y : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) :
    (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 :=
  unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound 4
    (fun hε hε_le =>
      unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_four hε hε_le)
    hε hε_le

end

end Quantum.TraceInequality.Loewner
