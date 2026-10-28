import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Uniqueness of normalized interval integral representations

This file contains the measure-uniqueness layer for
`IntegralRepOnUnitInterval`.  It is kept separate from the operator-monotone
consumer so that the half-line uniqueness theorem can reuse it without
touching the CFC proof.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped Topology
open scoped Polynomial

noncomputable section

private def unitIntervalMomentStep (m : ℕ) : ℝ :=
  ((m : ℝ) + 2)⁻¹

private theorem unitIntervalMomentStep_pos (m : ℕ) :
    0 < unitIntervalMomentStep m := by
  unfold unitIntervalMomentStep
  positivity

private theorem unitIntervalMomentStep_le_half (m : ℕ) :
    unitIntervalMomentStep m ≤ (1 / 2 : ℝ) := by
  unfold unitIntervalMomentStep
  have hden : (2 : ℝ) ≤ (m : ℝ) + 2 := by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  simpa [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2) hden

private theorem unitIntervalMomentStep_mem_Ioo (m : ℕ) :
    unitIntervalMomentStep m ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · have hpos := unitIntervalMomentStep_pos m
    linarith
  · have hle := unitIntervalMomentStep_le_half m
    linarith

private theorem unitIntervalMomentStep_ne_zero (m : ℕ) :
    unitIntervalMomentStep m ≠ 0 :=
  (unitIntervalMomentStep_pos m).ne'

private theorem tendsto_unitIntervalMomentStep_zero :
    Tendsto unitIntervalMomentStep atTop (𝓝 (0 : ℝ)) := by
  simpa [unitIntervalMomentStep, one_div] using
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))

private theorem unitInterval_resolvent_moment_bound_two
    (n : ℕ) {lambda x : ℝ}
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    (hx_nonneg : 0 ≤ x) (hx_le : x ≤ (1 / 2 : ℝ)) :
    ‖lambda ^ n * (1 + lambda * x)⁻¹‖ ≤ (2 : ℝ) := by
  have hlambda_abs : |lambda| ≤ 1 := abs_le.mpr hlambda
  have hpow : |lambda ^ n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg lambda) hlambda_abs
  have hlambda_mul : -x ≤ lambda * x := by
    have hmul := mul_le_mul_of_nonneg_right hlambda.1 hx_nonneg
    simpa using hmul
  have hden_lower : (1 / 2 : ℝ) ≤ 1 + lambda * x := by
    linarith
  have hden_pos : 0 < 1 + lambda * x := by
    linarith
  have hinv_nonneg : 0 ≤ (1 + lambda * x)⁻¹ := inv_nonneg.mpr hden_pos.le
  have hinv_le : (1 + lambda * x)⁻¹ ≤ (2 : ℝ) := by
    have h :=
      (one_div_le hden_pos (by norm_num : (0 : ℝ) < 2)).2 hden_lower
    simpa [one_div] using h
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hinv_nonneg]
  calc
    |lambda ^ n| * (1 + lambda * x)⁻¹ ≤ 1 * (2 : ℝ) := by
      exact mul_le_mul hpow hinv_le hinv_nonneg (by norm_num)
    _ = 2 := by norm_num

private theorem integrableOn_unitInterval_resolvent_moment
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun lambda : ℝ => lambda ^ n * (1 + lambda * x)⁻¹)
      (Set.Icc (-1 : ℝ) 1) μ := by
  have hcont :
      ContinuousOn (fun lambda : ℝ => lambda ^ n * (1 + lambda * x)⁻¹)
        (Set.Icc (-1 : ℝ) 1) := by
    refine (continuousOn_id.pow n).mul ?_
    refine (continuousOn_const.add (continuousOn_id.mul continuousOn_const)).inv₀ ?_
    intro lambda hlambda
    exact (unitIntervalOperatorKernel_denominator_pos hlambda hx).ne'
  exact hcont.integrableOn_compact isCompact_Icc

private theorem integralRepOnUnitInterval_kernel_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        unitIntervalOperatorKernel lambda x ∂(rep₁.ν : Measure ℝ)) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        unitIntervalOperatorKernel lambda x ∂(rep₂.ν : Measure ℝ) := by
  calc
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        unitIntervalOperatorKernel lambda x ∂(rep₁.ν : Measure ℝ)) =
        f x - f 0 := (rep₁.real_formula_setIntegral hx).symm
    _ =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        unitIntervalOperatorKernel lambda x ∂(rep₂.ν : Measure ℝ) :=
        rep₂.real_formula_setIntegral hx

private theorem integralRepOnUnitInterval_resolvent_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ) := by
  have hkernel := integralRepOnUnitInterval_kernel_setIntegral_eq rep₁ rep₂ hx
  have h₁ :
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          unitIntervalOperatorKernel lambda x ∂(rep₁.ν : Measure ℝ)) =
        x *
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ) := by
    simp [unitIntervalOperatorKernel, div_eq_mul_inv, integral_const_mul]
  have h₂ :
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          unitIntervalOperatorKernel lambda x ∂(rep₂.ν : Measure ℝ)) =
        x *
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ) := by
    simp [unitIntervalOperatorKernel, div_eq_mul_inv, integral_const_mul]
  apply mul_left_cancel₀ hx0
  exact h₁ ▸ h₂ ▸ hkernel

private theorem tendsto_integral_unitInterval_resolvent_moment
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    Tendsto
      (fun m : ℕ =>
        ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ n * (1 + lambda * unitIntervalMomentStep m)⁻¹ ∂μ)
      atTop
      (𝓝 (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1, lambda ^ n ∂μ)) := by
  let s : Set ℝ := Set.Icc (-1 : ℝ) 1
  change
    Tendsto
      (fun m : ℕ =>
        ∫ lambda : ℝ,
          lambda ^ n * (1 + lambda * unitIntervalMomentStep m)⁻¹ ∂(μ.restrict s))
      atTop
      (𝓝 (∫ lambda : ℝ, lambda ^ n ∂(μ.restrict s)))
  refine
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ.restrict s) (bound := fun _ : ℝ => (2 : ℝ)) ?hmeas ?hbound
      ?hbound_int ?hlim
  · exact Filter.Eventually.of_forall fun m =>
      (by fun_prop :
        AEStronglyMeasurable
          (fun lambda : ℝ => lambda ^ n * (1 + lambda * unitIntervalMomentStep m)⁻¹)
          (μ.restrict s))
  · refine Filter.Eventually.of_forall fun m => ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    exact unitInterval_resolvent_moment_bound_two n hlambda
      (unitIntervalMomentStep_pos m).le (unitIntervalMomentStep_le_half m)
  · exact integrable_const (2 : ℝ)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    have hstep := tendsto_unitIntervalMomentStep_zero
    have hden :
        Tendsto (fun m : ℕ => 1 + lambda * unitIntervalMomentStep m)
          atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hstep)
    have hinv :
        Tendsto (fun m : ℕ => (1 + lambda * unitIntervalMomentStep m)⁻¹)
          atTop (𝓝 (1 : ℝ)) := by
      simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun m : ℕ => lambda ^ n * (1 + lambda * unitIntervalMomentStep m)⁻¹)
        atTop (𝓝 (lambda ^ n * 1)))

private theorem integralRepOnUnitInterval_moment_setIntegral_eq_of_resolvent_moment
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) (n : ℕ)
    (hres :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → x ≠ 0 →
        (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ)) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n ∂(rep₁.ν : Measure ℝ)) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n ∂(rep₂.ν : Measure ℝ) := by
  have hlim₁ :=
    tendsto_integral_unitInterval_resolvent_moment (rep₁.ν : Measure ℝ) n
  have hlim₂ :=
    tendsto_integral_unitInterval_resolvent_moment (rep₂.ν : Measure ℝ) n
  refine tendsto_nhds_unique hlim₁ ?_
  refine hlim₂.congr' ?_
  exact Filter.Eventually.of_forall fun m =>
    (hres (unitIntervalMomentStep_mem_Ioo m) (unitIntervalMomentStep_ne_zero m)).symm

private theorem unitInterval_resolvent_moment_setIntegral_eq_sub
    (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n * (1 + lambda * x)⁻¹ ∂μ) =
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1, lambda ^ n ∂μ) -
        x *
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ (n + 1) * (1 + lambda * x)⁻¹ ∂μ := by
  have hmoment :
      IntegrableOn (fun lambda : ℝ => lambda ^ n)
        (Set.Icc (-1 : ℝ) 1) μ := by
    exact (continuousOn_id.pow n).integrableOn_compact isCompact_Icc
  have hnext :
      IntegrableOn
        (fun lambda : ℝ => lambda ^ (n + 1) * (1 + lambda * x)⁻¹)
        (Set.Icc (-1 : ℝ) 1) μ :=
    integrableOn_unitInterval_resolvent_moment μ (n + 1) hx
  calc
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n * (1 + lambda * x)⁻¹ ∂μ) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n -
          x * (lambda ^ (n + 1) * (1 + lambda * x)⁻¹) ∂μ := by
        refine setIntegral_congr_fun measurableSet_Icc ?_
        intro lambda hlambda
        have hden : 1 + lambda * x ≠ 0 :=
          (unitIntervalOperatorKernel_denominator_pos hlambda hx).ne'
        field_simp [hden]
        ring
    _ =
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1, lambda ^ n ∂μ) -
        x *
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ (n + 1) * (1 + lambda * x)⁻¹ ∂μ := by
        rw [integral_sub hmoment (hnext.const_mul x), integral_const_mul]

private theorem integralRepOnUnitInterval_resolvent_moment_succ_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) (n : ℕ)
    (hmoment :
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ n ∂(rep₁.ν : Measure ℝ)) =
        ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ n ∂(rep₂.ν : Measure ℝ))
    (hres :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → x ≠ 0 →
        (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ)) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → x ≠ 0 →
      (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ (n + 1) * (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
        ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ (n + 1) * (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ) := by
  intro x hx hx0
  have hdecomp₁ :=
    unitInterval_resolvent_moment_setIntegral_eq_sub
      (rep₁.ν : Measure ℝ) n hx
  have hdecomp₂ :=
    unitInterval_resolvent_moment_setIntegral_eq_sub
      (rep₂.ν : Measure ℝ) n hx
  have hresx := hres hx hx0
  apply mul_left_cancel₀ hx0
  nlinarith [hdecomp₁, hdecomp₂, hresx, hmoment]

private theorem integralRepOnUnitInterval_moment_and_resolvent_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) :
    ∀ n : ℕ,
      ((∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ n ∂(rep₁.ν : Measure ℝ)) =
        ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          lambda ^ n ∂(rep₂.ν : Measure ℝ)) ∧
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → x ≠ 0 →
        (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            lambda ^ n * (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ)) := by
  intro n
  induction n with
  | zero =>
      have hres :
          ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → x ≠ 0 →
            (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
                lambda ^ 0 * (1 + lambda * x)⁻¹ ∂(rep₁.ν : Measure ℝ)) =
              ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
                lambda ^ 0 * (1 + lambda * x)⁻¹ ∂(rep₂.ν : Measure ℝ) := by
        intro x hx hx0
        simpa using integralRepOnUnitInterval_resolvent_setIntegral_eq rep₁ rep₂ hx hx0
      exact ⟨
        integralRepOnUnitInterval_moment_setIntegral_eq_of_resolvent_moment
          rep₁ rep₂ 0 hres,
        hres⟩
  | succ n ih =>
      rcases ih with ⟨hmoment, hres⟩
      have hres_succ :=
        integralRepOnUnitInterval_resolvent_moment_succ_setIntegral_eq
          rep₁ rep₂ n hmoment hres
      exact ⟨
        integralRepOnUnitInterval_moment_setIntegral_eq_of_resolvent_moment
          rep₁ rep₂ (n + 1) hres_succ,
        hres_succ⟩

private theorem integralRepOnUnitInterval_moment_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) (n : ℕ) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n ∂(rep₁.ν : Measure ℝ)) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        lambda ^ n ∂(rep₂.ν : Measure ℝ) :=
  (integralRepOnUnitInterval_moment_and_resolvent_setIntegral_eq rep₁ rep₂ n).1

private theorem integrableOn_polynomial_eval
    (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ[X]) :
    IntegrableOn (fun lambda : ℝ => p.eval lambda)
      (Set.Icc (-1 : ℝ) 1) μ :=
  p.continuous.continuousOn.integrableOn_compact isCompact_Icc

private theorem integralRepOnUnitInterval_polynomial_setIntegral_eq
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) (p : ℝ[X]) :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        p.eval lambda ∂(rep₁.ν : Measure ℝ)) =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        p.eval lambda ∂(rep₂.ν : Measure ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hp₁ := integrableOn_polynomial_eval (rep₁.ν : Measure ℝ) p
      have hq₁ := integrableOn_polynomial_eval (rep₁.ν : Measure ℝ) q
      have hp₂ := integrableOn_polynomial_eval (rep₂.ν : Measure ℝ) p
      have hq₂ := integrableOn_polynomial_eval (rep₂.ν : Measure ℝ) q
      simp_rw [Polynomial.eval_add]
      rw [integral_add hp₁ hq₁, integral_add hp₂ hq₂, hp, hq]
  | monomial n a =>
      calc
        (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            (Polynomial.monomial n a).eval lambda ∂(rep₁.ν : Measure ℝ)) =
            a *
              ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
                lambda ^ n ∂(rep₁.ν : Measure ℝ) := by
          simp [Polynomial.eval_monomial, integral_const_mul]
        _ =
            a *
              ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
                lambda ^ n ∂(rep₂.ν : Measure ℝ) := by
          rw [integralRepOnUnitInterval_moment_setIntegral_eq rep₁ rep₂ n]
        _ =
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            (Polynomial.monomial n a).eval lambda ∂(rep₂.ν : Measure ℝ) := by
          simp [Polynomial.eval_monomial, integral_const_mul]

/-- The representing finite measure in a normalized interval integral representation is unique. -/
theorem integralRepOnUnitInterval_measure_unique
    {f : ℝ → ℝ} (rep₁ rep₂ : IntegralRepOnUnitInterval f) :
    rep₁.ν = rep₂.ν := by
  classical
  let s : Set ℝ := Set.Icc (-1 : ℝ) 1
  refine FiniteMeasure.ext_of_forall_integral_eq ?_
  intro g
  rw [← rep₁.restrict_Icc_eq_self, ← rep₂.restrict_Icc_eq_self]
  change
    (∫ x : ℝ in s, g x ∂(rep₁.ν : Measure ℝ)) =
      ∫ x : ℝ in s, g x ∂(rep₂.ν : Measure ℝ)
  refine eq_of_forall_dist_le fun ε hε => ?_
  set mass : ℝ := (rep₁.ν : Measure ℝ).real s + (rep₂.ν : Measure ℝ).real s + 1
  have hmass_pos : 0 < mass := by
    have h₁ : 0 ≤ (rep₁.ν : Measure ℝ).real s := measureReal_nonneg
    have h₂ : 0 ≤ (rep₂.ν : Measure ℝ).real s := measureReal_nonneg
    linarith [h₁, h₂]
  set δ : ℝ := ε / mass
  have hδ_pos : 0 < δ := div_pos hε hmass_pos
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-1 : ℝ) 1
      (fun x : ℝ => g x) g.continuous.continuousOn δ hδ_pos
  have hg₁ :
      IntegrableOn (fun x : ℝ => g x) s (rep₁.ν : Measure ℝ) :=
    g.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hg₂ :
      IntegrableOn (fun x : ℝ => g x) s (rep₂.ν : Measure ℝ) :=
    g.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hp₁ := integrableOn_polynomial_eval (rep₁.ν : Measure ℝ) p
  have hp₂ := integrableOn_polynomial_eval (rep₂.ν : Measure ℝ) p
  have hpoly := integralRepOnUnitInterval_polynomial_setIntegral_eq rep₁ rep₂ p
  have herr₁ :
      ‖∫ x : ℝ in s, (g x - p.eval x) ∂(rep₁.ν : Measure ℝ)‖ ≤
        δ * (rep₁.ν : Measure ℝ).real s := by
    refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) ?_
    intro x hx
    rw [Real.norm_eq_abs]
    exact le_of_lt (by simpa [abs_sub_comm] using hp x hx)
  have herr₂ :
      ‖∫ x : ℝ in s, (g x - p.eval x) ∂(rep₂.ν : Measure ℝ)‖ ≤
        δ * (rep₂.ν : Measure ℝ).real s := by
    refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) ?_
    intro x hx
    rw [Real.norm_eq_abs]
    exact le_of_lt (by simpa [abs_sub_comm] using hp x hx)
  have hsub₁ :
      ∫ x : ℝ in s, (g x - p.eval x) ∂(rep₁.ν : Measure ℝ) =
        (∫ x : ℝ in s, g x ∂(rep₁.ν : Measure ℝ)) -
          ∫ x : ℝ in s, p.eval x ∂(rep₁.ν : Measure ℝ) := by
    rw [integral_sub hg₁ hp₁]
  have hsub₂ :
      ∫ x : ℝ in s, (g x - p.eval x) ∂(rep₂.ν : Measure ℝ) =
        (∫ x : ℝ in s, g x ∂(rep₂.ν : Measure ℝ)) -
          ∫ x : ℝ in s, p.eval x ∂(rep₂.ν : Measure ℝ) := by
    rw [integral_sub hg₂ hp₂]
  have herr₁' :
      |(∫ x : ℝ in s, g x ∂(rep₁.ν : Measure ℝ)) -
          ∫ x : ℝ in s, p.eval x ∂(rep₁.ν : Measure ℝ)| ≤
        δ * (rep₁.ν : Measure ℝ).real s := by
    simpa [hsub₁, Real.norm_eq_abs] using herr₁
  have herr₂' :
      |(∫ x : ℝ in s, g x ∂(rep₂.ν : Measure ℝ)) -
          ∫ x : ℝ in s, p.eval x ∂(rep₂.ν : Measure ℝ)| ≤
        δ * (rep₂.ν : Measure ℝ).real s := by
    simpa [hsub₂, Real.norm_eq_abs] using herr₂
  have hmass_lt : (rep₁.ν : Measure ℝ).real s + (rep₂.ν : Measure ℝ).real s < mass := by
    dsimp [mass]
    linarith
  have hsum_lt :
      δ * (rep₁.ν : Measure ℝ).real s + δ * (rep₂.ν : Measure ℝ).real s < ε := by
    calc
      δ * (rep₁.ν : Measure ℝ).real s + δ * (rep₂.ν : Measure ℝ).real s =
          δ * ((rep₁.ν : Measure ℝ).real s + (rep₂.ν : Measure ℝ).real s) := by ring
      _ < δ * mass := mul_lt_mul_of_pos_left hmass_lt hδ_pos
      _ = ε := by
        rw [show δ = ε / mass by rfl]
        field_simp [hmass_pos.ne']
  let A : ℝ := ∫ x : ℝ in s, g x ∂(rep₁.ν : Measure ℝ)
  let B : ℝ := ∫ x : ℝ in s, p.eval x ∂(rep₁.ν : Measure ℝ)
  let C : ℝ := ∫ x : ℝ in s, p.eval x ∂(rep₂.ν : Measure ℝ)
  let D : ℝ := ∫ x : ℝ in s, g x ∂(rep₂.ν : Measure ℝ)
  have hpoly' : B = C := by
    simpa [B, C, s] using hpoly
  have herrA : |A - B| ≤ δ * (rep₁.ν : Measure ℝ).real s := by
    simpa [A, B] using herr₁'
  have herrD : |C - D| ≤ δ * (rep₂.ν : Measure ℝ).real s := by
    simpa [C, D, abs_sub_comm] using herr₂'
  rw [Real.dist_eq]
  change |A - D| ≤ ε
  refine le_trans ?_ (le_of_lt hsum_lt)
  calc
    |A - D| = |(A - B) + (C - D)| := by
      apply congrArg abs
      rw [← hpoly']
      ring
    _ ≤ |A - B| + |C - D| :=
        abs_add_le _ _
    _ ≤ δ * (rep₁.ν : Measure ℝ).real s + δ * (rep₂.ν : Measure ℝ).real s := by
      exact add_le_add herrA herrD

end

end Quantum.TraceInequality.Loewner
