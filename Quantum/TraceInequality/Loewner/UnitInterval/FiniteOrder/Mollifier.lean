import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Chapter 20 Hiai mollifier package

This file contains the smooth compactly supported mollifier package and the
endpoint / first-moment identities used by the Chapter 20 finite-order
regularity proof.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal

noncomputable section

/--
Book/Hiai mollifier package for the regularized finite-order route.

The support and integral are recorded on the concrete interval used in the
Japanese proof excerpt, while smoothness is stated with the book's `C∞` order.
-/
structure HiaiMollifier (φ : ℝ → ℝ) : Prop where
  nonneg : ∀ t : ℝ, 0 ≤ φ t
  support_subset : Function.support φ ⊆ Set.Icc (-1 : ℝ) 1
  integral_eq_one : (∫ t in (-1 : ℝ)..1, φ t) = 1
  smooth : ContDiff ℝ loewnerBookSmoothOrder φ

/-- A concrete smooth Hiai mollifier on the normalized support interval. -/
theorem exists_hiaiMollifier :
    ∃ φ : ℝ → ℝ, HiaiMollifier φ := by
  let β : ContDiffBump (0 : ℝ) := ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩
  refine ⟨β.normed volume, ?_⟩
  have hsuppIoc :
      Function.support (β.normed volume) ⊆ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) β.rOut := by
      rw [← β.support_normed_eq (μ := volume)]
      exact ht
    have hdist : dist t (0 : ℝ) < 1 := by
      simpa [β] using htball
    have habs : |t| < 1 := by
      simpa [Real.dist_eq] using hdist
    exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact β.nonneg_normed (μ := volume) t
  · exact hsuppIoc.trans (fun _ ht => ⟨ht.1.le, ht.2⟩)
  · have hwhole : (∫ t, β.normed volume t) = 1 :=
      β.integral_normed (μ := volume)
    calc
      (∫ t in (-1 : ℝ)..1, β.normed volume t) = ∫ t, β.normed volume t := by
        exact intervalIntegral.integral_eq_integral_of_support_subset hsuppIoc
      _ = 1 := hwhole
  · exact β.contDiff_normed (μ := volume)

/-- The mollifier vanishes at the left endpoint of its support interval. -/
theorem hiaiMollifier_left_endpoint_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) :
    φ (-1) = 0 := by
  have hzero : φ =ᶠ[𝓝[<] ((-1 : ℝ))] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    by_contra hne
    have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := hφ.support_subset hne
    exact (not_lt_of_ge hyIcc.1) hy
  have hlimφ : Tendsto φ (𝓝[<] ((-1 : ℝ))) (𝓝 (φ (-1))) :=
    hφ.smooth.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto φ (𝓝[<] ((-1 : ℝ))) (𝓝 0) :=
    tendsto_const_nhds.congr' hzero.symm
  exact tendsto_nhds_unique hlimφ hlim0

/-- The mollifier vanishes at the right endpoint of its support interval. -/
theorem hiaiMollifier_right_endpoint_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) :
    φ 1 = 0 := by
  have hzero : φ =ᶠ[𝓝[>] (1 : ℝ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    by_contra hne
    have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := hφ.support_subset hne
    exact (not_lt_of_ge hyIcc.2) hy
  have hlimφ : Tendsto φ (𝓝[>] (1 : ℝ)) (𝓝 (φ 1)) :=
    hφ.smooth.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto φ (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' hzero.symm
  exact tendsto_nhds_unique hlimφ hlim0

/-- The derivative of a Hiai mollifier has zero total integral. -/
theorem hiaiMollifier_integral_deriv_eq_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) :
    (∫ t in (-1 : ℝ)..1, deriv φ t) = 0 := by
  have hφ1 : ContDiffOn ℝ 1 φ (Set.Icc (-1 : ℝ) 1) := by
    have h1le : (1 : WithTop ℕ∞) ≤ loewnerBookSmoothOrder := by
      dsimp [loewnerBookSmoothOrder]
      exact WithTop.coe_le_coe.2 le_top
    exact (hφ.smooth.of_le h1le).contDiffOn
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ1 (by norm_num)]
  rw [hiaiMollifier_right_endpoint_zero hφ,
    hiaiMollifier_left_endpoint_zero hφ]
  ring

/-- First moment of the derivative of a Hiai mollifier. -/
theorem hiaiMollifier_integral_deriv_mul_neg_id_eq_one
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) :
    (∫ t in (-1 : ℝ)..1, deriv φ t * (-t)) = 1 := by
  have hderivφ : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  have hφ_cont : Continuous φ := hφ.smooth.continuous
  have hparts :
      (∫ t in (-1 : ℝ)..1, φ t * (-(1 : ℝ))) =
        φ 1 * (-(1 : ℝ)) - φ (-1) * (-(-1 : ℝ)) -
          ∫ t in (-1 : ℝ)..1, deriv φ t * (-t) := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := φ) (u' := deriv φ)
      (v := fun t : ℝ => -t) (v' := fun _ : ℝ => -(1 : ℝ))
      hφ_cont.continuousOn
      (by fun_prop)
      (fun t _ht =>
        (hφ.smooth.differentiable
          (by simp [loewnerBookSmoothOrder])).differentiableAt.hasDerivAt)
      (fun t _ht => by simpa using (hasDerivAt_id t).neg)
      hderivφ.continuousOn.intervalIntegrable
      continuous_const.continuousOn.intervalIntegrable
  have hconst : (∫ t in (-1 : ℝ)..1, φ t * (-(1 : ℝ))) = -1 := by
    rw [intervalIntegral.integral_mul_const, hφ.integral_eq_one]
    ring
  rw [hiaiMollifier_right_endpoint_zero hφ,
    hiaiMollifier_left_endpoint_zero hφ] at hparts
  linarith

end

end Quantum.TraceInequality.Loewner
