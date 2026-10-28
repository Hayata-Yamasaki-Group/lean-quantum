import Quantum.TraceInequality.Loewner.Statement
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Sequences

/-!
# Chapter 3 Pick kernel and integral transform

This file contains the book Pick domain, normalized interval Pick kernel, the
integral-side Pick transform attached to an `IntegralRepOnUnitInterval`, and the
forward construction of a Pick extension from an interval integral representation.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-- Non-real points lie in the book Pick domain. -/
theorem mem_unitIntervalPickDomain_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ (unitIntervalPickDomain : Set ℂ) := by
  change z.im ≠ 0 ∨ z.re ∈ Set.Ioo (-1 : ℝ) 1
  exact Or.inl hz

/-- Real points in `(-1, 1)` lie in the book Pick domain. -/
theorem ofReal_mem_unitIntervalPickDomain {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (x : ℂ) ∈ (unitIntervalPickDomain : Set ℂ) := by
  change (x : ℂ).im ≠ 0 ∨ (x : ℂ).re ∈ Set.Ioo (-1 : ℝ) 1
  exact Or.inr (by simpa using hx)

/-- The normalized interval Pick kernel from book Theorem 3.8. -/
def unitIntervalPickKernel (z : ℂ) (t : ℝ) : ℂ :=
  z / (1 + (t : ℂ) * z)

/--
The candidate Pick transform attached to an interval integral representation.

The next stages show that this transform is analytic on the slit domain and is
a Pick function; this first stage records the concrete formula and its real-axis
agreement with the representation.
-/
def integralRepPickTransform {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) (z : ℂ) : ℂ :=
  (f 0 : ℂ) +
    ∫ t : ℝ, unitIntervalPickKernel z t ∂(rep.ν : Measure ℝ)

/-- The book Pick domain is open. -/
theorem unitIntervalPickDomain_isOpen :
    IsOpen (unitIntervalPickDomain : Set ℂ) := by
  rw [unitIntervalPickDomain]
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_Ioo.preimage Complex.continuous_re)

/-- Complex derivative of the normalized interval Pick kernel. -/
def unitIntervalPickKernelDeriv (z : ℂ) (t : ℝ) : ℂ :=
  1 / (1 + (t : ℂ) * z) ^ 2

/-- The representing measure of an interval representation is a.e. supported on `[-1,1]`. -/
theorem IntegralRepOnUnitInterval.ae_mem_Icc {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) :
    ∀ᵐ t ∂(rep.ν : Measure ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  exact rep.support

/-- If `z` is non-real, the interval Pick kernel denominator cannot vanish. -/
theorem unitIntervalPickKernel_den_ne_zero_of_im_ne_zero
    {z : ℂ} (t : ℝ) (hz : z.im ≠ 0) :
    1 + (t : ℂ) * z ≠ 0 := by
  intro h
  by_cases ht : t = 0
  · subst t
    norm_num at h
  · have him0 : (1 + (t : ℂ) * z).im = 0 := by
      simp [h]
    have him : (1 + (t : ℂ) * z).im = t * z.im := by
      simp [Complex.add_im, Complex.mul_im]
    have hmul : t * z.im = 0 := by
      simpa [him] using him0
    exact hz ((mul_eq_zero.mp hmul).resolve_left ht)

/--
For `z` in the book Pick domain and `t ∈ [-1,1]`, the interval kernel
denominator is nonzero.
-/
theorem unitIntervalPickKernel_den_ne_zero_of_mem_domain_of_mem_Icc
    {z : ℂ} {t : ℝ}
    (hz : z ∈ (unitIntervalPickDomain : Set ℂ))
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    1 + (t : ℂ) * z ≠ 0 := by
  change z.im ≠ 0 ∨ z.re ∈ Set.Ioo (-1 : ℝ) 1 at hz
  rcases hz with hz_im | hz_re
  · exact unitIntervalPickKernel_den_ne_zero_of_im_ne_zero t hz_im
  · intro h
    have hreal0 : (1 + (t : ℂ) * z).re = 0 := by
      simp [h]
    have hreal : (1 + (t : ℂ) * z).re = 1 + t * z.re := by
      simp [Complex.add_re, Complex.mul_re]
    have hprod : t * z.re = -1 := by
      linarith
    have ht_abs : |t| ≤ 1 := by
      exact abs_le.mpr ht
    have hz_abs : |z.re| < 1 := by
      exact abs_lt.mpr hz_re
    have hprod_abs_lt : |t * z.re| < 1 := by
      calc
        |t * z.re| = |t| * |z.re| := abs_mul t z.re
        _ ≤ 1 * |z.re| := by
          exact mul_le_mul_of_nonneg_right ht_abs (abs_nonneg z.re)
        _ < 1 * 1 := by
          exact mul_lt_mul_of_pos_left hz_abs (by norm_num)
        _ = 1 := by norm_num
    have hprod_abs_eq : |t * z.re| = 1 := by
      rw [hprod, abs_neg, abs_one]
    linarith

/-- Imaginary part of the interval Pick kernel. -/
theorem unitIntervalPickKernel_im_eq (z : ℂ) (t : ℝ) :
    (unitIntervalPickKernel z t).im =
      z.im / Complex.normSq (1 + (t : ℂ) * z) := by
  simp [unitIntervalPickKernel, Complex.div_im, Complex.normSq]
  ring

/-- On the upper half-plane, the interval Pick kernel has nonnegative imaginary part. -/
theorem unitIntervalPickKernel_im_nonneg_of_upper
    {z : ℂ} (t : ℝ) (hz : 0 < z.im) :
    0 ≤ (unitIntervalPickKernel z t).im := by
  rw [unitIntervalPickKernel_im_eq]
  exact div_nonneg (le_of_lt hz)
    (Complex.normSq_nonneg (1 + (t : ℂ) * z))

/-- The interval Pick kernel has derivative `1 / (1 + t*z)^2` in the complex variable. -/
theorem unitIntervalPickKernel_hasDerivAt
    {z : ℂ} (t : ℝ) (hden : 1 + (t : ℂ) * z ≠ 0) :
    HasDerivAt (fun w : ℂ => unitIntervalPickKernel w t)
      (unitIntervalPickKernelDeriv z t) z := by
  have hnum : HasDerivAt (fun w : ℂ => w) 1 z := by
    simpa using hasDerivAt_id z
  have hden' : HasDerivAt (fun w : ℂ => 1 + (t : ℂ) * w) (t : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (t : ℂ)).const_add (1 : ℂ)
  have h := hnum.div hden' hden
  have hder :
      (1 * (1 + (t : ℂ) * z) - z * (t : ℂ)) /
          (1 + (t : ℂ) * z) ^ 2 =
        unitIntervalPickKernelDeriv z t := by
    simp [unitIntervalPickKernelDeriv]
    field_simp [hden]
    ring
  change HasDerivAt ((fun w : ℂ => w) / fun w => 1 + (t : ℂ) * w)
    (unitIntervalPickKernelDeriv z t) z
  rw [← hder]
  exact h

/-- On `[-1,1]`, the interval Pick kernel is continuous for non-real `z`. -/
theorem unitIntervalPickKernel_continuousOn_Icc_of_im_ne_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    ContinuousOn (fun t : ℝ => unitIntervalPickKernel z t)
      (Set.Icc (-1 : ℝ) 1) := by
  refine continuousOn_const.div ?_ ?_
  · fun_prop
  · intro t _ht
    exact unitIntervalPickKernel_den_ne_zero_of_im_ne_zero t hz

/-- On `[-1,1]`, the interval Pick kernel is continuous for `z` in the Pick domain. -/
theorem unitIntervalPickKernel_continuousOn_Icc_of_mem_domain
    {z : ℂ} (hz : z ∈ (unitIntervalPickDomain : Set ℂ)) :
    ContinuousOn (fun t : ℝ => unitIntervalPickKernel z t)
      (Set.Icc (-1 : ℝ) 1) := by
  refine continuousOn_const.div ?_ ?_
  · fun_prop
  · intro t ht
    exact unitIntervalPickKernel_den_ne_zero_of_mem_domain_of_mem_Icc hz ht

/-- The interval Pick kernel is integrable against an interval representing measure. -/
theorem unitIntervalPickKernel_integrable_of_im_ne_zero
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f)
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t : ℝ => unitIntervalPickKernel z t)
      (rep.ν : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => unitIntervalPickKernel z t)
        (rep.ν : Measure ℝ) := by
    have hmeas' : Measurable (fun t : ℝ => unitIntervalPickKernel z t) := by
      unfold unitIntervalPickKernel
      measurability
    exact hmeas'.aestronglyMeasurable
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (unitIntervalPickKernel_continuousOn_Icc_of_im_ne_zero hz)
  refine Integrable.of_bound hmeas C ?_
  filter_upwards [rep.ae_mem_Icc] with t ht
  exact hC t ht

/--
The interval Pick kernel is integrable against an interval representing measure
on the domain.
-/
theorem unitIntervalPickKernel_integrable_of_mem_domain
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f)
    {z : ℂ} (hz : z ∈ (unitIntervalPickDomain : Set ℂ)) :
    Integrable (fun t : ℝ => unitIntervalPickKernel z t)
      (rep.ν : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => unitIntervalPickKernel z t)
        (rep.ν : Measure ℝ) := by
    have hmeas' : Measurable (fun t : ℝ => unitIntervalPickKernel z t) := by
      unfold unitIntervalPickKernel
      measurability
    exact hmeas'.aestronglyMeasurable
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (unitIntervalPickKernel_continuousOn_Icc_of_mem_domain hz)
  refine Integrable.of_bound hmeas C ?_
  filter_upwards [rep.ae_mem_Icc] with t ht
  exact hC t ht

/--
Near a domain point, the kernel denominator is uniformly bounded away from
zero for all interval parameters.
-/
theorem unitIntervalPickKernel_local_den_norm_lower
    {z₀ : ℂ} (hz₀ : z₀ ∈ (unitIntervalPickDomain : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (-1 : ℝ) 1 →
      ∀ ⦃z : ℂ⦄, z ∈ Metric.ball z₀ r →
        r ≤ ‖1 + (t : ℂ) * z‖ := by
  let g : ℝ → ℝ := fun t => ‖1 + (t : ℂ) * z₀‖
  have hg : ContinuousOn g (Set.Icc (-1 : ℝ) 1) := by
    unfold g
    fun_prop
  obtain ⟨t₀, ht₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by norm_num)) hg
  let m : ℝ := g t₀
  have hm_pos : 0 < m := by
    unfold m g
    exact norm_pos_iff.mpr
      (unitIntervalPickKernel_den_ne_zero_of_mem_domain_of_mem_Icc hz₀ ht₀)
  refine ⟨m / 2, half_pos hm_pos, ?_⟩
  intro t ht z hz
  have hmin_t : m ≤ ‖1 + (t : ℂ) * z₀‖ := by
    simpa [m, g] using hmin ht
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    have ht_abs : |t| ≤ 1 := abs_le.mpr ht
    simpa using ht_abs
  have hz_norm : ‖z - z₀‖ < m / 2 := by
    simpa [dist_eq_norm] using hz
  have hdiff :
      ‖(1 + (t : ℂ) * z₀) - (1 + (t : ℂ) * z)‖ ≤ m / 2 := by
    calc
      ‖(1 + (t : ℂ) * z₀) - (1 + (t : ℂ) * z)‖ =
          ‖(t : ℂ) * (z₀ - z)‖ := by
        congr 1
        ring
      _ = ‖(t : ℂ)‖ * ‖z₀ - z‖ := norm_mul _ _
      _ ≤ 1 * ‖z₀ - z‖ := by
        exact mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
      _ = ‖z₀ - z‖ := by ring
      _ = ‖z - z₀‖ := by rw [← norm_neg (z - z₀)]; ring_nf
      _ ≤ m / 2 := le_of_lt hz_norm
  have hsub :
      ‖1 + (t : ℂ) * z₀‖ - m / 2 ≤ ‖1 + (t : ℂ) * z‖ := by
    have htri :=
      norm_sub_norm_le (1 + (t : ℂ) * z₀) (1 + (t : ℂ) * z)
    linarith
  calc
    m / 2 = m - m / 2 := by ring
    _ ≤ ‖1 + (t : ℂ) * z₀‖ - m / 2 := by
      exact sub_le_sub_right hmin_t (m / 2)
    _ ≤ ‖1 + (t : ℂ) * z‖ := hsub

/-- Near a domain point, the complex derivative of the kernel is uniformly bounded on `[-1,1]`. -/
theorem unitIntervalPickKernel_local_deriv_bound
    {z₀ : ℂ} (hz₀ : z₀ ∈ (unitIntervalPickDomain : Set ℂ)) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (-1 : ℝ) 1 →
      ∀ ⦃z : ℂ⦄, z ∈ Metric.ball z₀ r →
        ‖unitIntervalPickKernelDeriv z t‖ ≤ C := by
  obtain ⟨r, hr_pos, hden⟩ :=
    unitIntervalPickKernel_local_den_norm_lower hz₀
  refine ⟨r, 1 / r ^ 2, hr_pos, by positivity, ?_⟩
  intro t ht z hz
  have hden_norm : r ≤ ‖1 + (t : ℂ) * z‖ := hden ht hz
  have hden_pos : 0 < ‖1 + (t : ℂ) * z‖ :=
    lt_of_lt_of_le hr_pos hden_norm
  have hsq : r ^ 2 ≤ ‖1 + (t : ℂ) * z‖ ^ 2 := by
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (le_of_lt hr_pos), abs_of_nonneg (norm_nonneg _)]
      exact hden_norm)
  calc
    ‖unitIntervalPickKernelDeriv z t‖ =
        1 / ‖1 + (t : ℂ) * z‖ ^ 2 := by
      simp [unitIntervalPickKernelDeriv, norm_pow]
    _ ≤ 1 / r ^ 2 := by
      exact div_le_div_of_nonneg_left zero_le_one (pow_pos hr_pos 2) hsq

/-- The imaginary part of the Pick transform is the integral of the kernel imaginary part. -/
theorem integralRepPickTransform_im_eq_integral_im
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f)
    {z : ℂ} (hz : z.im ≠ 0) :
    (integralRepPickTransform rep z).im =
      ∫ t : ℝ, (unitIntervalPickKernel z t).im ∂(rep.ν : Measure ℝ) := by
  have hInt := unitIntervalPickKernel_integrable_of_im_ne_zero rep hz
  have him :=
    (integral_im (μ := (rep.ν : Measure ℝ))
      (f := fun t : ℝ => unitIntervalPickKernel z t) hInt)
  calc
    (integralRepPickTransform rep z).im =
        (∫ t : ℝ, unitIntervalPickKernel z t ∂(rep.ν : Measure ℝ)).im := by
      simp [integralRepPickTransform]
    _ = ∫ t : ℝ, (unitIntervalPickKernel z t).im ∂(rep.ν : Measure ℝ) := by
      exact him.symm

/-- The integral-side Pick transform maps the upper half-plane to the closed upper half-plane. -/
theorem integralRepPickTransform_im_nonneg_of_upper
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (integralRepPickTransform rep z).im := by
  rw [integralRepPickTransform_im_eq_integral_im rep (ne_of_gt hz)]
  exact integral_nonneg_of_ae
    (MeasureTheory.ae_of_all (rep.ν : Measure ℝ)
      (fun t : ℝ => unitIntervalPickKernel_im_nonneg_of_upper t hz))

/-- The integral-side Pick transform is complex differentiable at every point of the Pick domain. -/
theorem integralRepPickTransform_hasDerivAt
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f)
    {z₀ : ℂ} (hz₀ : z₀ ∈ (unitIntervalPickDomain : Set ℂ)) :
    HasDerivAt (fun z : ℂ => integralRepPickTransform rep z)
      (∫ t : ℝ, unitIntervalPickKernelDeriv z₀ t ∂(rep.ν : Measure ℝ)) z₀ := by
  obtain ⟨r, hr_pos, hden_lower⟩ :=
    unitIntervalPickKernel_local_den_norm_lower hz₀
  obtain ⟨r', C, hr'_pos, _hC_nonneg, hC⟩ :=
    unitIntervalPickKernel_local_deriv_bound hz₀
  let ρ : ℝ := min r r'
  have hρ_pos : 0 < ρ := lt_min hr_pos hr'_pos
  let F : ℂ → ℝ → ℂ := fun z t => unitIntervalPickKernel z t
  let F' : ℂ → ℝ → ℂ := fun z t => unitIntervalPickKernelDeriv z t
  have hF_meas :
      ∀ᶠ z : ℂ in 𝓝 z₀,
        AEStronglyMeasurable (F z) (rep.ν : Measure ℝ) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have hmeas : Measurable (fun t : ℝ => F z t) := by
      unfold F unitIntervalPickKernel
      measurability
    exact hmeas.aestronglyMeasurable
  have hF_int : Integrable (F z₀) (rep.ν : Measure ℝ) := by
    simpa [F] using unitIntervalPickKernel_integrable_of_mem_domain rep hz₀
  have hF'_meas :
      AEStronglyMeasurable (F' z₀) (rep.ν : Measure ℝ) := by
    have hmeas : Measurable (fun t : ℝ => F' z₀ t) := by
      unfold F' unitIntervalPickKernelDeriv
      measurability
    exact hmeas.aestronglyMeasurable
  have h_bound :
      ∀ᵐ t : ℝ ∂(rep.ν : Measure ℝ),
        ∀ z : ℂ, z ∈ Metric.ball z₀ ρ → ‖F' z t‖ ≤ C := by
    filter_upwards [rep.ae_mem_Icc] with t ht z hz
    have hz' : z ∈ Metric.ball z₀ r' := by
      rw [mem_ball_iff_norm] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_right _ _)
    simpa [F'] using hC ht hz'
  have h_bound_int : Integrable (fun _t : ℝ => C) (rep.ν : Measure ℝ) :=
    MeasureTheory.integrable_const C
  have h_diff :
      ∀ᵐ t : ℝ ∂(rep.ν : Measure ℝ),
        ∀ z : ℂ, z ∈ Metric.ball z₀ ρ →
          HasDerivAt (fun z : ℂ => F z t) (F' z t) z := by
    filter_upwards [rep.ae_mem_Icc] with t ht z hz
    have hz_r : z ∈ Metric.ball z₀ r := by
      rw [mem_ball_iff_norm] at hz ⊢
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hden_pos : 0 < ‖1 + (t : ℂ) * z‖ :=
      lt_of_lt_of_le hr_pos (hden_lower ht hz_r)
    have hden_ne : 1 + (t : ℂ) * z ≠ 0 :=
      norm_pos_iff.mp hden_pos
    simpa [F, F'] using unitIntervalPickKernel_hasDerivAt t hden_ne
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z₀ hρ_pos) hF_meas hF_int hF'_meas
      h_bound h_bound_int h_diff
  simpa [integralRepPickTransform, F, F'] using hmain.2.const_add (f 0 : ℂ)

/-- The integral-side Pick transform is differentiable on the book Pick domain. -/
theorem integralRepPickTransform_differentiableOn
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    DifferentiableOn ℂ (fun z : ℂ => integralRepPickTransform rep z)
      unitIntervalPickDomain := by
  intro z hz
  exact (integralRepPickTransform_hasDerivAt rep hz).differentiableAt.differentiableWithinAt

/-- The integral-side Pick transform is analytic on the book Pick domain. -/
theorem integralRepPickTransform_analyticOn
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    AnalyticOn ℂ (fun z : ℂ => integralRepPickTransform rep z)
      unitIntervalPickDomain :=
  (integralRepPickTransform_differentiableOn rep).analyticOn
    unitIntervalPickDomain_isOpen

/--
The integral-side Pick transform agrees with the original real function on
`(-1,1)`.
-/
theorem integralRepPickTransform_real_eq {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    integralRepPickTransform rep (x : ℂ) = (f x : ℂ) := by
  simpa [integralRepPickTransform, unitIntervalPickKernel] using (rep.formula hx).symm

/-- An interval integral representation produces the Pick extension from book Theorem 3.8. -/
def pickExtensionOnUnitInterval_of_integralRep
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    PickExtensionOnUnitInterval f where
  F := integralRepPickTransform rep
  analyticOn := integralRepPickTransform_analyticOn rep
  agreesOnReal := by
    intro x hx
    exact integralRepPickTransform_real_eq rep hx
  mapsUpper := by
    intro z hz
    exact integralRepPickTransform_im_nonneg_of_upper rep hz

end

end Quantum.TraceInequality.Loewner
