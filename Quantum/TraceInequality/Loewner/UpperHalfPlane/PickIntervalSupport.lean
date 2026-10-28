import Quantum.TraceInequality.Loewner.UpperHalfPlane.PoissonBoundary
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.MeasureDomination

/-!
# Interval support for upper-half-plane Nevanlinna representations

This file starts the analytic-continuation side of Proposition 144.  The
producer contracts live in `Nevanlinna.lean`; this module contains concrete
supporting API that depends on the Poisson boundary bridge without creating an
import cycle.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open Set MeasureTheory Filter
open scoped UpperHalfPlane Topology Manifold ContDiff

noncomputable section

/-! ### Pick interval domain -/

/-- The upper-half-plane Pick interval domain is open in `ℂ`. -/
theorem isOpen_upperHalfPlanePickIntervalDomain (a b : ℝ) :
    IsOpen (upperHalfPlanePickIntervalDomain a b) := by
  have h_nonreal : IsOpen {z : ℂ | z.im ≠ 0} := by
    simpa using (isOpen_ne_fun Complex.continuous_im continuous_const)
  have h_interval : IsOpen {z : ℂ | z.re ∈ Set.Ioo a b} := by
    simpa using (isOpen_Ioo.preimage Complex.continuous_re)
  simpa [upperHalfPlanePickIntervalDomain, Set.setOf_or] using h_nonreal.union h_interval

/-! ### The complement-supported extension -/

/-- The Nevanlinna formula, read as a complex function on the continuation domain. -/
noncomputable def NevanlinnaRepOnComplement.extension
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) : ℂ → ℂ :=
  fun z =>
    (rep.alpha : ℂ) + ((rep.beta : ℝ) : ℂ) * z +
      ∫ t : ℝ, nevanlinnaKernelC t z ∂(rep.ν : Measure ℝ)

/-- Algebraic decomposition of the complex Nevanlinna kernel away from the pole. -/
theorem nevanlinnaKernelC_eq_decomp {t : ℝ} {z : ℂ}
    (hden : ((t : ℂ) - z) ≠ 0) :
    nevanlinnaKernelC t z =
      z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z) := by
  unfold nevanlinnaKernelC
  field_simp [hden]
  ring

/-- A denominator lower bound and a norm bound on `z` give a uniform kernel bound. -/
theorem nevanlinnaKernelC_norm_bound_of_den_lower
    {t : ℝ} {z : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hden : δ ≤ ‖(t : ℂ) - z‖) (hR : ‖z‖ ≤ R) :
    ‖nevanlinnaKernelC t z‖ ≤
      R + (1 + R ^ (2 : ℕ)) / δ := by
  have hden_ne : ((t : ℂ) - z) ≠ 0 := by
    intro h
    have : ‖(t : ℂ) - z‖ = 0 := by simp [h]
    linarith
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg z) hR
  rw [nevanlinnaKernelC_eq_decomp hden_ne]
  calc
    ‖z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ ≤
        ‖z‖ + ‖(1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ R + (1 + R ^ (2 : ℕ)) / δ := by
      gcongr
      rw [norm_div]
      refine div_le_div₀ ?num_nonneg ?num_le hδ hden
      · nlinarith [sq_nonneg R]
      · calc
          ‖1 + z ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ := norm_add_le _ _
          _ = 1 + ‖z‖ ^ (2 : ℕ) := by rw [norm_one, norm_pow]
          _ ≤ 1 + R ^ (2 : ℕ) := by
            gcongr

/-- The kernel is integrable under an a.e. denominator lower bound. -/
theorem nevanlinnaKernelC_integrable_of_ae_den_lower
    (ν : FiniteMeasure ℝ) {z : ℂ} {δ R : ℝ}
    (hδ : 0 < δ)
    (hden : ∀ᵐ t : ℝ ∂(ν : Measure ℝ), δ ≤ ‖(t : ℂ) - z‖)
    (hR : ‖z‖ ≤ R) :
    Integrable (fun t : ℝ => nevanlinnaKernelC t z) (ν : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => nevanlinnaKernelC t z) (ν : Measure ℝ) := by
    apply Measurable.aestronglyMeasurable
    unfold nevanlinnaKernelC
    fun_prop
  have hbound :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ‖nevanlinnaKernelC t z‖ ≤ R + (1 + R ^ (2 : ℕ)) / δ := by
    filter_upwards [hden] with t ht
    exact nevanlinnaKernelC_norm_bound_of_den_lower hδ ht hR
  exact Integrable.of_bound hmeas (R + (1 + R ^ (2 : ℕ)) / δ) hbound

/-- Differentiation passes under the finite-measure kernel integral on a protected ball. -/
theorem nevanlinnaKernelC_integral_hasDerivAt_of_ae_ball_den_lower
    (ν : FiniteMeasure ℝ) {z : ℂ} {r δ R : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (hden :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z r →
          δ ≤ ‖(t : ℂ) - w‖)
    (hR : ∀ w : ℂ, w ∈ Metric.ball z r → ‖w‖ ≤ R) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ, nevanlinnaKernelC t w ∂(ν : Measure ℝ))
      (∫ t : ℝ, nevanlinnaKernelCDeriv t z ∂(ν : Measure ℝ)) z := by
  let C : ℝ := 1 + (2 * R) / δ + (1 + R ^ (2 : ℕ)) / δ ^ (2 : ℕ)
  have hball : Metric.ball z r ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have h_meas :
      ∀ᶠ w : ℂ in 𝓝 z,
        AEStronglyMeasurable (fun t : ℝ => nevanlinnaKernelC t w) (ν : Measure ℝ) := by
    refine Filter.Eventually.of_forall fun w => ?_
    apply Measurable.aestronglyMeasurable
    unfold nevanlinnaKernelC
    fun_prop
  have hz_mem : z ∈ Metric.ball z r := by simpa [Metric.mem_ball]
  have h_int : Integrable (fun t : ℝ => nevanlinnaKernelC t z) (ν : Measure ℝ) := by
    exact nevanlinnaKernelC_integrable_of_ae_den_lower ν hδ
      (hden.mono fun t ht => ht z hz_mem) (hR z hz_mem)
  have h_deriv_meas :
      AEStronglyMeasurable (fun t : ℝ => nevanlinnaKernelCDeriv t z)
        (ν : Measure ℝ) := by
    apply Measurable.aestronglyMeasurable
    unfold nevanlinnaKernelCDeriv
    fun_prop
  have h_bound :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z r →
          ‖nevanlinnaKernelCDeriv t w‖ ≤ C := by
    filter_upwards [hden] with t ht w hw
    exact nevanlinnaKernelCDeriv_norm_bound hδ (ht w hw) (hR w hw)
  have h_bound_int : Integrable (fun _t : ℝ => C) (ν : Measure ℝ) := by
    exact integrable_const _
  have h_deriv :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z r →
          HasDerivAt (fun w : ℂ => nevanlinnaKernelC t w)
            (nevanlinnaKernelCDeriv t w) w := by
    filter_upwards [hden] with t ht w hw
    have hden_ne : ((t : ℂ) - w) ≠ 0 := by
      intro h
      have : ‖(t : ℂ) - w‖ = 0 := by simp [h]
      have hpos : 0 < ‖(t : ℂ) - w‖ := lt_of_lt_of_le hδ (ht w hw)
      linarith
    exact hasDerivAt_nevanlinnaKernelC_of_den_ne_zero hden_ne
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (ν : Measure ℝ))
    (bound := fun _t : ℝ => C)
    (F := fun w t => nevanlinnaKernelC t w)
    (F' := fun w t => nevanlinnaKernelCDeriv t w)
    hball h_meas h_int h_deriv_meas h_bound h_bound_int h_deriv).2

/-- The imaginary part of a point is bounded by its distance from any real point. -/
theorem complex_abs_im_le_norm_sub_ofReal (t : ℝ) (w : ℂ) :
    |w.im| ≤ ‖(t : ℂ) - w‖ := by
  have h := Complex.abs_im_le_norm ((t : ℂ) - w)
  have him : (((t : ℂ) - w)).im = -w.im := by simp
  simpa [him, abs_neg] using h

/-- The real-coordinate gap from `t` is bounded by the distance to `(t : ℂ)`. -/
theorem complex_abs_re_sub_le_norm_sub_ofReal (t : ℝ) (w : ℂ) :
    |t - w.re| ≤ ‖(t : ℂ) - w‖ := by
  have h := Complex.abs_re_le_norm ((t : ℂ) - w)
  have hre : (((t : ℂ) - w)).re = t - w.re := by simp
  simpa [hre] using h

/-- Away from the real line, a small ball has a uniform a.e. denominator lower bound. -/
theorem ae_ball_den_lower_of_im_ne_zero
    (ν : FiniteMeasure ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ r δ R : ℝ,
      0 < r ∧ 0 < δ ∧
      (∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z r →
          δ ≤ ‖(t : ℂ) - w‖) ∧
      (∀ w : ℂ, w ∈ Metric.ball z r → ‖w‖ ≤ R) := by
  let δ : ℝ := |z.im| / 2
  refine ⟨δ, δ, ‖z‖ + δ, ?_, ?_, ?_, ?_⟩
  · dsimp [δ]
    positivity
  · dsimp [δ]
    positivity
  · refine ae_of_all _ ?_
    intro t w hw
    have hdist : ‖w - z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
    have him_abs : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa using Complex.abs_im_le_norm (w - z)
    have him_lt : |w.im - z.im| < δ := lt_of_le_of_lt him_abs hdist
    have hzw : |z.im| ≤ |w.im| + |w.im - z.im| := by
      have hsub : z.im - w.im = -(w.im - z.im) := by ring
      calc
        |z.im| = |w.im + (z.im - w.im)| := by
          congr 1
          ring
        _ ≤ |w.im| + |z.im - w.im| := abs_add_le _ _
        _ = |w.im| + |w.im - z.im| := by rw [hsub, abs_neg]
    have hδ_le_abs : δ ≤ |w.im| := by
      dsimp [δ] at him_lt ⊢
      linarith
    exact hδ_le_abs.trans (complex_abs_im_le_norm_sub_ofReal t w)
  · intro w hw
    have hdist : ‖w - z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
    calc
      ‖w‖ = ‖z + (w - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + δ := by linarith

/-- On real points of `(a,b)`, complement support gives a denominator lower bound. -/
theorem ae_ball_den_lower_of_real_mem_Ioo_of_support_complement
    {a b x : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F)
    (hx : x ∈ Set.Ioo a b) :
    ∃ r δ R : ℝ,
      0 < r ∧ 0 < δ ∧
      (∀ᵐ t : ℝ ∂(rep.ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball (x : ℂ) r →
          δ ≤ ‖(t : ℂ) - w‖) ∧
      (∀ w : ℂ, w ∈ Metric.ball (x : ℂ) r → ‖w‖ ≤ R) := by
  let d : ℝ := min (x - a) (b - x)
  let r : ℝ := d / 4
  let δ : ℝ := d / 2
  have hd_pos : 0 < d := by
    dsimp [d]
    exact lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  refine ⟨r, δ, ‖(x : ℂ)‖ + r, ?_, ?_, ?_, ?_⟩
  · dsimp [r]
    positivity
  · dsimp [δ]
    positivity
  · have hae_out : ∀ᵐ t : ℝ ∂(rep.ν : Measure ℝ), t ∉ Set.Ioo a b := by
      rw [ae_iff]
      simpa only [Set.mem_setOf_eq, not_not] using rep.support_complement
    filter_upwards [hae_out] with t ht w hw
    have hdist : ‖w - (x : ℂ)‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
    have hre_abs : |w.re - x| ≤ ‖w - (x : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (w - (x : ℂ))
    have hre_lt : |w.re - x| < r := lt_of_le_of_lt hre_abs hdist
    have ht_cases : t ≤ a ∨ b ≤ t := by
      by_cases hta : t ≤ a
      · exact Or.inl hta
      · have hat : a < t := lt_of_not_ge hta
        right
        by_contra hbt
        exact ht ⟨hat, lt_of_not_ge hbt⟩
    have hδ_re : δ ≤ |t - w.re| := by
      rcases ht_cases with hta | hbt
      · have hw_lower : x - r < w.re := by
          have hneg : x - w.re = -(w.re - x) := by ring
          have hxw_lt : x - w.re < r := by
            rw [hneg]
            exact lt_of_le_of_lt (neg_le_abs _) hre_lt
          linarith
        have hdt : d ≤ x - a := min_le_left _ _
        have hmain : δ ≤ w.re - t := by
          dsimp [r, δ] at hw_lower ⊢
          nlinarith
        exact hmain.trans (by
          have hneg : w.re - t = -(t - w.re) := by ring
          rw [hneg]
          exact neg_le_abs _)
      · have hw_upper : w.re < x + r := by
          have hxw_lt : w.re - x < r :=
            lt_of_le_of_lt (le_abs_self _) hre_lt
          linarith
        have hdt : d ≤ b - x := min_le_right _ _
        have hmain : δ ≤ t - w.re := by
          dsimp [r, δ] at hw_upper ⊢
          nlinarith
        exact hmain.trans (le_abs_self _)
    exact hδ_re.trans (complex_abs_re_sub_le_norm_sub_ofReal t w)
  · intro w hw
    have hdist : ‖w - (x : ℂ)‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
    calc
      ‖w‖ = ‖(x : ℂ) + (w - (x : ℂ))‖ := by ring_nf
      _ ≤ ‖(x : ℂ)‖ + ‖w - (x : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖(x : ℂ)‖ + r := by linarith

/-- Every point of the interval Pick domain has a local a.e. denominator lower bound. -/
theorem NevanlinnaRepOnComplement.ae_ball_den_lower_of_mem_domain
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) {z : ℂ}
    (hz : z ∈ upperHalfPlanePickIntervalDomain a b) :
    ∃ r δ R : ℝ,
      0 < r ∧ 0 < δ ∧
      (∀ᵐ t : ℝ ∂(rep.ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z r →
          δ ≤ ‖(t : ℂ) - w‖) ∧
      (∀ w : ℂ, w ∈ Metric.ball z r → ‖w‖ ≤ R) := by
  rcases hz with hz_im | hz_re
  · exact ae_ball_den_lower_of_im_ne_zero rep.ν hz_im
  · by_cases hz_im : z.im = 0
    · have hz_eq : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [hz_im]
      simpa [hz_eq] using
        ae_ball_den_lower_of_real_mem_Ioo_of_support_complement
          (rep := rep) (x := z.re) hz_re
    · exact ae_ball_den_lower_of_im_ne_zero rep.ν hz_im

/-- The complement-supported extension is complex differentiable on the Pick domain. -/
theorem NevanlinnaRepOnComplement.extension_hasDerivAt
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) {z : ℂ}
    (hz : z ∈ upperHalfPlanePickIntervalDomain a b) :
    HasDerivAt rep.extension
      (((rep.beta : ℝ) : ℂ) +
        ∫ t : ℝ, nevanlinnaKernelCDeriv t z ∂(rep.ν : Measure ℝ)) z := by
  obtain ⟨r, δ, R, hr, hδ, hden, hR⟩ :=
    rep.ae_ball_den_lower_of_mem_domain hz
  have h_int :=
    nevanlinnaKernelC_integral_hasDerivAt_of_ae_ball_den_lower
      rep.ν hr hδ hden hR
  have h_const :
      HasDerivAt (fun _w : ℂ => (rep.alpha : ℂ)) 0 z :=
    hasDerivAt_const z (rep.alpha : ℂ)
  have h_linear :
      HasDerivAt (fun w : ℂ => ((rep.beta : ℝ) : ℂ) * w)
        ((rep.beta : ℝ) : ℂ) z :=
    by simpa using (hasDerivAt_id z).const_mul ((rep.beta : ℝ) : ℂ)
  have hsum := h_const.add (h_linear.add h_int)
  convert hsum using 1
  · ext w
    simp [NevanlinnaRepOnComplement.extension, add_assoc]
  · ring

/-- The complement-supported extension is differentiable throughout the Pick domain. -/
theorem NevanlinnaRepOnComplement.extension_differentiableOn
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) :
    DifferentiableOn ℂ rep.extension (upperHalfPlanePickIntervalDomain a b) := by
  intro z hz
  exact (rep.extension_hasDerivAt hz).differentiableAt.differentiableWithinAt

/-- The complement-supported extension is analytic on the interval Pick domain. -/
theorem NevanlinnaRepOnComplement.extension_analyticOn
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) :
    AnalyticOn ℂ rep.extension (upperHalfPlanePickIntervalDomain a b) :=
  (rep.extension_differentiableOn).analyticOn
    (isOpen_upperHalfPlanePickIntervalDomain a b)

/-- On the upper half-plane, the complement-supported extension agrees with `F`. -/
theorem NevanlinnaRepOnComplement.extension_eq_F_of_im_pos
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F)
    {z : ℂ} (hz : 0 < z.im) :
    rep.extension z = F (UpperHalfPlane.ofComplex z) := by
  have hkernel :
      (∫ t : ℝ, nevanlinnaKernelC t z ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ, nevanlinnaKernel t (UpperHalfPlane.ofComplex z)
          ∂(rep.ν : Measure ℝ) := by
    refine integral_congr_ae ?_
    exact ae_of_all _ fun t => nevanlinnaKernelC_eq_ofComplex t hz
  calc
    rep.extension z =
        (rep.alpha : ℂ) + (rep.beta : ℝ) * z +
          ∫ t : ℝ, nevanlinnaKernel t (UpperHalfPlane.ofComplex z)
            ∂(rep.ν : Measure ℝ) := by
          simp [NevanlinnaRepOnComplement.extension, hkernel]
    _ = F (UpperHalfPlane.ofComplex z) := by
          simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
            (rep.formula (UpperHalfPlane.ofComplex z)).symm

/-- The complement-supported extension has nonnegative imaginary part on the upper half-plane. -/
theorem NevanlinnaRepOnComplement.extension_mapsUpper
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (rep.extension z).im := by
  rw [rep.extension_eq_F_of_im_pos hz]
  exact rep.pick_nonnegative (UpperHalfPlane.ofComplex z)

/-- At a real point, the complex kernel has zero imaginary part. -/
theorem nevanlinnaKernelC_ofReal_im_eq_zero_of_ne
    {t x : ℝ} :
    (nevanlinnaKernelC t (x : ℂ)).im = 0 := by
  unfold nevanlinnaKernelC
  have hnum : (1 + (t : ℂ) * (x : ℂ)) = ((1 + t * x : ℝ) : ℂ) := by
    norm_num
  have hden : ((t : ℂ) - (x : ℂ)) = ((t - x : ℝ) : ℂ) := by
    norm_num
  rw [hnum, hden, ← Complex.ofReal_div]
  ring_nf
  simp

/-- On `(a,b)`, the complement-supported extension has real boundary values. -/
theorem NevanlinnaRepOnComplement.extension_real_im_zero
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    (rep.extension (x : ℂ)).im = 0 := by
  obtain ⟨r, δ, R, hr, hδ, hden, hR⟩ :=
    ae_ball_den_lower_of_real_mem_Ioo_of_support_complement (rep := rep) hx
  have hx_mem : (x : ℂ) ∈ Metric.ball (x : ℂ) r := by
    simpa [Metric.mem_ball] using hr
  have h_int : Integrable (fun t : ℝ => nevanlinnaKernelC t (x : ℂ))
      (rep.ν : Measure ℝ) := by
    exact nevanlinnaKernelC_integrable_of_ae_den_lower rep.ν hδ
      (hden.mono fun t ht => ht (x : ℂ) hx_mem) (hR (x : ℂ) hx_mem)
  have him_integral :
      (∫ t : ℝ, nevanlinnaKernelC t (x : ℂ) ∂(rep.ν : Measure ℝ)).im =
        ∫ t : ℝ, (nevanlinnaKernelC t (x : ℂ)).im ∂(rep.ν : Measure ℝ) := by
    simpa using (integral_im h_int).symm
  have hzero :
      (∫ t : ℝ, (nevanlinnaKernelC t (x : ℂ)).im ∂(rep.ν : Measure ℝ)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    exact ae_of_all _ fun t => nevanlinnaKernelC_ofReal_im_eq_zero_of_ne
  simp [NevanlinnaRepOnComplement.extension, Complex.add_im, Complex.mul_im,
    him_integral, hzero]

/-- A complement-supported Nevanlinna representation gives the interval Pick class. -/
theorem mem_pickInterval_of_nevanlinnaRepOnComplement
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRepOnComplement a b F) :
    MemPickInterval a b F := by
  refine ⟨?_⟩
  exact
    { G := rep.extension
      analyticOn := rep.extension_analyticOn
      agreesOnUpper := by
        intro z
        simpa [UpperHalfPlane.ofComplex_apply_of_im_pos z.coe_im_pos] using
          rep.extension_eq_F_of_im_pos z.coe_im_pos
      real_im_zero := by
        intro x hx
        exact rep.extension_real_im_zero hx
      mapsUpper := by
        intro z hz
        exact rep.extension_mapsUpper hz }

/-! ### Boundary approach inside the interval -/

/-- Vertical approach to a real point from the upper half-plane, using the
same scale as the Stieltjes uniqueness proof. -/
def upperHalfPlaneIntervalBoundarySeq (x : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) + (stieltjesUniqScale n : ℂ) * Complex.I

/-- The vertical boundary sequence lies in the upper half-plane. -/
theorem upperHalfPlaneIntervalBoundarySeq_im_pos (x : ℝ) (n : ℕ) :
    0 < (upperHalfPlaneIntervalBoundarySeq x n).im := by
  simpa [upperHalfPlaneIntervalBoundarySeq] using stieltjesUniqScale_pos n

/-- Its distance from the boundary point equals the Stieltjes uniqueness scale. -/
theorem upperHalfPlaneIntervalBoundarySeq_dist_ofReal (x : ℝ) (n : ℕ) :
    dist ((x : ℂ)) (upperHalfPlaneIntervalBoundarySeq x n) =
      stieltjesUniqScale n := by
  have hre :
      ((x : ℂ)).re = (upperHalfPlaneIntervalBoundarySeq x n).re := by
    simp [upperHalfPlaneIntervalBoundarySeq]
  rw [Complex.dist_of_re_eq hre]
  simp only [upperHalfPlaneIntervalBoundarySeq, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
    mul_zero, Real.dist_eq]
  have hnonneg : 0 ≤ stieltjesUniqScale n := le_of_lt (stieltjesUniqScale_pos n)
  simp [hnonneg]

/-- The vertical boundary sequence converges uniformly to the real boundary point. -/
theorem upperHalfPlaneIntervalBoundarySeq_tendstoUniformlyOn_ofReal
    (K : Set ℝ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ => upperHalfPlaneIntervalBoundarySeq x n)
      (fun x : ℝ => (x : ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall :
      ∀ᶠ n : ℕ in atTop, stieltjesUniqScale n < ε := by
    refine ((tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually (Metric.ball_mem_nhds (0 : ℝ) hε)).mono ?_
    intro n hn
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hbase : 1 / ((n : ℝ) + 1) < ε := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hden_pos] using hn
    have hle : stieltjesUniqScale n ≤ 1 / ((n : ℝ) + 1) := by
      unfold stieltjesUniqScale
      exact one_div_le_one_div_of_le hden_pos (by norm_num)
    exact lt_of_le_of_lt hle hbase
  filter_upwards [hsmall] with n hn x _hx
  simpa [upperHalfPlaneIntervalBoundarySeq_dist_ofReal] using hn

/-- The interval Pick extension is continuous at real points of `(a,b)`. -/
theorem PickExtensionOnInterval.continuousAt_real
    {a b : ℝ} {F : ℍ → ℂ} (pick : PickExtensionOnInterval a b F)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    ContinuousAt pick.G (x : ℂ) :=
  pick.analyticOn.continuousOn.continuousAt
    ((isOpen_upperHalfPlanePickIntervalDomain a b).mem_nhds
      (by
        right
        simpa using hx))

/-- Along the vertical boundary sequence, the imaginary part tends uniformly to zero
on compact subsets of `(a,b)`. -/
theorem PickExtensionOnInterval.boundary_im_tendstoUniformlyOn_zero_of_isCompact
    {a b : ℝ} {F : ℍ → ℂ} (pick : PickExtensionOnInterval a b F)
    {K : Set ℝ} (hKc : IsCompact K) (hKsub : K ⊆ Set.Ioo a b) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        (F (UpperHalfPlane.ofComplex
          (upperHalfPlaneIntervalBoundarySeq x n))).im)
      (fun _x : ℝ => 0) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hloc :
      ∀ x : K, ∃ δ : ℝ, 0 < δ ∧
        ∀ ⦃z : ℂ⦄, dist z (x : ℂ) < δ →
          dist ((pick.G z).im) 0 < ε := by
    intro x
    have hxI : (x : ℝ) ∈ Set.Ioo a b := hKsub x.2
    have hcont :
        ContinuousAt (fun z : ℂ => (pick.G z).im) (x : ℂ) :=
      Complex.continuous_im.continuousAt.comp
        (pick.continuousAt_real hxI)
    have hreal : (pick.G (x : ℂ)).im = 0 := pick.real_im_zero hxI
    rw [Metric.continuousAt_iff] at hcont
    rcases hcont ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro z hz
    simpa [hreal] using hδ hz
  choose δ hδpos hδ using hloc
  rcases hKc.elim_finite_subcover
      (fun x : K => Metric.ball (x : ℝ) (δ x / 4))
      (fun _x => Metric.isOpen_ball)
      (by
        intro x hx
        refine mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
        simp [Metric.mem_ball, hδpos]) with ⟨t, ht⟩
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ t, stieltjesUniqScale n < δ x / 4 := by
    rw [Filter.eventually_all_finset]
    intro x hx
    have hδquarter : 0 < δ x / 4 := by
      exact div_pos (hδpos x) (by norm_num)
    refine ((tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually
        (Metric.ball_mem_nhds (0 : ℝ) hδquarter)).mono ?_
    intro n hn
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    have hbase : 1 / ((n : ℝ) + 1) < δ x / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hden_pos] using hn
    have hle : stieltjesUniqScale n ≤ 1 / ((n : ℝ) + 1) := by
      unfold stieltjesUniqScale
      exact one_div_le_one_div_of_le hden_pos (by norm_num)
    exact lt_of_le_of_lt hle hbase
  filter_upwards [hevent] with n hn x hxK
  rcases mem_iUnion₂.1 (ht hxK) with ⟨c, hct, hxc⟩
  have hdist_vertical :
      dist ((x : ℂ)) (upperHalfPlaneIntervalBoundarySeq x n) =
        stieltjesUniqScale n :=
    upperHalfPlaneIntervalBoundarySeq_dist_ofReal x n
  have hzdist :
      dist (upperHalfPlaneIntervalBoundarySeq x n) (c : ℂ) < δ c := by
    calc
      dist (upperHalfPlaneIntervalBoundarySeq x n) (c : ℂ)
          ≤ dist (upperHalfPlaneIntervalBoundarySeq x n) (x : ℂ) +
              dist ((x : ℂ)) (c : ℂ) := dist_triangle _ _ _
      _ = stieltjesUniqScale n + dist x (c : ℝ) := by
            rw [dist_comm (upperHalfPlaneIntervalBoundarySeq x n) (x : ℂ),
              hdist_vertical]
            simpa using
              congrArg (fun r => stieltjesUniqScale n + r)
                (Complex.isometry_ofReal.dist_eq x (c : ℝ))
      _ < δ c / 4 + δ c / 4 := by
            exact add_lt_add (hn c hct) (by simpa [Metric.mem_ball] using hxc)
      _ < δ c := by
            linarith [hδpos c]
  have hagree :
      pick.G (upperHalfPlaneIntervalBoundarySeq x n) =
        F (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n)) := by
    have him := upperHalfPlaneIntervalBoundarySeq_im_pos x n
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos him] using
      pick.agreesOnUpper
        (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n))
  simpa [hagree] using hδ c hzdist

/-- The finite Poisson boundary integral is the imaginary part minus the linear slope. -/
theorem NevanlinnaRep.finiteBoundaryPoissonKernel_integral_eq_im_sub_slope
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (x y : ℝ) (hy : 0 < y) :
    (∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(rep.ν : Measure ℝ)) =
      (F (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).im -
        (rep.beta : ℝ) * y := by
  have h :=
    (poissonBoundaryMeasureData_of_nevanlinnaRep rep).poisson_formula x y hy
  dsimp [poissonBoundaryMeasureData_of_nevanlinnaRep] at h
  rw [poissonKernel_integral_nevanlinnaWeightedMeasure_eq_finiteBoundaryPoissonKernel] at h
  linarith

/-- The boundary-sequence finite Poisson integral equals the boundary imaginary part. -/
theorem NevanlinnaRep.finiteBoundaryPoissonKernel_integral_boundarySeq_eq
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (x : ℝ) (n : ℕ) :
    (∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ)) =
      (F (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n))).im -
        (rep.beta : ℝ) * stieltjesUniqScale n := by
  have h :=
    rep.finiteBoundaryPoissonKernel_integral_eq_im_sub_slope
      x (stieltjesUniqScale n) (stieltjesUniqScale_pos n)
  simpa [upperHalfPlaneIntervalBoundarySeq] using h

/-- The finite boundary Poisson kernel is nonnegative for nonnegative height. -/
theorem finiteBoundaryPoissonKernel_nonneg {t x y : ℝ} (hy : 0 ≤ y) :
    0 ≤ finiteBoundaryPoissonKernel t x y := by
  unfold finiteBoundaryPoissonKernel
  exact mul_nonneg ENNReal.toReal_nonneg
    (upperHalfPlanePoissonKernel_nonneg hy)

/-- Finite Poisson boundary integrals against a Nevanlinna measure are nonnegative. -/
theorem NevanlinnaRep.finiteBoundaryPoissonKernel_integral_nonneg
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(rep.ν : Measure ℝ) :=
  integral_nonneg fun _t => finiteBoundaryPoissonKernel_nonneg hy

/-- The boundary-sequence Poisson integral is bounded by the boundary imaginary part. -/
theorem NevanlinnaRep.finiteBoundaryPoissonKernel_integral_boundarySeq_le_im
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (x : ℝ) (n : ℕ) :
    (∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ)) ≤
      (F (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n))).im := by
  rw [rep.finiteBoundaryPoissonKernel_integral_boundarySeq_eq x n]
  have hβ_nonneg : 0 ≤ (rep.beta : ℝ) * stieltjesUniqScale n :=
    mul_nonneg rep.beta.2 (le_of_lt (stieltjesUniqScale_pos n))
  linarith

/-- The finite Poisson boundary integrals tend uniformly to zero on compact subintervals. -/
theorem NevanlinnaRep.finiteBoundaryPoissonKernel_integral_tendstoUniformlyOn_zero
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRep F) (pick : PickExtensionOnInterval a b F)
    {K : Set ℝ} (hKc : IsCompact K) (hKsub : K ⊆ Set.Ioo a b) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        ∫ t : ℝ,
          finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
            ∂(rep.ν : Measure ℝ))
      (fun _x : ℝ => 0) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hU :=
    Metric.tendstoUniformlyOn_iff.mp
      (pick.boundary_im_tendstoUniformlyOn_zero_of_isCompact hKc hKsub) ε hε
  filter_upwards [hU] with n hn x hxK
  have hinner_nonneg :
      0 ≤ ∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ) :=
    rep.finiteBoundaryPoissonKernel_integral_nonneg x
      (le_of_lt (stieltjesUniqScale_pos n))
  have him_nonneg :
      0 ≤ (F (UpperHalfPlane.ofComplex
        (upperHalfPlaneIntervalBoundarySeq x n))).im :=
    rep.pick_nonnegative
      (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n))
  have him_lt :
      (F (UpperHalfPlane.ofComplex
        (upperHalfPlaneIntervalBoundarySeq x n))).im < ε := by
    have hdist := hn x hxK
    simpa [Real.dist_eq, abs_of_nonneg him_nonneg] using hdist
  have hle :=
    rep.finiteBoundaryPoissonKernel_integral_boundarySeq_le_im x n
  simpa [Real.dist_eq, abs_of_nonneg hinner_nonneg] using hle.trans_lt him_lt

/-! ### Interior part of the Prop.144 test-integral bridge -/

/-- A test function that vanishes off `(a,b)` vanishes at both endpoints.
Proposition 1.44 of [simon2019]. -/
theorem interval_test_endpoint_values_zero
    {a b : ℝ} (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ) :
    g a = 0 ∧ g b = 0 := by
  constructor
  · exact hg_zero (by simp)
  · exact hg_zero (by simp)

/-- A continuous nonnegative interval test is uniformly small near the endpoints.
Proposition 1.44 of [simon2019]. -/
theorem interval_test_small_on_endpoint_collar
    {a b : ℝ} (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η := by
  have hleft0 : g a = 0 := (interval_test_endpoint_values_zero g hg_zero).1
  have hright0 : g b = 0 := (interval_test_endpoint_values_zero g hg_zero).2
  have hcontL : ContinuousAt g a := hg_cont.continuousAt
  have hcontR : ContinuousAt g b := hg_cont.continuousAt
  rw [Metric.continuousAt_iff] at hcontL
  rw [Metric.continuousAt_iff] at hcontR
  rcases hcontL η hη with ⟨δl, hδl, hδlprop⟩
  rcases hcontR η hη with ⟨δr, hδr, hδrprop⟩
  refine ⟨min δl δr, lt_min hδl hδr, ?_⟩
  intro x _hx hdist
  rcases hdist with hdist | hdist
  · have hxclose : dist x a < δl :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have habs : dist (g x) (g a) < η := hδlprop hxclose
    rw [hleft0] at habs
    simpa [Real.dist_eq, abs_of_nonneg (hg_nonneg x)] using habs.le
  · have hxclose : dist x b < δr :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have habs : dist (g x) (g b) < η := hδrprop hxclose
    rw [hright0] at habs
    simpa [Real.dist_eq, abs_of_nonneg (hg_nonneg x)] using habs.le

/-- The closed shrunken interval `[a + δ, b - δ]` is compact.
Proposition 1.44 of [simon2019]. -/
theorem intervalInteriorCompact_isCompact (a b δ : ℝ) :
    IsCompact (Set.Icc (a + δ) (b - δ)) :=
  isCompact_Icc

/-- A positive shrink lies inside the open interval `(a,b)`.
Proposition 1.44 of [simon2019]. -/
theorem intervalInteriorCompact_subset_Ioo
    {a b δ : ℝ} (hδpos : 0 < δ) :
    Set.Icc (a + δ) (b - δ) ⊆ Set.Ioo a b := by
  intro x hx
  rcases hx with ⟨hxL, hxR⟩
  constructor <;> linarith

/-- The boundary imaginary part tends uniformly to zero on a shrunken interval.
Proposition 1.44 of [simon2019]. -/
theorem PickExtensionOnInterval.boundary_im_tendstoUniformlyOn_zero_on_intervalInterior
    {a b : ℝ} {F : ℍ → ℂ} (pick : PickExtensionOnInterval a b F)
    {δ : ℝ} (hδpos : 0 < δ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        (F (UpperHalfPlane.ofComplex
          (upperHalfPlaneIntervalBoundarySeq x n))).im)
      (fun _x : ℝ => 0) atTop (Set.Icc (a + δ) (b - δ)) := by
  exact pick.boundary_im_tendstoUniformlyOn_zero_of_isCompact
    (intervalInteriorCompact_isCompact a b δ)
    (intervalInteriorCompact_subset_Ioo hδpos)

/-- Weighted Poisson test integrand for the interval-support argument.
Proposition 1.44 of [simon2019]. -/
noncomputable def upperHalfPlaneIntervalWeightedPoissonIntegrand
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  g x * Real.pi⁻¹ *
    (∫ t : ℝ,
      finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
        ∂(ν : Measure ℝ))

/-- The weighted Poisson test integrand is nonnegative for nonnegative tests.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonIntegrand_nonneg
    {F : ℍ → ℂ} (rep : NevanlinnaRep F)
    (g : ℝ → ℝ) (hg_nonneg : 0 ≤ g) (n : ℕ) (x : ℝ) :
    0 ≤ upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x := by
  unfold upperHalfPlaneIntervalWeightedPoissonIntegrand
  have hinner :
      0 ≤ ∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ) :=
    rep.finiteBoundaryPoissonKernel_integral_nonneg x
      (le_of_lt (stieltjesUniqScale_pos n))
  exact mul_nonneg (mul_nonneg (hg_nonneg x) (inv_nonneg.mpr Real.pi_pos.le))
    hinner

/-- The interval normalization factor `π⁻¹` is at most one.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeight_le_one :
    (Real.pi)⁻¹ ≤ (1 : ℝ) :=
  inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])

/-- The weighted Poisson integrand is bounded by the unweighted Poisson integral.
Proposition 1.44 of [simon2019]. -/
theorem NevanlinnaRep.upperHalfPlaneIntervalWeightedPoissonIntegrand_le_integral
    {F : ℍ → ℂ} (rep : NevanlinnaRep F)
    (g : ℝ → ℝ) (hg_le_one : g ≤ 1)
    (n : ℕ) (x : ℝ) :
    upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x ≤
      ∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ) := by
  have hinner_nonneg :
      0 ≤ ∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(rep.ν : Measure ℝ) :=
    rep.finiteBoundaryPoissonKernel_integral_nonneg x
      (le_of_lt (stieltjesUniqScale_pos n))
  have hfac_le : g x * Real.pi⁻¹ ≤ 1 := by
    exact mul_le_one₀ (hg_le_one x) (inv_nonneg.mpr Real.pi_pos.le)
      upperHalfPlaneIntervalWeight_le_one
  calc
    upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x
        ≤ 1 *
          (∫ t : ℝ,
            finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
              ∂(rep.ν : Measure ℝ)) := by
          unfold upperHalfPlaneIntervalWeightedPoissonIntegrand
          exact mul_le_mul_of_nonneg_right hfac_le hinner_nonneg
    _ = ∫ t : ℝ,
          finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
            ∂(rep.ν : Measure ℝ) := by ring

/-- The weighted Poisson integrand is bounded by the boundary imaginary part of `F`.
Proposition 1.44 of [simon2019]. -/
theorem NevanlinnaRep.upperHalfPlaneIntervalWeightedPoissonIntegrand_le_boundary_im
    {F : ℍ → ℂ} (rep : NevanlinnaRep F)
    (g : ℝ → ℝ) (_hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (n : ℕ) (x : ℝ) :
    upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x ≤
      (F (UpperHalfPlane.ofComplex (upperHalfPlaneIntervalBoundarySeq x n))).im := by
  exact
    (rep.upperHalfPlaneIntervalWeightedPoissonIntegrand_le_integral
      g hg_le_one n x).trans
      (rep.finiteBoundaryPoissonKernel_integral_boundarySeq_le_im x n)

/-- The weighted Poisson integral over a shrunken interval tends to zero.
Proposition 1.44 of [simon2019]. -/
theorem NevanlinnaRep.upperHalfPlaneIntervalWeightedPoissonInterior_tendsto_zero
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRep F) (pick : PickExtensionOnInterval a b F)
    (g : ℝ → ℝ) (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    {δ : ℝ} (hδpos : 0 < δ) :
    Tendsto
      (fun n : ℕ => ∫ x in Set.Icc (a + δ) (b - δ),
        upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x)
      atTop (𝓝 0) := by
  let K : Set ℝ := Set.Icc (a + δ) (b - δ)
  have hKcompact : IsCompact K := intervalInteriorCompact_isCompact a b δ
  have hKfinite : (volume : Measure ℝ) K < (⊤ : ENNReal) := hKcompact.measure_lt_top
  have hU :
      TendstoUniformlyOn
        (fun n : ℕ => fun x : ℝ =>
          ∫ t : ℝ,
            finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
              ∂(rep.ν : Measure ℝ))
        (fun _x : ℝ => 0) atTop K := by
    exact rep.finiteBoundaryPoissonKernel_integral_tendstoUniformlyOn_zero
      pick hKcompact (intervalInteriorCompact_subset_Ioo hδpos)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := ε / ((volume : Measure ℝ).real K + 1)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hUevent := (Metric.tendstoUniformlyOn_iff.mp hU) C hCpos
  filter_upwards [hUevent] with n hn
  have hnorm :
      ‖∫ x in K,
          upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x
          ∂(volume : Measure ℝ)‖ ≤
        C * (volume : Measure ℝ).real K := by
    refine norm_setIntegral_le_of_norm_le_const hKfinite ?_
    intro x hx
    have hinner_nonneg :
        0 ≤ ∫ t : ℝ,
          finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
            ∂(rep.ν : Measure ℝ) :=
      rep.finiteBoundaryPoissonKernel_integral_nonneg x
        (le_of_lt (stieltjesUniqScale_pos n))
    have hinner_lt :
        (∫ t : ℝ,
          finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
            ∂(rep.ν : Measure ℝ)) < C := by
      have hdist := hn x hx
      simpa [Real.dist_eq, abs_of_nonneg hinner_nonneg] using hdist
    have hle := rep.upperHalfPlaneIntervalWeightedPoissonIntegrand_le_integral
      g hg_le_one n x
    have hnonneg :=
      upperHalfPlaneIntervalWeightedPoissonIntegrand_nonneg rep g hg_nonneg n x
    rw [Real.norm_of_nonneg hnonneg]
    exact hle.trans hinner_lt.le
  · have hprod_lt : C * (volume : Measure ℝ).real K < ε := by
      have hM_nonneg : 0 ≤ (volume : Measure ℝ).real K := ENNReal.toReal_nonneg
      dsimp [C]
      have hden_pos : 0 < (volume : Measure ℝ).real K + 1 := by positivity
      have hM_lt : (volume : Measure ℝ).real K <
          (volume : Measure ℝ).real K + 1 := by linarith
      calc
        ε / ((volume : Measure ℝ).real K + 1) *
            (volume : Measure ℝ).real K
            < ε / ((volume : Measure ℝ).real K + 1) *
                ((volume : Measure ℝ).real K + 1) := by
              exact mul_lt_mul_of_pos_left hM_lt (by positivity)
        _ = ε := by field_simp [hden_pos.ne']
    simpa [K, Real.dist_eq] using hnorm.trans_lt hprod_lt

/-- Collar of points in `[a,b]` that are within `δ` of an endpoint.
Proposition 1.44 of [simon2019]. -/
def intervalEndpointCollar (a b δ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc a b ∧ (dist x a < δ ∨ dist x b < δ)}

/-- The endpoint collar is measurable.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_measurableSet (a b δ : ℝ) :
    MeasurableSet (intervalEndpointCollar a b δ) := by
  unfold intervalEndpointCollar
  measurability

/-- The indicator of a continuous test on the endpoint collar is a.e. strongly measurable.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_indicator_aestronglyMeasurable
    {a b : ℝ} (g : ℝ → ℝ) (hg_cont : Continuous g) (δ : ℝ) :
    AEStronglyMeasurable ((intervalEndpointCollar a b δ).indicator g)
      (volume : Measure ℝ) := by
  have hmeas : Measurable ((intervalEndpointCollar a b δ).indicator g) :=
    hg_cont.measurable.indicator (intervalEndpointCollar_measurableSet a b δ)
  exact hmeas.aestronglyMeasurable

/-- The endpoint-collar indicator of a nonnegative test is nonnegative.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_indicator_nonneg
    {a b : ℝ} (g : ℝ → ℝ) (hg_nonneg : 0 ≤ g) (δ : ℝ) :
    0 ≤ (intervalEndpointCollar a b δ).indicator g := by
  intro x
  by_cases hx : x ∈ intervalEndpointCollar a b δ
  · simpa [Set.indicator_of_mem hx] using hg_nonneg x
  · simp [Set.indicator_of_notMem hx]

/-- A test small on the endpoint collar bounds its collar indicator by `η`.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_indicator_le
    {a b : ℝ} (g : ℝ → ℝ) {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η) :
    (intervalEndpointCollar a b δ).indicator g ≤ fun _x : ℝ => η := by
  intro x
  by_cases hx : x ∈ intervalEndpointCollar a b δ
  · rcases hx with ⟨hxI, hxdist⟩
    rw [Set.indicator_of_mem (show x ∈ intervalEndpointCollar a b δ from ⟨hxI, hxdist⟩)]
    exact hsmall x hxI hxdist
  · rw [Set.indicator_of_notMem hx]
    exact hη_nonneg

/-- The open interval is covered by the shrunken interior and endpoint collar.
Proposition 1.44 of [simon2019]. -/
theorem Ioo_subset_intervalInterior_union_endpointCollar
    {a b δ : ℝ} :
    Set.Ioo a b ⊆
      Set.Icc (a + δ) (b - δ) ∪ intervalEndpointCollar a b δ := by
  intro x hxI
  by_cases hxK : x ∈ Set.Icc (a + δ) (b - δ)
  · exact Or.inl hxK
  · right
    rcases hxI with ⟨hxL, hxR⟩
    unfold intervalEndpointCollar
    refine ⟨⟨hxL.le, hxR.le⟩, ?_⟩
    simp only [Set.mem_Icc, not_and_or] at hxK
    rcases hxK with hxleft | hxright
    · left
      rw [Real.dist_eq]
      have hnonneg : 0 ≤ x - a := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
    · right
      rw [Real.dist_eq]
      have hnonpos : x - b ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith

/-- The shrunken interior and endpoint collar are disjoint.
Proposition 1.44 of [simon2019]. -/
theorem intervalInterior_disjoint_endpointCollar
    {a b δ : ℝ} :
    Disjoint (Set.Icc (a + δ) (b - δ)) (intervalEndpointCollar a b δ) := by
  rw [Set.disjoint_left]
  intro x hxK hxC
  rcases hxK with ⟨hxKL, hxKR⟩
  rcases hxC with ⟨hxI, hxdist⟩
  rcases hxdist with hleft | hright
  · rw [Real.dist_eq] at hleft
    have hδpos : 0 < δ := lt_of_le_of_lt (abs_nonneg (x - a)) hleft
    have hxa_ge : δ ≤ x - a := by linarith
    have hnonneg : 0 ≤ x - a := le_trans hδpos.le hxa_ge
    rw [abs_of_nonneg hnonneg] at hleft
    linarith
  · rw [Real.dist_eq] at hright
    have hδpos : 0 < δ := lt_of_le_of_lt (abs_nonneg (x - b)) hright
    have hxb_le : x - b ≤ -δ := by linarith
    have hnonpos : x - b ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos] at hright
    linarith

/-- The weighted Poisson integrand vanishes outside `(a,b)` when the test does.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_zero_of_not_mem_Ioo
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ)
    {a b : ℝ} (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (n : ℕ) {x : ℝ} (hx : x ∉ Set.Ioo a b) :
    upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x = 0 := by
  have hxzero : g x = 0 := hg_zero hx
  simp [upperHalfPlaneIntervalWeightedPoissonIntegrand, hxzero]

/-- Rewrites the finite Poisson kernel with `π⁻¹` as a weighted Cauchy density.
Proposition 1.44 of [simon2019]. -/
theorem finiteBoundaryPoissonKernel_mul_pi_inv_eq_weighted_cauchy
    (g : ℝ → ℝ) (n : ℕ) (t x : ℝ) :
    g x * Real.pi⁻¹ *
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n) =
      (nevanlinnaWeightedMeasureDensity t).toReal *
        (g x *
          ProbabilityTheory.cauchyPDFReal t
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x) := by
  have hε : 0 ≤ stieltjesUniqScale n := (stieltjesUniqScale_pos n).le
  rw [← cauchyPDFReal_comm x t hε]
  rw [cauchyPDFReal_eq_pi_inv_mul_upperHalfPlanePoissonKernel x t hε]
  unfold finiteBoundaryPoissonKernel
  ring

/-- The weighted Poisson integrand equals an inner weighted Cauchy integral.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_cauchy_inner
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x =
      ∫ t : ℝ,
        (nevanlinnaWeightedMeasureDensity t).toReal *
          (g x *
            ProbabilityTheory.cauchyPDFReal t
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
        ∂(ν : Measure ℝ) := by
  calc
    upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x =
        g x * Real.pi⁻¹ *
          (∫ t : ℝ,
            finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
              ∂(ν : Measure ℝ)) := by
          rfl
    _ = ∫ t : ℝ,
          g x * Real.pi⁻¹ *
            finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(ν : Measure ℝ) := by
          rw [integral_const_mul]
    _ = ∫ t : ℝ,
        (nevanlinnaWeightedMeasureDensity t).toReal *
          (g x *
            ProbabilityTheory.cauchyPDFReal t
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
        ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            finiteBoundaryPoissonKernel_mul_pi_inv_eq_weighted_cauchy g n t x

/-- Cauchy averages at the Stieltjes scale converge to the test value.
Proposition 1.44 of [simon2019]. -/
theorem intervalCauchyAverage_tendsto
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) (t : ℝ) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ,
        g x *
          ProbabilityTheory.cauchyPDFReal t
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
      atTop (𝓝 (g t)) := by
  exact unitIntervalHerglotz_cauchyAverage_tendsto_stieltjesUniqScale
    g t 1 hg_cont
    (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by
        have hx0 : 0 ≤ g x := hg_nonneg x
        linarith, hg_le_one x⟩)

/-- Weighted Cauchy averages converge to the density-weighted test value.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedCauchyAverage_tendsto
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (nevanlinnaWeightedMeasureDensity t).toReal *
          ∫ x : ℝ,
            g x *
              ProbabilityTheory.cauchyPDFReal t
                ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
      atTop
        (𝓝 ((nevanlinnaWeightedMeasureDensity t).toReal * g t)) := by
  exact tendsto_const_nhds.mul
    (intervalCauchyAverage_tendsto g hg_cont hg_nonneg hg_le_one t)

/-! ### Prop.144 weighted-test normalization -/

/-- A uniform bound for the interval weight `1 + x^2` on `[a,b]`.
Proposition 1.44 of [simon2019]. -/
def intervalWeightBound (a b : ℝ) : ℝ :=
  1 + (|a| + |b| + 1) ^ (2 : ℕ)

/-- The interval weight bound is nonnegative.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightBound_nonneg (a b : ℝ) :
    0 ≤ intervalWeightBound a b := by
  unfold intervalWeightBound
  positivity

/-- On `[a,b]`, the weight `1 + x^2` is bounded by `intervalWeightBound`.
Proposition 1.44 of [simon2019]. -/
theorem one_add_sq_le_intervalWeightBound_of_mem_Icc
    {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    1 + x ^ (2 : ℕ) ≤ intervalWeightBound a b := by
  let M : ℝ := |a| + |b| + 1
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hx_abs_le : |x| ≤ M := by
    have hx_upper : x ≤ M := by
      have hb_le_abs : b ≤ |b| := le_abs_self b
      have ha_abs_nonneg : 0 ≤ |a| := abs_nonneg a
      dsimp [M]
      linarith [hx.2, hb_le_abs, ha_abs_nonneg]
    have hx_lower : -M ≤ x := by
      have hneg_abs_le_a : -|a| ≤ a := by
        have h : -a ≤ |a| := by
          simpa using (le_abs_self (-a))
        linarith
      have hb_abs_nonneg : 0 ≤ |b| := abs_nonneg b
      dsimp [M]
      linarith [hx.1, hneg_abs_le_a, hb_abs_nonneg]
    exact abs_le.mpr ⟨hx_lower, hx_upper⟩
  have hx_sq : x ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    have hx_abs_sq : |x| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      nlinarith [hx_abs_le, abs_nonneg x, hM_nonneg]
    simpa [sq_abs] using hx_abs_sq
  unfold intervalWeightBound
  dsimp [M] at hx_sq
  linarith

/-- On `(a,b)`, the weight `1 + x^2` is bounded by `intervalWeightBound`.
Proposition 1.44 of [simon2019]. -/
theorem one_add_sq_le_intervalWeightBound_of_mem_Ioo
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    1 + x ^ (2 : ℕ) ≤ intervalWeightBound a b :=
  one_add_sq_le_intervalWeightBound_of_mem_Icc
    ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- Test function multiplied by the Nevanlinna weight `1 + x^2`.
Proposition 1.44 of [simon2019]. -/
def intervalWeightedTest (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  g x * (1 + x ^ (2 : ℕ))

/-- The interval weighted test is measurable when the original test is continuous.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedTest_measurable
    {g : ℝ → ℝ} (hg_cont : Continuous g) :
    Measurable (intervalWeightedTest g) := by
  unfold intervalWeightedTest
  fun_prop

/-- A nonnegative test gives a nonnegative weighted test.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedTest_nonneg
    {g : ℝ → ℝ} (hg_nonneg : 0 ≤ g) :
    0 ≤ intervalWeightedTest g := by
  intro x
  unfold intervalWeightedTest
  exact mul_nonneg (hg_nonneg x) (by positivity)

/-- A bounded interval test is bounded by the interval weight bound after weighting.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedTest_le_intervalWeightBound
    {a b : ℝ} {g : ℝ → ℝ}
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_le_one : g ≤ 1) :
    intervalWeightedTest g ≤ fun _x : ℝ => intervalWeightBound a b := by
  intro x
  by_cases hx : x ∈ Set.Ioo a b
  · unfold intervalWeightedTest
    calc
      g x * (1 + x ^ (2 : ℕ))
          ≤ 1 * (1 + x ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_right (hg_le_one x) (by positivity)
      _ = 1 + x ^ (2 : ℕ) := by ring
      _ ≤ intervalWeightBound a b :=
            one_add_sq_le_intervalWeightBound_of_mem_Ioo hx
  · have hgx : g x = 0 := hg_zero hx
    simp [intervalWeightedTest, hgx, intervalWeightBound_nonneg]

/-- A bounded test controls the norm of the unit-kernel `x` integral. -/
theorem unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_of_test_le_scale
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η ε : ℝ} (hη_nonneg : 0 ≤ η) (hε : 0 < ε) (hε_le : ε ≤ 1)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (y : ℝ) :
    ‖∫ x : ℝ, u x * unitIntervalHerglotzProp35TestKernel ε x y‖
      ≤ η * 4 := by
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hinner_norm := MeasureTheory.norm_integral_le_integral_norm
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
  have hmono :
      (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖) ≤
        ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := by
    refine integral_mono hUK_norm_int (hK_norm_int.const_mul η) ?_
    intro x
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hK_bound :
      (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 :=
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete hε hε_le
  calc
    ‖∫ x : ℝ, u x * unitIntervalHerglotzProp35TestKernel ε x y‖
        ≤ ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ :=
          hinner_norm
    _ ≤ ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := hmono
    _ = η * (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) := by
          rw [integral_const_mul]
    _ ≤ η * 4 := mul_le_mul_of_nonneg_left hK_bound hη_nonneg

/-- A bounded test controls the integral of the unit-kernel integrand norm. -/
theorem unitIntervalHerglotzProp35TestKernel_xIntegral_norm_integral_bound_of_test_le_scale
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η ε : ℝ} (hη_nonneg : 0 ≤ η) (hε : 0 < ε) (hε_le : ε ≤ 1)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (y : ℝ) :
    (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      ≤ η * 4 := by
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hmono :
      (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖) ≤
        ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := by
    refine integral_mono hUK_norm_int (hK_norm_int.const_mul η) ?_
    intro x
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hK_bound :
      (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 :=
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete hε hε_le
  calc
    (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
        ≤ ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := hmono
    _ = η * (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) := by
          rw [integral_const_mul]
    _ ≤ η * 4 := mul_le_mul_of_nonneg_left hK_bound hη_nonneg

/-- A bounded test makes the unit-kernel `x` integrand integrable. -/
theorem unitIntervalHerglotzProp35TestKernel_integrable_x_of_test_le_scale
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η ε : ℝ} (hη_nonneg : 0 ≤ η) (hε : 0 < ε)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (y : ℝ) :
    Integrable (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  exact (integrable_norm_iff hUK_meas).1 hUK_norm_int

/-- A bounded test makes the weighted Poisson kernel integrable on the product.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedPoissonKernel_integrable_prod_of_test_le
    (ν : FiniteMeasure ℝ)
    (u : ℝ → ℝ) (hu_meas : Measurable u)
    {η ε : ℝ} (hη_nonneg : 0 ≤ η) (hε : 0 < ε) (hε_le : ε ≤ 1)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η) :
    Integrable (Function.uncurry fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel ε x t)
      ((volume : Measure ℝ).prod (ν : Measure ℝ)) := by
  let F : ℝ × ℝ → ℝ := Function.uncurry fun x t : ℝ =>
    u x * unitIntervalHerglotzProp35TestKernel ε x t
  have hF : AEStronglyMeasurable F
      ((volume : Measure ℝ).prod (ν : Measure ℝ)) := by
    have hm : Measurable F := by
      dsimp [F, Function.uncurry]
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  have hnorm_meas : AEStronglyMeasurable
      (fun t : ℝ => ∫ x : ℝ,
        ‖u x * unitIntervalHerglotzProp35TestKernel ε x t‖)
      (ν : Measure ℝ) := by
    have hs := hF.norm.prod_swap
    simpa [F, Function.comp_def, Function.uncurry] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := (ν : Measure ℝ)) (ν := (volume : Measure ℝ)) hs)
  have hnorm_int : Integrable
      (fun t : ℝ => ∫ x : ℝ,
        ‖u x * unitIntervalHerglotzProp35TestKernel ε x t‖)
      (ν : Measure ℝ) := by
    refine (MeasureTheory.integrable_const (η * 4)).mono' hnorm_meas ?_
    filter_upwards with t
    have hnonneg :
        0 ≤ ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x t‖ := by
      exact integral_nonneg_of_ae
        (MeasureTheory.ae_of_all (volume : Measure ℝ) fun x => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact
      unitIntervalHerglotzProp35TestKernel_xIntegral_norm_integral_bound_of_test_le_scale
        u hu_meas.aestronglyMeasurable hη_nonneg hε hε_le
        hu_nonneg hu_le t
  have hprod := (MeasureTheory.integrable_prod_iff' hF).2 ?_
  · simpa [F, Function.uncurry] using hprod
  constructor
  · exact MeasureTheory.ae_of_all (ν : Measure ℝ) fun t =>
      unitIntervalHerglotzProp35TestKernel_integrable_x_of_test_le_scale
        u hu_meas.aestronglyMeasurable hη_nonneg hε hu_nonneg hu_le t
  · exact hnorm_int

/-- The weighted test times the unit kernel is the finite-boundary Cauchy density.
Proposition 1.44 of [simon2019]. -/
theorem intervalWeightedTest_unitKernel_eq_finiteBoundary_cauchy
    (g : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x t : ℝ) :
    intervalWeightedTest g x * unitIntervalHerglotzProp35TestKernel ε x t =
      (nevanlinnaWeightedMeasureDensity t).toReal *
        (g x * ProbabilityTheory.cauchyPDFReal t ⟨ε, hε⟩ x) := by
  rw [unitIntervalHerglotzProp35TestKernel_eq_weighted_cauchyPDFReal hε]
  unfold intervalWeightedTest
  rw [nevanlinnaWeightedMeasureDensity, ENNReal.toReal_ofReal]
  · have hx : 1 + x ^ (2 : ℕ) ≠ 0 := by positivity
    field_simp [hx]
  · positivity

/-- Rewrite the weighted Poisson integrand as an inner unit-kernel integral.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_unitKernel_inner
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x =
      ∫ t : ℝ,
        intervalWeightedTest g x *
          unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
        ∂(ν : Measure ℝ) := by
  calc
    upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal *
            (g x *
              ProbabilityTheory.cauchyPDFReal t
                ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
          ∂(ν : Measure ℝ) :=
          upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_cauchy_inner ν g n x
    _ = ∫ t : ℝ,
        intervalWeightedTest g x *
          unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
        ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            (intervalWeightedTest_unitKernel_eq_finiteBoundary_cauchy
              g (stieltjesUniqScale_pos n).le x t).symm

/-- The weighted Poisson integrand is integrable for compactly supported tests.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonIntegrand_integrable
    (ν : FiniteMeasure ℝ) {a b : ℝ} (g : ℝ → ℝ)
    (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (n : ℕ) :
    Integrable (fun x : ℝ =>
      upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x)
      (volume : Measure ℝ) := by
  let u : ℝ → ℝ := intervalWeightedTest g
  have hu_meas : Measurable u := by
    simpa [u] using intervalWeightedTest_measurable hg_cont
  have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
    simpa [u] using intervalWeightedTest_nonneg hg_nonneg
  have hu_le : ∀ x : ℝ, u x ≤ intervalWeightBound a b := by
    simpa [u] using
      intervalWeightedTest_le_intervalWeightBound
        (a := a) (b := b) (g := g) hg_zero hg_le_one
  have hprodInt : Integrable (Function.uncurry fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
      ((volume : Measure ℝ).prod (ν : Measure ℝ)) :=
    intervalWeightedPoissonKernel_integrable_prod_of_test_le
      ν u hu_meas (intervalWeightBound_nonneg a b)
      (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
      hu_nonneg hu_le
  have hxint : Integrable (fun x : ℝ => ∫ t : ℝ,
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
      ∂(ν : Measure ℝ)) (volume : Measure ℝ) := by
    simpa [Function.uncurry] using
      MeasureTheory.Integrable.integral_prod_left hprodInt
  refine hxint.congr ?_
  filter_upwards with x
  simpa [u] using
    (upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_unitKernel_inner
      ν g n x).symm

/-- The endpoint-collar weighted-test indicator is nonnegative.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_indicator_weightedTest_nonneg
    {a b : ℝ} (g : ℝ → ℝ) (hg_nonneg : 0 ≤ g) (δ : ℝ) :
    ∀ x : ℝ,
      0 ≤ (intervalEndpointCollar a b δ).indicator (intervalWeightedTest g) x := by
  intro x
  by_cases hx : x ∈ intervalEndpointCollar a b δ
  · rw [Set.indicator_of_mem hx]
    exact intervalWeightedTest_nonneg hg_nonneg x
  · rw [Set.indicator_of_notMem hx]

/-- Smallness of the test on the collar bounds the weighted-test indicator.
Proposition 1.44 of [simon2019]. -/
theorem intervalEndpointCollar_indicator_weightedTest_le
    {a b : ℝ} (g : ℝ → ℝ) {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η) :
    ∀ x : ℝ,
      (intervalEndpointCollar a b δ).indicator (intervalWeightedTest g) x ≤
        η * intervalWeightBound a b := by
  intro x
  by_cases hx : x ∈ intervalEndpointCollar a b δ
  · rcases hx with ⟨hxI, hxdist⟩
    rw [Set.indicator_of_mem (show x ∈ intervalEndpointCollar a b δ from ⟨hxI, hxdist⟩)]
    unfold intervalWeightedTest
    exact mul_le_mul (hsmall x hxI hxdist)
      (one_add_sq_le_intervalWeightBound_of_mem_Icc hxI)
      (by positivity) hη_nonneg
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg hη_nonneg (intervalWeightBound_nonneg a b)

/-- The endpoint-collar unit-kernel integral is bounded by the collar scale.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonEndpointCollar_bound
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_nonneg : 0 ≤ g)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η)
    (n : ℕ) :
    ‖∫ t : ℝ, (∫ x : ℝ,
        (intervalEndpointCollar a b δ).indicator (intervalWeightedTest g) x *
          unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
        ∂(ν : Measure ℝ)‖ ≤
      ((η * intervalWeightBound a b) * 4) *
        (ν : Measure ℝ).real Set.univ := by
  refine MeasureTheory.norm_integral_le_of_norm_le_const ?_
  exact MeasureTheory.ae_of_all (ν : Measure ℝ) fun t =>
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_of_test_le_scale
      ((intervalEndpointCollar a b δ).indicator (intervalWeightedTest g))
      ((intervalWeightedTest_measurable hg_cont).indicator
        (intervalEndpointCollar_measurableSet a b δ)).aestronglyMeasurable
      (mul_nonneg hη_nonneg (intervalWeightBound_nonneg a b))
      (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
      (intervalEndpointCollar_indicator_weightedTest_nonneg
        g hg_nonneg δ)
      (intervalEndpointCollar_indicator_weightedTest_le
        g hη_nonneg hsmall)
      t

/-- Fubini rewrites the endpoint-collar weighted Poisson set integral.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonEndpointCollar_setIntegral_eq_fubini
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_nonneg : 0 ≤ g)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η)
    (n : ℕ) :
    (∫ x in intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) =
      ∫ t : ℝ, (∫ x : ℝ,
        (intervalEndpointCollar a b δ).indicator (intervalWeightedTest g) x *
          unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
        ∂(ν : Measure ℝ) := by
  let u : ℝ → ℝ :=
    (intervalEndpointCollar a b δ).indicator (intervalWeightedTest g)
  have hu_meas : Measurable u :=
    (intervalWeightedTest_measurable hg_cont).indicator
      (intervalEndpointCollar_measurableSet a b δ)
  have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
    simpa [u] using
      intervalEndpointCollar_indicator_weightedTest_nonneg
        g hg_nonneg δ
  have hu_le : ∀ x : ℝ, u x ≤ η * intervalWeightBound a b := by
    simpa [u] using
      intervalEndpointCollar_indicator_weightedTest_le
        g hη_nonneg hsmall
  have hInt : Integrable (Function.uncurry fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
      ((volume : Measure ℝ).prod (ν : Measure ℝ)) :=
    intervalWeightedPoissonKernel_integrable_prod_of_test_le
      ν u hu_meas
      (mul_nonneg hη_nonneg (intervalWeightBound_nonneg a b))
      (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
      hu_nonneg hu_le
  have hswap := integral_integral_swap
    (μ := (volume : Measure ℝ)) (ν := (ν : Measure ℝ))
    (f := fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
    hInt
  have hleft_u :
      (∫ x in intervalEndpointCollar a b δ,
          upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) =
        ∫ x in intervalEndpointCollar a b δ,
          ∫ t : ℝ,
            intervalWeightedTest g x *
              unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
            ∂(ν : Measure ℝ) := by
    refine setIntegral_congr_fun (intervalEndpointCollar_measurableSet a b δ) ?_
    intro x _hx
    exact upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_unitKernel_inner
      ν g n x
  have hcollar_u :
      (∫ x in intervalEndpointCollar a b δ,
          ∫ t : ℝ,
            intervalWeightedTest g x *
              unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
            ∂(ν : Measure ℝ)) =
        ∫ x in intervalEndpointCollar a b δ,
          ∫ t : ℝ,
            u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
            ∂(ν : Measure ℝ) := by
    refine setIntegral_congr_fun (intervalEndpointCollar_measurableSet a b δ) ?_
    intro x hx
    dsimp [u]
    rw [Set.indicator_of_mem hx]
  have hu_support :
      (∫ x in intervalEndpointCollar a b δ,
          ∫ t : ℝ,
            u x *
              unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
            ∂(ν : Measure ℝ)) =
        ∫ x : ℝ, ∫ t : ℝ,
          u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
          ∂(ν : Measure ℝ) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure ℝ))
      (s := intervalEndpointCollar a b δ)
      (f := fun x : ℝ => ∫ t : ℝ,
        u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
        ∂(ν : Measure ℝ)) ?_
    intro x hx
    dsimp [u]
    rw [Set.indicator_of_notMem hx]
    simp
  rw [hleft_u, hcollar_u, hu_support]
  simpa [u, Function.uncurry] using hswap

/-- The endpoint-collar set integral is bounded by the collar smallness scale.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalWeightedPoissonEndpointCollar_setIntegral_norm_bound
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_nonneg : 0 ≤ g)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc a b →
        (dist x a < δ ∨ dist x b < δ) → g x ≤ η)
    (n : ℕ) :
    ‖∫ x in intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x‖ ≤
      ((η * intervalWeightBound a b) * 4) *
        (ν : Measure ℝ).real Set.univ := by
  rw [upperHalfPlaneIntervalWeightedPoissonEndpointCollar_setIntegral_eq_fubini
    ν g hg_cont hg_nonneg hη_nonneg hsmall n]
  exact upperHalfPlaneIntervalWeightedPoissonEndpointCollar_bound
    ν g hg_cont hg_nonneg hη_nonneg hsmall n

/-! ### Test-integral bridge for the reverse direction -/

/-- The weighted Nevanlinna measure is finite on every compact interval. -/
theorem nevanlinnaWeightedMeasure_Icc_lt_top
    (ν : FiniteMeasure ℝ) (a b : ℝ) :
    nevanlinnaWeightedMeasure ν (Set.Icc a b) < ⊤ := by
  let M : ℝ := |a| + |b| + 1
  let C : NNReal := ⟨1 + M ^ (2 : ℕ), by nlinarith [sq_nonneg M]⟩
  have hbound :
      ∃ C : NNReal, ∀ x : ℝ,
        (Set.Icc a b).indicator nevanlinnaWeightedMeasureDensity x ≤
          (C : ENNReal) := by
    refine ⟨C, ?_⟩
    intro x
    by_cases hx : x ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hx]
      have hM_nonneg : 0 ≤ M := by
        dsimp [M]
        positivity
      have hx_abs_le : |x| ≤ M := by
        have hx_upper : x ≤ M := by
          have hb_le_abs : b ≤ |b| := le_abs_self b
          have ha_abs_nonneg : 0 ≤ |a| := abs_nonneg a
          dsimp [M]
          linarith [hx.2, hb_le_abs, ha_abs_nonneg]
        have hx_lower : -M ≤ x := by
          have hneg_abs_le_a : -|a| ≤ a := by
            have h : -a ≤ |a| := by
              simpa using (le_abs_self (-a))
            linarith
          have hb_abs_nonneg : 0 ≤ |b| := abs_nonneg b
          dsimp [M]
          linarith [hx.1, hneg_abs_le_a, hb_abs_nonneg]
        exact abs_le.mpr ⟨hx_lower, hx_upper⟩
      have hx_sq : x ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
        have hx_abs_sq : |x| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
          nlinarith [hx_abs_le, abs_nonneg x, hM_nonneg]
        simpa [sq_abs] using hx_abs_sq
      have hreal : 1 + x ^ (2 : ℕ) ≤ 1 + M ^ (2 : ℕ) := by
        linarith
      have hC : (C : ENNReal) = ENNReal.ofReal (1 + M ^ (2 : ℕ)) := by
        rw [ENNReal.coe_nnreal_eq]
        congr
      rw [hC]
      exact ENNReal.ofReal_le_ofReal hreal
    · rw [Set.indicator_of_notMem hx]
      exact zero_le _
  rw [nevanlinnaWeightedMeasure, withDensity_apply _ measurableSet_Icc]
  rw [← lintegral_indicator measurableSet_Icc]
  exact IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    (ν : Measure ℝ) hbound

/-- The weighted Nevanlinna measure restricted to `[a,b]` is finite. -/
instance nevanlinnaWeightedMeasure_restrict_Icc_isFiniteMeasure
    (ν : FiniteMeasure ℝ) (a b : ℝ) :
    IsFiniteMeasure ((nevanlinnaWeightedMeasure ν).restrict (Set.Icc a b)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact nevanlinnaWeightedMeasure_Icc_lt_top ν a b⟩

/-- A finite measure vanishes on `(a,b)` if all positive interval tests integrate to zero. -/
theorem finiteMeasure_Ioo_eq_zero_of_continuous_test_integrals_zero
    {a b : ℝ} (μ : Measure ℝ)
    [IsFiniteMeasure μ]
    (hzero :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo a b)ᶜ →
        0 ≤ g → g ≤ 1 →
          ∫ x : ℝ, g x ∂μ = 0) :
    μ (Set.Ioo a b) = 0 := by
  have hsup :=
    isOpen_Ioo.measure_eq_biSup_integral_continuous
      (U := Set.Ioo a b) μ
  rw [hsup]
  apply ENNReal.iSup_eq_zero.2
  intro g
  apply ENNReal.iSup_eq_zero.2
  intro hg_cont
  apply ENNReal.iSup_eq_zero.2
  intro hg_zero
  apply ENNReal.iSup_eq_zero.2
  intro hg_nonneg
  apply ENNReal.iSup_eq_zero.2
  intro hg_le_one
  rw [hzero g hg_cont hg_zero hg_nonneg hg_le_one]
  simp

/-- The same test-integral criterion applies when only the compact restriction is finite. -/
theorem measure_Ioo_eq_zero_of_continuous_test_integrals_zero
    {a b : ℝ} (μ : Measure ℝ)
    [IsFiniteMeasure (μ.restrict (Set.Icc a b))]
    (hzero :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo a b)ᶜ →
        0 ≤ g → g ≤ 1 →
          ∫ x : ℝ, g x ∂μ = 0) :
    μ (Set.Ioo a b) = 0 := by
  have hzero_restrict :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo a b)ᶜ →
        0 ≤ g → g ≤ 1 →
          ∫ x : ℝ, g x ∂(μ.restrict (Set.Icc a b)) = 0 := by
    intro g hg_cont hg_zero hg_nonneg hg_le_one
    have hind : (Set.Icc a b).indicator g = g := by
      funext x
      by_cases hx : x ∈ Set.Icc a b
      · simp [hx]
      · have hxI : x ∉ Set.Ioo a b := by
          intro hxI
          exact hx ⟨le_of_lt hxI.1, le_of_lt hxI.2⟩
        simp [hx, hg_zero hxI]
    rw [← integral_indicator measurableSet_Icc, hind]
    exact hzero g hg_cont hg_zero hg_nonneg hg_le_one
  have hrestrict_zero :
      μ.restrict (Set.Icc a b) (Set.Ioo a b) = 0 :=
    finiteMeasure_Ioo_eq_zero_of_continuous_test_integrals_zero
      (μ.restrict (Set.Icc a b)) hzero_restrict
  rw [Measure.restrict_apply measurableSet_Ioo] at hrestrict_zero
  have hinter : Set.Ioo a b ∩ Set.Icc a b = Set.Ioo a b := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  simpa [hinter] using hrestrict_zero

/--
The Prop.144 test-integral sequence.  The analytic work identifies this
sequence both with the boundary-imaginary-part limit and with the Cauchy
approximate identity limit against the weighted boundary measure; both
identifications are provided by `upperHalfPlanePickIntervalTestIntegralBridgeProducer_concrete`
below.

Proposition 1.44 of [simon2019].
-/
noncomputable def upperHalfPlaneIntervalTestIntegralSeq
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ,
    g x * Real.pi⁻¹ *
      (∫ t : ℝ,
        finiteBoundaryPoissonKernel t x (stieltjesUniqScale n)
          ∂(ν : Measure ℝ))

/-- The test-integral sequence is the integral of the weighted Poisson integrand.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalTestIntegralSeq_eq_integral_integrand
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) :
    upperHalfPlaneIntervalTestIntegralSeq ν g n =
      ∫ x : ℝ, upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x := by
  rfl

/-- Split the test-integral sequence into interior and endpoint-collar parts.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalTestIntegralSeq_eq_interior_add_endpointCollar
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (δ : ℝ) (n : ℕ) :
    upperHalfPlaneIntervalTestIntegralSeq ν g n =
      (∫ x in Set.Icc (a + δ) (b - δ),
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) +
      ∫ x in intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x := by
  have hint : Integrable
      (fun x : ℝ => upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x)
      (volume : Measure ℝ) :=
    upperHalfPlaneIntervalWeightedPoissonIntegrand_integrable
      ν g hg_cont hg_zero hg_nonneg hg_le_one n
  have hrestrict :
      (∫ x in Set.Icc (a + δ) (b - δ) ∪ intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) =
      ∫ x : ℝ, upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure ℝ))
      (s := Set.Icc (a + δ) (b - δ) ∪ intervalEndpointCollar a b δ)
      (f := fun x : ℝ => upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) ?_
    intro x hxnot
    have hxnotI : x ∉ Set.Ioo a b := by
      intro hxI
      exact hxnot (Ioo_subset_intervalInterior_union_endpointCollar (δ := δ) hxI)
    exact upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_zero_of_not_mem_Ioo
      ν g hg_zero n hxnotI
  have hsplit :
      (∫ x in Set.Icc (a + δ) (b - δ) ∪ intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) =
      (∫ x in Set.Icc (a + δ) (b - δ),
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x) +
      ∫ x in intervalEndpointCollar a b δ,
        upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x := by
    exact setIntegral_union intervalInterior_disjoint_endpointCollar
      (intervalEndpointCollar_measurableSet a b δ) hint.integrableOn hint.integrableOn
  rw [upperHalfPlaneIntervalTestIntegralSeq_eq_integral_integrand]
  rw [← hrestrict, hsplit]

/-- Interval Pick continuation forces the Prop.144 test-integral sequence to vanish.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalTestIntegralSeq_tendsto_zero_of_mem_pickInterval
    {a b : ℝ} {F : ℍ → ℂ}
    (rep : NevanlinnaRep F) (pick : PickExtensionOnInterval a b F)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) :
    Tendsto
      (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq rep.ν g n)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := (rep.ν : Measure ℝ).real Set.univ
  let C : ℝ := intervalWeightBound a b
  let η : ℝ := ε / (8 * (C + 1) * (M + 1))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact ENNReal.toReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact intervalWeightBound_nonneg a b
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  rcases interval_test_small_on_endpoint_collar
      g hg_cont hg_zero hg_nonneg hηpos with
    ⟨δ, hδpos, hsmall⟩
  have hinterior :=
    rep.upperHalfPlaneIntervalWeightedPoissonInterior_tendsto_zero
      pick g hg_nonneg hg_le_one hδpos
  have hhalf : 0 < ε / 2 := by positivity
  have hinterior_event := (Metric.tendsto_nhds.mp hinterior) (ε / 2) hhalf
  have hcollar_lt : ((η * C) * 4) * M < ε / 2 := by
    have hCM_lt : C * M < (C + 1) * (M + 1) := by
      nlinarith [hC_nonneg, hM_nonneg]
    calc
      ((η * C) * 4) * M = η * 4 * (C * M) := by ring
      _ < η * 4 * ((C + 1) * (M + 1)) := by
            exact mul_lt_mul_of_pos_left hCM_lt (by positivity)
      _ = ε / 2 := by
            dsimp [η]
            have hden : 8 * (C + 1) * (M + 1) ≠ 0 := by positivity
            field_simp [hden]
            ring
  filter_upwards [hinterior_event] with n hn
  let interior : ℝ :=
    ∫ x in Set.Icc (a + δ) (b - δ),
      upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x
  let collar : ℝ :=
    ∫ x in intervalEndpointCollar a b δ,
      upperHalfPlaneIntervalWeightedPoissonIntegrand rep.ν g n x
  have hsplit :
      upperHalfPlaneIntervalTestIntegralSeq rep.ν g n = interior + collar := by
    dsimp [interior, collar]
    exact upperHalfPlaneIntervalTestIntegralSeq_eq_interior_add_endpointCollar
      rep.ν g hg_cont hg_zero hg_nonneg hg_le_one δ n
  have hinterior_lt : ‖interior‖ < ε / 2 := by
    dsimp [interior]
    simpa [Real.dist_eq] using hn
  have hcollar_le :
      ‖collar‖ ≤ ((η * intervalWeightBound a b) * 4) *
          (rep.ν : Measure ℝ).real Set.univ := by
    dsimp [collar]
    exact upperHalfPlaneIntervalWeightedPoissonEndpointCollar_setIntegral_norm_bound
      rep.ν g hg_cont hg_nonneg hηpos.le hsmall n
  have hcollar_lt' : ‖collar‖ < ε / 2 := by
    simpa [M, C] using hcollar_le.trans_lt hcollar_lt
  have hnorm_lt : ‖upperHalfPlaneIntervalTestIntegralSeq rep.ν g n‖ < ε := by
    calc
      ‖upperHalfPlaneIntervalTestIntegralSeq rep.ν g n‖ = ‖interior + collar‖ := by
        rw [hsplit]
      _ ≤ ‖interior‖ + ‖collar‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hinterior_lt hcollar_lt'
      _ = ε := by ring
  simpa [Real.dist_eq] using hnorm_lt

/-- Inner integral used in the Fubini approximation of the test-integral sequence.
Proposition 1.44 of [simon2019]. -/
noncomputable def upperHalfPlaneIntervalFubiniApproxInner
    (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ,
    intervalWeightedTest g x *
      unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t

/-- Fubini-side approximation sequence for the weighted boundary integral.
Proposition 1.44 of [simon2019]. -/
noncomputable def upperHalfPlaneIntervalFubiniApproxSeq
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ, upperHalfPlaneIntervalFubiniApproxInner g n t
    ∂(ν : Measure ℝ)

/-- The original test-integral sequence equals the Fubini approximation sequence.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalTestIntegralSeq_eq_fubiniApproxSeq
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (n : ℕ) :
    upperHalfPlaneIntervalTestIntegralSeq ν g n =
      upperHalfPlaneIntervalFubiniApproxSeq ν g n := by
  let u : ℝ → ℝ := intervalWeightedTest g
  have hu_meas : Measurable u := by
    simpa [u] using intervalWeightedTest_measurable hg_cont
  have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
    simpa [u] using intervalWeightedTest_nonneg hg_nonneg
  have hu_le : ∀ x : ℝ, u x ≤ intervalWeightBound a b := by
    simpa [u] using
      intervalWeightedTest_le_intervalWeightBound
        (a := a) (b := b) (g := g) hg_zero hg_le_one
  have hInt : Integrable (Function.uncurry fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
      ((volume : Measure ℝ).prod (ν : Measure ℝ)) :=
    intervalWeightedPoissonKernel_integrable_prod_of_test_le
      ν u hu_meas (intervalWeightBound_nonneg a b)
      (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
      hu_nonneg hu_le
  have hswap := integral_integral_swap
    (μ := (volume : Measure ℝ)) (ν := (ν : Measure ℝ))
    (f := fun x t : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
    hInt
  calc
    upperHalfPlaneIntervalTestIntegralSeq ν g n =
        ∫ x : ℝ, upperHalfPlaneIntervalWeightedPoissonIntegrand ν g n x := by
          rfl
    _ = ∫ x : ℝ, ∫ t : ℝ,
          u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
          ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun x => by
            simpa [u] using
              upperHalfPlaneIntervalWeightedPoissonIntegrand_eq_unitKernel_inner
                ν g n x
    _ = ∫ t : ℝ, ∫ x : ℝ,
          u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t
          ∂(volume : Measure ℝ) ∂(ν : Measure ℝ) := by
          simpa [Function.uncurry] using hswap
    _ = upperHalfPlaneIntervalFubiniApproxSeq ν g n := by
          rfl

/-- The Fubini inner integral is a weighted Cauchy average.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalFubiniApproxInner_eq_weightedCauchyAverage
    (g : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    upperHalfPlaneIntervalFubiniApproxInner g n t =
      (nevanlinnaWeightedMeasureDensity t).toReal *
        ∫ x : ℝ,
          g x *
            ProbabilityTheory.cauchyPDFReal t
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x := by
  calc
    upperHalfPlaneIntervalFubiniApproxInner g n t =
        ∫ x : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal *
            (g x *
              ProbabilityTheory.cauchyPDFReal t
                ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x) := by
          unfold upperHalfPlaneIntervalFubiniApproxInner
          refine integral_congr_ae ?_
          exact ae_of_all _ fun x =>
            intervalWeightedTest_unitKernel_eq_finiteBoundary_cauchy
              g (stieltjesUniqScale_pos n).le x t
    _ = (nevanlinnaWeightedMeasureDensity t).toReal *
        ∫ x : ℝ,
          g x *
            ProbabilityTheory.cauchyPDFReal t
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x := by
          rw [integral_const_mul]

/-- The Fubini inner integrals converge to the weighted test value.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalFubiniApproxInner_tendsto
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) (t : ℝ) :
    Tendsto
      (fun n : ℕ => upperHalfPlaneIntervalFubiniApproxInner g n t)
      atTop
        (𝓝 ((nevanlinnaWeightedMeasureDensity t).toReal * g t)) := by
  refine (intervalWeightedCauchyAverage_tendsto
    g hg_cont hg_nonneg hg_le_one t).congr' ?_
  filter_upwards with n
  exact (upperHalfPlaneIntervalFubiniApproxInner_eq_weightedCauchyAverage
    g n t).symm

/-- The Fubini inner integral has a uniform domination bound.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalFubiniApproxInner_bound
    {a b : ℝ} (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (n : ℕ) (t : ℝ) :
    ‖upperHalfPlaneIntervalFubiniApproxInner g n t‖ ≤
      intervalWeightBound a b * 4 := by
  let u : ℝ → ℝ := intervalWeightedTest g
  have hu_meas : AEStronglyMeasurable u (volume : Measure ℝ) := by
    have hm : Measurable u := by
      simpa [u] using intervalWeightedTest_measurable hg_cont
    exact hm.aestronglyMeasurable
  have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
    simpa [u] using intervalWeightedTest_nonneg hg_nonneg
  have hu_le : ∀ x : ℝ, u x ≤ intervalWeightBound a b := by
    simpa [u] using
      intervalWeightedTest_le_intervalWeightBound
        (a := a) (b := b) (g := g) hg_zero hg_le_one
  simpa [upperHalfPlaneIntervalFubiniApproxInner, u] using
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_of_test_le_scale
      u hu_meas (intervalWeightBound_nonneg a b)
      (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
      hu_nonneg hu_le t

/-- Integrating against the weighted measure equals density-weighted finite integration. -/
theorem integral_nevanlinnaWeightedMeasure_eq_density_mul
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ) :
    (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν) =
      ∫ t : ℝ, (nevanlinnaWeightedMeasureDensity t).toReal * g t
        ∂(ν : Measure ℝ) := by
  have htop :
      ∀ᵐ t ∂(ν : Measure ℝ),
        nevanlinnaWeightedMeasureDensity t < (⊤ : ENNReal) := by
    exact ae_of_all _ (fun t => by simp [nevanlinnaWeightedMeasureDensity])
  have hwd :
      (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ, (nevanlinnaWeightedMeasureDensity t).toReal • g t
          ∂(ν : Measure ℝ) := by
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_nevanlinnaWeightedMeasureDensity htop g
  simpa [smul_eq_mul] using hwd

/-- The Fubini approximation converges to the weighted Nevanlinna integral.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalFubiniApproxSeq_tendsto_weightedIntegral
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) :
    Tendsto
      (fun n : ℕ => upperHalfPlaneIntervalFubiniApproxSeq ν g n)
      atTop
        (𝓝 (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν)) := by
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (ν : Measure ℝ))
    (F := fun (n : ℕ) (t : ℝ) =>
      upperHalfPlaneIntervalFubiniApproxInner g n t)
    (f := fun t : ℝ => (nevanlinnaWeightedMeasureDensity t).toReal * g t)
    (bound := fun _t : ℝ => intervalWeightBound a b * 4)
    (fun n => by
      let u : ℝ → ℝ := intervalWeightedTest g
      have hu_meas : Measurable u := by
        simpa [u] using intervalWeightedTest_measurable hg_cont
      have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
        simpa [u] using intervalWeightedTest_nonneg hg_nonneg
      have hu_le : ∀ x : ℝ, u x ≤ intervalWeightBound a b := by
        simpa [u] using
          intervalWeightedTest_le_intervalWeightBound
            (a := a) (b := b) (g := g) hg_zero hg_le_one
      have hInt : Integrable (Function.uncurry fun x t : ℝ =>
          u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
          ((volume : Measure ℝ).prod (ν : Measure ℝ)) :=
        intervalWeightedPoissonKernel_integrable_prod_of_test_le
          ν u hu_meas (intervalWeightBound_nonneg a b)
          (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n).le
          hu_nonneg hu_le
      have hs : Integrable (Function.uncurry fun t x : ℝ =>
          u x * unitIntervalHerglotzProp35TestKernel (stieltjesUniqScale n) x t)
          ((ν : Measure ℝ).prod (volume : Measure ℝ)) := by
        simpa [Function.comp_def, Function.uncurry] using hInt.swap
      have hinner := MeasureTheory.Integrable.integral_prod_left hs
      simpa [upperHalfPlaneIntervalFubiniApproxInner, u, Function.uncurry] using
        hinner.aestronglyMeasurable)
    (integrable_const (c := intervalWeightBound a b * 4)
      (μ := (ν : Measure ℝ)))
    (fun n => ae_of_all _ fun t =>
      upperHalfPlaneIntervalFubiniApproxInner_bound
        g hg_cont hg_zero hg_nonneg hg_le_one n t)
    (ae_of_all _ fun t =>
      upperHalfPlaneIntervalFubiniApproxInner_tendsto
        g hg_cont hg_nonneg hg_le_one t)
  have htarget :
      (∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal * g t
          ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν := by
    exact (integral_nevanlinnaWeightedMeasure_eq_density_mul ν g).symm
  simpa [upperHalfPlaneIntervalFubiniApproxSeq, htarget] using hdc

/-- The test-integral sequence converges to the weighted Nevanlinna integral.
Proposition 1.44 of [simon2019]. -/
theorem upperHalfPlaneIntervalTestIntegralSeq_tendsto_weightedIntegral
    (ν : FiniteMeasure ℝ) {a b : ℝ}
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo a b)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) :
    Tendsto
      (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq ν g n)
      atTop
        (𝓝 (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν)) := by
  refine (upperHalfPlaneIntervalFubiniApproxSeq_tendsto_weightedIntegral
    ν g hg_cont hg_zero hg_nonneg hg_le_one).congr' ?_
  filter_upwards with n
  exact (upperHalfPlaneIntervalTestIntegralSeq_eq_fubiniApproxSeq
    ν g hg_cont hg_zero hg_nonneg hg_le_one n).symm

/-- If the same sequence tends to zero and to an integral, that integral is zero.
Proposition 1.44 of [simon2019]. -/
theorem interval_testIntegral_eq_zero_of_tendsto_zero_and_approx
    (ν : FiniteMeasure ℝ) (g : ℝ → ℝ)
    (hzero :
      Tendsto (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq ν g n)
        atTop (𝓝 0))
    (happrox :
      Tendsto (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq ν g n)
        atTop (𝓝 (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν))) :
    (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure ν) = 0 :=
  tendsto_nhds_unique happrox hzero

/--
Producer for the Prop.144 reverse-direction estimates.  A concrete one is
`upperHalfPlanePickIntervalTestIntegralBridgeProducer_concrete` below.

For each regularity test function, it supplies the two limits of the
test-integral sequence: the boundary Pick continuation forces the sequence to
converge to `0`, while the Cauchy approximate identity identifies the same
sequence with the integral against the weighted boundary measure.
-/
structure UpperHalfPlanePickIntervalTestIntegralBridgeProducer where
  prop144_testIntegral_bridge :
    ∀ {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F),
      PickExtensionOnInterval a b F →
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo a b)ᶜ →
        0 ≤ g → g ≤ 1 →
          Tendsto
              (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq rep.ν g n)
              atTop (𝓝 0) ∧
            Tendsto
              (fun n : ℕ => upperHalfPlaneIntervalTestIntegralSeq rep.ν g n)
              atTop
                (𝓝 (∫ t : ℝ, g t ∂nevanlinnaWeightedMeasure rep.ν))

/-- Concrete Prop.144 bridge producer built from the two established limits. -/
def upperHalfPlanePickIntervalTestIntegralBridgeProducer_concrete :
    UpperHalfPlanePickIntervalTestIntegralBridgeProducer where
  prop144_testIntegral_bridge := by
    intro a b F rep pick g hg_cont hg_zero hg_nonneg hg_le_one
    exact
      ⟨upperHalfPlaneIntervalTestIntegralSeq_tendsto_zero_of_mem_pickInterval
          rep pick g hg_cont hg_zero hg_nonneg hg_le_one,
        upperHalfPlaneIntervalTestIntegralSeq_tendsto_weightedIntegral
          rep.ν g hg_cont hg_zero hg_nonneg hg_le_one⟩

/-- Interval Pick continuation implies weighted measure vanishing on `(a,b)`. -/
theorem weightedMeasure_zero_of_mem_pickInterval
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    MemPickInterval a b F →
      nevanlinnaWeightedMeasure rep.ν (Set.Ioo a b) = 0 := by
  rintro ⟨pick⟩
  refine measure_Ioo_eq_zero_of_continuous_test_integrals_zero
    (μ := nevanlinnaWeightedMeasure rep.ν) ?_
  intro g hg_cont hg_zero hg_nonneg hg_le_one
  rcases upperHalfPlanePickIntervalTestIntegralBridgeProducer_concrete
      |>.prop144_testIntegral_bridge rep pick g hg_cont hg_zero hg_nonneg hg_le_one with
    ⟨hzero, happrox⟩
  exact interval_testIntegral_eq_zero_of_tendsto_zero_and_approx
    rep.ν g hzero happrox

/--
Reverse-only producer for the other direction of Proposition 144.

The support-to-continuation direction is supplied by
`mem_pickInterval_of_nevanlinnaRepOnComplement`; this producer extracts weighted
measure vanishing from an interval Pick continuation, and a concrete one is
`upperHalfPlanePickIntervalWeightedSupportReverseProducer_concrete` below.
-/
structure UpperHalfPlanePickIntervalWeightedSupportReverseProducer where
  weightedMeasure_zero_of_mem_pickInterval :
    ∀ {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F),
      MemPickInterval a b F →
        nevanlinnaWeightedMeasure rep.ν (Set.Ioo a b) = 0

/-- Convert a test-integral bridge producer into a reverse weighted-support producer. -/
def upperHalfPlanePickIntervalWeightedSupportReverseProducer_of_testIntegralBridgeProducer
    (producer : UpperHalfPlanePickIntervalTestIntegralBridgeProducer) :
    UpperHalfPlanePickIntervalWeightedSupportReverseProducer where
  weightedMeasure_zero_of_mem_pickInterval := by
    intro a b F rep
    rintro ⟨pick⟩
    refine measure_Ioo_eq_zero_of_continuous_test_integrals_zero
      (μ := nevanlinnaWeightedMeasure rep.ν) ?_
    intro g hg_cont hg_zero hg_nonneg hg_le_one
    rcases producer.prop144_testIntegral_bridge rep pick
        g hg_cont hg_zero hg_nonneg hg_le_one with ⟨hzero, happrox⟩
    exact interval_testIntegral_eq_zero_of_tendsto_zero_and_approx
      rep.ν g hzero happrox

/-- Concrete reverse weighted-support producer from the Prop.144 bridge. -/
def upperHalfPlanePickIntervalWeightedSupportReverseProducer_concrete :
    UpperHalfPlanePickIntervalWeightedSupportReverseProducer :=
  upperHalfPlanePickIntervalWeightedSupportReverseProducer_of_testIntegralBridgeProducer
    upperHalfPlanePickIntervalTestIntegralBridgeProducer_concrete

/-- Add the already proved support-to-continuation direction to a reverse producer. -/
def upperHalfPlanePickIntervalWeightedSupportProducer_of_reverseProducer
    (producer : UpperHalfPlanePickIntervalWeightedSupportReverseProducer) :
    UpperHalfPlanePickIntervalWeightedSupportProducer where
  mem_pickInterval_of_nevanlinnaRepOnComplement := by
    intro a b F rep
    exact mem_pickInterval_of_nevanlinnaRepOnComplement rep
  weightedMeasure_zero_of_mem_pickInterval := by
    intro a b F rep hF
    exact producer.weightedMeasure_zero_of_mem_pickInterval rep hF

/-- Concrete weighted-support producer for the interval-support equivalence. -/
def upperHalfPlanePickIntervalWeightedSupportProducer_concrete :
    UpperHalfPlanePickIntervalWeightedSupportProducer :=
  upperHalfPlanePickIntervalWeightedSupportProducer_of_reverseProducer
    upperHalfPlanePickIntervalWeightedSupportReverseProducer_concrete

/-- Interval Pick continuation gives a complement-supported Nevanlinna representation. -/
theorem nevanlinnaRepOnComplement_of_mem_pickInterval
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    MemPickInterval a b F → Nonempty (NevanlinnaRepOnComplement a b F) := by
  intro hF
  exact ⟨nevanlinnaRepOnComplement_of_weightedMeasure_zero rep
    (weightedMeasure_zero_of_mem_pickInterval rep hF)⟩

/-- The interval-support equivalence for upper-half-plane Nevanlinna representations. -/
theorem nevanlinnaRepOnComplement_iff_mem_pickInterval
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    Nonempty (NevanlinnaRepOnComplement a b F) ↔ MemPickInterval a b F := by
  constructor
  · rintro ⟨repOnComplement⟩
    exact mem_pickInterval_of_nevanlinnaRepOnComplement repOnComplement
  · exact nevanlinnaRepOnComplement_of_mem_pickInterval rep

end

end Loewner
end TraceInequality
end Quantum
