import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.LocalClipStieltjes

/-!
# Chapter 20 dominated data for Hiai regularization

This file contains the measurability, integrability, and compact-window
domination inputs used to differentiate the clipped Hiai regularization under
the integral sign.
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
Pointwise bound for the center-derivative integrand in the clipped scaled-weight
convolution.  This reduces the dominated-differentiation bound to a scalar bound
on the smooth mollifier derivative times the endpoint bound for the clipped
monotone function.
-/
theorem hiaiScaledMollifierWeight_xDeriv_bound_on_window
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x z y : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
        hiaiLocalClip f (x - ε) (x + ε) y‖ ≤
      |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| *
        max |f (x - ε)| |f (x + ε)| := by
  have hclip :=
    hiaiLocalClip_abs_le_endpoint_max_of_loewnerPosOnUnitInterval
      (f := f) (ε := ε) (x := x) (y := y) hε hx hpos
  rw [hiaiScaledMollifierWeight_deriv_x
    (φ := φ) (ε := ε) (x := z) (y := y) hφ]
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hclip (abs_nonneg _)

/--
For a fixed center, the derivative of the scaled mollifier weight in the center
variable is continuous as a function of the integration variable.
-/
theorem hiaiScaledMollifierWeight_deriv_x_continuous
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} :
    Continuous
      (fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x) := by
  have hderivφ : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  rw [show
      (fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x) =
        fun y : ℝ => ε⁻¹ * (deriv φ ((x - y) / ε) * ε⁻¹) by
        funext y
        exact hiaiScaledMollifierWeight_deriv_x
          (φ := φ) (ε := ε) (x := x) (y := y) hφ]
  fun_prop

/-- A global bound for the derivative of a Hiai mollifier. -/
theorem hiaiMollifier_deriv_abs_bound
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv φ t| ≤ M := by
  have hderivφ : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      hderivφ.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · have hCt : ‖deriv φ t‖ ≤ C := hC t ht
    have hCt_abs : |deriv φ t| ≤ C := by
      simpa [Real.norm_eq_abs] using hCt
    exact hCt_abs.trans (le_max_left _ _)
  · have htsupp : tsupport φ ⊆ Set.Icc (-1 : ℝ) 1 := by
      rw [tsupport]
      exact closure_minimal hφ.support_subset isClosed_Icc
    have hnot_supp_deriv : t ∉ Function.support (deriv φ) := by
      intro hsupp
      exact ht (htsupp (support_deriv_subset hsupp))
    have hderiv : deriv φ t = 0 := by
      by_contra hne
      exact hnot_supp_deriv hne
    simp [hderiv]

/--
The scaled mollifier weight times the clipped monotone extension is strongly
measurable for the Lebesgue integral.
-/
theorem hiaiScaledMollifierWeight_localClip_aestronglyMeasurable
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x z : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        hiaiScaledMollifierWeight φ ε z y *
          hiaiLocalClip f (x - ε) (x + ε) y) volume := by
  have hlin : Continuous (fun y : ℝ => (z - y) / ε) :=
    (continuous_const.sub continuous_id).div_const ε
  have hW : Continuous (hiaiScaledMollifierWeight φ ε z) := by
    simpa [hiaiScaledMollifierWeight] using
      (continuous_const.mul (hφ.smooth.continuous.comp hlin))
  exact
    hW.aestronglyMeasurable.mul
    (hiaiLocalClip_aestronglyMeasurable_of_loewnerPosOnUnitInterval
      (f := f) hε.le hx hpos)

/--
The scaled mollifier weight times the clipped monotone extension is integrable,
using compact support of the weight.
-/
theorem hiaiScaledMollifierWeight_localClip_integrable
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Integrable
      (fun y : ℝ =>
        hiaiScaledMollifierWeight φ ε x y *
          hiaiLocalClip f (x - ε) (x + ε) y) volume := by
  let F : ℝ → ℝ := fun y =>
    hiaiScaledMollifierWeight φ ε x y *
      hiaiLocalClip f (x - ε) (x + ε) y
  have hlin : Continuous (fun y : ℝ => (x - y) / ε) :=
    (continuous_const.sub continuous_id).div_const ε
  have hW : Continuous (hiaiScaledMollifierWeight φ ε x) := by
    simpa [hiaiScaledMollifierWeight] using
      (continuous_const.mul (hφ.smooth.continuous.comp hlin))
  have hcont : Continuous F :=
    hW.mul
      (hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
        (f := f) hε.le hx hpos)
  have hsupp : Function.support F ⊆ Set.Icc (x - ε) (x + ε) := by
    intro y hy
    have hW : hiaiScaledMollifierWeight φ ε x y ≠ 0 := by
      intro hzero
      exact hy (by simp [F, hzero])
    exact hiaiScaledMollifierWeight_mem_window_of_ne_zero
      (φ := φ) hφ hε hW
  have hIntOn : IntegrableOn F (Set.Icc (x - ε) (x + ε)) volume := by
    exact hcont.continuousOn.integrableOn_of_subset_isCompact
      isCompact_Icc measurableSet_Icc subset_rfl measure_Icc_lt_top.ne
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/--
The center-derivative integrand with the clipped monotone extension is strongly
measurable.
-/
theorem hiaiScaledMollifierWeight_xDeriv_localClip_aestronglyMeasurable
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y) volume := by
  exact
    (hiaiScaledMollifierWeight_deriv_x_continuous
      (φ := φ) (ε := ε) (x := x) hφ).aestronglyMeasurable.mul
    (hiaiLocalClip_aestronglyMeasurable_of_loewnerPosOnUnitInterval
      (f := f) hε.le hx hpos)

/--
The scaled mollifier weight times the original function is strongly measurable
on the compact window where the weight is supported.
-/
theorem
    hiaiScaledMollifierWeight_original_aestronglyMeasurable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε z : ℝ} (hε : 0 < ε)
    (hz : z ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    AEStronglyMeasurable
      (fun y : ℝ => hiaiScaledMollifierWeight φ ε z y * f y) volume := by
  let K : Set ℝ := Set.Icc (z - ε) (z + ε)
  let F : ℝ → ℝ := fun y => hiaiScaledMollifierWeight φ ε z y * f y
  have hsub : K ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩
  have hlin : Continuous (fun y : ℝ => (z - y) / ε) :=
    (continuous_const.sub continuous_id).div_const ε
  have hW : Continuous (hiaiScaledMollifierWeight φ ε z) := by
    simpa [hiaiScaledMollifierWeight] using
      (continuous_const.mul (hφ.smooth.continuous.comp hlin))
  have hcont : ContinuousOn F K :=
    hW.continuousOn.mul (hpos.differentiable.continuousOn.mono hsub)
  have hmeas_restrict : AEStronglyMeasurable F (volume.restrict K) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  have hmeas_indicator : AEStronglyMeasurable (K.indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hmeas_restrict
  refine hmeas_indicator.congr ?_
  filter_upwards with y
  by_cases hy : y ∈ K
  · simp [Set.indicator_of_mem hy, F]
  · have hWzero : hiaiScaledMollifierWeight φ ε z y = 0 := by
      by_contra hne
      exact hy (hiaiScaledMollifierWeight_mem_window_of_ne_zero
        (φ := φ) hφ hε hne)
    simp [Set.indicator_of_notMem hy, F, hWzero]

/--
The scaled mollifier weight times the original function is integrable on the
compact support window.
-/
theorem
    hiaiScaledMollifierWeight_original_integrable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Integrable
      (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y * f y) volume := by
  let K : Set ℝ := Set.Icc (x - ε) (x + ε)
  let F : ℝ → ℝ := fun y => hiaiScaledMollifierWeight φ ε x y * f y
  have hsub : K ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hlin : Continuous (fun y : ℝ => (x - y) / ε) :=
    (continuous_const.sub continuous_id).div_const ε
  have hW : Continuous (hiaiScaledMollifierWeight φ ε x) := by
    simpa [hiaiScaledMollifierWeight] using
      (continuous_const.mul (hφ.smooth.continuous.comp hlin))
  have hcont : ContinuousOn F K :=
    hW.continuousOn.mul (hpos.differentiable.continuousOn.mono hsub)
  have hsupp : Function.support F ⊆ K := by
    intro y hy
    have hWne : hiaiScaledMollifierWeight φ ε x y ≠ 0 := by
      intro hzero
      exact hy (by simp [F, hzero])
    exact hiaiScaledMollifierWeight_mem_window_of_ne_zero
      (φ := φ) hφ hε hWne
  have hIntOn : IntegrableOn F K volume := by
    exact hcont.integrableOn_of_subset_isCompact
      isCompact_Icc measurableSet_Icc subset_rfl measure_Icc_lt_top.ne
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/--
The center-derivative integrand with the original function is strongly
measurable on its compact support window.
-/
theorem
    scaledMollifierWeight_xDeriv_original_aestronglyMeasurable_of_loewnerPos
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y)
      volume := by
  let K : Set ℝ := Set.Icc (x - ε) (x + ε)
  let F : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y
  have hsub : K ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hcont : ContinuousOn F K :=
    (hiaiScaledMollifierWeight_deriv_x_continuous
      (φ := φ) (ε := ε) (x := x) hφ).continuousOn.mul
      (hpos.differentiable.continuousOn.mono hsub)
  have hmeas_restrict : AEStronglyMeasurable F (volume.restrict K) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  have hmeas_indicator : AEStronglyMeasurable (K.indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hmeas_restrict
  refine hmeas_indicator.congr ?_
  filter_upwards with y
  by_cases hy : y ∈ K
  · simp [Set.indicator_of_mem hy, F]
  · have hdx :
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x = 0 :=
      hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
        (φ := φ) hφ hε hy
    simp [Set.indicator_of_notMem hy, F, hdx]

/--
The original-function center-derivative integrand admits local dominated data
on the regularized interior.
-/
theorem hiaiRegularization_original_xDeriv_publicBoundData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∃ s : Set ℝ, ∃ bound : ℝ → ℝ,
      s ∈ 𝓝 x ∧ s ⊆ hiaiRegularizedInterior ε ∧
      (∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            f y‖ ≤ bound y) ∧
      Integrable bound volume := by
  obtain ⟨M, hM_nonneg, hM⟩ :=
    hiaiMollifier_deriv_abs_bound (φ := φ) hφ
  let leftMargin : ℝ := x - ((-1 : ℝ) + ε)
  let rightMargin : ℝ := (1 - ε) - x
  let δ : ℝ := min leftMargin rightMargin / 2
  have hleft_pos : 0 < leftMargin := by
    dsimp [leftMargin]
    linarith [hx.1]
  have hright_pos : 0 < rightMargin := by
    dsimp [rightMargin]
    linarith [hx.2]
  have hmin_pos : 0 < min leftMargin rightMargin := lt_min hleft_pos hright_pos
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_lt_left : δ < leftMargin := by
    have hδ_le_half : δ ≤ leftMargin / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hhalf_lt : leftMargin / 2 < leftMargin := by linarith
    exact lt_of_le_of_lt hδ_le_half hhalf_lt
  have hδ_lt_right : δ < rightMargin := by
    have hδ_le_half : δ ≤ rightMargin / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hhalf_lt : rightMargin / 2 < rightMargin := by linarith
    exact lt_of_le_of_lt hδ_le_half hhalf_lt
  let s : Set ℝ := Set.Ioo (x - δ) (x + δ)
  let K : Set ℝ := Set.Icc (x - ε - δ) (x + ε + δ)
  have hKsub : K ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    constructor
    · dsimp [K] at hy
      dsimp [leftMargin] at hδ_lt_left
      linarith [hy.1, hδ_lt_left]
    · dsimp [K] at hy
      dsimp [rightMargin] at hδ_lt_right
      linarith [hy.2, hδ_lt_right]
  have hfK : ContinuousOn f K := hpos.differentiable.continuousOn.mono hKsub
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact K).exists_bound_of_continuousOn hfK
  let C0 : ℝ := max C 0
  let B : ℝ := |ε⁻¹| * M * |ε⁻¹| * C0
  let bound : ℝ → ℝ := K.indicator (fun _ : ℝ => B)
  refine ⟨s, bound, ?_, ?_, ?_, ?_⟩
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · intro z hz
    constructor
    · dsimp [s] at hz
      dsimp [leftMargin] at hδ_lt_left
      linarith [hz.1, hδ_lt_left]
    · dsimp [s] at hz
      dsimp [rightMargin] at hδ_lt_right
      linarith [hz.2, hδ_lt_right]
  · filter_upwards with y z hz
    by_cases hyK : y ∈ K
    · have hcoeff :
          |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| ≤ |ε⁻¹| * M * |ε⁻¹| := by
        calc
          |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)|
              = |ε⁻¹| * |deriv φ ((z - y) / ε)| * |ε⁻¹| := by
                rw [abs_mul, abs_mul, mul_assoc]
          _ ≤ |ε⁻¹| * M * |ε⁻¹| := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))
                  (abs_nonneg _)
      have hf_bound : |f y| ≤ C0 := by
        have hCy : ‖f y‖ ≤ C := hC y hyK
        have hCy_abs : |f y| ≤ C := by
          simpa [Real.norm_eq_abs] using hCy
        exact hCy_abs.trans (le_max_left _ _)
      rw [hiaiScaledMollifierWeight_deriv_x
        (φ := φ) (ε := ε) (x := z) (y := y) hφ]
      rw [Real.norm_eq_abs, abs_mul]
      have hcoeff_nonneg : 0 ≤ |ε⁻¹| * M * |ε⁻¹| :=
        mul_nonneg (mul_nonneg (abs_nonneg _) hM_nonneg) (abs_nonneg _)
      calc
        |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| * |f y|
            ≤ (|ε⁻¹| * M * |ε⁻¹|) * C0 :=
              mul_le_mul hcoeff hf_bound (abs_nonneg _) hcoeff_nonneg
        _ = bound y := by
              simp [bound, K, B, hyK]
    · have hyz : y ∉ Set.Icc (z - ε) (z + ε) := by
        intro hyz
        exact hyK ⟨by
          dsimp [s] at hz
          linarith [hyz.1, hz.1], by
          dsimp [s] at hz
          linarith [hyz.2, hz.2]⟩
      have hdx :=
        hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
          (φ := φ) hφ hε hyz
      simp [bound, K, hyK, hdx]
  · exact
      (integrableOn_const (μ := volume) (s := K) (C := B)
        measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc

/--
Compact-window scalar domination for the center-derivative part of the scaled
mollifier convolution.  The bound is integrable because it is a constant on a
compact interval and zero outside.
-/
theorem hiaiScaledMollifierWeight_xDeriv_publicBoundData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    ∃ s : Set ℝ, ∃ bound : ℝ → ℝ,
      s ∈ 𝓝 x ∧
      (∀ᵐ y ∂volume, ∀ z ∈ s,
        |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| *
            max |f (x - ε)| |f (x + ε)| ≤ bound y) ∧
      Integrable bound volume := by
  obtain ⟨M, hM_nonneg, hM⟩ :=
    hiaiMollifier_deriv_abs_bound (φ := φ) hφ
  let s : Set ℝ := Set.Ioo (x - ε / 2) (x + ε / 2)
  let K : Set ℝ := Set.Icc (x - 3 * ε / 2) (x + 3 * ε / 2)
  let C : ℝ := |ε⁻¹| * M * |ε⁻¹| * max |f (x - ε)| |f (x + ε)|
  let bound : ℝ → ℝ := K.indicator (fun _ : ℝ => C)
  refine ⟨s, bound, ?_, ?_, ?_⟩
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · filter_upwards with y z hz
    by_cases hyK : y ∈ K
    · have hcoeff :
          |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| ≤ |ε⁻¹| * M * |ε⁻¹| := by
        calc
          |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)|
              = |ε⁻¹| * |deriv φ ((z - y) / ε)| * |ε⁻¹| := by
                rw [abs_mul, abs_mul, mul_assoc]
          _ ≤ |ε⁻¹| * M * |ε⁻¹| := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))
                  (abs_nonneg _)
      have hmax_nonneg : 0 ≤ max |f (x - ε)| |f (x + ε)| :=
        (abs_nonneg _).trans (le_max_left _ _)
      calc
        |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| *
            max |f (x - ε)| |f (x + ε)|
            ≤ (|ε⁻¹| * M * |ε⁻¹|) *
                max |f (x - ε)| |f (x + ε)| :=
              mul_le_mul_of_nonneg_right hcoeff hmax_nonneg
        _ = bound y := by
              simp [bound, K, C, hyK]
    · have hyz : y ∉ Set.Icc (z - ε) (z + ε) := by
        intro hyz
        exact hyK ⟨by linarith [hyz.1, hz.1], by linarith [hyz.2, hz.2]⟩
      have hdx :=
        hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
          (φ := φ) hφ hε hyz
      have hformula :
          ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹) = 0 := by
        simpa [hiaiScaledMollifierWeight_deriv_x (φ := φ) hφ] using hdx
      simp [bound, K, hyK, hformula]
  · exact
      (integrableOn_const (μ := volume) (s := K) (C := C)
        measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc

/--
Public Löwner positivity supplies the monotone clipped extension used by the
Stieltjes measure, so the scaled mollifier weight is integrable there without
any additional analytic input.
-/
theorem hiaiScaledMollifierWeight_integrable_stieltjes_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Integrable (hiaiScaledMollifierWeight φ ε x)
      (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
        (f := f) hε.le hx hpos).stieltjesFunction.measure :=
  hiaiScaledMollifierWeight_integrable_stieltjes
    (φ := φ) hφ hε
    (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
      (f := f) hε.le hx hpos)

end

end Quantum.TraceInequality.Loewner
