import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.AffinePullbackPSD
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff


/-!
# Chapter 20 Hiai regularization smoothness ladder

This file contains the compactly supported scaled mollifier kernel, the
regularized `ContDiff` ladder, and the affine-pullback smooth Löwner positivity
inputs used by the finite-order regularity route.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution

noncomputable section

/-- The compactly supported smooth kernel behind Hiai regularization. -/
noncomputable def hiaiScaledMollifierKernel
    (φ : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  ε⁻¹ * φ (t / ε)

/-- The shifted kernel is exactly the scaled mollifier weight. -/
theorem hiaiScaledMollifierKernel_eq_weight
    {φ : ℝ → ℝ} {ε x y : ℝ} :
    hiaiScaledMollifierKernel φ ε (x - y) =
      hiaiScaledMollifierWeight φ ε x y := by
  rfl

/-- A positive scale preserves compact support of the Chapter 20 mollifier kernel. -/
theorem hiaiScaledMollifierKernel_hasCompactSupport
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (hiaiScaledMollifierKernel φ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  unfold hiaiScaledMollifierKernel
  by_contra hne
  have hφne : φ (t / ε) ≠ 0 := (mul_ne_zero_iff.mp hne).2
  have harg : t / ε ∈ Set.Icc (-1 : ℝ) 1 := hφ.support_subset hφne
  have hlow : -ε ≤ t := by
    simpa using (le_div_iff₀ hε).1 harg.1
  have hhigh : t ≤ ε := by
    simpa using (div_le_iff₀ hε).1 harg.2
  exact ht ⟨hlow, hhigh⟩

/-- The scaled mollifier kernel is `C^m` for every finite order `m`. -/
theorem hiaiScaledMollifierKernel_contDiff_anyOrder
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (m : ℕ) {ε : ℝ} :
    ContDiff ℝ m (hiaiScaledMollifierKernel φ ε) := by
  have hφm : ContDiff ℝ m φ := by
    have hmle : (m : WithTop ℕ∞) ≤ loewnerBookSmoothOrder := by
      dsimp [loewnerBookSmoothOrder]
      exact WithTop.coe_le_coe.2 le_top
    exact hφ.smooth.of_le hmle
  have harg : ContDiff ℝ m (fun t : ℝ => t / ε) := by
    fun_prop
  unfold hiaiScaledMollifierKernel
  exact contDiff_const.mul (hφm.comp harg)

/-- The scaled mollifier kernel is `C^3`. -/
theorem hiaiScaledMollifierKernel_contDiff_order3
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} :
    ContDiff ℝ 3 (hiaiScaledMollifierKernel φ ε) := by
  have hφ3 : ContDiff ℝ 3 φ := by
    have h3le : (3 : WithTop ℕ∞) ≤ loewnerBookSmoothOrder := by
      dsimp [loewnerBookSmoothOrder]
      exact WithTop.coe_le_coe.2 le_top
    exact hφ.smooth.of_le h3le
  have harg : ContDiff ℝ 3 (fun t : ℝ => t / ε) := by
    fun_prop
  unfold hiaiScaledMollifierKernel
  exact contDiff_const.mul (hφ3.comp harg)

/-- The scaled mollifier kernel is `C^5`. -/
theorem hiaiScaledMollifierKernel_contDiff_order5
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} :
    ContDiff ℝ 5 (hiaiScaledMollifierKernel φ ε) := by
  have hφ5 : ContDiff ℝ 5 φ := by
    have h5le : (5 : WithTop ℕ∞) ≤ loewnerBookSmoothOrder := by
      dsimp [loewnerBookSmoothOrder]
      exact WithTop.coe_le_coe.2 le_top
    exact hφ.smooth.of_le h5le
  have harg : ContDiff ℝ 5 (fun t : ℝ => t / ε) := by
    fun_prop
  unfold hiaiScaledMollifierKernel
  exact contDiff_const.mul (hφ5.comp harg)

/--
Convolution with the compactly supported smooth kernel makes the Hiai
regularization `C^3` for locally integrable input.
-/
theorem hiaiRegularization_contDiff_order3_of_locallyIntegrable
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ 3 (hiaiRegularization φ ε g) := by
  let κ : ℝ → ℝ := hiaiScaledMollifierKernel φ ε
  have hκ_support : HasCompactSupport κ :=
    hiaiScaledMollifierKernel_hasCompactSupport
      (φ := φ) hφ hε
  have hκ_smooth : ContDiff ℝ 3 κ :=
    hiaiScaledMollifierKernel_contDiff_order3
      (φ := φ) (ε := ε) hφ
  have hconv :
      ContDiff ℝ 3
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) :=
    hκ_support.contDiff_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hg hκ_smooth
  rw [← contDiffOn_univ] at hconv ⊢
  refine hconv.congr ?_
  intro z _hz
  rw [hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := g) (x := z) hφ hε]
  rw [MeasureTheory.convolution_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp [κ, hiaiScaledMollifierKernel,
    hiaiScaledMollifierWeight, mul_comm]

/--
Convolution with the compactly supported smooth kernel makes the Hiai
regularization `C^5` for locally integrable input.
-/
theorem hiaiRegularization_contDiff_order5_of_locallyIntegrable
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ 5 (hiaiRegularization φ ε g) := by
  let κ : ℝ → ℝ := hiaiScaledMollifierKernel φ ε
  have hκ_support : HasCompactSupport κ :=
    hiaiScaledMollifierKernel_hasCompactSupport
      (φ := φ) hφ hε
  have hκ_smooth : ContDiff ℝ 5 κ :=
    hiaiScaledMollifierKernel_contDiff_order5
      (φ := φ) (ε := ε) hφ
  have hconv :
      ContDiff ℝ 5
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) :=
    hκ_support.contDiff_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hg hκ_smooth
  rw [← contDiffOn_univ] at hconv ⊢
  refine hconv.congr ?_
  intro z _hz
  rw [hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := g) (x := z) hφ hε]
  rw [MeasureTheory.convolution_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp [κ, hiaiScaledMollifierKernel,
    hiaiScaledMollifierWeight, mul_comm]

/-- The same convolution smoothness statement at an arbitrary finite order. -/
theorem hiaiRegularization_contDiff_of_locallyIntegrable_anyOrder
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ m (hiaiRegularization φ ε g) := by
  let κ : ℝ → ℝ := hiaiScaledMollifierKernel φ ε
  have hκ_support : HasCompactSupport κ :=
    hiaiScaledMollifierKernel_hasCompactSupport
      (φ := φ) hφ hε
  have hκ_smooth : ContDiff ℝ m κ :=
    hiaiScaledMollifierKernel_contDiff_anyOrder
      (φ := φ) hφ m
  have hconv :
      ContDiff ℝ m
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) :=
    hκ_support.contDiff_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hg hκ_smooth
  rw [← contDiffOn_univ] at hconv ⊢
  refine hconv.congr ?_
  intro z _hz
  rw [hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := g) (x := z) hφ hε]
  rw [MeasureTheory.convolution_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp [κ, hiaiScaledMollifierKernel,
    hiaiScaledMollifierWeight, mul_comm]

/-- The regularization of the local clip is `C^3`. -/
theorem hiaiRegularization_localClip_contDiff_order3
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε η x : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hx : x ∈ hiaiRegularizedInterior η)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiff ℝ 3
      (hiaiRegularization φ ε
        (hiaiLocalClip f (x - η) (x + η))) := by
  exact hiaiRegularization_contDiff_order3_of_locallyIntegrable
    (φ := φ) (g := hiaiLocalClip f (x - η) (x + η)) hφ hε
    ((hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
      (f := f) (ε := η) (x := x) hη hx hpos).locallyIntegrable)

/-- The regularization of the local clip is `C^5`. -/
theorem hiaiRegularization_localClip_contDiff_order5
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε η x : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hx : x ∈ hiaiRegularizedInterior η)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiff ℝ 5
      (hiaiRegularization φ ε
        (hiaiLocalClip f (x - η) (x + η))) := by
  exact hiaiRegularization_contDiff_order5_of_locallyIntegrable
    (φ := φ) (g := hiaiLocalClip f (x - η) (x + η)) hφ hε
    ((hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
      (f := f) (ε := η) (x := x) hη hx hpos).locallyIntegrable)

/-- The regularization of the local clip is `C^m` for every finite order `m`. -/
theorem hiaiRegularization_localClip_contDiff_anyOrder
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (m : ℕ) {ε η x : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hx : x ∈ hiaiRegularizedInterior η)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiff ℝ m
      (hiaiRegularization φ ε
        (hiaiLocalClip f (x - η) (x + η))) := by
  exact hiaiRegularization_contDiff_of_locallyIntegrable_anyOrder
    (φ := φ) (g := hiaiLocalClip f (x - η) (x + η)) hφ m hε
    ((hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
      (f := f) (ε := η) (x := x) hη hx hpos).locallyIntegrable)

/--
On a small center interval, the regularization only samples points where the
local clip agrees with the original function.
-/
theorem hiaiRegularization_eq_localClip_on_small_interval
    {φ f : ℝ → ℝ} {ε δ x z : ℝ}
    (hε : 0 < ε)
    (hz : z ∈ Set.Ioo (x - δ) (x + δ)) :
    hiaiRegularization φ ε f z =
      hiaiRegularization φ ε
        (hiaiLocalClip f (x - (ε + δ)) (x + (ε + δ))) z := by
  unfold hiaiRegularization
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have htlow : -ε ≤ ε * t := by
    have h := mul_le_mul_of_nonneg_left ht.1 hε.le
    simpa using h
  have hthigh : ε * t ≤ ε := by
    have h := mul_le_mul_of_nonneg_left ht.2 hε.le
    simpa using h
  have hy :
      z - ε * t ∈ Set.Icc (x - (ε + δ)) (x + (ε + δ)) := by
    constructor
    · linarith [hz.1, hthigh]
    · linarith [hz.2, htlow]
  change φ t * f (z - ε * t) =
    φ t * hiaiLocalClip f (x - (ε + δ)) (x + (ε + δ)) (z - ε * t)
  rw [hiaiLocalClip_eq_on_Icc (f := f) hy]

/--
The mollified regularization is `C^m` on the regularized interior for every
finite order `m`.  This is the order-generic replacement for the deleted
fixed C7/C9/.../C17 scaffolds from the historical pilot route.
-/
theorem hiaiRegularization_contDiffOn_regularizedInterior_anyOrder
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ m (hiaiRegularization φ ε f)
      (hiaiRegularizedInterior ε) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro x hx
  let leftMargin : ℝ := x - ((-1 : ℝ) + ε)
  let rightMargin : ℝ := (1 - ε) - x
  let δ : ℝ := min leftMargin rightMargin / 2
  let η : ℝ := ε + δ
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
  let u : Set ℝ := Set.Ioo (x - δ) (x + δ)
  have huopen : IsOpen u := by
    simpa [u] using isOpen_Ioo
  have hxu : x ∈ u := by
    dsimp [u]
    constructor <;> linarith
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    linarith
  have hxη : x ∈ hiaiRegularizedInterior η := by
    dsimp [hiaiRegularizedInterior, η, leftMargin, rightMargin] at *
    constructor <;> linarith
  refine ⟨u, huopen, hxu, ?_⟩
  have hclip :
      ContDiff ℝ m
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η))) :=
    hiaiRegularization_localClip_contDiff_anyOrder
      (φ := φ) (f := f) hφ m hε hη_nonneg hxη hpos
  have hclipOn :
      ContDiffOn ℝ m
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η)))
        (hiaiRegularizedInterior ε ∩ u) :=
    (contDiffOn_univ.2 hclip).mono (Set.subset_univ _)
  refine hclipOn.congr ?_
  intro z hz
  have hzu : z ∈ Set.Ioo (x - δ) (x + δ) := by
    simpa [u] using hz.2
  have hEq :=
    hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := δ) (x := x) (z := z)
      hε hzu
  simpa [η] using hEq

/-- The scaled-weight `x`-derivative is jointly continuous in center and sample. -/
theorem hiaiScaledMollifierWeight_xDeriv_continuous_uncurry
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) {ε : ℝ} :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z p.2) p.1) := by
  have hlin : Continuous (fun p : ℝ × ℝ => (p.1 - p.2) / ε) :=
    (continuous_fst.sub continuous_snd).div_const ε
  have hderivφ : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  rw [show
      (fun p : ℝ × ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z p.2) p.1) =
        fun p : ℝ × ℝ => ε⁻¹ * (deriv φ ((p.1 - p.2) / ε) * ε⁻¹) by
        funext p
        exact hiaiScaledMollifierWeight_deriv_x
          (φ := φ) (ε := ε) (x := p.1) (y := p.2) hφ]
  exact continuous_const.mul ((hderivφ.comp hlin).mul continuous_const)

/--
The center-derivative integral in the scaled-weight expression is continuous
at every point of the regularized interior.  This is the analytic core of the
first smoothness package for the mollified function.
-/
theorem hiaiRegularization_xDerivIntegral_continuousAt
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContinuousAt
      (fun z : ℝ =>
        ∫ y,
          deriv (fun w : ℝ => hiaiScaledMollifierWeight φ ε w y) z *
            f y) x := by
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
  have hf_int : IntegrableOn f K volume := by
    exact
      (hpos.differentiable.continuousOn.mono hKsub).integrableOn_of_subset_isCompact
        isCompact_Icc measurableSet_Icc subset_rfl measure_Icc_lt_top.ne
  have hparam :
      ContinuousOn
        (Function.uncurry
          (fun z y : ℝ =>
            deriv (fun w : ℝ => hiaiScaledMollifierWeight φ ε w y) z))
        (s ×ˢ Set.univ) := by
    simpa [Function.uncurry] using
      (hiaiScaledMollifierWeight_xDeriv_continuous_uncurry
        (φ := φ) hφ (ε := ε)).continuousOn
  have hsupp :
      ∀ z y : ℝ, z ∈ s → y ∉ K →
        deriv (fun w : ℝ => hiaiScaledMollifierWeight φ ε w y) z = 0 := by
    intro z y hz hyK
    have hywin : y ∉ Set.Icc (z - ε) (z + ε) := by
      intro hywin
      exact hyK ⟨by
        dsimp [s] at hz
        linarith [hywin.1, hz.1], by
        dsimp [s] at hz
        linarith [hywin.2, hz.2]⟩
    exact hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
      (φ := φ) hφ hε hywin
  have hcont_lsmul :
      ContinuousOn
        (fun z : ℝ =>
          ∫ y,
            (ContinuousLinearMap.lsmul ℝ ℝ (f y))
              (deriv (fun w : ℝ =>
                hiaiScaledMollifierWeight φ ε w y) z) ∂volume)
        s := by
    exact
      continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (k := K)
        (s := s)
        (f := fun z y : ℝ =>
          deriv (fun w : ℝ => hiaiScaledMollifierWeight φ ε w y) z)
        (g := f)
        isCompact_Icc hparam hsupp hf_int
  have hcont :
      ContinuousOn
        (fun z : ℝ =>
          ∫ y,
            deriv (fun w : ℝ => hiaiScaledMollifierWeight φ ε w y) z *
              f y) s := by
    refine hcont_lsmul.congr ?_
    intro z _hz
    apply integral_congr_ae
    filter_upwards with y
    simp [mul_comm]
  exact hcont.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)

/-- The derivative of the Hiai regularization is continuous on its interior. -/
theorem hiaiRegularization_deriv_continuousOn_regularizedInterior
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContinuousOn
      (deriv (fun z : ℝ => hiaiRegularization φ ε f z))
      (hiaiRegularizedInterior ε) := by
  intro x hx
  have hcont :=
    hiaiRegularization_xDerivIntegral_continuousAt
      (φ := φ) (f := f) hφ hε hx hpos
  have htarget : ContinuousAt
      (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) x := by
    refine hcont.congr ?_
    have hopen : IsOpen (hiaiRegularizedInterior ε) := by
      simpa [hiaiRegularizedInterior] using isOpen_Ioo
    have hinterior_mem :
        hiaiRegularizedInterior ε ∈ 𝓝 x :=
      hopen.mem_nhds hx
    filter_upwards [hinterior_mem] with z hz
    exact
      (hiaiRegularization_original_deriv_eq_scaledWeight_xDeriv_integral
        (φ := φ) (f := f) hφ hε hz hpos).symm
  exact htarget.continuousWithinAt

/-- The Hiai regularization is `C^1` on the regularized interior. -/
theorem hiaiRegularization_contDiffOn_regularizedInterior_order
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1 (hiaiRegularization φ ε f)
      (hiaiRegularizedInterior ε) := by
  have hopen : IsOpen (hiaiRegularizedInterior ε) := by
    simpa [hiaiRegularizedInterior] using isOpen_Ioo
  have h :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
        (hiaiRegularization φ ε f)
        (hiaiRegularizedInterior ε) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact
        ((regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
          (φ := φ) (f := f) hφ hε hx hpos).differentiableAt).differentiableWithinAt
    · intro htop
      cases htop
    · exact contDiffOn_zero.2
        (hiaiRegularization_deriv_continuousOn_regularizedInterior
          (φ := φ) (f := f) hφ hε hpos)
  simpa using h

/--
The mollified regularization is `C³` on the regularized interior.  The proof is
local: around each center point the original function is replaced by its clipped
continuous extension, and the regularization is a convolution with the compactly
supported smooth scaled mollifier kernel.
-/
theorem hiaiRegularization_contDiffOn_regularizedInterior_order3
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 3 (hiaiRegularization φ ε f)
      (hiaiRegularizedInterior ε) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro x hx
  let leftMargin : ℝ := x - ((-1 : ℝ) + ε)
  let rightMargin : ℝ := (1 - ε) - x
  let δ : ℝ := min leftMargin rightMargin / 2
  let η : ℝ := ε + δ
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
  let u : Set ℝ := Set.Ioo (x - δ) (x + δ)
  have huopen : IsOpen u := by
    simpa [u] using isOpen_Ioo
  have hxu : x ∈ u := by
    dsimp [u]
    constructor <;> linarith
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    linarith
  have hxη : x ∈ hiaiRegularizedInterior η := by
    dsimp [hiaiRegularizedInterior, η, leftMargin, rightMargin] at *
    constructor <;> linarith
  refine ⟨u, huopen, hxu, ?_⟩
  have hclip :
      ContDiff ℝ 3
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η))) :=
    hiaiRegularization_localClip_contDiff_order3
      (φ := φ) (f := f) hφ hε hη_nonneg hxη hpos
  have hclipOn :
      ContDiffOn ℝ 3
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η)))
        (hiaiRegularizedInterior ε ∩ u) :=
    (contDiffOn_univ.2 hclip).mono (Set.subset_univ _)
  refine hclipOn.congr ?_
  intro z hz
  have hzu : z ∈ Set.Ioo (x - δ) (x + δ) := by
    simpa [u] using hz.2
  have hEq :=
    hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := δ) (x := x) (z := z)
      hε hzu
  simpa [η] using hEq

/--
The mollified regularization is `C⁵` on the regularized interior.  This is the
finite smoothness level needed by the three-point confluent determinant pilot.
-/
theorem hiaiRegularization_contDiffOn_regularizedInterior_order5
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 5 (hiaiRegularization φ ε f)
      (hiaiRegularizedInterior ε) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro x hx
  let leftMargin : ℝ := x - ((-1 : ℝ) + ε)
  let rightMargin : ℝ := (1 - ε) - x
  let δ : ℝ := min leftMargin rightMargin / 2
  let η : ℝ := ε + δ
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
  let u : Set ℝ := Set.Ioo (x - δ) (x + δ)
  have huopen : IsOpen u := by
    simpa [u] using isOpen_Ioo
  have hxu : x ∈ u := by
    dsimp [u]
    constructor <;> linarith
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    linarith
  have hxη : x ∈ hiaiRegularizedInterior η := by
    dsimp [hiaiRegularizedInterior, η, leftMargin, rightMargin] at *
    constructor <;> linarith
  refine ⟨u, huopen, hxu, ?_⟩
  have hclip :
      ContDiff ℝ 5
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η))) :=
    hiaiRegularization_localClip_contDiff_order5
      (φ := φ) (f := f) hφ hε hη_nonneg hxη hpos
  have hclipOn :
      ContDiffOn ℝ 5
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - η) (x + η)))
        (hiaiRegularizedInterior ε ∩ u) :=
    (contDiffOn_univ.2 hclip).mono (Set.subset_univ _)
  refine hclipOn.congr ?_
  intro z hz
  have hzu : z ∈ Set.Ioo (x - δ) (x + δ) := by
    simpa [u] using hz.2
  have hEq :=
    hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := δ) (x := x) (z := z)
      hε hzu
  simpa [η] using hEq

/--
The affine pullback of the regularization is `C^m` on `(-1,1)` whenever the
rescaled interval stays inside the regularized interior.
-/
theorem hiaiRegularization_affinePullback_contDiffOn_anyOrder
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (m : ℕ) {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ m
      (hiaiRegularizationAffinePullback φ ε f x r)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hreg :=
    hiaiRegularization_contDiffOn_regularizedInterior_anyOrder
      (φ := φ) (f := f) hφ m hε hpos
  have hlin : ContDiffOn ℝ m (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1) := by
    fun_prop
  have hmap :
      Set.MapsTo (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1)
        (hiaiRegularizedInterior ε) := by
    intro u hu
    exact hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u) hr hsub hu
  simpa [hiaiRegularizationAffinePullback, Function.comp_def] using
    hreg.comp hlin hmap

/-- The affine pullback is `C^1` on the normalized interval. -/
theorem hiaiRegularization_affinePullback_contDiffOn_order
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1
      (hiaiRegularizationAffinePullback φ ε f x r)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hreg :=
    hiaiRegularization_contDiffOn_regularizedInterior_order
      (φ := φ) (f := f) hφ hε hpos
  have hlin : ContDiffOn ℝ 1 (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1) := by
    fun_prop
  have hmap :
      Set.MapsTo (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1)
        (hiaiRegularizedInterior ε) := by
    intro u hu
    exact hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u) hr hsub hu
  simpa [hiaiRegularizationAffinePullback, Function.comp_def] using
    hreg.comp hlin hmap

/-- The affine pullback is `C^3` on the normalized interval. -/
theorem hiaiRegularization_affinePullback_contDiffOn_order3
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 3
      (hiaiRegularizationAffinePullback φ ε f x r)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hreg :=
    hiaiRegularization_contDiffOn_regularizedInterior_order3
      (φ := φ) (f := f) hφ hε hpos
  have hlin : ContDiffOn ℝ 3 (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1) := by
    fun_prop
  have hmap :
      Set.MapsTo (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1)
        (hiaiRegularizedInterior ε) := by
    intro u hu
    exact hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u) hr hsub hu
  simpa [hiaiRegularizationAffinePullback, Function.comp_def] using
    hreg.comp hlin hmap

/-- The affine pullback is `C^5` on the normalized interval. -/
theorem hiaiRegularization_affinePullback_contDiffOn_order5
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 5
      (hiaiRegularizationAffinePullback φ ε f x r)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hreg :=
    hiaiRegularization_contDiffOn_regularizedInterior_order5
      (φ := φ) (f := f) hφ hε hpos
  have hlin : ContDiffOn ℝ 5 (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1) := by
    fun_prop
  have hmap :
      Set.MapsTo (fun u : ℝ => x + r * u) (Set.Ioo (-1 : ℝ) 1)
        (hiaiRegularizedInterior ε) := by
    intro u hu
    exact hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u) hr hsub hu
  simpa [hiaiRegularizationAffinePullback, Function.comp_def] using
    hreg.comp hlin hmap

/--
The regularized affine pullback now has both unit-interval Löwner positivity
and the `C¹` smoothness required for the first smooth Hiai bridge.
-/
theorem hiaiRegularization_affinePullback_C1_loewnerPosInput
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval
        (hiaiRegularizationAffinePullback φ ε f x r) ∧
      ContDiffOn ℝ 1
        (hiaiRegularizationAffinePullback φ ε f x r)
        (Set.Ioo (-1 : ℝ) 1) :=
  ⟨hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hr hsub hpos,
    hiaiRegularization_affinePullback_contDiffOn_order
      (φ := φ) (f := f) hφ hε hr hsub hpos⟩

/--
The same local regularized input, upgraded to the finite `C³` smoothness needed
for the smooth Hiai step.  This is deliberately weaker than book
`C∞`; the book-smooth wrapper `hiaiRegularization_affinePullback_smoothHiaiInput`
(`ConditionalKernelPSD.lean`) takes the book-smooth order as an explicit argument.
-/
theorem hiaiRegularization_affinePullback_C3_loewnerPosInput
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval
        (hiaiRegularizationAffinePullback φ ε f x r) ∧
      ContDiffOn ℝ 3
        (hiaiRegularizationAffinePullback φ ε f x r)
        (Set.Ioo (-1 : ℝ) 1) :=
  ⟨hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hr hsub hpos,
    hiaiRegularization_affinePullback_contDiffOn_order3
      (φ := φ) (f := f) hφ hε hr hsub hpos⟩

/--
The same local regularized input at the finite `C⁵` level needed by the
three-point confluent determinant route.
-/
theorem hiaiRegularization_affinePullback_C5_loewnerPosInput
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval
        (hiaiRegularizationAffinePullback φ ε f x r) ∧
      ContDiffOn ℝ 5
        (hiaiRegularizationAffinePullback φ ε f x r)
        (Set.Ioo (-1 : ℝ) 1) :=
  ⟨hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hr hsub hpos,
    hiaiRegularization_affinePullback_contDiffOn_order5
      (φ := φ) (f := f) hφ hε hr hsub hpos⟩

end

end Quantum.TraceInequality.Loewner
