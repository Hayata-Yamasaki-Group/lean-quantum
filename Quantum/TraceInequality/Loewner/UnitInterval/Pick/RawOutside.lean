import Quantum.TraceInequality.Loewner.UnitInterval.Pick.OutsideHerglotz

/-!
# Chapter 3 raw outside Herglotz data

This module contains the raw book (3.46) outside Herglotz representation, its
real boundary-value passage, and the wrappers reducing raw outside data to the
post-rewrite outside Herglotz data.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-- The raw Herglotz kernel in the book formula (3.46). -/
def unitIntervalHerglotzRawKernel (z : ℂ) (y : ℝ) : ℂ :=
  (1 + (y : ℂ) * z) / ((y : ℂ) - z)

/--
Raw outside Herglotz representation data in the book formula (3.46).

This is the output expected from Theorem 3.4 together with Corollary 3.6,
before the book rewrites it into the normalized interval kernel.
-/
structure UnitIntervalPickHerglotzRawOutsideData (f : ℝ → ℝ) where
  pick : PickExtensionOnUnitInterval f
  constant : ℝ
  slope : ℝ≥0
  outsideMeasure : FiniteMeasure ℝ
  outside_support :
    (outsideMeasure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0
  raw_formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      (f x : ℂ) =
        (constant : ℂ) + ((slope : ℝ) : ℂ) * (x : ℂ) +
          ∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y
            ∂(outsideMeasure : Measure ℝ)

/-- The raw outside measure is a.e. supported outside `(-1,1)`. -/
theorem UnitIntervalPickHerglotzRawOutsideData.ae_outside_not_mem_Ioo
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzRawOutsideData f) :
    ∀ᵐ y ∂(data.outsideMeasure : Measure ℝ), y ∉ Set.Ioo (-1 : ℝ) 1 := by
  rw [ae_iff]
  simpa using data.outside_support

/-- An outside point stays at least `1 - |x|` away from an interior point `x`. -/
private theorem one_sub_abs_le_abs_sub_of_mem_Ioo_of_not_mem_Ioo
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    (1 : ℝ) - |x| ≤ |y - x| := by
  have hx_abs_lt : |x| < (1 : ℝ) := abs_lt.mpr hx
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_not_mem_Ioo hy
  have hle₁ : (1 : ℝ) - |x| ≤ |y| - |x| := by
    exact sub_le_sub_right hy_abs |x|
  have hle₂ : |y| - |x| ≤ |y - x| :=
    abs_sub_abs_le_abs_sub y x
  exact hle₁.trans hle₂

/-- The raw Herglotz kernel has an outside-line bound for fixed interior `x`. -/
private theorem unitIntervalHerglotzRawKernel_norm_le_of_not_mem_Ioo
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    ‖unitIntervalHerglotzRawKernel (x : ℂ) y‖ ≤
      |x| + (1 + x ^ (2 : ℕ)) / (1 - |x|) := by
  have hx_abs_lt : |x| < (1 : ℝ) := abs_lt.mpr hx
  have hx_den_pos : 0 < (1 : ℝ) - |x| := by linarith
  have hyx : y ≠ x := by
    intro h
    exact hy (by simpa [h] using hx)
  have hyxC : (y : ℂ) - (x : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hyx)
  have hden_lower_real :
      (1 : ℝ) - |x| ≤ |y - x| :=
    one_sub_abs_le_abs_sub_of_mem_Ioo_of_not_mem_Ioo hx hy
  have hden_lower :
      (1 : ℝ) - |x| ≤ ‖(y : ℂ) - (x : ℂ)‖ := by
    simpa [← Complex.ofReal_sub] using hden_lower_real
  have hnum_nonneg : 0 ≤ 1 + x ^ (2 : ℕ) := by positivity
  have hraw :
      unitIntervalHerglotzRawKernel (x : ℂ) y =
        (x : ℂ) + ((1 + x ^ (2 : ℕ) : ℝ) : ℂ) / ((y : ℂ) - (x : ℂ)) := by
    unfold unitIntervalHerglotzRawKernel
    field_simp [hyxC]
    norm_num
    ring
  rw [hraw]
  calc
    ‖(x : ℂ) + ((1 + x ^ (2 : ℕ) : ℝ) : ℂ) / ((y : ℂ) - (x : ℂ))‖
        ≤ ‖(x : ℂ)‖ +
            ‖((1 + x ^ (2 : ℕ) : ℝ) : ℂ) / ((y : ℂ) - (x : ℂ))‖ :=
          norm_add_le _ _
    _ = |x| +
          ‖((1 + x ^ (2 : ℕ) : ℝ) : ℂ)‖ / ‖(y : ℂ) - (x : ℂ)‖ := by
          simp
    _ = |x| + (1 + x ^ (2 : ℕ)) / ‖(y : ℂ) - (x : ℂ)‖ := by
          rw [Complex.norm_of_nonneg hnum_nonneg]
    _ ≤ |x| + (1 + x ^ (2 : ℕ)) / (1 - |x|) := by
          exact add_le_add (le_refl |x|)
            (div_le_div_of_nonneg_left hnum_nonneg hx_den_pos hden_lower)

/-- The raw Herglotz kernel is integrable against the raw outside measure. -/
theorem UnitIntervalPickHerglotzRawOutsideData.rawKernel_integrable
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzRawOutsideData f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Integrable (fun y : ℝ => unitIntervalHerglotzRawKernel (x : ℂ) y)
      (data.outsideMeasure : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ => unitIntervalHerglotzRawKernel (x : ℂ) y)
        (data.outsideMeasure : Measure ℝ) := by
    have hmeas' :
        Measurable fun y : ℝ => unitIntervalHerglotzRawKernel (x : ℂ) y := by
      unfold unitIntervalHerglotzRawKernel
      measurability
    exact hmeas'.aestronglyMeasurable
  refine Integrable.of_bound hmeas
    (|x| + (1 + x ^ (2 : ℕ)) / (1 - |x|)) ?_
  filter_upwards [data.ae_outside_not_mem_Ioo] with y hy
  exact unitIntervalHerglotzRawKernel_norm_le_of_not_mem_Ioo hx hy

/-- Subtracting the raw kernel at zero gives the normalized interval Pick kernel. -/
theorem unitIntervalHerglotzRawKernel_sub_zero_eq_rewritten
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    unitIntervalHerglotzRawKernel (x : ℂ) y -
        unitIntervalHerglotzRawKernel (0 : ℂ) y =
      unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
        ((unitIntervalHerglotzWeight y : ℝ) : ℂ) := by
  have hy0 : y ≠ 0 := ne_zero_of_not_mem_Ioo hy
  have hy0C : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
  have hyx : y ≠ x := by
    intro h
    exact hy (by simpa [h] using hx)
  have hyxC : (y : ℂ) - (x : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hyx)
  have hden_transform :
      1 + ((-(y⁻¹) : ℝ) : ℂ) * (x : ℂ) =
        ((y : ℂ) - (x : ℂ)) / (y : ℂ) := by
    norm_num
    field_simp [hy0C]
    ring
  have hweight_cast :
      (((1 + y ^ (2 : ℕ)) / y ^ (2 : ℕ) : ℝ) : ℂ) =
        (1 + (y : ℂ) ^ (2 : ℕ)) / (y : ℂ) ^ (2 : ℕ) := by
    norm_num
  unfold unitIntervalHerglotzRawKernel unitIntervalPickKernel
    unitIntervalHerglotzOutsideMap unitIntervalHerglotzWeight
  rw [hden_transform, hweight_cast]
  field_simp [hy0C, hyxC]
  norm_num
  ring

/-- Convert the raw book (3.46) outside Herglotz data to the post-rewrite data. -/
def unitIntervalPickHerglotzOutsideData_of_rawOutsideData
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzRawOutsideData f) :
    UnitIntervalPickHerglotzOutsideData f where
  pick := data.pick
  slope := data.slope
  outsideMeasure := data.outsideMeasure
  outside_support := data.outside_support
  rewritten_formula := by
    intro x hx
    let μ : Measure ℝ := data.outsideMeasure
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
    have hIntx :
        Integrable (fun y : ℝ => unitIntervalHerglotzRawKernel (x : ℂ) y) μ :=
      data.rawKernel_integrable hx
    have hInt0 :
        Integrable (fun y : ℝ => unitIntervalHerglotzRawKernel (0 : ℂ) y) μ :=
      data.rawKernel_integrable h0
    have hdiff :
        (∫ y : ℝ,
            (unitIntervalHerglotzRawKernel (x : ℂ) y -
              unitIntervalHerglotzRawKernel (0 : ℂ) y) ∂μ) =
          (∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y ∂μ) -
            ∫ y : ℝ, unitIntervalHerglotzRawKernel (0 : ℂ) y ∂μ := by
      exact integral_sub hIntx hInt0
    have hrew :
        (∫ y : ℝ,
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
              ((unitIntervalHerglotzWeight y : ℝ) : ℂ) ∂μ) =
          (∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y ∂μ) -
            ∫ y : ℝ, unitIntervalHerglotzRawKernel (0 : ℂ) y ∂μ := by
      rw [← hdiff]
      refine integral_congr_ae ?_
      filter_upwards [data.ae_outside_not_mem_Ioo] with y hy
      exact (unitIntervalHerglotzRawKernel_sub_zero_eq_rewritten hx hy).symm
    have hraw0 :
        (f 0 : ℂ) =
          (data.constant : ℂ) +
            ∫ y : ℝ, unitIntervalHerglotzRawKernel (0 : ℂ) y ∂μ := by
      simpa [μ] using data.raw_formula h0
    calc
      (f x : ℂ) =
          (data.constant : ℂ) + ((data.slope : ℝ) : ℂ) * (x : ℂ) +
            ∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y ∂μ := by
          simpa [μ] using data.raw_formula hx
      _ = (f 0 : ℂ) + ((data.slope : ℝ) : ℂ) * (x : ℂ) +
            ∫ y : ℝ,
              unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
                ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
              ∂(data.outsideMeasure : Measure ℝ) := by
          rw [hraw0, hrew]
          ring

/-- Raw book (3.46) outside Herglotz data already imply the interval representation. -/
def integralRepOnUnitInterval_of_pickHerglotzRawOutsideData
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzRawOutsideData f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickHerglotzOutsideData
    (unitIntervalPickHerglotzOutsideData_of_rawOutsideData data)

/-- Producer interface for the raw book (3.46) outside Herglotz representation. -/
structure UnitIntervalPickHerglotzRawOutsideProducer where
  produce :
    ∀ {f : ℝ → ℝ}, PickExtensionOnUnitInterval f →
      UnitIntervalPickHerglotzRawOutsideData f

/-- A raw outside producer gives the post-rewrite outside-data producer. -/
def unitIntervalPickHerglotzOutsideProducer_of_rawOutsideProducer
    (producer : UnitIntervalPickHerglotzRawOutsideProducer) :
    UnitIntervalPickHerglotzOutsideProducer where
  produce := by
    intro f pick
    exact unitIntervalPickHerglotzOutsideData_of_rawOutsideData
      (producer.produce (f := f) pick)

/-- Reverse Theorem 3.8 from Pick extension, assuming the raw outside producer. -/
def integralRepOnUnitInterval_of_pickExtension_of_rawHerglotzOutsideProducer
    (producer : UnitIntervalPickHerglotzRawOutsideProducer)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_herglotzOutsideProducer
    (unitIntervalPickHerglotzOutsideProducer_of_rawOutsideProducer producer) pick

/-- Approach a real point from the upper half-plane by a canonical vertical sequence. -/
def unitIntervalUpperBoundarySeq (x : ℝ) (n : ℕ) : ℂ :=
  (x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I

/-- The canonical vertical boundary sequence always lies in the upper half-plane. -/
theorem unitIntervalUpperBoundarySeq_im_pos (x : ℝ) (n : ℕ) :
    0 < (unitIntervalUpperBoundarySeq x n).im := by
  simp only [unitIntervalUpperBoundarySeq, one_div, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.inv_re, Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.normSq,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.natCast_im, Complex.one_im, add_zero,
    mul_zero, div_self_mul_self', Complex.I_im, mul_one, Complex.inv_im, neg_zero, zero_div,
    Complex.I_re, zero_add, inv_pos]
  positivity

/-- The vertical upper-boundary sequence converges to the real point `x`. -/
theorem unitIntervalUpperBoundarySeq_tendsto_ofReal (x : ℝ) :
    Tendsto (fun n : ℕ => unitIntervalUpperBoundarySeq x n) atTop (𝓝 (x : ℂ)) := by
  have h :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hC :
      Tendsto
        (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by
    simpa using (h.ofReal.mul tendsto_const_nhds)
  simpa [unitIntervalUpperBoundarySeq] using tendsto_const_nhds.add hC

/-- A Pick extension is continuous at real points of the open interval. -/
theorem PickExtensionOnUnitInterval.continuousAt_real
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt pick.F (x : ℂ) :=
  pick.analyticOn.continuousOn.continuousAt
    (unitIntervalPickDomain_isOpen.mem_nhds
      (ofReal_mem_unitIntervalPickDomain hx))

/-- Simon Ch.3 [simon2019]: the raw outside kernel has vertical boundary limits. -/
theorem unitIntervalHerglotzRawKernel_tendsto_real_of_upper
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun n : ℕ =>
        unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y)
      atTop (𝓝 (unitIntervalHerglotzRawKernel (x : ℂ) y)) := by
  have hyx : (y : ℂ) - (x : ℂ) ≠ 0 := by
    have hyxR : y ≠ x := by
      intro h
      exact hy (by simpa [h] using hx)
    exact sub_ne_zero.mpr (by exact_mod_cast hyxR)
  have hcont :
      ContinuousAt (fun z : ℂ => unitIntervalHerglotzRawKernel z y) (x : ℂ) := by
    unfold unitIntervalHerglotzRawKernel
    exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id) hyx
  exact hcont.tendsto.comp (unitIntervalUpperBoundarySeq_tendsto_ofReal x)

/--
Near a real point of `(-1,1)`, the raw Herglotz kernel is uniformly bounded
on the outside support line.
-/
theorem unitIntervalHerglotzRawKernel_near_real_bound_of_outside
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ ⦃z : ℂ⦄, z ∈ Metric.ball (x : ℂ) r →
      ∀ ⦃y : ℝ⦄, y ∉ Set.Ioo (-1 : ℝ) 1 →
        ‖unitIntervalHerglotzRawKernel z y‖ ≤ C := by
  have hx_abs_lt : |x| < (1 : ℝ) := abs_lt.mpr hx
  let r : ℝ := ((1 : ℝ) - |x|) / 2
  let B : ℝ := |x| + 1
  let C : ℝ := B + (1 + B ^ (2 : ℕ)) / r
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨r, C, hr_pos, hC_nonneg, ?_⟩
  intro z hz y hy
  have hyxR : y ≠ x := by
    intro h
    exact hy (by simpa [h] using hx)
  have hyxz : (y : ℂ) - z ≠ 0 := by
    have hden_lower : r ≤ ‖(y : ℂ) - z‖ := by
      have hyx_lower_real :
          (1 : ℝ) - |x| ≤ |y - x| :=
        one_sub_abs_le_abs_sub_of_mem_Ioo_of_not_mem_Ioo hx hy
      have hyx_lower :
          (1 : ℝ) - |x| ≤ ‖(y : ℂ) - (x : ℂ)‖ := by
        simpa [← Complex.ofReal_sub] using hyx_lower_real
      have hz_norm : ‖z - (x : ℂ)‖ < r := by
        simpa [dist_eq_norm] using hz
      have htri :
          ‖(y : ℂ) - (x : ℂ)‖ - ‖z - (x : ℂ)‖ ≤
            ‖(y : ℂ) - z‖ := by
        have h :=
          norm_sub_norm_le ((y : ℂ) - (x : ℂ)) (z - (x : ℂ))
        convert h using 1
        ring_nf
      dsimp [r] at *
      linarith
    exact norm_pos_iff.mp (lt_of_lt_of_le hr_pos hden_lower)
  have hden_lower : r ≤ ‖(y : ℂ) - z‖ := by
    have hyx_lower_real :
        (1 : ℝ) - |x| ≤ |y - x| :=
      one_sub_abs_le_abs_sub_of_mem_Ioo_of_not_mem_Ioo hx hy
    have hyx_lower :
        (1 : ℝ) - |x| ≤ ‖(y : ℂ) - (x : ℂ)‖ := by
      simpa [← Complex.ofReal_sub] using hyx_lower_real
    have hz_norm : ‖z - (x : ℂ)‖ < r := by
      simpa [dist_eq_norm] using hz
    have htri :
        ‖(y : ℂ) - (x : ℂ)‖ - ‖z - (x : ℂ)‖ ≤
          ‖(y : ℂ) - z‖ := by
      have h :=
        norm_sub_norm_le ((y : ℂ) - (x : ℂ)) (z - (x : ℂ))
      convert h using 1
      ring_nf
    dsimp [r] at *
    linarith
  have hz_norm_bound : ‖z‖ ≤ B := by
    have hz_norm : ‖z - (x : ℂ)‖ < r := by
      simpa [dist_eq_norm] using hz
    have htriangle : ‖z‖ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := by
      calc
        ‖z‖ = ‖(x : ℂ) + (z - (x : ℂ))‖ := by
          congr 1
          ring
        _ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
    have hr_le_one : r ≤ 1 := by
      dsimp [r]
      linarith [abs_nonneg x]
    calc
      ‖z‖ ≤ ‖(x : ℂ)‖ + ‖z - (x : ℂ)‖ := htriangle
      _ ≤ |x| + r := by
        have hxnorm : ‖(x : ℂ)‖ = |x| := by
          simp
        rw [hxnorm]
        linarith
      _ ≤ |x| + 1 := by
        linarith
      _ = B := by rfl
  have hnum_bound : ‖(1 : ℂ) + z ^ (2 : ℕ)‖ ≤ 1 + B ^ (2 : ℕ) := by
    have hz_sq : ‖z‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg z) hz_norm_bound 2
    calc
      ‖(1 : ℂ) + z ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ :=
        norm_add_le _ _
      _ = 1 + ‖z‖ ^ (2 : ℕ) := by simp [norm_pow]
      _ ≤ 1 + B ^ (2 : ℕ) := by linarith
  have hraw :
      unitIntervalHerglotzRawKernel z y =
        z + ((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z) := by
    unfold unitIntervalHerglotzRawKernel
    field_simp [hyxz]
    ring
  rw [hraw]
  calc
    ‖z + ((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z)‖
        ≤ ‖z‖ + ‖((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z)‖ :=
          norm_add_le _ _
    _ = ‖z‖ + ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / ‖(y : ℂ) - z‖ := by
          simp
    _ ≤ B + (1 + B ^ (2 : ℕ)) / r := by
          have hdiv :
              ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / ‖(y : ℂ) - z‖ ≤
                (1 + B ^ (2 : ℕ)) / r := by
            have hdiv₁ :
                ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / ‖(y : ℂ) - z‖ ≤
                  (1 + B ^ (2 : ℕ)) / ‖(y : ℂ) - z‖ := by
              exact div_le_div_of_nonneg_right hnum_bound (norm_nonneg _)
            have hnum_nonneg : 0 ≤ 1 + B ^ (2 : ℕ) := by positivity
            have hdiv₂ :
                (1 + B ^ (2 : ℕ)) / ‖(y : ℂ) - z‖ ≤
                  (1 + B ^ (2 : ℕ)) / r := by
              exact div_le_div_of_nonneg_left hnum_nonneg hr_pos hden_lower
            exact hdiv₁.trans hdiv₂
          exact add_le_add hz_norm_bound hdiv
    _ = C := by rfl

/--
Upper-half-plane raw outside Herglotz data in the book formula (3.46), before
taking the real boundary values on `(-1,1)`.
-/
structure UnitIntervalPickHerglotzUpperRawOutsideData (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: the Pick extension represented by the upper formula. -/
  pick : PickExtensionOnUnitInterval f
  /-- Simon Ch.3 [simon2019]: the real constant term in formula (3.46). -/
  constant : ℝ
  /-- Simon Ch.3 [simon2019]: the nonnegative linear coefficient in (3.46). -/
  slope : ℝ≥0
  /-- Simon Ch.3 [simon2019]: the finite outside-line measure in (3.46). -/
  outsideMeasure : FiniteMeasure ℝ
  /-- Simon Ch.3 [simon2019]: the measure has no mass on the open interval. -/
  outside_support :
    (outsideMeasure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0
  /-- Simon Ch.3 [simon2019]: the raw Herglotz formula on the upper half-plane. -/
  upper_formula :
    ∀ ⦃z : ℂ⦄, 0 < z.im →
      pick.F z =
        (constant : ℂ) + ((slope : ℝ) : ℂ) * z +
          ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
            ∂(outsideMeasure : Measure ℝ)

/-- Simon Ch.3 [simon2019]: the upper raw measure is a.e. outside `(-1,1)`. -/
theorem UnitIntervalPickHerglotzUpperRawOutsideData.ae_outside_not_mem_Ioo
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawOutsideData f) :
    ∀ᵐ y ∂(data.outsideMeasure : Measure ℝ), y ∉ Set.Ioo (-1 : ℝ) 1 := by
  rw [ae_iff]
  simpa using data.outside_support

/-- Simon Ch.3 [simon2019]: dominated convergence moves the raw integral to the boundary. -/
theorem UnitIntervalPickHerglotzUpperRawOutsideData.raw_integral_tendsto_real
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawOutsideData f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n : ℕ =>
        ∫ y : ℝ,
          unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y
          ∂(data.outsideMeasure : Measure ℝ))
      atTop
      (𝓝
        (∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y
          ∂(data.outsideMeasure : Measure ℝ))) := by
  obtain ⟨r, C, hr_pos, _hC_nonneg, hbound⟩ :=
    unitIntervalHerglotzRawKernel_near_real_bound_of_outside hx
  have hseq_eventually :
      ∀ᶠ n : ℕ in atTop,
        unitIntervalUpperBoundarySeq x n ∈ Metric.ball (x : ℂ) r :=
    (unitIntervalUpperBoundarySeq_tendsto_ofReal x)
      (Metric.ball_mem_nhds (x : ℂ) hr_pos)
  have hF_meas :
      ∀ᶠ n : ℕ in atTop,
        AEStronglyMeasurable
          (fun y : ℝ =>
            unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y)
          (data.outsideMeasure : Measure ℝ) := by
    refine Eventually.of_forall fun n => ?_
    have hmeas :
        Measurable fun y : ℝ =>
          unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y := by
      unfold unitIntervalHerglotzRawKernel
      measurability
    exact hmeas.aestronglyMeasurable
  have h_bound :
      ∀ᶠ n : ℕ in atTop,
        ∀ᵐ y : ℝ ∂(data.outsideMeasure : Measure ℝ),
          ‖unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y‖ ≤ C := by
    filter_upwards [hseq_eventually] with n hn
    filter_upwards [data.ae_outside_not_mem_Ioo] with y hy
    exact hbound hn hy
  have hC_int : Integrable (fun _y : ℝ => C)
      (data.outsideMeasure : Measure ℝ) :=
    MeasureTheory.integrable_const C
  have hlim :
      ∀ᵐ y : ℝ ∂(data.outsideMeasure : Measure ℝ),
        Tendsto
          (fun n : ℕ =>
            unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y)
          atTop (𝓝 (unitIntervalHerglotzRawKernel (x : ℂ) y)) := by
    filter_upwards [data.ae_outside_not_mem_Ioo] with y hy
    exact unitIntervalHerglotzRawKernel_tendsto_real_of_upper hx hy
  exact tendsto_integral_filter_of_dominated_convergence
    (μ := (data.outsideMeasure : Measure ℝ)) (fun _y : ℝ => C)
    hF_meas h_bound hC_int hlim

/-- Simon Ch.3 [simon2019]: upper raw data have the real interval formula. -/
theorem UnitIntervalPickHerglotzUpperRawOutsideData.raw_formula_real
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawOutsideData f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (f x : ℂ) =
      (data.constant : ℂ) + ((data.slope : ℝ) : ℂ) * (x : ℂ) +
        ∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y
          ∂(data.outsideMeasure : Measure ℝ) := by
  have hseq := unitIntervalUpperBoundarySeq_tendsto_ofReal x
  have hleft :
      Tendsto (fun n : ℕ => data.pick.F (unitIntervalUpperBoundarySeq x n))
        atTop (𝓝 (f x : ℂ)) := by
    have hcont := data.pick.continuousAt_real hx
    have h :=
      hcont.tendsto.comp hseq
    simpa [data.pick.agreesOnReal hx] using h
  have hint := data.raw_integral_tendsto_real hx
  have hright :
      Tendsto
        (fun n : ℕ =>
          (data.constant : ℂ) +
            ((data.slope : ℝ) : ℂ) * unitIntervalUpperBoundarySeq x n +
            ∫ y : ℝ,
              unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y
              ∂(data.outsideMeasure : Measure ℝ))
        atTop
        (𝓝
          ((data.constant : ℂ) + ((data.slope : ℝ) : ℂ) * (x : ℂ) +
            ∫ y : ℝ, unitIntervalHerglotzRawKernel (x : ℂ) y
              ∂(data.outsideMeasure : Measure ℝ))) := by
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul hseq)).add hint
  have heq :
      (fun n : ℕ => data.pick.F (unitIntervalUpperBoundarySeq x n)) =ᶠ[atTop]
        fun n : ℕ =>
          (data.constant : ℂ) +
            ((data.slope : ℝ) : ℂ) * unitIntervalUpperBoundarySeq x n +
            ∫ y : ℝ,
              unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y
              ∂(data.outsideMeasure : Measure ℝ) := by
    exact Eventually.of_forall fun n =>
      data.upper_formula (unitIntervalUpperBoundarySeq_im_pos x n)
  exact tendsto_nhds_unique (hleft.congr' heq) hright

/-- Convert upper-half-plane raw Herglotz outside data to real raw outside data. -/
def unitIntervalPickHerglotzRawOutsideData_of_upperRawOutsideData
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawOutsideData f) :
    UnitIntervalPickHerglotzRawOutsideData f where
  pick := data.pick
  constant := data.constant
  slope := data.slope
  outsideMeasure := data.outsideMeasure
  outside_support := data.outside_support
  raw_formula := by
    intro x hx
    exact data.raw_formula_real hx

/-- Upper-half-plane raw outside Herglotz data imply the interval representation. -/
def integralRepOnUnitInterval_of_pickHerglotzUpperRawOutsideData
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawOutsideData f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickHerglotzRawOutsideData
    (unitIntervalPickHerglotzRawOutsideData_of_upperRawOutsideData data)

/-- Producer interface for the upper-half-plane raw outside Herglotz representation. -/
structure UnitIntervalPickHerglotzUpperRawOutsideProducer where
  /-- Simon Ch.3 [simon2019]: produce upper raw outside data for a Pick extension. -/
  produce :
    ∀ {f : ℝ → ℝ}, PickExtensionOnUnitInterval f →
      UnitIntervalPickHerglotzUpperRawOutsideData f

/-- An upper raw outside producer gives the real raw outside producer. -/
def unitIntervalPickHerglotzRawOutsideProducer_of_upperRawOutsideProducer
    (producer : UnitIntervalPickHerglotzUpperRawOutsideProducer) :
    UnitIntervalPickHerglotzRawOutsideProducer where
  produce := by
    intro f pick
    exact unitIntervalPickHerglotzRawOutsideData_of_upperRawOutsideData
      (producer.produce (f := f) pick)

/-- Reverse Theorem 3.8 from Pick extension, assuming the upper raw outside producer. -/
def integralRepOnUnitInterval_of_pickExtension_of_upperRawHerglotzOutsideProducer
    (producer : UnitIntervalPickHerglotzUpperRawOutsideProducer)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_rawHerglotzOutsideProducer
    (unitIntervalPickHerglotzRawOutsideProducer_of_upperRawOutsideProducer producer) pick

end

end Quantum.TraceInequality.Loewner
