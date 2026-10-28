import Quantum.TraceInequality.Loewner.UnitInterval.Pick.Kernel

/-!
# Chapter 3 outside Herglotz data to interval integral representation

This module contains the post-Herglotz change of variables in book Theorem 3.8.
It takes outside-line Herglotz data and produces the normalized interval measure
used by `IntegralRepOnUnitInterval`.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-- The book change of variables from the outside Herglotz line to `[-1,1]`. -/
def unitIntervalHerglotzOutsideMap (y : ℝ) : ℝ :=
  -(y⁻¹)

/-- The book density `(1 + y^2) / y^2` used in Theorem 3.8. -/
def unitIntervalHerglotzWeight (y : ℝ) : ℝ :=
  (1 + y ^ (2 : ℕ)) / y ^ (2 : ℕ)

/-- The `ENNReal` density corresponding to `unitIntervalHerglotzWeight`. -/
def unitIntervalHerglotzDensity (y : ℝ) : ENNReal :=
  ENNReal.ofReal (unitIntervalHerglotzWeight y)

/--
Post-Herglotz outside representation data for the reverse direction of book
Theorem 3.8.

The actual Herglotz representation theorem and Corollary 3.6 are not proved
here.  This structure records exactly the data obtained after the book
rewriting (3.46)--(3.47): an outside measure, the nonnegative slope term, and
the rewritten formula that still integrates over the outside line.
-/
structure UnitIntervalPickHerglotzOutsideData (f : ℝ → ℝ) where
  pick : PickExtensionOnUnitInterval f
  slope : ℝ≥0
  outsideMeasure : FiniteMeasure ℝ
  outside_support :
    (outsideMeasure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0
  rewritten_formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      (f x : ℂ) =
        (f 0 : ℂ) + ((slope : ℝ) : ℂ) * (x : ℂ) +
          ∫ y : ℝ,
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
              ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
            ∂(outsideMeasure : Measure ℝ)

/-- The outside-to-interval change of variables is measurable. -/
private theorem measurable_unitIntervalHerglotzOutsideMap :
    Measurable unitIntervalHerglotzOutsideMap := by
  change Measurable fun y : ℝ => -(y⁻¹)
  exact measurable_id.inv.neg

/-- The `ENNReal` density attached to the outside Herglotz weight is measurable. -/
private theorem measurable_unitIntervalHerglotzDensity :
    Measurable unitIntervalHerglotzDensity := by
  have hpow : Measurable fun y : ℝ => y ^ (2 : ℕ) := by
    simpa using (measurable_id.pow_const (2 : ℕ))
  have hweight : Measurable unitIntervalHerglotzWeight := by
    unfold unitIntervalHerglotzWeight
    exact (measurable_const.add hpow).div hpow
  simpa [unitIntervalHerglotzDensity] using ENNReal.measurable_ofReal.comp hweight

/-- Points outside `(-1,1)` have absolute value at least one. -/
theorem one_le_abs_of_not_mem_Ioo {y : ℝ}
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    (1 : ℝ) ≤ |y| := by
  by_cases hle : y ≤ -1
  · have hnonpos : y ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  · have hneg : (-1 : ℝ) < y := lt_of_not_ge hle
    have hnotlt : ¬ y < 1 := by
      intro hlt
      exact hy ⟨hneg, hlt⟩
    have hge : (1 : ℝ) ≤ y := le_of_not_gt hnotlt
    rw [abs_of_nonneg (by linarith)]
    exact hge

/-- A point outside `(-1,1)` is nonzero. -/
theorem ne_zero_of_not_mem_Ioo {y : ℝ}
    (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    y ≠ 0 := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_not_mem_Ioo hy
  exact abs_pos.mp (lt_of_lt_of_le zero_lt_one hy_abs)

/-- The outside-to-interval map sends the complement of `(-1,1)` into `[-1,1]`. -/
theorem unitIntervalHerglotzOutsideMap_mem_Icc_of_not_mem_Ioo
    {y : ℝ} (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    unitIntervalHerglotzOutsideMap y ∈ Set.Icc (-1 : ℝ) 1 := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_not_mem_Ioo hy
  have h_inv : |unitIntervalHerglotzOutsideMap y| ≤ (1 : ℝ) := by
    have h : |y|⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hy_abs
    simpa [unitIntervalHerglotzOutsideMap, abs_neg, abs_inv] using h
  simpa [Set.mem_Icc] using (abs_le.mp h_inv)

/-- The outside Herglotz weight is nonnegative. -/
private theorem unitIntervalHerglotzWeight_nonneg (y : ℝ) :
    0 ≤ unitIntervalHerglotzWeight y := by
  unfold unitIntervalHerglotzWeight
  positivity

/-- On the outside line, the Herglotz weight is bounded by two. -/
theorem unitIntervalHerglotzWeight_le_two_of_not_mem_Ioo
    {y : ℝ} (hy : y ∉ Set.Ioo (-1 : ℝ) 1) :
    unitIntervalHerglotzWeight y ≤ 2 := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_not_mem_Ioo hy
  have hy_sq_ge : (1 : ℝ) ≤ y ^ (2 : ℕ) := by
    have hsq_abs : |y| ^ (2 : ℕ) = y ^ (2 : ℕ) := sq_abs y
    nlinarith [hy_abs, abs_nonneg y, hsq_abs]
  have hy_sq_pos : 0 < y ^ (2 : ℕ) :=
    lt_of_lt_of_le zero_lt_one hy_sq_ge
  have hnum_le : 1 + y ^ (2 : ℕ) ≤ 2 * y ^ (2 : ℕ) := by
    nlinarith
  calc
    unitIntervalHerglotzWeight y =
        (1 + y ^ (2 : ℕ)) / y ^ (2 : ℕ) := rfl
    _ ≤ (2 * y ^ (2 : ℕ)) / y ^ (2 : ℕ) := by
          exact div_le_div_of_nonneg_right hnum_le (le_of_lt hy_sq_pos)
    _ = 2 := by
          have hy_ne : y ≠ 0 := ne_zero_of_not_mem_Ioo hy
          field_simp [hy_ne]

/-- The outside Herglotz measure is a.e. supported outside `(-1,1)`. -/
theorem UnitIntervalPickHerglotzOutsideData.ae_outside_not_mem_Ioo
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f) :
    ∀ᵐ y ∂(data.outsideMeasure : Measure ℝ), y ∉ Set.Ioo (-1 : ℝ) 1 := by
  rw [ae_iff]
  simpa using data.outside_support

/-- The weighted outside measure before pushing it to the normalized interval. -/
def unitIntervalHerglotzWeightedOutsideMeasure {f : ℝ → ℝ}
    (data : UnitIntervalPickHerglotzOutsideData f) : Measure ℝ :=
  (data.outsideMeasure : Measure ℝ).withDensity unitIntervalHerglotzDensity

/-- The weighted outside measure has finite total mass. -/
private theorem unitIntervalHerglotzWeightedOutsideMeasure_univ_lt_top
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f) :
    unitIntervalHerglotzWeightedOutsideMeasure data Set.univ < ⊤ := by
  have hbound :
      ∀ᵐ y ∂(data.outsideMeasure : Measure ℝ),
        unitIntervalHerglotzDensity y ≤ (2 : ENNReal) := by
    filter_upwards [data.ae_outside_not_mem_Ioo] with y hy
    simpa [unitIntervalHerglotzDensity] using
      ENNReal.ofReal_le_ofReal
        (unitIntervalHerglotzWeight_le_two_of_not_mem_Ioo hy)
  calc
    unitIntervalHerglotzWeightedOutsideMeasure data Set.univ =
        ∫⁻ y, unitIntervalHerglotzDensity y
          ∂(data.outsideMeasure : Measure ℝ) := by
          simp [unitIntervalHerglotzWeightedOutsideMeasure,
            MeasureTheory.withDensity_apply]
    _ ≤ ∫⁻ _y, (2 : ENNReal) ∂(data.outsideMeasure : Measure ℝ) :=
          lintegral_mono_ae hbound
    _ = (2 : ENNReal) * (data.outsideMeasure : Measure ℝ) Set.univ := by
          simp
    _ < ⊤ := by
          exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)

/-- The weighted outside measure pushed forward to the normalized interval. -/
def unitIntervalHerglotzWeightedPushforward {f : ℝ → ℝ}
    (data : UnitIntervalPickHerglotzOutsideData f) : FiniteMeasure ℝ :=
  ⟨(unitIntervalHerglotzWeightedOutsideMeasure data).map unitIntervalHerglotzOutsideMap, by
    refine ⟨?_⟩
    calc
      ((unitIntervalHerglotzWeightedOutsideMeasure data).map
          unitIntervalHerglotzOutsideMap) Set.univ =
          unitIntervalHerglotzWeightedOutsideMeasure data Set.univ := by
          simp [Measure.map_apply, measurable_unitIntervalHerglotzOutsideMap]
      _ < ⊤ := unitIntervalHerglotzWeightedOutsideMeasure_univ_lt_top data⟩

/-- The atom at `0` which represents the Herglotz slope term. -/
def unitIntervalHerglotzDiracZero : FiniteMeasure ℝ :=
  ⟨Measure.dirac (0 : ℝ), inferInstance⟩

/-- The normalized interval measure obtained from the outside Herglotz data. -/
def unitIntervalHerglotzIntervalMeasure {f : ℝ → ℝ}
    (data : UnitIntervalPickHerglotzOutsideData f) : FiniteMeasure ℝ :=
  data.slope • unitIntervalHerglotzDiracZero +
    unitIntervalHerglotzWeightedPushforward data

/-- The weighted pushforward measure is supported on `[-1,1]`. -/
theorem unitIntervalHerglotzWeightedPushforward_support_Icc
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f) :
    (unitIntervalHerglotzWeightedPushforward data : Measure ℝ)
      (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Icc (-1 : ℝ) 1)ᶜ) :=
    isClosed_Icc.measurableSet.compl
  have hpre0 :
      (data.outsideMeasure : Measure ℝ)
          (unitIntervalHerglotzOutsideMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [data.ae_outside_not_mem_Ioo] with y hy hpre
    exact hpre (unitIntervalHerglotzOutsideMap_mem_Icc_of_not_mem_Ioo hy)
  have hac :
      unitIntervalHerglotzWeightedOutsideMeasure data ≪
        (data.outsideMeasure : Measure ℝ) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hwd0 :
      unitIntervalHerglotzWeightedOutsideMeasure data
          (unitIntervalHerglotzOutsideMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) = 0 :=
    hac hpre0
  calc
    (unitIntervalHerglotzWeightedPushforward data : Measure ℝ)
        (Set.Icc (-1 : ℝ) 1)ᶜ =
        unitIntervalHerglotzWeightedOutsideMeasure data
          (unitIntervalHerglotzOutsideMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) := by
          rw [unitIntervalHerglotzWeightedPushforward, FiniteMeasure.toMeasure_mk,
            Measure.map_apply measurable_unitIntervalHerglotzOutsideMap hS]
    _ = 0 := hwd0

/-- The Dirac mass at `0` is supported on `[-1,1]`. -/
theorem unitIntervalHerglotzDiracZero_support_Icc :
    (unitIntervalHerglotzDiracZero : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  simp [unitIntervalHerglotzDiracZero, h0]

/-- The normalized interval measure is supported on `[-1,1]`. -/
theorem unitIntervalHerglotzIntervalMeasure_support_Icc
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f) :
    (unitIntervalHerglotzIntervalMeasure data : Measure ℝ)
      (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  simp [unitIntervalHerglotzIntervalMeasure, unitIntervalHerglotzDiracZero_support_Icc,
    unitIntervalHerglotzWeightedPushforward_support_Icc]

/-- The interval Pick kernel is integrable against finite measures supported on `[-1,1]`. -/
private theorem unitIntervalPickKernel_integrable_of_finiteMeasure_support_Icc
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    {z : ℂ} (hz : z ∈ (unitIntervalPickDomain : Set ℂ)) :
    Integrable (fun t : ℝ => unitIntervalPickKernel z t) (ν : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => unitIntervalPickKernel z t)
        (ν : Measure ℝ) := by
    have hmeas' : Measurable (fun t : ℝ => unitIntervalPickKernel z t) := by
      unfold unitIntervalPickKernel
      measurability
    exact hmeas'.aestronglyMeasurable
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (unitIntervalPickKernel_continuousOn_Icc_of_mem_domain hz)
  refine Integrable.of_bound hmeas C ?_
  have hae : ∀ᵐ t ∂(ν : Measure ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hν
  filter_upwards [hae] with t ht
  exact hC t ht

/-- Integrating the interval Pick kernel against the slope atom gives the slope term. -/
theorem unitIntervalHerglotzSlope_integral_kernel
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f)
    (x : ℝ) :
    (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
        ∂(data.slope • unitIntervalHerglotzDiracZero : FiniteMeasure ℝ)) =
      ((data.slope : ℝ) : ℂ) * (x : ℂ) := by
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  change (data.slope : ℝ≥0) •
      (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t ∂Measure.dirac (0 : ℝ)) =
    ((data.slope : ℝ) : ℂ) * (x : ℂ)
  rw [MeasureTheory.integral_dirac]
  simp only [unitIntervalPickKernel, Complex.ofReal_zero, zero_mul, add_zero, div_one]
  change ((data.slope : ℂ) • (x : ℂ)) = ((data.slope : ℝ) : ℂ) * (x : ℂ)
  rw [smul_eq_mul]

/-- The weighted pushforward integral is the outside-line weighted kernel integral. -/
theorem unitIntervalHerglotzWeightedPushforward_integral_kernel
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f)
    (x : ℝ) :
    (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
        ∂(unitIntervalHerglotzWeightedPushforward data : Measure ℝ)) =
      ∫ y : ℝ,
        unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
          ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
        ∂(data.outsideMeasure : Measure ℝ) := by
  let μ0 : Measure ℝ := unitIntervalHerglotzWeightedOutsideMeasure data
  have hmap :
      (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
          ∂(unitIntervalHerglotzWeightedPushforward data : Measure ℝ)) =
        ∫ y : ℝ, unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)
          ∂μ0 := by
    have hφ : AEMeasurable unitIntervalHerglotzOutsideMap μ0 :=
      measurable_unitIntervalHerglotzOutsideMap.aemeasurable
    have hf :
        AEStronglyMeasurable (fun t : ℝ => unitIntervalPickKernel (x : ℂ) t)
          (Measure.map unitIntervalHerglotzOutsideMap μ0) := by
      have hmeas : Measurable fun t : ℝ => unitIntervalPickKernel (x : ℂ) t := by
        unfold unitIntervalPickKernel
        measurability
      exact hmeas.aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := μ0)
        (φ := unitIntervalHerglotzOutsideMap) hφ
        (f := fun t : ℝ => unitIntervalPickKernel (x : ℂ) t) hf
    simpa [unitIntervalHerglotzWeightedPushforward, μ0] using h
  have hwd :
      (∫ y : ℝ, unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)
          ∂μ0) =
        ∫ y : ℝ,
          (unitIntervalHerglotzDensity y).toReal •
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)
          ∂(data.outsideMeasure : Measure ℝ) := by
    have htop :
        ∀ᵐ y ∂(data.outsideMeasure : Measure ℝ),
          unitIntervalHerglotzDensity y < (⊤ : ENNReal) :=
      MeasureTheory.ae_of_all (μ := (data.outsideMeasure : Measure ℝ)) (fun y => by
        simp [unitIntervalHerglotzDensity])
    have h :=
      integral_withDensity_eq_integral_toReal_smul
        (μ := (data.outsideMeasure : Measure ℝ))
        (f := unitIntervalHerglotzDensity)
        measurable_unitIntervalHerglotzDensity htop
        (g := fun y : ℝ =>
          unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y))
    simpa [μ0, unitIntervalHerglotzWeightedOutsideMeasure] using h
  have hEq :
      (fun y : ℝ =>
          (unitIntervalHerglotzDensity y).toReal •
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)) =ᵐ[
          (data.outsideMeasure : Measure ℝ)]
        fun y : ℝ =>
          unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
            ((unitIntervalHerglotzWeight y : ℝ) : ℂ) := by
    filter_upwards with y
    have hnonneg : 0 ≤ unitIntervalHerglotzWeight y :=
      unitIntervalHerglotzWeight_nonneg y
    simp [unitIntervalHerglotzDensity, ENNReal.toReal_ofReal hnonneg,
      mul_comm]
  calc
    (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
        ∂(unitIntervalHerglotzWeightedPushforward data : Measure ℝ)) =
        ∫ y : ℝ, unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)
          ∂μ0 := hmap
    _ = ∫ y : ℝ,
          (unitIntervalHerglotzDensity y).toReal •
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y)
          ∂(data.outsideMeasure : Measure ℝ) := hwd
    _ = ∫ y : ℝ,
          unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
            ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
          ∂(data.outsideMeasure : Measure ℝ) :=
        integral_congr_ae hEq

/-- The interval measure integrates the Pick kernel as slope plus outside integral. -/
theorem unitIntervalHerglotzIntervalMeasure_integral_kernel
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
        ∂(unitIntervalHerglotzIntervalMeasure data : Measure ℝ)) =
      ((data.slope : ℝ) : ℂ) * (x : ℂ) +
        ∫ y : ℝ,
          unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
            ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
          ∂(data.outsideMeasure : Measure ℝ) := by
  have hz : (x : ℂ) ∈ (unitIntervalPickDomain : Set ℂ) :=
    ofReal_mem_unitIntervalPickDomain hx
  have hIntSlope :
      Integrable (fun t : ℝ => unitIntervalPickKernel (x : ℂ) t)
        (data.slope • unitIntervalHerglotzDiracZero : FiniteMeasure ℝ) := by
    refine unitIntervalPickKernel_integrable_of_finiteMeasure_support_Icc
      (data.slope • unitIntervalHerglotzDiracZero)
      ?_ hz
    simp [unitIntervalHerglotzDiracZero_support_Icc]
  have hIntPush :
      Integrable (fun t : ℝ => unitIntervalPickKernel (x : ℂ) t)
        (unitIntervalHerglotzWeightedPushforward data : Measure ℝ) :=
    unitIntervalPickKernel_integrable_of_finiteMeasure_support_Icc
      (unitIntervalHerglotzWeightedPushforward data)
      (unitIntervalHerglotzWeightedPushforward_support_Icc data) hz
  calc
    (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
        ∂(unitIntervalHerglotzIntervalMeasure data : Measure ℝ)) =
        ∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
          ∂((data.slope • unitIntervalHerglotzDiracZero : FiniteMeasure ℝ) +
              unitIntervalHerglotzWeightedPushforward data : FiniteMeasure ℝ) := by
          rfl
    _ = (∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
            ∂(data.slope • unitIntervalHerglotzDiracZero : FiniteMeasure ℝ)) +
          ∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
            ∂(unitIntervalHerglotzWeightedPushforward data : Measure ℝ) := by
          exact integral_add_measure hIntSlope hIntPush
    _ = ((data.slope : ℝ) : ℂ) * (x : ℂ) +
          ∫ y : ℝ,
            unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
              ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
            ∂(data.outsideMeasure : Measure ℝ) := by
          rw [unitIntervalHerglotzSlope_integral_kernel,
            unitIntervalHerglotzWeightedPushforward_integral_kernel]

/--
The book Theorem 3.8 reverse-direction core: once the outside Herglotz
representation has been supplied, the normalized interval integral
representation follows by the book change of variables.
-/
def integralRepOnUnitInterval_of_pickHerglotzOutsideData
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzOutsideData f) :
    IntegralRepOnUnitInterval f where
  ν := unitIntervalHerglotzIntervalMeasure data
  support := unitIntervalHerglotzIntervalMeasure_support_Icc data
  formula := by
    intro x hx
    have hInt := unitIntervalHerglotzIntervalMeasure_integral_kernel data hx
    calc
      (f x : ℂ) =
          (f 0 : ℂ) + ((data.slope : ℝ) : ℂ) * (x : ℂ) +
            ∫ y : ℝ,
              unitIntervalPickKernel (x : ℂ) (unitIntervalHerglotzOutsideMap y) *
                ((unitIntervalHerglotzWeight y : ℝ) : ℂ)
              ∂(data.outsideMeasure : Measure ℝ) :=
          data.rewritten_formula hx
      _ = (f 0 : ℂ) +
            ∫ t : ℝ, unitIntervalPickKernel (x : ℂ) t
              ∂(unitIntervalHerglotzIntervalMeasure data : Measure ℝ) := by
          rw [hInt]
          ring

/--
Producer interface for the Herglotz representation input in book Theorem 3.8.

The concrete proof of this producer is the book Theorem 3.4 together with
Corollary 3.6.  This interface keeps that substantial Herglotz theorem separate
from the already formalized post-Herglotz change of variables.
-/
structure UnitIntervalPickHerglotzOutsideProducer where
  produce :
    ∀ {f : ℝ → ℝ}, PickExtensionOnUnitInterval f →
      UnitIntervalPickHerglotzOutsideData f

/--
Given the Herglotz outside-data producer, the reverse direction of book
Theorem 3.8 reduces to the already formalized outside-data-to-interval core.
-/
def integralRepOnUnitInterval_of_pickExtension_of_herglotzOutsideProducer
    (producer : UnitIntervalPickHerglotzOutsideProducer)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickHerglotzOutsideData
    (producer.produce (f := f) pick)

end

end Quantum.TraceInequality.Loewner
