import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
import Quantum.TraceInequality.Loewner.HalfLine.Basic

/-!
# From normalized interval representations to half-line representations

This module contains the Cayley measure transport from normalized interval
integral representations to the Hiai--Matsumoto half-line representation,
together with the positive-half-line existence wrapper.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-- The parameter change `u ↦ (1 - u)/(1 + u)` sends `(-1, 1]` into `[0, ∞)`. -/
theorem unitToHalfLineParam_mem_Ici {u : ℝ}
    (hu : u ∈ Set.Ioc (-1 : ℝ) 1) :
    unitToHalfLineParam u ∈ Set.Ici (0 : ℝ) := by
  have hnum : 0 ≤ 1 - u := by linarith [hu.2]
  have hden : 0 ≤ 1 + u := by linarith [hu.1]
  exact div_nonneg hnum hden

/-- The inverse parameter change `t ↦ (1 - t)/(1 + t)` sends `[0, ∞)` into `[-1, 1]`. -/
theorem halfLineToUnitParam_mem_Icc {t : ℝ}
    (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineToUnitParam t ∈ Set.Icc (-1 : ℝ) 1 := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hden : 0 < 1 + t := by linarith
  constructor
  · rw [halfLineToUnitParam, le_div_iff₀ hden]
    ring_nf
    linarith
  · rw [halfLineToUnitParam, div_le_iff₀ hden]
    ring_nf
    linarith

/-- The inverse parameter change sends `[0, ∞)` into `(-1, 1]`. -/
theorem halfLineToUnitParam_mem_Ioc {t : ℝ}
    (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineToUnitParam t ∈ Set.Ioc (-1 : ℝ) 1 := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hden : 0 < 1 + t := by linarith
  constructor
  · rw [halfLineToUnitParam, lt_div_iff₀ hden]
    ring_nf
    linarith
  · exact (halfLineToUnitParam_mem_Icc ht).2

/-- The unit-to-half-line and half-line-to-unit parameter changes are mutually inverse on
`[0, ∞)`. -/
theorem unitToHalfLineParam_halfLineToUnitParam_of_Ici {t : ℝ}
    (ht : t ∈ Set.Ici (0 : ℝ)) :
    unitToHalfLineParam (halfLineToUnitParam t) = t := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hden : 1 + t ≠ 0 := by linarith
  have hunitden : 1 + halfLineToUnitParam t ≠ 0 := by
    have hu : -1 < halfLineToUnitParam t :=
      (halfLineToUnitParam_mem_Ioc ht).1
    linarith
  unfold unitToHalfLineParam halfLineToUnitParam
  field_simp [hden, hunitden]
  ring_nf

/-- The half-line-to-unit and unit-to-half-line parameter changes are mutually inverse on
`(-1, 1]`. -/
theorem halfLineToUnitParam_unitToHalfLineParam_of_Ioc {u : ℝ}
    (hu : u ∈ Set.Ioc (-1 : ℝ) 1) :
    halfLineToUnitParam (unitToHalfLineParam u) = u := by
  have huden : 1 + u ≠ 0 := by linarith [hu.1]
  have hhalfden : 1 + unitToHalfLineParam u ≠ 0 := by
    have ht : 0 ≤ unitToHalfLineParam u := by
      simpa using unitToHalfLineParam_mem_Ici hu
    linarith
  unfold halfLineToUnitParam unitToHalfLineParam
  field_simp [huden, hhalfden]
  ring_nf

/-- The Cayley-transported measure `halfLineMeasureOfUnitInterval ν` is supported on `[0, ∞)`
whenever `ν` is supported on `[-1, 1]`. -/
theorem halfLineMeasureOfUnitInterval_support_Ici
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
    halfLineMeasureOfUnitInterval ν (Set.Ici (0 : ℝ))ᶜ = 0 := by
  let μ0 : Measure ℝ := (ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ))
  have hS : MeasurableSet ((Set.Ici (0 : ℝ))ᶜ) :=
    isClosed_Ici.measurableSet.compl
  have hpre0 :
      μ0 (unitToHalfLineParam ⁻¹' (Set.Ici (0 : ℝ))ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    have hae_ioi :
        ∀ᵐ u ∂μ0, u ∈ Set.Ioi (-1 : ℝ) := by
      exact ae_restrict_mem measurableSet_Ioi
    have hae_icc :
        ∀ᵐ u ∂μ0, u ∈ Set.Icc (-1 : ℝ) 1 := by
      exact ae_restrict_of_ae ((mem_ae_iff).mpr hν)
    filter_upwards [hae_ioi, hae_icc] with u hu_gt hu_icc hpre
    exact hpre (unitToHalfLineParam_mem_Ici ⟨hu_gt, hu_icc.2⟩)
  have hac :
      μ0.withDensity unitToHalfLineDensity ≪ μ0 :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hwd0 :
      μ0.withDensity unitToHalfLineDensity
          (unitToHalfLineParam ⁻¹' (Set.Ici (0 : ℝ))ᶜ) = 0 :=
    hac hpre0
  calc
    halfLineMeasureOfUnitInterval ν (Set.Ici (0 : ℝ))ᶜ =
        μ0.withDensity unitToHalfLineDensity
          (unitToHalfLineParam ⁻¹' (Set.Ici (0 : ℝ))ᶜ) := by
          rw [halfLineMeasureOfUnitInterval, Measure.map_apply measurable_unitToHalfLineParam hS]
    _ = 0 := hwd0

private theorem unitToHalfLine_density_mul_weight_le_one
    {u : ℝ} (hu : u ∈ Set.Ioc (-1 : ℝ) 1) :
    unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) ≤ 1 := by
  have hden_pos : 0 < 1 + u := by linarith [hu.1]
  have hden_ne : 1 + u ≠ 0 := hden_pos.ne'
  have htau_nonneg : 0 ≤ unitToHalfLineParam u :=
    unitToHalfLineParam_mem_Ici hu
  have hweight_nonneg : 0 ≤ (1 + unitToHalfLineParam u)⁻¹ := by
    exact inv_nonneg.mpr (by linarith)
  have hdensity_nonneg : 0 ≤ (1 + u)⁻¹ := by
    exact inv_nonneg.mpr hden_pos.le
  have hreal :
      (1 + u)⁻¹ * (1 + unitToHalfLineParam u)⁻¹ = (2 : ℝ)⁻¹ := by
    unfold unitToHalfLineParam
    field_simp [hden_ne]
    ring_nf
  calc
    unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) =
        ENNReal.ofReal ((1 + u)⁻¹) *
          ENNReal.ofReal ((1 + unitToHalfLineParam u)⁻¹) := by
          rfl
    _ = ENNReal.ofReal ((1 + u)⁻¹ * (1 + unitToHalfLineParam u)⁻¹) := by
          rw [ENNReal.ofReal_mul hdensity_nonneg]
    _ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by rw [hreal]
    _ ≤ 1 := by norm_num

/-- The half-line weight is integrable against the Cayley-transported measure: its total mass is
finite. -/
theorem halfLineMeasureOfUnitInterval_weight_lintegral_lt_top
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
    (∫⁻ t : ℝ, halfLineWeight t ∂halfLineMeasureOfUnitInterval ν) < ⊤ := by
  let μ0 : Measure ℝ := (ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ))
  have hrewrite :
      (∫⁻ t : ℝ, halfLineWeight t ∂halfLineMeasureOfUnitInterval ν) =
        ∫⁻ u : ℝ,
          unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) ∂μ0 := by
    calc
      (∫⁻ t : ℝ, halfLineWeight t ∂halfLineMeasureOfUnitInterval ν) =
          ∫⁻ u : ℝ, halfLineWeight (unitToHalfLineParam u)
            ∂(μ0.withDensity unitToHalfLineDensity) := by
            rw [halfLineMeasureOfUnitInterval]
            exact MeasureTheory.lintegral_map measurable_halfLineWeight
              measurable_unitToHalfLineParam
      _ = ∫⁻ u : ℝ,
            (unitToHalfLineDensity * fun u => halfLineWeight (unitToHalfLineParam u)) u
            ∂μ0 := by
            have h :=
              MeasureTheory.lintegral_withDensity_eq_lintegral_mul μ0
                measurable_unitToHalfLineDensity
                (measurable_halfLineWeight.comp measurable_unitToHalfLineParam)
            simpa [Function.comp_def] using h
      _ = ∫⁻ u : ℝ,
            unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) ∂μ0 := rfl
  have hae_ioi :
      ∀ᵐ u ∂μ0, u ∈ Set.Ioi (-1 : ℝ) := by
    exact ae_restrict_mem measurableSet_Ioi
  have hae_icc :
      ∀ᵐ u ∂μ0, u ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ae_restrict_of_ae ((mem_ae_iff).mpr hν)
  have hbound :
      ∀ᵐ u ∂μ0,
        unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) ≤ 1 := by
    filter_upwards [hae_ioi, hae_icc] with u hu_gt hu_icc
    exact unitToHalfLine_density_mul_weight_le_one ⟨hu_gt, hu_icc.2⟩
  rw [hrewrite]
  calc
    (∫⁻ u : ℝ,
        unitToHalfLineDensity u * halfLineWeight (unitToHalfLineParam u) ∂μ0) ≤
        ∫⁻ _u : ℝ, (1 : ENNReal) ∂μ0 :=
          lintegral_mono_ae hbound
    _ = μ0 Set.univ := by simp
    _ < ⊤ := measure_lt_top μ0 Set.univ

/-- Cayley identity: for `u ∈ (-1, 1]`, the unit-interval operator kernel at the Cayley image of
`x` equals `(1 + u)⁻¹` times the half-line kernel at the transported parameter. -/
theorem unitIntervalOperatorKernel_cayley_of_Ioc
    {x u : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (hu : u ∈ Set.Ioc (-1 : ℝ) 1) :
    unitIntervalOperatorKernel u (positiveToUnitCayley x) =
      (1 + u)⁻¹ * halfLineKernel x (unitToHalfLineParam u) := by
  have hx0 : 0 < x := by simpa using hx
  have hxden : x + 1 ≠ 0 := by linarith
  have huden_pos : 0 < 1 + u := by linarith [hu.1]
  have huden : 1 + u ≠ 0 := by positivity
  have hkerden :
      1 + u * positiveToUnitCayley x ≠ 0 := by
    have hucc : u ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hu.1, hu.2⟩
    exact (unitIntervalOperatorKernel_denominator_pos hucc
      (positiveToUnitCayley_mem_Ioo hx)).ne'
  have htau_nonneg : 0 ≤ unitToHalfLineParam u :=
    unitToHalfLineParam_mem_Ici hu
  have hxtau : x + unitToHalfLineParam u ≠ 0 := by
    have hpos : 0 < x + unitToHalfLineParam u := by linarith
    exact hpos.ne'
  have hkerden' : 1 + u * ((x - 1) / (x + 1)) ≠ 0 := by
    simpa [positiveToUnitCayley] using hkerden
  have hxtau' : x + ((1 - u) / (1 + u)) ≠ 0 := by
    simpa [unitToHalfLineParam] using hxtau
  unfold unitIntervalOperatorKernel positiveToUnitCayley halfLineKernel unitToHalfLineParam
  field_simp [hxden, huden, hkerden', hxtau']
  ring_nf

private theorem measurable_halfLineKernel_right (x : ℝ) :
    Measurable fun t : ℝ => halfLineKernel x t := by
  unfold halfLineKernel
  measurability

/-- The integral of the half-line kernel against the Cayley-transported measure equals the
integral of the unit-interval operator kernel over `(-1, ∞)` against `ν`. -/
theorem halfLineMeasureOfUnitInterval_integral_kernel
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval ν) =
      ∫ u : ℝ in Set.Ioi (-1 : ℝ),
        unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ) := by
  let μ0 : Measure ℝ := (ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ))
  have hmap :
      (∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval ν) =
        ∫ u : ℝ, halfLineKernel x (unitToHalfLineParam u)
          ∂(μ0.withDensity unitToHalfLineDensity) := by
    have hφ : AEMeasurable unitToHalfLineParam
        (μ0.withDensity unitToHalfLineDensity) :=
      measurable_unitToHalfLineParam.aemeasurable
    have hf :
        AEStronglyMeasurable (fun t : ℝ => halfLineKernel x t)
          (Measure.map unitToHalfLineParam
            (μ0.withDensity unitToHalfLineDensity)) :=
      (measurable_halfLineKernel_right x).aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := μ0.withDensity unitToHalfLineDensity)
        (φ := unitToHalfLineParam) hφ
        (f := fun t : ℝ => halfLineKernel x t) hf
    simpa [halfLineMeasureOfUnitInterval, μ0] using h
  have hwd :
      (∫ u : ℝ, halfLineKernel x (unitToHalfLineParam u)
          ∂(μ0.withDensity unitToHalfLineDensity)) =
        ∫ u : ℝ,
          (unitToHalfLineDensity u).toReal • halfLineKernel x (unitToHalfLineParam u)
          ∂μ0 := by
    have htop :
        ∀ᵐ u ∂μ0, unitToHalfLineDensity u < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun _ => by simp [unitToHalfLineDensity])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_unitToHalfLineDensity htop
      (fun u : ℝ => halfLineKernel x (unitToHalfLineParam u))
  have hae_ioi :
      ∀ᵐ u ∂μ0, u ∈ Set.Ioi (-1 : ℝ) := by
    exact ae_restrict_mem measurableSet_Ioi
  have hae_icc :
      ∀ᵐ u ∂μ0, u ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ae_restrict_of_ae ((mem_ae_iff).mpr hν)
  have hkernel :
      (fun u : ℝ =>
          (unitToHalfLineDensity u).toReal • halfLineKernel x (unitToHalfLineParam u))
        =ᵐ[μ0]
        fun u : ℝ => unitIntervalOperatorKernel u (positiveToUnitCayley x) := by
    filter_upwards [hae_ioi, hae_icc] with u hu_gt hu_icc
    have hu : u ∈ Set.Ioc (-1 : ℝ) 1 := ⟨hu_gt, hu_icc.2⟩
    have hden_pos : 0 < 1 + u := by linarith [hu.1]
    have htoReal :
        (unitToHalfLineDensity u).toReal = (1 + u)⁻¹ := by
      rw [unitToHalfLineDensity, ENNReal.toReal_ofReal]
      exact inv_nonneg.mpr hden_pos.le
    calc
      (unitToHalfLineDensity u).toReal • halfLineKernel x (unitToHalfLineParam u) =
          (1 + u)⁻¹ * halfLineKernel x (unitToHalfLineParam u) := by
          simp [htoReal]
      _ = unitIntervalOperatorKernel u (positiveToUnitCayley x) :=
          (unitIntervalOperatorKernel_cayley_of_Ioc hx hu).symm
  calc
    (∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval ν) =
        ∫ u : ℝ, halfLineKernel x (unitToHalfLineParam u)
          ∂(μ0.withDensity unitToHalfLineDensity) := hmap
    _ =
        ∫ u : ℝ,
          (unitToHalfLineDensity u).toReal • halfLineKernel x (unitToHalfLineParam u)
          ∂μ0 := hwd
    _ = ∫ u : ℝ, unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂μ0 :=
        integral_congr_ae hkernel
    _ = ∫ u : ℝ in Set.Ioi (-1 : ℝ),
        unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ) := rfl

private theorem unitIntervalOperatorKernel_left_continuousOn_Icc
    {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun u : ℝ => unitIntervalOperatorKernel u y)
      (Set.Icc (-1 : ℝ) 1) := by
  intro u hu
  have hden :
      1 + u * y ≠ 0 :=
    (unitIntervalOperatorKernel_denominator_pos hu hy).ne'
  change ContinuousWithinAt
    (fun u : ℝ => y / (1 + u * y))
    (Set.Icc (-1 : ℝ) 1) u
  exact continuousAt_const.div
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const)) hden
    |>.continuousWithinAt

/-- Split the unit-interval kernel integral over `[-1, 1]` into the atomic contribution at the
endpoint `-1` and the tail integral over `(-1, ∞)`. -/
theorem unitIntervalOperatorKernel_integral_split_neg_one_Ioi
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ u : ℝ, unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ)) =
      ((ν : Measure ℝ).real ({-1} : Set ℝ)) *
          unitIntervalOperatorKernel (-1) (positiveToUnitCayley x) +
        ∫ u : ℝ in Set.Ioi (-1 : ℝ),
          unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ) := by
  let μ : Measure ℝ := (ν : Measure ℝ)
  let y : ℝ := positiveToUnitCayley x
  let f : ℝ → ℝ := fun u => unitIntervalOperatorKernel u y
  have hy : y ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa [y] using positiveToUnitCayley_mem_Ioo hx
  have hfIcc : IntegrableOn f (Set.Icc (-1 : ℝ) 1) μ := by
    exact (unitIntervalOperatorKernel_left_continuousOn_Icc hy).integrableOn_compact
      isCompact_Icc
  have hsupport : ∀ᵐ u ∂μ, u ∈ Set.Icc (-1 : ℝ) 1 := by
    exact (mem_ae_iff).mpr hν
  have htotal :
      (∫ u : ℝ, f u ∂μ) =
        ∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u ∂μ := by
    have hzero :
        ∀ᵐ u ∂μ, u ∉ Set.Icc (-1 : ℝ) 1 → f u = 0 := by
      filter_upwards [hsupport] with u hu hnot
      exact False.elim (hnot hu)
    exact (setIntegral_eq_integral_of_ae_compl_eq_zero hzero).symm
  have hsingle_subset :
      ({-1} : Set ℝ) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro u hu
    simp at hu
    subst u
    norm_num
  have hIoc_subset :
      Set.Ioc (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro u hu
    exact ⟨le_of_lt hu.1, hu.2⟩
  have hdisj : Disjoint ({-1} : Set ℝ) (Set.Ioc (-1 : ℝ) 1) := by
    rw [Set.disjoint_left]
    intro u hu_single hu_ioc
    rw [Set.mem_singleton_iff] at hu_single
    subst u
    exact (lt_irrefl (-1 : ℝ)) hu_ioc.1
  have hunion :
      ({-1} : Set ℝ) ∪ Set.Ioc (-1 : ℝ) 1 =
        Set.Icc (-1 : ℝ) 1 := by
    ext u
    constructor
    · intro hu
      rcases hu with hu | hu
      · simp at hu
        subst u
        norm_num
      · exact ⟨le_of_lt hu.1, hu.2⟩
    · intro hu
      by_cases hu_eq : u = -1
      · left
        simp [hu_eq]
      · right
        exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hu_eq), hu.2⟩
  have hsplit :
      (∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u ∂μ) =
        ∫ u : ℝ in ({-1} : Set ℝ), f u ∂μ +
          ∫ u : ℝ in Set.Ioc (-1 : ℝ) 1, f u ∂μ := by
    calc
      (∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u ∂μ) =
          ∫ u : ℝ in ({-1} : Set ℝ) ∪ Set.Ioc (-1 : ℝ) 1, f u ∂μ := by
            rw [hunion]
      _ = ∫ u : ℝ in ({-1} : Set ℝ), f u ∂μ +
            ∫ u : ℝ in Set.Ioc (-1 : ℝ) 1, f u ∂μ := by
            exact setIntegral_union hdisj measurableSet_Ioc
              (hfIcc.mono_set hsingle_subset) (hfIcc.mono_set hIoc_subset)
  have hsingle :
      (∫ u : ℝ in ({-1} : Set ℝ), f u ∂μ) =
        μ.real ({-1} : Set ℝ) * f (-1) := by
    simpa [smul_eq_mul] using (integral_singleton (μ := μ) f (-1))
  have hIoc_Ioi :
      Set.Ioc (-1 : ℝ) 1 =ᵐ[μ] Set.Ioi (-1 : ℝ) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hsupport] with u hu
    constructor
    · intro hu_ioc
      exact hu_ioc.1
    · intro hu_gt
      exact ⟨hu_gt, hu.2⟩
  have hIoc :
      (∫ u : ℝ in Set.Ioc (-1 : ℝ) 1, f u ∂μ) =
        ∫ u : ℝ in Set.Ioi (-1 : ℝ), f u ∂μ :=
    setIntegral_congr_set hIoc_Ioi
  calc
    (∫ u : ℝ, unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ)) =
        ∫ u : ℝ, f u ∂μ := by rfl
    _ = ∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u ∂μ := htotal
    _ = ∫ u : ℝ in ({-1} : Set ℝ), f u ∂μ +
          ∫ u : ℝ in Set.Ioc (-1 : ℝ) 1, f u ∂μ := hsplit
    _ = μ.real ({-1} : Set ℝ) * f (-1) +
          ∫ u : ℝ in Set.Ioi (-1 : ℝ), f u ∂μ := by
          rw [hsingle, hIoc]
    _ = ((ν : Measure ℝ).real ({-1} : Set ℝ)) *
          unitIntervalOperatorKernel (-1) (positiveToUnitCayley x) +
        ∫ u : ℝ in Set.Ioi (-1 : ℝ),
          unitIntervalOperatorKernel u (positiveToUnitCayley x) ∂(ν : Measure ℝ) := by
          rfl

/-- At the endpoint `u = -1` and the Cayley image of `x`, the unit-interval operator kernel equals
`(x - 1)/2`; this endpoint atom becomes the half-line slope term. -/
theorem unitIntervalOperatorKernel_cayley_neg_one
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    unitIntervalOperatorKernel (-1) (positiveToUnitCayley x) =
      (x - 1) / 2 := by
  have hx0 : 0 < x := by simpa using hx
  have hxden : x + 1 ≠ 0 := by linarith
  have hkerden :
      1 + (-1 : ℝ) * positiveToUnitCayley x ≠ 0 := by
    have hpos :
        0 < 1 + (-1 : ℝ) * positiveToUnitCayley x :=
      unitIntervalOperatorKernel_denominator_pos
        (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
        (positiveToUnitCayley_mem_Ioo hx)
    exact hpos.ne'
  have hkerden' : 1 + (-1 : ℝ) * ((x - 1) / (x + 1)) ≠ 0 := by
    simpa [positiveToUnitCayley] using hkerden
  unfold unitIntervalOperatorKernel positiveToUnitCayley
  field_simp [hxden, hkerden']
  ring_nf

/-- Cayley identity for the half-line kernel: `halfLineKernel (unitToPositiveCayley y) t` equals
`2/(1 + t)` times the unit-interval operator kernel at the transported parameter. -/
theorem halfLineKernel_cayley
    {y t : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineKernel (unitToPositiveCayley y) t =
      (2 / (1 + t)) * unitIntervalOperatorKernel (halfLineToUnitParam t) y := by
  have hyden : 1 - y ≠ 0 := by linarith [hy.2]
  have ht0 : 0 ≤ t := by simpa using ht
  have htden_pos : 0 < 1 + t := by linarith
  have htden : 1 + t ≠ 0 := by positivity
  have hunitden :
      1 + halfLineToUnitParam t * y ≠ 0 := by
    exact (unitIntervalOperatorKernel_denominator_pos
      (halfLineToUnitParam_mem_Icc ht) hy).ne'
  have hxpos : 0 < unitToPositiveCayley y :=
    unitToPositiveCayley_mem_Ioi hy
  have hxt : unitToPositiveCayley y + t ≠ 0 := by
    have hpos : 0 < unitToPositiveCayley y + t := by linarith
    exact hpos.ne'
  have hunitden' : 1 + ((1 - t) / (1 + t)) * y ≠ 0 := by
    simpa [halfLineToUnitParam] using hunitden
  have hxt' : (1 + y) / (1 - y) + t ≠ 0 := by
    simpa [unitToPositiveCayley] using hxt
  unfold halfLineKernel unitToPositiveCayley unitIntervalOperatorKernel halfLineToUnitParam
  field_simp [hyden, htden, hunitden', hxt']
  ring_nf

/-- The unit-interval operator kernel is measurable in its left variable. -/
theorem measurable_unitIntervalOperatorKernel_left (y : ℝ) :
    Measurable fun u : ℝ => unitIntervalOperatorKernel u y := by
  unfold unitIntervalOperatorKernel
  measurability

/-- Build a half-line integral representation of `h` from a normalized-interval integral
representation of its positive-Cayley pullback: the endpoint atom at `-1` becomes the half-line
slope term and the interior measure transports through the Cayley change of variables.
[simon2019] -/
def halfLineIntegralRep_of_integralRepOnUnitInterval_cayley
    {h : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval (positiveCayleyPullback h)) :
    HalfLineIntegralRep h where
  b := halfLineSlopeOfUnitInterval rep.ν
  μ := halfLineMeasureOfUnitInterval rep.ν
  support := halfLineMeasureOfUnitInterval_support_Ici rep.ν rep.support
  weight_lintegral_lt_top :=
    halfLineMeasureOfUnitInterval_weight_lintegral_lt_top rep.ν rep.support
  formula := by
    intro x hx
    let y : ℝ := positiveToUnitCayley x
    have hy : y ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa [y] using positiveToUnitCayley_mem_Ioo hx
    have hpull_x :
        positiveCayleyPullback h y = h x := by
      simp [positiveCayleyPullback, y, unitToPositiveCayley_positiveToUnitCayley hx]
    have hpull_zero :
        positiveCayleyPullback h 0 = h 1 := by
      simp [positiveCayleyPullback]
    have hrep :
        positiveCayleyPullback h y - positiveCayleyPullback h 0 =
          ∫ u : ℝ, unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ) :=
      rep.real_formula hy
    have hsplit :
        (∫ u : ℝ, unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ)) =
          ((rep.ν : Measure ℝ).real ({-1} : Set ℝ)) *
              unitIntervalOperatorKernel (-1) y +
            ∫ u : ℝ in Set.Ioi (-1 : ℝ),
              unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ) := by
      simpa [y] using
        unitIntervalOperatorKernel_integral_split_neg_one_Ioi rep.ν rep.support hx
    have htail :
        (∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval rep.ν) =
          ∫ u : ℝ in Set.Ioi (-1 : ℝ),
            unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ) := by
      simpa [y] using halfLineMeasureOfUnitInterval_integral_kernel rep.ν rep.support hx
    have hatom :
        ((rep.ν : Measure ℝ).real ({-1} : Set ℝ)) *
            unitIntervalOperatorKernel (-1) y =
          ((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) := by
      have hneg :
          unitIntervalOperatorKernel (-1) y = (x - 1) / 2 := by
        simpa [y] using unitIntervalOperatorKernel_cayley_neg_one hx
      calc
        ((rep.ν : Measure ℝ).real ({-1} : Set ℝ)) *
            unitIntervalOperatorKernel (-1) y =
            ((rep.ν : Measure ℝ).real ({-1} : Set ℝ)) * ((x - 1) / 2) := by
              rw [hneg]
        _ = ((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) := by
              simp [halfLineSlopeOfUnitInterval, measureReal_def]
              ring_nf
    have hdiff :
        h x - h 1 =
          ((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval rep.ν := by
      calc
        h x - h 1 =
            positiveCayleyPullback h y - positiveCayleyPullback h 0 := by
              rw [hpull_x, hpull_zero]
        _ = ∫ u : ℝ, unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ) := hrep
        _ =
            ((rep.ν : Measure ℝ).real ({-1} : Set ℝ)) *
                unitIntervalOperatorKernel (-1) y +
              ∫ u : ℝ in Set.Ioi (-1 : ℝ),
                unitIntervalOperatorKernel u y ∂(rep.ν : Measure ℝ) := hsplit
        _ =
            ((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) +
              ∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval rep.ν := by
              rw [hatom, ← htail]
    calc
      h x = h 1 + (h x - h 1) := by ring_nf
      _ = h 1 +
          (((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval rep.ν) := by
            rw [hdiff]
      _ =
          h 1 + ((halfLineSlopeOfUnitInterval rep.ν : NNReal) : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂halfLineMeasureOfUnitInterval rep.ν := by
            ring_nf
/--
Positive-half-line operator monotonicity supplies a half-line integral
representation via the normalized interval Loewner theorem and the Cayley
producer.
-/
def halfLineIntegralRep_of_operatorMonotoneOnPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    HalfLineIntegralRep h :=
  halfLineIntegralRep_of_integralRepOnUnitInterval_cayley
    (integralRepOnUnitInterval_of_loewnerPosOnUnitInterval
      (loewnerPosOnUnitInterval_of_operatorMonotone
        (operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval)))

/--
Existence form of the half-line integral representation: positive-half-line
operator monotonicity implies a half-line integral representation exists.
-/
theorem halfLineIntegralRep_nonempty_of_operatorMonotoneOnPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    Nonempty (HalfLineIntegralRep h) :=
  ⟨halfLineIntegralRep_of_operatorMonotoneOnPositive hh⟩

end

end Loewner
end TraceInequality
end Quantum
