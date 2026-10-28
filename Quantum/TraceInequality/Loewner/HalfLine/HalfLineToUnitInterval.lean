import Quantum.TraceInequality.Loewner.HalfLine.UnitIntervalToHalfLine

/-!
# From half-line representations back to normalized interval representations

This module contains the reverse Cayley transport from Hiai--Matsumoto
half-line integral representations back to normalized interval integral
representations, and the reverse monotonicity wrapper.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

private theorem halfLineToUnitDensity_eq_two_mul_weight
    {t : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineToUnitDensity t = (2 : ENNReal) * halfLineWeight t := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hnonneg : 0 ≤ (1 + t)⁻¹ := by
    exact inv_nonneg.mpr (by linarith)
  calc
    halfLineToUnitDensity t = ENNReal.ofReal (2 * (1 + t)⁻¹) := rfl
    _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((1 + t)⁻¹) := by
          rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    _ = (2 : ENNReal) * halfLineWeight t := by
          norm_num [halfLineWeight]

private theorem halfLineToUnitDensity_lintegral_lt_top
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    (∫⁻ t : ℝ, halfLineToUnitDensity t ∂rep.μ) < ⊤ := by
  have hbound :
      ∀ᵐ t ∂rep.μ, halfLineToUnitDensity t ≤ (2 : ENNReal) * halfLineWeight t := by
    filter_upwards [rep.ae_mem_Ici] with t ht
    rw [halfLineToUnitDensity_eq_two_mul_weight ht]
  calc
    (∫⁻ t : ℝ, halfLineToUnitDensity t ∂rep.μ) ≤
        ∫⁻ t : ℝ, (2 : ENNReal) * halfLineWeight t ∂rep.μ :=
          lintegral_mono_ae hbound
    _ = (2 : ENNReal) * ∫⁻ t : ℝ, halfLineWeight t ∂rep.μ := by
          rw [lintegral_const_mul]
          exact measurable_halfLineWeight
    _ < ⊤ :=
          ENNReal.mul_lt_top (by norm_num : (2 : ENNReal) < ⊤)
            rep.weight_lintegral_lt_top

private theorem halfLineToUnit_withDensity_isFiniteMeasure
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    IsFiniteMeasure (rep.μ.withDensity halfLineToUnitDensity) where
  measure_univ_lt_top := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact halfLineToUnitDensity_lintegral_lt_top rep

/--
Push a half-line representation measure back to the normalized interval.  The
atom with mass `2 * b` at `-1` records the linear term, while the remaining
part is the pushforward of `(2 / (1+t)) dμ(t)` along `t ↦ (1-t)/(1+t)`.
-/
def unitIntervalMeasureOfHalfLine {h : ℝ → ℝ}
    (rep : HalfLineIntegralRep h) : FiniteMeasure ℝ :=
  let tail : Measure ℝ :=
    (rep.μ.withDensity halfLineToUnitDensity).map halfLineToUnitParam
  ⟨((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ) + tail, by
    haveI : IsFiniteMeasure (rep.μ.withDensity halfLineToUnitDensity) :=
      halfLineToUnit_withDensity_isFiniteMeasure rep
    infer_instance⟩

/-- The reverse Cayley-transported measure `unitIntervalMeasureOfHalfLine rep` is supported on
`[-1, 1]`. -/
theorem unitIntervalMeasureOfHalfLine_support_Icc
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    (unitIntervalMeasureOfHalfLine rep : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  let S : Set ℝ := (Set.Icc (-1 : ℝ) 1)ᶜ
  let tail : Measure ℝ :=
    (rep.μ.withDensity halfLineToUnitDensity).map halfLineToUnitParam
  have hS : MeasurableSet S := isClosed_Icc.measurableSet.compl
  have hatom : (((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ)) S = 0 := by
    have hmem : (-1 : ℝ) ∉ S := by
      simp [S]
    simp [S, hmem]
  have hpre0 : rep.μ (halfLineToUnitParam ⁻¹' S) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [rep.ae_mem_Ici] with t ht hpre
    exact hpre (halfLineToUnitParam_mem_Icc ht)
  have hac :
      rep.μ.withDensity halfLineToUnitDensity ≪ rep.μ :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have htail : tail S = 0 := by
    calc
      tail S =
          rep.μ.withDensity halfLineToUnitDensity (halfLineToUnitParam ⁻¹' S) := by
            rw [Measure.map_apply measurable_halfLineToUnitParam hS]
      _ = 0 := hac hpre0
  calc
    (unitIntervalMeasureOfHalfLine rep : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ =
        (((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ) + tail) S := by
          rfl
    _ = 0 := by
          rw [Measure.add_apply, hatom, htail, zero_add]

/-- Restricting the reverse-transported measure to `(-1, ∞)` drops the endpoint atom at `-1` and
recovers the pushforward of the tail measure along `t ↦ (1 - t)/(1 + t)`. -/
theorem unitIntervalMeasureOfHalfLine_restrict_Ioi
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    (unitIntervalMeasureOfHalfLine rep : Measure ℝ).restrict (Set.Ioi (-1 : ℝ)) =
      (rep.μ.withDensity halfLineToUnitDensity).map halfLineToUnitParam := by
  let tail : Measure ℝ :=
    (rep.μ.withDensity halfLineToUnitDensity).map halfLineToUnitParam
  let atom : Measure ℝ := ((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ)
  have htail_support : ∀ᵐ u ∂tail, u ∈ Set.Ioi (-1 : ℝ) := by
    have hac : rep.μ.withDensity halfLineToUnitDensity ≪ rep.μ :=
      MeasureTheory.withDensity_absolutelyContinuous _ _
    have hwd_mem : ∀ᵐ t ∂rep.μ.withDensity halfLineToUnitDensity,
        t ∈ Set.Ici (0 : ℝ) :=
      (mem_ae_iff).mpr (hac rep.support)
    have hpre : ∀ᵐ t ∂rep.μ.withDensity halfLineToUnitDensity,
        halfLineToUnitParam t ∈ Set.Ioi (-1 : ℝ) :=
      hwd_mem.mono
      (fun t ht => (halfLineToUnitParam_mem_Ioc ht).1)
    simpa [tail] using
      (ae_map_iff measurable_halfLineToUnitParam.aemeasurable measurableSet_Ioi).mpr hpre
  have htail_restrict : tail.restrict (Set.Ioi (-1 : ℝ)) = tail :=
    Measure.restrict_eq_self_of_ae_mem htail_support
  have hatom_restrict : atom.restrict (Set.Ioi (-1 : ℝ)) = 0 := by
    ext s hs
    rw [Measure.restrict_apply hs]
    have hmem : (-1 : ℝ) ∉ s ∩ Set.Ioi (-1 : ℝ) := by simp
    simp [atom, hmem]
  calc
    (unitIntervalMeasureOfHalfLine rep : Measure ℝ).restrict (Set.Ioi (-1 : ℝ)) =
        (atom + tail).restrict (Set.Ioi (-1 : ℝ)) := by rfl
    _ = atom.restrict (Set.Ioi (-1 : ℝ)) +
          tail.restrict (Set.Ioi (-1 : ℝ)) := by
          rw [Measure.restrict_add]
    _ = tail := by
          rw [hatom_restrict, htail_restrict, zero_add]

/-- Reverse kernel identity: the integral of the unit-interval operator kernel against the
reverse-transported measure equals the half-line slope term `b · (x - 1)` plus the integral of the
half-line kernel against `rep.μ`, where `x = unitToPositiveCayley y`. -/
theorem unitIntervalMeasureOfHalfLine_integral_kernel
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ u : ℝ, unitIntervalOperatorKernel u y
        ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ)) =
      (rep.b : ℝ) * (unitToPositiveCayley y - 1) +
        ∫ t : ℝ, halfLineKernel (unitToPositiveCayley y) t ∂rep.μ := by
  let x : ℝ := unitToPositiveCayley y
  let ν : FiniteMeasure ℝ := unitIntervalMeasureOfHalfLine rep
  let tail : Measure ℝ := (rep.μ.withDensity halfLineToUnitDensity).map halfLineToUnitParam
  let f : ℝ → ℝ := fun u => unitIntervalOperatorKernel u y
  have hx : x ∈ Set.Ioi (0 : ℝ) := by
    simpa [x] using unitToPositiveCayley_mem_Ioi hy
  have hpy : positiveToUnitCayley x = y := by
    simpa [x] using positiveToUnitCayley_unitToPositiveCayley hy
  have hsplit :
      (∫ u : ℝ, unitIntervalOperatorKernel u y ∂(ν : Measure ℝ)) =
        ((ν : Measure ℝ).real ({-1} : Set ℝ)) *
            unitIntervalOperatorKernel (-1) y +
          ∫ u : ℝ in Set.Ioi (-1 : ℝ),
            unitIntervalOperatorKernel u y ∂(ν : Measure ℝ) := by
    have h := unitIntervalOperatorKernel_integral_split_neg_one_Ioi
      ν (unitIntervalMeasureOfHalfLine_support_Icc rep) hx
    simpa [ν, x, hpy] using h
  have htail_single : tail ({-1} : Set ℝ) = 0 := by
    have hpre0 : rep.μ (halfLineToUnitParam ⁻¹' ({-1} : Set ℝ)) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [rep.ae_mem_Ici] with t ht hpre
      have hneq : halfLineToUnitParam t ≠ -1 := by
        have ht0 : 0 ≤ t := by simpa using ht
        have hden : 1 + t ≠ 0 := by linarith
        unfold halfLineToUnitParam
        intro heq
        field_simp [hden] at heq
        linarith
      exact hneq (Set.mem_singleton_iff.mp hpre)
    have hac : rep.μ.withDensity halfLineToUnitDensity ≪ rep.μ :=
      MeasureTheory.withDensity_absolutelyContinuous _ _
    calc
      tail ({-1} : Set ℝ) =
          rep.μ.withDensity halfLineToUnitDensity
            (halfLineToUnitParam ⁻¹' ({-1} : Set ℝ)) := by
            rw [Measure.map_apply measurable_halfLineToUnitParam
              (measurableSet_singleton (-1 : ℝ))]
      _ = 0 := hac hpre0
  have hν_single :
      (ν : Measure ℝ).real ({-1} : Set ℝ) =
        (((2 : NNReal) * rep.b : NNReal) : ℝ) := by
    have hmeasure :
        (ν : Measure ℝ) ({-1} : Set ℝ) =
          (((2 : NNReal) * rep.b : NNReal) : ENNReal) := by
      change ((((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ) + tail)
          ({-1} : Set ℝ)) = (((2 : NNReal) * rep.b : NNReal) : ENNReal)
      rw [Measure.add_apply]
      rw [htail_single, add_zero]
      simp only [Measure.smul_apply, MeasurableSet.singleton, Measure.dirac_apply',
        mem_singleton_iff, indicator_of_mem, Pi.one_apply, ENNReal.coe_mul, ENNReal.coe_ofNat]
      change (((2 : NNReal) * rep.b : NNReal) : ENNReal) * (1 : ENNReal) =
        2 * (rep.b : ENNReal)
      simp
    rw [measureReal_def, hmeasure]
    simp
  have hneg : unitIntervalOperatorKernel (-1) y = (x - 1) / 2 := by
    have h := unitIntervalOperatorKernel_cayley_neg_one (x := x) hx
    simpa [x, hpy] using h
  have hatom :
      ((ν : Measure ℝ).real ({-1} : Set ℝ)) * unitIntervalOperatorKernel (-1) y =
        (rep.b : ℝ) * (x - 1) := by
    rw [hν_single, hneg]
    norm_num [NNReal.coe_mul]
    ring_nf
  have hrestrict :
      (ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ)) = tail := by
    let atom : Measure ℝ := ((2 : NNReal) * rep.b) • Measure.dirac (-1 : ℝ)
    have htail_support : ∀ᵐ u ∂tail, u ∈ Set.Ioi (-1 : ℝ) := by
      have hac : rep.μ.withDensity halfLineToUnitDensity ≪ rep.μ :=
        MeasureTheory.withDensity_absolutelyContinuous _ _
      have hwd_mem : ∀ᵐ t ∂rep.μ.withDensity halfLineToUnitDensity,
          t ∈ Set.Ici (0 : ℝ) :=
        (mem_ae_iff).mpr (hac rep.support)
      have hpre : ∀ᵐ t ∂rep.μ.withDensity halfLineToUnitDensity,
          halfLineToUnitParam t ∈ Set.Ioi (-1 : ℝ) :=
        hwd_mem.mono
        (fun t ht => (halfLineToUnitParam_mem_Ioc ht).1)
      simpa [tail] using
        (ae_map_iff measurable_halfLineToUnitParam.aemeasurable measurableSet_Ioi).mpr hpre
    have htail_restrict : tail.restrict (Set.Ioi (-1 : ℝ)) = tail :=
      Measure.restrict_eq_self_of_ae_mem htail_support
    have hatom_restrict : atom.restrict (Set.Ioi (-1 : ℝ)) = 0 := by
      ext s hs
      rw [Measure.restrict_apply hs]
      have hmem : (-1 : ℝ) ∉ s ∩ Set.Ioi (-1 : ℝ) := by simp
      simp [atom, hmem]
    calc
      (ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ)) =
          (atom + tail).restrict (Set.Ioi (-1 : ℝ)) := by rfl
      _ = atom.restrict (Set.Ioi (-1 : ℝ)) +
            tail.restrict (Set.Ioi (-1 : ℝ)) := by
            rw [Measure.restrict_add]
      _ = tail := by
            rw [hatom_restrict, htail_restrict, zero_add]
  have htail_integral :
      (∫ u : ℝ, f u ∂tail) =
        ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
    have hmap :
        (∫ u : ℝ, f u ∂tail) =
          ∫ t : ℝ, f (halfLineToUnitParam t)
            ∂(rep.μ.withDensity halfLineToUnitDensity) := by
      have hφ : AEMeasurable halfLineToUnitParam
          (rep.μ.withDensity halfLineToUnitDensity) :=
        measurable_halfLineToUnitParam.aemeasurable
      have hf :
          AEStronglyMeasurable f
            (Measure.map halfLineToUnitParam
              (rep.μ.withDensity halfLineToUnitDensity)) :=
        (measurable_unitIntervalOperatorKernel_left y).aestronglyMeasurable
      have h :=
        MeasureTheory.integral_map (μ := rep.μ.withDensity halfLineToUnitDensity)
          (φ := halfLineToUnitParam) hφ (f := f) hf
      simpa [tail, f] using h
    have hwd :
        (∫ t : ℝ, f (halfLineToUnitParam t)
            ∂(rep.μ.withDensity halfLineToUnitDensity)) =
          ∫ t : ℝ,
            (halfLineToUnitDensity t).toReal • f (halfLineToUnitParam t) ∂rep.μ := by
      have htop :
          ∀ᵐ t ∂rep.μ, halfLineToUnitDensity t < (⊤ : ENNReal) := by
        exact ae_of_all _ (fun _ => by exact ENNReal.ofReal_lt_top)
      exact integral_withDensity_eq_integral_toReal_smul
        measurable_halfLineToUnitDensity htop
        (fun t : ℝ => f (halfLineToUnitParam t))
    have hkernel :
        (fun t : ℝ =>
            (halfLineToUnitDensity t).toReal • f (halfLineToUnitParam t))
          =ᵐ[rep.μ]
          fun t : ℝ => halfLineKernel x t := by
      filter_upwards [rep.ae_mem_Ici] with t ht
      have ht0 : 0 ≤ t := by simpa using ht
      have hden_pos : 0 < 1 + t := by linarith
      have htoReal :
          (halfLineToUnitDensity t).toReal = 2 * (1 + t)⁻¹ := by
        rw [halfLineToUnitDensity, ENNReal.toReal_ofReal]
        exact mul_nonneg (by norm_num) (inv_nonneg.mpr hden_pos.le)
      calc
        (halfLineToUnitDensity t).toReal • f (halfLineToUnitParam t) =
            (2 * (1 + t)⁻¹) * unitIntervalOperatorKernel (halfLineToUnitParam t) y := by
              simp [f, htoReal]
        _ = halfLineKernel x t := by
              have hker := halfLineKernel_cayley (y := y) (t := t) hy ht
              simpa [x, div_eq_mul_inv, mul_assoc] using hker.symm
    calc
      (∫ u : ℝ, f u ∂tail) =
          ∫ t : ℝ, f (halfLineToUnitParam t)
            ∂(rep.μ.withDensity halfLineToUnitDensity) := hmap
      _ = ∫ t : ℝ,
            (halfLineToUnitDensity t).toReal • f (halfLineToUnitParam t) ∂rep.μ := hwd
      _ = ∫ t : ℝ, halfLineKernel x t ∂rep.μ := integral_congr_ae hkernel
  have htail :
      (∫ u : ℝ in Set.Ioi (-1 : ℝ),
          unitIntervalOperatorKernel u y ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
    calc
      (∫ u : ℝ in Set.Ioi (-1 : ℝ),
          unitIntervalOperatorKernel u y ∂(ν : Measure ℝ)) =
          ∫ u : ℝ, f u ∂((ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ))) := by rfl
      _ = ∫ u : ℝ, f u ∂tail := by rw [hrestrict]
      _ = ∫ t : ℝ, halfLineKernel x t ∂rep.μ := htail_integral
  calc
    (∫ u : ℝ, unitIntervalOperatorKernel u y
        ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ)) =
        ∫ u : ℝ, unitIntervalOperatorKernel u y ∂(ν : Measure ℝ) := by rfl
    _ = ((ν : Measure ℝ).real ({-1} : Set ℝ)) *
            unitIntervalOperatorKernel (-1) y +
          ∫ u : ℝ in Set.Ioi (-1 : ℝ),
            unitIntervalOperatorKernel u y ∂(ν : Measure ℝ) := hsplit
    _ = (rep.b : ℝ) * (x - 1) +
          ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by rw [hatom, htail]
    _ = (rep.b : ℝ) * (unitToPositiveCayley y - 1) +
          ∫ t : ℝ, halfLineKernel (unitToPositiveCayley y) t ∂rep.μ := by rfl

/-- Build a normalized-interval integral representation of the positive-Cayley pullback of `h`
from a half-line integral representation of `h`, transporting the measure back through the Cayley
change of variables. [simon2019] -/
noncomputable def unitIntervalIntegralRep_of_halfLineIntegralRep_cayley
    {h : ℝ → ℝ}
    (rep : HalfLineIntegralRep h) :
    IntegralRepOnUnitInterval (positiveCayleyPullback h) where
  ν := unitIntervalMeasureOfHalfLine rep
  support := unitIntervalMeasureOfHalfLine_support_Icc rep
  formula := by
    intro y hy
    let x : ℝ := unitToPositiveCayley y
    have hx : x ∈ Set.Ioi (0 : ℝ) := by
      simpa [x] using unitToPositiveCayley_mem_Ioi hy
    have hpull_y : positiveCayleyPullback h y = h x := by
      rfl
    have hpull_zero : positiveCayleyPullback h 0 = h 1 := by
      simp [positiveCayleyPullback]
    have hhalf_diff :
        h x - h 1 =
          (rep.b : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
      calc
        h x - h 1 =
            (h 1 + (rep.b : ℝ) * (x - 1) +
                ∫ t : ℝ, halfLineKernel x t ∂rep.μ) - h 1 := by
              rw [rep.formula hx]
        _ = (rep.b : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by ring_nf
    have hintegral :
        (∫ u : ℝ, unitIntervalOperatorKernel u y
            ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ)) =
          h x - h 1 := by
      rw [unitIntervalMeasureOfHalfLine_integral_kernel rep hy, hhalf_diff]
    have hreal :
        positiveCayleyPullback h y - positiveCayleyPullback h 0 =
          ∫ u : ℝ, unitIntervalOperatorKernel u y
            ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) := by
      rw [hpull_y, hpull_zero, hintegral]
    have hkernel :
        (∫ lambda : ℝ, ((y : ℂ) / (1 + (lambda : ℂ) * y))
            ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ)) =
          ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda y
              ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) : ℝ) : ℂ) := by
      calc
        (∫ lambda : ℝ, ((y : ℂ) / (1 + (lambda : ℂ) * y))
            ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ)) =
            ∫ lambda : ℝ, ((unitIntervalOperatorKernel lambda y : ℝ) : ℂ)
              ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with lambda
          exact (unitIntervalOperatorKernel_complex_eq lambda y).symm
        _ = ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda y
                ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) : ℝ) : ℂ) := by
          exact integral_ofReal
    calc
      (positiveCayleyPullback h y : ℂ) =
          (positiveCayleyPullback h 0 : ℂ) +
            ((positiveCayleyPullback h y - positiveCayleyPullback h 0 : ℝ) : ℂ) := by
            simp
      _ = (positiveCayleyPullback h 0 : ℂ) +
            ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda y
                ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) : ℝ) : ℂ) := by
            rw [hreal]
      _ = (positiveCayleyPullback h 0 : ℂ) +
            ∫ lambda : ℝ, ((y : ℂ) / (1 + (lambda : ℂ) * y))
              ∂(unitIntervalMeasureOfHalfLine rep : Measure ℝ) := by
            rw [hkernel]

/-- A half-line integral representation of `h` implies that `h` is operator monotone on the
positive half-line. [simon2019] -/
theorem operatorMonotoneOnPositive_of_halfLineIntegralRep
    {h : ℝ → ℝ}
    (rep : HalfLineIntegralRep h) :
    OperatorMonotoneOnPositive.{u} h :=
  let unitRep := unitIntervalIntegralRep_of_halfLineIntegralRep_cayley rep
  ⟨operatorMonotoneOnUnitInterval_of_integralRep unitRep⟩

/--
gcongr form of half-line integral-representation monotonicity after Cayley pullback.
It delegates through `operatorMonotoneOnPositive_of_halfLineIntegralRep`.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_halfLineIntegralRep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) b :=
  (operatorMonotoneOnPositive_of_halfLineIntegralRep rep).to_unitInterval.cfc_monotone
    ⟨ha, hqa⟩ ⟨hb, hqb⟩ hab

/--
gcongr form of nonempty half-line representation monotonicity after Cayley pullback.
It unwraps the representation and uses the representation wrapper.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_nonempty_halfLineIntegralRep
    {h : ℝ → ℝ} (hrep : Nonempty (HalfLineIntegralRep h))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) b := by
  rcases hrep with ⟨rep⟩
  exact
    cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_halfLineIntegralRep
      rep hab ha hqa hb hqb

/--
Positive-half-line operator monotonicity is equivalent to the existence of a
half-line integral representation.
-/
theorem operatorMonotoneOnPositive_iff_nonempty_halfLineIntegralRep
    {h : ℝ → ℝ} :
    OperatorMonotoneOnPositive.{u} h ↔ Nonempty (HalfLineIntegralRep h) := by
  constructor
  · intro hh
    exact ⟨halfLineIntegralRep_of_operatorMonotoneOnPositive hh⟩
  · intro hrep
    rcases hrep with ⟨rep⟩
    exact operatorMonotoneOnPositive_of_halfLineIntegralRep rep

end

end Loewner
end TraceInequality
end Quantum
