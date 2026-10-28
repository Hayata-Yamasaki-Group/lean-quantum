import Quantum.TraceInequality.Loewner.UnitInterval.Pick.RadialFamily
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
# Chapter 3 concrete radial boundary measures

This module constructs the concrete radial boundary measures used in book
Theorem 3.1 and packages the resulting radial-family producer.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Concrete radial boundary measures for Theorem 3.1 -/

/-- The standard angle parametrization of the unit circle, as a boundary subtype point. -/
def unitDiskBoundaryParam (θ : ℝ) : UnitDiskBoundary :=
  ⟨circleMap (0 : ℂ) 1 θ, by
    simp [unitDiskBoundary]⟩

/-- Lebesgue measure restricted to one full turn of angles. -/
noncomputable def unitDiskAngleMeasure : FiniteMeasure ℝ where
  val := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))
  property := by infer_instance

/-- The angle measure has total mass `2π`. -/
theorem unitDiskAngleMeasure_mass :
    unitDiskAngleMeasure.mass = Real.toNNReal (2 * Real.pi) := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change
    (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) Set.univ =
      ↑(Real.toNNReal (2 * Real.pi))
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  simp [ENNReal.ofReal, sub_zero]

/--
The normalized boundary arc measure on the unit circle subtype.

It is the probability normalization of the pushforward of Lebesgue measure on
`[0, 2π]` by the standard circle parametrization.
-/
noncomputable def unitDiskBoundaryArcMeasure : FiniteMeasure UnitDiskBoundary :=
  ((Real.toNNReal (2 * Real.pi))⁻¹ : ℝ≥0) •
    (unitDiskAngleMeasure.map unitDiskBoundaryParam)

/-- The normalized boundary arc measure has total mass one. -/
theorem unitDiskBoundaryArcMeasure_mass :
    unitDiskBoundaryArcMeasure.mass = 1 := by
  unfold unitDiskBoundaryArcMeasure
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass, FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change
    (((Real.toNNReal (2 * Real.pi))⁻¹ : ℝ≥0) : ℝ≥0∞) *
        ((unitDiskAngleMeasure.map unitDiskBoundaryParam : Measure UnitDiskBoundary) Set.univ) =
      ↑(1 : ℝ≥0)
  rw [← FiniteMeasure.ennreal_mass]
  have hmap :
      (unitDiskAngleMeasure.map unitDiskBoundaryParam).mass =
        unitDiskAngleMeasure.mass := by
    unfold FiniteMeasure.mass
    rw [FiniteMeasure.map_apply unitDiskAngleMeasure
      (by unfold unitDiskBoundaryParam; fun_prop) MeasurableSet.univ]
    simp
  rw [hmap, unitDiskAngleMeasure_mass]
  have hnn : Real.toNNReal (2 * Real.pi) ≠ 0 := by
    exact ne_of_gt (by positivity)
  rw [ENNReal.coe_inv]
  · rw [ENNReal.inv_mul_cancel]
    · simp
    · exact_mod_cast hnn
    · exact ENNReal.coe_ne_top
  · exact hnn

/-- The normalized boundary arc measure is the scaled angle-measure pushforward. -/
theorem unitDiskBoundaryArcMeasure_eq_scaled_anglePushforward :
    (unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary) =
      ((Real.toNNReal (2 * Real.pi))⁻¹ : ℝ≥0) •
        (unitDiskAngleMeasure.map unitDiskBoundaryParam : Measure UnitDiskBoundary) := by
  unfold unitDiskBoundaryArcMeasure
  rw [FiniteMeasure.toMeasure_smul]

/-- Boundary integration against normalized arc measure equals the circle average. -/
theorem unitDiskBoundaryArcMeasure_integral_eq_circleAverage
    (F : ℂ → ℂ) (hF : ContinuousOn F unitDiskBoundary) :
    ∫ ξ : UnitDiskBoundary, F (ξ : ℂ)
        ∂(unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary) =
      Real.circleAverage F 0 1 := by
  rw [unitDiskBoundaryArcMeasure_eq_scaled_anglePushforward]
  change
    ∫ ξ : UnitDiskBoundary, F (ξ : ℂ)
        ∂((((Real.toNNReal (2 * Real.pi))⁻¹ : ℝ≥0) : ℝ≥0∞) •
          (unitDiskAngleMeasure.map unitDiskBoundaryParam : Measure UnitDiskBoundary)) =
      Real.circleAverage F 0 1
  rw [integral_smul_measure]
  rw [FiniteMeasure.toMeasure_map]
  rw [integral_map]
  · unfold unitDiskAngleMeasure unitDiskBoundaryParam Real.circleAverage
    simp only [FiniteMeasure.toMeasure_mk]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le]
    · have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      congr 1
      simp [ENNReal.toReal, Real.toNNReal_of_nonneg hpos.le]
    · positivity
  · unfold unitDiskBoundaryParam
    fun_prop
  · exact (continuousOn_iff_continuous_restrict.mp hF).aestronglyMeasurable

/-- The origin belongs to the unit disk. -/
theorem zero_mem_unitDiskDomain :
    (0 : ℂ) ∈ (unitDiskDomain : Set ℂ) := by
  simp [unitDiskDomain]

/-- Radial boundary evaluation stays inside the unit disk. -/
theorem unitDiskRadialBoundary_eval_mem_unitDisk
    (n : ℕ) (ξ : UnitDiskBoundary) :
    (unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ) ∈
      (unitDiskDomain : Set ℂ) := by
  have hξ : ‖(ξ : ℂ)‖ = 1 := unitDiskBoundary_norm_eq_one ξ
  have hrpos : 0 < unitDiskHerglotzRadius n :=
    unitDiskHerglotzRadius_pos n
  have hrlt : unitDiskHerglotzRadius n < 1 :=
    unitDiskHerglotzRadius_lt_one n
  simpa [unitDiskDomain, dist_eq_norm, norm_mul, hξ,
    abs_of_pos hrpos] using hrlt

/-- The radial real-part density appearing in book Theorem 3.1. -/
def unitDiskTheorem31RadialDensity
    (G : ℂ → ℂ) (n : ℕ) (ξ : UnitDiskBoundary) : ENNReal :=
  ENNReal.ofReal
    (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re

/-- The radial real part is continuous on the compact boundary circle. -/
theorem unitDiskTheorem31RadialRealPart_continuous
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    Continuous fun ξ : UnitDiskBoundary =>
      (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re := by
  have heval :
      Continuous fun ξ : UnitDiskBoundary =>
        (unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ) :=
    continuous_const.mul continuous_subtype_val
  have hcont :
      Continuous fun ξ : UnitDiskBoundary =>
        G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro ξ
    exact (hG.analyticOn.continuousOn.continuousAt
      (x := (unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))
      (unitDiskDomain_isOpen.mem_nhds
        (unitDiskRadialBoundary_eval_mem_unitDisk n ξ))).comp
      (x := ξ) heval.continuousAt
  exact Complex.continuous_re.comp hcont

/-- The radial real-part density is bounded on the compact boundary circle. -/
theorem unitDiskTheorem31RadialDensity_bounded
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    ∃ C : ℝ≥0, ∀ ξ : UnitDiskBoundary,
      unitDiskTheorem31RadialDensity G n ξ ≤ (C : ENNReal) := by
  obtain ⟨C, hC⟩ :=
    isCompact_univ.exists_bound_of_continuousOn
      (unitDiskTheorem31RadialRealPart_continuous hG n).continuousOn
  refine ⟨Real.toNNReal (max C 0), ?_⟩
  intro ξ
  have hnonneg :
      0 ≤ (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re :=
    hG.real_nonneg (unitDiskRadialBoundary_eval_mem_unitDisk n ξ)
  have hleC :
      (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re ≤ C := by
    have h := hC ξ (by simp)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using h
  have hle :
      (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re ≤ max C 0 :=
    hleC.trans (le_max_left C 0)
  have hle' :
      (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re ≤
        (Real.toNNReal (max C 0) : ℝ) := by
    simpa [Real.coe_toNNReal _ (le_max_right C 0)] using hle
  simpa [unitDiskTheorem31RadialDensity] using
    (ENNReal.ofReal_le_coe.mpr hle')

/--
The concrete radial boundary measure
`Re G(r_n ξ) dθ/(2π)` used in the proof of book Theorem 3.2.
-/
noncomputable def unitDiskTheorem31RadialBoundaryMeasure
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    FiniteMeasure UnitDiskBoundary where
  val :=
    (unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary).withDensity
      (unitDiskTheorem31RadialDensity G n)
  property := by
    refine isFiniteMeasure_withDensity ?_
    exact (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
      (unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary)
      (unitDiskTheorem31RadialDensity_bounded hG n)).ne

/-- At `w = 0`, the disk Herglotz boundary kernel is identically one. -/
theorem unitDiskBoundaryKernel_zero (ξ : UnitDiskBoundary) :
    unitDiskBoundaryKernel (0 : ℂ) zero_mem_unitDiskDomain ξ = 1 := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by
    intro h
    have hnorm : ‖(ξ : ℂ)‖ = 1 := unitDiskBoundary_norm_eq_one ξ
    simp [h] at hnorm
  change ((ξ : ℂ) + 0) / ((ξ : ℂ) - 0) = 1
  field_simp [hξ0]
  ring

/-- A boundary point and an interior disk point give a nonzero kernel denominator. -/
theorem unitDiskCaratheodoryKernel_den_ne_zero_of_boundary_of_mem_disk
    {ξ w : ℂ} (hξ : ξ ∈ unitDiskBoundary) (hw : w ∈ unitDiskDomain) :
    ξ - w ≠ 0 := by
  intro h
  have heq : ξ = w := sub_eq_zero.mp h
  have hξnorm : ‖ξ‖ = 1 := by
    simpa [unitDiskBoundary] using hξ
  have hwnorm : ‖w‖ < 1 := by
    simpa [unitDiskDomain, Metric.mem_ball, dist_eq_norm] using hw
  rw [heq] at hξnorm
  linarith

/-- For an interior point, the disk Carathéodory kernel is continuous on the boundary. -/
theorem unitDiskCaratheodoryKernel_continuousOn_boundary
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    ContinuousOn (fun z : ℂ => unitDiskCaratheodoryKernel z w)
      unitDiskBoundary := by
  unfold unitDiskCaratheodoryKernel
  refine (continuousOn_id.add continuousOn_const).div
    (continuousOn_id.sub continuousOn_const) ?_
  intro z hz h
  exact unitDiskCaratheodoryKernel_den_ne_zero_of_boundary_of_mem_disk hz hw h

/-- Radial dilation of a disk input is differentiably continuous on the closed disk. -/
theorem unitDiskTheorem31_scaled_diffContOnCl
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    DiffContOnCl ℂ
      (fun z : ℂ => G ((unitDiskHerglotzRadius n : ℂ) * z))
      (Metric.ball (0 : ℂ) 1) := by
  have hdiffG : DifferentiableOn ℂ G unitDiskDomain :=
    hG.analyticOn.differentiableOn
  have hlin :
      DifferentiableOn ℂ
        (fun z : ℂ => (unitDiskHerglotzRadius n : ℂ) * z)
        (Metric.closedBall (0 : ℂ) 1) := by
    exact
      (differentiable_id.const_mul
        (unitDiskHerglotzRadius n : ℂ)).differentiableOn
  have hmaps :
      MapsTo (fun z : ℂ => (unitDiskHerglotzRadius n : ℂ) * z)
        (Metric.closedBall (0 : ℂ) 1) unitDiskDomain := by
    intro z hz
    have hznorm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hrpos : 0 < unitDiskHerglotzRadius n :=
      unitDiskHerglotzRadius_pos n
    have hrlt : unitDiskHerglotzRadius n < 1 :=
      unitDiskHerglotzRadius_lt_one n
    have hmul :
        ‖(unitDiskHerglotzRadius n : ℂ) * z‖ ≤
          unitDiskHerglotzRadius n := by
      calc
        ‖(unitDiskHerglotzRadius n : ℂ) * z‖ =
            unitDiskHerglotzRadius n * ‖z‖ := by
          rw [norm_mul]
          simp [abs_of_pos hrpos]
        _ ≤ unitDiskHerglotzRadius n * 1 := by
          exact mul_le_mul_of_nonneg_left hznorm hrpos.le
        _ = unitDiskHerglotzRadius n := by ring
    rw [unitDiskDomain]
    simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hmul hrlt
  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => G ((unitDiskHerglotzRadius n : ℂ) * z))
        (Metric.closedBall (0 : ℂ) 1) := by
    simpa [Function.comp_def] using hdiffG.comp hlin hmaps
  exact DifferentiableOn.diffContOnCl_ball hdiff subset_rfl

/-- Integrating the boundary kernel against the radial measure gives a circle average. -/
theorem unitDiskTheorem31RadialBoundaryMeasure_integral_kernel_eq_circleAverage
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
        ∂(unitDiskTheorem31RadialBoundaryMeasure hG n :
          Measure UnitDiskBoundary) =
      Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
        0 1 := by
  unfold unitDiskTheorem31RadialBoundaryMeasure
    unitDiskTheorem31RadialDensity
  change
    ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
        ∂((unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary).withDensity
          fun ξ =>
            ENNReal.ofReal
              (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re) =
      Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
        0 1
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hcont :
        ContinuousOn
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
          unitDiskBoundary := by
      exact
        (unitDiskCaratheodoryKernel_continuousOn_boundary hw).mul
          (by
            rw [continuousOn_iff_continuous_restrict]
            exact Complex.continuous_ofReal.comp
              (unitDiskTheorem31RadialRealPart_continuous hG n))
    calc
      (∫ x : UnitDiskBoundary,
          (ENNReal.ofReal
              (G ((unitDiskHerglotzRadius n : ℂ) * (x : ℂ))).re).toReal •
            unitDiskBoundaryKernel w hw x
          ∂(unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary)) =
          ∫ ξ : UnitDiskBoundary,
            unitDiskCaratheodoryKernel (ξ : ℂ) w *
              ((G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re : ℂ)
            ∂(unitDiskBoundaryArcMeasure : Measure UnitDiskBoundary) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          have hnonneg :
              0 ≤ (G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re :=
            hG.real_nonneg (unitDiskRadialBoundary_eval_mem_unitDisk n ξ)
          rw [ENNReal.toReal_ofReal hnonneg]
          change
            (((G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re : ℂ) *
                unitDiskCaratheodoryKernel (ξ : ℂ) w) =
              unitDiskCaratheodoryKernel (ξ : ℂ) w *
                ((G ((unitDiskHerglotzRadius n : ℂ) * (ξ : ℂ))).re : ℂ)
          ring
      _ = Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
          0 1 :=
        unitDiskBoundaryArcMeasure_integral_eq_circleAverage _ hcont
  · exact
      (unitDiskTheorem31RadialRealPart_continuous hG n).measurable
        |>.ennreal_ofReal
  · filter_upwards with ξ
    exact ENNReal.ofReal_lt_top

private theorem unitDiskBoundary_subset_closure_ball :
    unitDiskBoundary ⊆ closure (Metric.ball (0 : ℂ) 1) := by
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  intro z hz
  have hz_norm : ‖z‖ = 1 := by
    simpa [unitDiskBoundary] using hz
  simp [Metric.mem_closedBall, dist_eq_norm, hz_norm]

private theorem unitDiskTheorem31_scaled_circleIntegrable
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    CircleIntegrable
      (fun z : ℂ => G ((unitDiskHerglotzRadius n : ℂ) * z)) 0 1 := by
  have hcont :
      ContinuousOn (fun z : ℂ => G ((unitDiskHerglotzRadius n : ℂ) * z))
        unitDiskBoundary :=
    (unitDiskTheorem31_scaled_diffContOnCl hG n).continuousOn.mono
      unitDiskBoundary_subset_closure_ball
  have hcont' :
      ContinuousOn (fun z : ℂ => G ((unitDiskHerglotzRadius n : ℂ) * z))
        (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hcont
  simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using
    hcont'.circleIntegrable'

/-- A scaled Cauchy circle average equals `2 * G (r_n * w) - G 0`. -/
theorem unitDiskTheorem31_circleAverage_kernel_mul_scaled
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            G ((unitDiskHerglotzRadius n : ℂ) * z))
        0 1 =
      2 * G ((unitDiskHerglotzRadius n : ℂ) * w) - G 0 := by
  let H : ℂ → ℂ := fun z => G ((unitDiskHerglotzRadius n : ℂ) * z)
  have hH : DiffContOnCl ℂ H (Metric.ball (0 : ℂ) 1) := by
    simpa [H] using unitDiskTheorem31_scaled_diffContOnCl hG n
  have hHabs : DiffContOnCl ℂ H (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    simpa [abs_of_pos zero_lt_one] using hH
  have hw_ball : w ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| := by
    simpa [unitDiskDomain, abs_of_pos zero_lt_one] using hw
  have hCauchy :
      Real.circleAverage (fun z : ℂ => ((z - 0) / (z - w)) • H z) 0 1 =
        H w := by
    exact hHabs.circleAverage_smul_div hw_ball
  have hCauchyMul :
      Real.circleAverage (fun z : ℂ => ((z - 0) / (z - w)) * H z) 0 1 =
        H w := by
    simpa [smul_eq_mul] using hCauchy
  have hMean : Real.circleAverage H 0 1 = H 0 := by
    exact hHabs.circleAverage
  have hIntCauchy :
      CircleIntegrable (fun z : ℂ => ((z - 0) / (z - w)) • H z) 0 1 := by
    have hcont :
        ContinuousOn (fun z : ℂ => ((z - 0) / (z - w)) • H z)
          unitDiskBoundary := by
      refine
        ((continuousOn_id.sub continuousOn_const).div
          (continuousOn_id.sub continuousOn_const) ?_).smul ?_
      · intro z hz hden
        have hzne : z - w ≠ 0 :=
          unitDiskCaratheodoryKernel_den_ne_zero_of_boundary_of_mem_disk hz hw
        exact hzne hden
      · exact hH.continuousOn.mono unitDiskBoundary_subset_closure_ball
    have hcont' :
        ContinuousOn (fun z : ℂ => ((z - 0) / (z - w)) • H z)
          (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
      simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hcont
    simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hcont'.circleIntegrable'
  have hIntCauchyMul :
      CircleIntegrable (fun z : ℂ => ((z - 0) / (z - w)) * H z) 0 1 := by
    simpa [smul_eq_mul] using hIntCauchy
  have hIntH :
      CircleIntegrable H 0 1 :=
    unitDiskTheorem31_scaled_circleIntegrable hG n
  have hrewrite :
      Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w * H z)
          0 1 =
        Real.circleAverage
          (fun z : ℂ => (2 : ℂ) * (((z - 0) / (z - w)) * H z) - H z)
          0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz_boundary : z ∈ unitDiskBoundary := by
      simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hz
    have hzne : z - w ≠ 0 :=
      unitDiskCaratheodoryKernel_den_ne_zero_of_boundary_of_mem_disk
        hz_boundary hw
    unfold unitDiskCaratheodoryKernel
    field_simp [hzne]
    ring
  calc
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            G ((unitDiskHerglotzRadius n : ℂ) * z))
        0 1 =
        Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w * H z)
          0 1 := by rfl
    _ =
        Real.circleAverage
          (fun z : ℂ => (2 : ℂ) * (((z - 0) / (z - w)) * H z) - H z)
          0 1 := hrewrite
    _ =
        (2 : ℂ) * Real.circleAverage
            (fun z : ℂ => ((z - 0) / (z - w)) * H z) 0 1 -
          Real.circleAverage H 0 1 := by
        rw [show
          (fun z : ℂ => (2 : ℂ) * (((z - 0) / (z - w)) * H z) - H z) =
            (fun z : ℂ => (2 : ℂ) • (((z - 0) / (z - w)) * H z) - H z) by
            funext z
            simp [smul_eq_mul]]
        rw [Real.circleAverage_fun_sub]
        · rw [Real.circleAverage_fun_smul]
          simp [smul_eq_mul]
        · simpa using hIntCauchyMul.const_smul (a := (2 : ℂ))
        · exact hIntH
    _ = 2 * G ((unitDiskHerglotzRadius n : ℂ) * w) - G 0 := by
        rw [hCauchyMul, hMean]
        simp [H]

private theorem unitDiskConj_mem_ball {z : ℂ} {r : ℝ}
    (hz : z ∈ Metric.ball (0 : ℂ) r) :
    (starRingEnd ℂ) z ∈ Metric.ball (0 : ℂ) r := by
  simpa [Metric.mem_ball, dist_eq_norm] using hz

private theorem unitDiskConj_mem_closedBall {z : ℂ} {r : ℝ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    (starRingEnd ℂ) z ∈ Metric.closedBall (0 : ℂ) r := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hz

private theorem unitDiskTheorem31_scaled_reflect_diffContOnCl
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        (starRingEnd ℂ)
          (G ((unitDiskHerglotzRadius n : ℂ) * (starRingEnd ℂ) z)))
      (Metric.ball (0 : ℂ) 1) := by
  let H : ℂ → ℂ := fun z => G ((unitDiskHerglotzRadius n : ℂ) * z)
  have hH : DiffContOnCl ℂ H (Metric.ball (0 : ℂ) 1) := by
    simpa [H] using unitDiskTheorem31_scaled_diffContOnCl hG n
  refine ⟨?_, ?_⟩
  · intro z hz
    have hcz : (starRingEnd ℂ) z ∈ Metric.ball (0 : ℂ) 1 :=
      unitDiskConj_mem_ball hz
    have hdiffH : DifferentiableAt ℂ H ((starRingEnd ℂ) z) :=
      DiffContOnCl.differentiableAt hH Metric.isOpen_ball hcz
    simpa [H, Function.comp_def] using hdiffH.conj_conj.differentiableWithinAt
  · have hmaps :
        MapsTo (fun z : ℂ => (starRingEnd ℂ) z)
          (closure (Metric.ball (0 : ℂ) 1))
          (closure (Metric.ball (0 : ℂ) 1)) := by
      intro z hz
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hz ⊢
      exact unitDiskConj_mem_closedBall hz
    have hcontH :
        ContinuousOn (fun z : ℂ => H ((starRingEnd ℂ) z))
          (closure (Metric.ball (0 : ℂ) 1)) :=
      hH.continuousOn.comp Complex.continuous_conj.continuousOn hmaps
    have hcont :
        ContinuousOn (fun z : ℂ => (starRingEnd ℂ) (H ((starRingEnd ℂ) z)))
          (closure (Metric.ball (0 : ℂ) 1)) :=
      Complex.continuous_conj.comp_continuousOn hcontH
    simpa [H] using hcont

private theorem unitDiskTheorem31_reflected_factor_diffContOnCl
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        ((1 + w * z) / (1 - w * z)) *
          (starRingEnd ℂ)
            (G ((unitDiskHerglotzRadius n : ℂ) * (starRingEnd ℂ) z)))
      (Metric.ball (0 : ℂ) 1) := by
  let R : ℂ → ℂ := fun z =>
    (starRingEnd ℂ)
      (G ((unitDiskHerglotzRadius n : ℂ) * (starRingEnd ℂ) z))
  have hR : DiffContOnCl ℂ R (Metric.ball (0 : ℂ) 1) := by
    simpa [R] using unitDiskTheorem31_scaled_reflect_diffContOnCl hG n
  let A : ℂ → ℂ := fun z => (1 + w * z) / (1 - w * z)
  have hA : DiffContOnCl ℂ A (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.diffContOnCl_ball ?_ subset_rfl
    intro z hz
    have hden : 1 - w * z ≠ 0 := by
      intro h
      have hw_norm : ‖w‖ < 1 := by
        simpa [unitDiskDomain, Metric.mem_ball, dist_eq_norm] using hw
      have hz_norm : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hmul_norm : ‖w * z‖ < 1 := by
        calc
          ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul _ _
          _ ≤ ‖w‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hz_norm (norm_nonneg w)
          _ < 1 := by
            simpa using hw_norm
      have hone : w * z = 1 := by
        exact (sub_eq_zero.mp h).symm
      have : ‖w * z‖ = 1 := by simp [hone]
      linarith
    exact
      ((differentiableAt_const (1 : ℂ)).add
        ((differentiableAt_id.const_mul w))).div
        ((differentiableAt_const (1 : ℂ)).sub
          ((differentiableAt_id.const_mul w))) hden |>.differentiableWithinAt
  have hprod := hA.smul hR
  simpa [A, R, smul_eq_mul] using hprod

/-- The conjugate scaled Cauchy circle average collapses to `(starRingEnd ℂ) (G 0)`. -/
theorem unitDiskTheorem31_circleAverage_kernel_mul_conj_scaled
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            (starRingEnd ℂ)
              (G ((unitDiskHerglotzRadius n : ℂ) * z)))
        0 1 =
      (starRingEnd ℂ) (G 0) := by
  let H : ℂ → ℂ := fun z => G ((unitDiskHerglotzRadius n : ℂ) * z)
  let R : ℂ → ℂ := fun z => (starRingEnd ℂ) (H ((starRingEnd ℂ) z))
  let F : ℂ → ℂ := fun z => ((1 + w * z) / (1 - w * z)) * R z
  have hF : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) 1) := by
    simpa [F, R, H] using
      unitDiskTheorem31_reflected_factor_diffContOnCl hG n hw
  have hFabs : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    simpa [abs_of_pos zero_lt_one] using hF
  have hmean : Real.circleAverage F 0 1 = F 0 :=
    hFabs.circleAverage
  have hinv :
      Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              (starRingEnd ℂ) (H z))
          0 1 =
        Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z⁻¹ w *
              (starRingEnd ℂ) (H z⁻¹))
          0 1 := by
    rw [← Real.circleAverage_zero_one_congr_inv
      (f := fun z : ℂ =>
        unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z))]
  have hcongr :
      Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z⁻¹ w *
              (starRingEnd ℂ) (H z⁻¹))
          0 1 =
        Real.circleAverage F 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz_norm : ‖z‖ = 1 := by
      simpa using (Metric.mem_sphere.mp hz)
    have hz0 : z ≠ 0 := by
      exact norm_pos_iff.mp (by simp [hz_norm])
    have hzinv : z⁻¹ = (starRingEnd ℂ) z :=
      Complex.inv_eq_conj hz_norm
    have hz_inv_boundary : z⁻¹ ∈ unitDiskBoundary := by
      have hnorm : ‖z⁻¹‖ = 1 := by
        rw [hzinv]
        simpa using hz_norm
      simpa [unitDiskBoundary] using hnorm
    have hden₁ : z⁻¹ - w ≠ 0 :=
      unitDiskCaratheodoryKernel_den_ne_zero_of_boundary_of_mem_disk
        hz_inv_boundary hw
    have hden₂ : 1 - w * z ≠ 0 := by
      intro h
      have hw_norm : ‖w‖ < 1 := by
        simpa [unitDiskDomain, Metric.mem_ball, dist_eq_norm] using hw
      have hmul : w * z = 1 := (sub_eq_zero.mp h).symm
      have hmul_norm : ‖w * z‖ = 1 := by simp [hmul]
      have hmul_norm_lt : ‖w * z‖ < 1 := by
        calc
          ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul _ _
          _ = ‖w‖ * 1 := by rw [hz_norm]
          _ < 1 := by simpa using hw_norm
      linarith
    unfold F R unitDiskCaratheodoryKernel
    change
      (z⁻¹ + w) / (z⁻¹ - w) * (starRingEnd ℂ) (H z⁻¹) =
        (1 + w * z) / (1 - w * z) *
          (starRingEnd ℂ) (H ((starRingEnd ℂ) z))
    have hden₁' : (starRingEnd ℂ) z - w ≠ 0 := by
      simpa [← hzinv] using hden₁
    rw [hzinv]
    have hconj_mul : (starRingEnd ℂ) z * z = 1 := by
      rw [← hzinv]
      exact inv_mul_cancel₀ hz0
    have hconj_w_mul : (starRingEnd ℂ) z * w * z = w := by
      calc
        (starRingEnd ℂ) z * w * z =
            w * ((starRingEnd ℂ) z * z) := by ring
        _ = w := by rw [hconj_mul]; ring
    have hk :
        ((starRingEnd ℂ) z + w) / ((starRingEnd ℂ) z - w) =
          (1 + w * z) / (1 - w * z) := by
      field_simp [hden₁', hden₂]
      ring_nf
      rw [hconj_w_mul]
      ring
    rw [hk]
  calc
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            (starRingEnd ℂ)
              (G ((unitDiskHerglotzRadius n : ℂ) * z)))
        0 1 =
        Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              (starRingEnd ℂ) (H z))
          0 1 := by rfl
    _ =
        Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z⁻¹ w *
              (starRingEnd ℂ) (H z⁻¹))
          0 1 := hinv
    _ = Real.circleAverage F 0 1 := hcongr
    _ = F 0 := hmean
    _ = (starRingEnd ℂ) (G 0) := by
      simp [F, R, H]

private theorem unitDiskTheorem31_kernel_mul_scaled_circleIntegrable
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    CircleIntegrable
      (fun z : ℂ =>
        unitDiskCaratheodoryKernel z w *
          G ((unitDiskHerglotzRadius n : ℂ) * z)) 0 1 := by
  have hcont :
      ContinuousOn
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            G ((unitDiskHerglotzRadius n : ℂ) * z))
        unitDiskBoundary := by
    exact (unitDiskCaratheodoryKernel_continuousOn_boundary hw).mul
      ((unitDiskTheorem31_scaled_diffContOnCl hG n).continuousOn.mono
        unitDiskBoundary_subset_closure_ball)
  have hcont' :
      ContinuousOn
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            G ((unitDiskHerglotzRadius n : ℂ) * z))
        (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hcont
  exact hcont'.circleIntegrable'

private theorem unitDiskTheorem31_kernel_mul_conj_scaled_circleIntegrable
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    CircleIntegrable
      (fun z : ℂ =>
        unitDiskCaratheodoryKernel z w *
          (starRingEnd ℂ)
            (G ((unitDiskHerglotzRadius n : ℂ) * z))) 0 1 := by
  have hcont :
      ContinuousOn
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            (starRingEnd ℂ)
              (G ((unitDiskHerglotzRadius n : ℂ) * z)))
        unitDiskBoundary := by
    exact (unitDiskCaratheodoryKernel_continuousOn_boundary hw).mul
      (Complex.continuous_conj.comp_continuousOn
        ((unitDiskTheorem31_scaled_diffContOnCl hG n).continuousOn.mono
          unitDiskBoundary_subset_closure_ball))
  have hcont' :
      ContinuousOn
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            (starRingEnd ℂ)
              (G ((unitDiskHerglotzRadius n : ℂ) * z)))
        (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa [unitDiskBoundary, abs_of_pos zero_lt_one] using hcont
  exact hcont'.circleIntegrable'

/-- The real-part circle average equals `G (r_n * w) - Complex.I * (G 0).im`. -/
theorem unitDiskTheorem31_circleAverage_kernel_mul_real_scaled
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
        0 1 =
      G ((unitDiskHerglotzRadius n : ℂ) * w) -
        Complex.I * ((G 0).im : ℂ) := by
  let H : ℂ → ℂ := fun z => G ((unitDiskHerglotzRadius n : ℂ) * z)
  have hInt₁ :
      CircleIntegrable (fun z : ℂ => unitDiskCaratheodoryKernel z w * H z)
        0 1 := by
    simpa [H] using unitDiskTheorem31_kernel_mul_scaled_circleIntegrable hG n hw
  have hInt₂ :
      CircleIntegrable
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)) 0 1 := by
    simpa [H] using
      unitDiskTheorem31_kernel_mul_conj_scaled_circleIntegrable hG n hw
  have hsplit :
      Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              ((H z).re : ℂ))
          0 1 =
        Real.circleAverage
          (fun z : ℂ =>
            (1 / 2 : ℂ) •
              (unitDiskCaratheodoryKernel z w * H z +
                unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)))
          0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z _hz
    have hre :
        unitDiskCaratheodoryKernel z w * ((H z).re : ℂ) =
          (1 / 2 : ℂ) *
            (unitDiskCaratheodoryKernel z w * H z +
              unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)) := by
      have hconj : H z + (starRingEnd ℂ) (H z) = (2 * (H z).re : ℂ) := by
        rw [Complex.add_conj]
        norm_num
      calc
        unitDiskCaratheodoryKernel z w * ((H z).re : ℂ) =
            (1 / 2 : ℂ) *
              (unitDiskCaratheodoryKernel z w *
                ((2 * (H z).re : ℝ) : ℂ)) := by
            norm_num
            ring
        _ = (1 / 2 : ℂ) *
              (unitDiskCaratheodoryKernel z w *
                (H z + (starRingEnd ℂ) (H z))) := by
            rw [hconj]
            norm_num
        _ = (1 / 2 : ℂ) *
              (unitDiskCaratheodoryKernel z w * H z +
                unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)) := by
            ring
    simpa [smul_eq_mul] using hre
  calc
    Real.circleAverage
        (fun z : ℂ =>
          unitDiskCaratheodoryKernel z w *
            ((G ((unitDiskHerglotzRadius n : ℂ) * z)).re : ℂ))
        0 1 =
        Real.circleAverage
          (fun z : ℂ =>
            unitDiskCaratheodoryKernel z w *
              ((H z).re : ℂ))
          0 1 := by rfl
    _ =
        Real.circleAverage
          (fun z : ℂ =>
            (1 / 2 : ℂ) •
              (unitDiskCaratheodoryKernel z w * H z +
                unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)))
          0 1 := hsplit
    _ =
        (1 / 2 : ℂ) *
          (Real.circleAverage
              (fun z : ℂ => unitDiskCaratheodoryKernel z w * H z) 0 1 +
            Real.circleAverage
              (fun z : ℂ =>
                unitDiskCaratheodoryKernel z w * (starRingEnd ℂ) (H z)) 0 1) := by
        rw [Real.circleAverage_fun_smul]
        rw [Real.circleAverage_fun_add hInt₁ hInt₂]
        simp [smul_eq_mul]
    _ =
        (1 / 2 : ℂ) *
          ((2 * H w - H 0) + (starRingEnd ℂ) (H 0)) := by
        rw [unitDiskTheorem31_circleAverage_kernel_mul_scaled hG n hw]
        rw [unitDiskTheorem31_circleAverage_kernel_mul_conj_scaled hG n hw]
        simp [H]
    _ = G ((unitDiskHerglotzRadius n : ℂ) * w) -
        Complex.I * ((G 0).im : ℂ) := by
        apply Complex.ext
        · simp [H, Complex.add_re, Complex.sub_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im]
        · simp [H, Complex.add_im, Complex.sub_im, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im]
          ring

/-- The concrete radial boundary measure represents the radial value of `G`. -/
theorem unitDiskTheorem31ConcreteRadialFormula
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ)
    {w : ℂ} (hw : w ∈ unitDiskDomain) :
    G ((unitDiskHerglotzRadius n : ℂ) * w) =
      Complex.I * ((G 0).im : ℂ) +
        ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
          ∂(unitDiskTheorem31RadialBoundaryMeasure hG n :
            Measure UnitDiskBoundary) := by
  have hInt :=
    unitDiskTheorem31RadialBoundaryMeasure_integral_kernel_eq_circleAverage
      hG n hw
  have hAvg :=
    unitDiskTheorem31_circleAverage_kernel_mul_real_scaled hG n hw
  rw [hInt, hAvg]
  ring

private theorem unitDisk_integral_const_one_eq_mass
    (μ : FiniteMeasure UnitDiskBoundary) :
    (∫ _ : UnitDiskBoundary, (1 : ℂ) ∂(μ : Measure UnitDiskBoundary)) =
      ((μ.mass : ℝ≥0) : ℂ) := by
  rw [integral_const]
  rw [Measure.real_def]
  change (((((μ : Measure UnitDiskBoundary) Set.univ).toReal : ℝ) : ℂ) * 1) =
    ((μ.mass : ℝ≥0) : ℂ)
  rw [mul_one]
  rw [MeasureTheory.FiniteMeasure.mass]
  rfl

/-- The concrete radial boundary measure has mass `(G 0).re` as a nonnegative real. -/
theorem unitDiskTheorem31ConcreteRadialMass_eq
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) (n : ℕ) :
    (unitDiskTheorem31RadialBoundaryMeasure hG n).mass =
      Real.toNNReal (G 0).re := by
  let μ : FiniteMeasure UnitDiskBoundary :=
    unitDiskTheorem31RadialBoundaryMeasure hG n
  have hform :=
    unitDiskTheorem31ConcreteRadialFormula hG n zero_mem_unitDiskDomain
  have hIntOne :
      (∫ ξ : UnitDiskBoundary,
          unitDiskBoundaryKernel (0 : ℂ) zero_mem_unitDiskDomain ξ
          ∂(μ : Measure UnitDiskBoundary)) =
        ((μ.mass : ℝ≥0) : ℂ) := by
    calc
      (∫ ξ : UnitDiskBoundary,
          unitDiskBoundaryKernel (0 : ℂ) zero_mem_unitDiskDomain ξ
          ∂(μ : Measure UnitDiskBoundary)) =
          ∫ ξ : UnitDiskBoundary, (1 : ℂ) ∂(μ : Measure UnitDiskBoundary) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          exact unitDiskBoundaryKernel_zero ξ
      _ = ((μ.mass : ℝ≥0) : ℂ) :=
          unitDisk_integral_const_one_eq_mass μ
  have hcomplex :
      G 0 = Complex.I * ((G 0).im : ℂ) + ((μ.mass : ℝ≥0) : ℂ) := by
    simpa [μ, hIntOne] using hform
  have hre : ((μ.mass : ℝ≥0) : ℝ) = (G 0).re := by
    have := congrArg Complex.re hcomplex
    simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im] using this.symm
  apply NNReal.coe_injective
  change
    (((unitDiskTheorem31RadialBoundaryMeasure hG n).mass : ℝ≥0) : ℝ) =
      ((Real.toNNReal (G 0).re : ℝ≥0) : ℝ)
  rw [Real.coe_toNNReal]
  · simpa [μ] using hre
  · rw [← hre]
    positivity

/--
Concrete radial Poisson formula data for book Theorem 3.1.

The substantial Poisson formula and its `w = 0` mass consequence are supplied
by the proved concrete radial formula and mass identity above.  The measure in
that formula is the concrete radial boundary measure defined above.
-/
structure UnitDiskTheorem31ConcreteRadialFormulaData
    (G : ℂ → ℂ) (hG : UnitDiskCaratheodoryInput G) where
  radial_mass_eq :
    ∀ n : ℕ,
      (unitDiskTheorem31RadialBoundaryMeasure hG n).mass =
        Real.toNNReal (G 0).re
  formula :
    ∀ (n : ℕ) ⦃w : ℂ⦄ (hw : w ∈ (unitDiskDomain : Set ℂ)),
      G ((unitDiskHerglotzRadius n : ℂ) * w) =
        Complex.I * ((G 0).im : ℂ) +
          ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
          ∂(unitDiskTheorem31RadialBoundaryMeasure hG n :
            Measure UnitDiskBoundary)

/-- The concrete radial Poisson formula supplies the concrete radial formula data. -/
def unitDiskTheorem31ConcreteRadialFormulaData_of_carathInput
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G) :
    UnitDiskTheorem31ConcreteRadialFormulaData G hG where
  radial_mass_eq := unitDiskTheorem31ConcreteRadialMass_eq hG
  formula := unitDiskTheorem31ConcreteRadialFormula hG

/-- Concrete radial Poisson data imply the abstract output used by the radial weak-limit core. -/
def unitDiskTheorem31RadialFamilyData_of_concreteFormulaData
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G)
    (data : UnitDiskTheorem31ConcreteRadialFormulaData G hG) :
    UnitDiskTheorem31RadialFamilyData G where
  radialMeasure := unitDiskTheorem31RadialBoundaryMeasure hG
  radialMass := Real.toNNReal (G 0).re
  radial_mass_eq := data.radial_mass_eq
  mass_eq := by
    simp [ENNReal.ofReal]
  formula := data.formula

/-- Producer interface for the concrete radial Poisson formula of Theorem 3.1. -/
structure UnitDiskTheorem31ConcreteRadialFormulaProducerFromCaratheodoryInput where
  produce :
    ∀ {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G),
      UnitDiskTheorem31ConcreteRadialFormulaData G hG

/-- Book Theorem 3.1 radial Poisson formula, specialized to the concrete radial measures. -/
def unitDiskTheorem31ConcreteRadialFormulaProducer :
    UnitDiskTheorem31ConcreteRadialFormulaProducerFromCaratheodoryInput where
  produce := by
    intro G hG
    exact unitDiskTheorem31ConcreteRadialFormulaData_of_carathInput hG

/-- A concrete radial formula producer supplies the Theorem 3.1 radial-family producer. -/
def unitDiskTheorem31RadialFamilyProducer_of_concreteFormulaProducer
    (producer : UnitDiskTheorem31ConcreteRadialFormulaProducerFromCaratheodoryInput) :
    UnitDiskTheorem31RadialFamilyProducerFromCaratheodoryInput where
  produce := by
    intro G hG
    exact unitDiskTheorem31RadialFamilyData_of_concreteFormulaData hG
      (producer.produce hG)

/--
Concrete Theorem 3.1 radial Poisson data and the radial weak-limit core give the
disk Herglotz producer.
-/
def unitDiskHerglotzCircleProducer_of_concreteTheorem31FormulaProducer
    (producer : UnitDiskTheorem31ConcreteRadialFormulaProducerFromCaratheodoryInput) :
    UnitDiskHerglotzCircleProducerFromCaratheodoryInput :=
  unitDiskHerglotzCircleProducer_of_theorem31RadialFamilyProducer
    (unitDiskTheorem31RadialFamilyProducer_of_concreteFormulaProducer producer)

/--
The concrete Poisson formula for radial measures closes the disk circle
Herglotz producer up to the later boundary-Cayley and outside-support steps.
-/
def unitDiskHerglotzCircleProducer_of_theorem31ConcreteFormula :
    UnitDiskHerglotzCircleProducerFromCaratheodoryInput :=
  unitDiskHerglotzCircleProducer_of_concreteTheorem31FormulaProducer
    unitDiskTheorem31ConcreteRadialFormulaProducer

end

end Quantum.TraceInequality.Loewner
