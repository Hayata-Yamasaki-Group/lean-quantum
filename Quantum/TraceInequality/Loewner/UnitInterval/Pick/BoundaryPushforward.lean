import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CircleHerglotz

/-!
# Chapter 3 boundary Cayley pushforward

This module pushes disk-boundary Herglotz circle data through the boundary
Cayley map to the real-line outside Herglotz data used by the interval theorem.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Boundary Cayley pushforward from disk circle data -/

/--
The real-line coordinate attached to a boundary point by the inverse Cayley
map.  At the exceptional point `1` this is only a harmless totalized value; the
pushforward measure below restricts away from that point.
-/
def unitDiskBoundaryCayleyReal (ξ : ℂ) : ℝ :=
  (diskToUpperCayley ξ).re

/-- The boundary Cayley real coordinate is measurable. -/
theorem unitDiskBoundaryCayleyReal_measurable :
    Measurable unitDiskBoundaryCayleyReal := by
  unfold unitDiskBoundaryCayleyReal diskToUpperCayley
  measurability

/-- The atom at the Cayley point at infinity, represented as the Herglotz slope. -/
def unitDiskBoundaryCayleySlope (μ : FiniteMeasure ℂ) : ℝ≥0 :=
  μ ({1} : Set ℂ)

/--
The real-line part of a disk boundary measure, obtained by removing the atom at
`1` and pushing the remaining boundary mass through the inverse Cayley real
coordinate.
-/
noncomputable def unitDiskBoundaryCayleyPushforwardMeasure
    (μ : FiniteMeasure ℂ) : FiniteMeasure ℝ :=
  (μ.restrict {ξ : ℂ | ξ ≠ 1}).map unitDiskBoundaryCayleyReal

/-- The disk Herglotz kernel at the Cayley point at infinity gives the slope term. -/
theorem unitDiskCaratheodoryKernel_one_cayley
    {z : ℂ} (hz : 0 < z.im) :
    unitDiskCaratheodoryKernel 1 (upperToDiskCayley z) = -Complex.I * z := by
  have hzden : z + Complex.I ≠ 0 :=
    upperToDiskCayley_den_ne_zero_of_im_pos hz
  have hdiff : (1 : ℂ) - upperToDiskCayley z ≠ 0 := by
    unfold upperToDiskCayley
    rw [show (1 : ℂ) - ((z - Complex.I) / (z + Complex.I)) =
        (z + Complex.I - (z - Complex.I)) / (z + Complex.I) by
      field_simp [hzden]]
    have hnum : z + Complex.I - (z - Complex.I) = 2 * Complex.I := by ring
    rw [hnum]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hzden
  unfold unitDiskCaratheodoryKernel upperToDiskCayley
  field_simp [hzden, hdiff, Complex.I_ne_zero]
  rw [show z + Complex.I + (z - Complex.I) = 2 * z by ring]
  rw [show -(z * Complex.I * (z + Complex.I - (z - Complex.I))) = 2 * z by
    rw [show z + Complex.I - (z - Complex.I) = 2 * Complex.I by ring]
    ring_nf
    rw [Complex.I_sq]
    ring]

/-- The inverse Cayley image of a non-exceptional boundary point lies on the real axis. -/
theorem diskToUpperCayley_im_eq_zero_of_mem_boundary_ne_one
    {ξ : ℂ} (hξ : ξ ∈ unitDiskBoundary) (hξ_ne : ξ ≠ 1) :
    (diskToUpperCayley ξ).im = 0 := by
  rw [diskToUpperCayley_im_eq]
  have hnorm : ‖ξ‖ = 1 := by
    simpa [unitDiskBoundary] using hξ
  have hnormSq : Complex.normSq ξ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hden : Complex.normSq (ξ - 1) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (sub_ne_zero.mpr hξ_ne)).ne'
  rw [hnormSq]
  field_simp [hden]
  ring

/-- The real Cayley coordinate coerced to `ℂ` equals the inverse Cayley image. -/
theorem ofReal_unitDiskBoundaryCayleyReal_eq_diskToUpperCayley
    {ξ : ℂ} (hξ : ξ ∈ unitDiskBoundary) (hξ_ne : ξ ≠ 1) :
    (unitDiskBoundaryCayleyReal ξ : ℂ) = diskToUpperCayley ξ := by
  have him := diskToUpperCayley_im_eq_zero_of_mem_boundary_ne_one hξ hξ_ne
  apply Complex.ext
  · simp [unitDiskBoundaryCayleyReal]
  · simp [unitDiskBoundaryCayleyReal, him]

/-- Applying the upper-to-disk Cayley map to the boundary real coordinate recovers `ξ`. -/
theorem upperToDiskCayley_boundaryCayleyReal_eq
    {ξ : ℂ} (hξ : ξ ∈ unitDiskBoundary) (hξ_ne : ξ ≠ 1) :
    upperToDiskCayley (unitDiskBoundaryCayleyReal ξ : ℂ) = ξ := by
  rw [ofReal_unitDiskBoundaryCayleyReal_eq_diskToUpperCayley hξ hξ_ne]
  exact upperToDiskCayley_diskToUpperCayley hξ_ne

/-- Replacing a boundary point by its Cayley real coordinate preserves the disk kernel. -/
theorem unitDiskCaratheodoryKernel_boundaryCayleyReal_eq
    {z ξ : ℂ} (hξ : ξ ∈ unitDiskBoundary) (hξ_ne : ξ ≠ 1) :
    unitDiskCaratheodoryKernel
        (upperToDiskCayley (unitDiskBoundaryCayleyReal ξ : ℂ)) z =
      unitDiskCaratheodoryKernel ξ z := by
  rw [upperToDiskCayley_boundaryCayleyReal_eq hξ hξ_ne]

/-- The Cayley pushforward has no mass in `(-1,1)` under the outside-support input. -/
theorem unitDiskBoundaryCayleyPushforwardMeasure_outside_support
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    (hzero :
      ((circle.boundaryMeasure.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
        (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) = 0) :
    (unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure :
        Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 := by
  rw [unitDiskBoundaryCayleyPushforwardMeasure, FiniteMeasure.toMeasure_map]
  rw [Measure.map_apply_of_aemeasurable
    unitDiskBoundaryCayleyReal_measurable.aemeasurable measurableSet_Ioo]
  exact hzero

/--
Circle Herglotz data plus the Corollary 3.6 outside-support input needed after
the boundary Cayley pushforward.
-/
structure UnitDiskHerglotzCircleCayleyOutsideData (G : ℂ → ℂ) where
  circle : UnitDiskHerglotzCircleData G
  interval_arc_zero :
    ((circle.boundaryMeasure.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
      (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) = 0

/-- The packaged Cayley outside-support data gives outside support for the pushforward. -/
theorem UnitDiskHerglotzCircleCayleyOutsideData.outside_support
    {G : ℂ → ℂ} (data : UnitDiskHerglotzCircleCayleyOutsideData G) :
    (unitDiskBoundaryCayleyPushforwardMeasure data.circle.boundaryMeasure :
        Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 :=
  unitDiskBoundaryCayleyPushforwardMeasure_outside_support
    data.circle data.interval_arc_zero

private theorem unitDiskCaratheodoryKernel_integrable_of_circle_support
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun ξ : ℂ => unitDiskCaratheodoryKernel ξ w)
      (circle.boundaryMeasure : Measure ℂ) := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℂ => unitDiskCaratheodoryKernel ξ w)
      (circle.boundaryMeasure : Measure ℂ) := by
    have h :
        Measurable (fun ξ : ℂ => (ξ + w) / (ξ - w)) :=
      (measurable_id.add measurable_const).div (measurable_id.sub measurable_const)
    simpa [unitDiskCaratheodoryKernel] using h.aestronglyMeasurable
  refine Integrable.of_bound hmeas ((1 + ‖w‖) / (1 - ‖w‖)) ?_
  have hae_boundary :
      ∀ᵐ ξ ∂(circle.boundaryMeasure : Measure ℂ), ξ ∈ unitDiskBoundary := by
    rw [ae_iff]
    simpa using circle.boundary_support
  filter_upwards [hae_boundary] with ξ hξ
  have hξnorm : ‖ξ‖ = 1 := by
    simpa [unitDiskBoundary] using hξ
  have hden_lower : 1 - ‖w‖ ≤ ‖ξ - w‖ := by
    simpa [hξnorm] using norm_sub_norm_le ξ w
  have hden_pos : 0 < ‖ξ - w‖ := by
    have hpos : 0 < 1 - ‖w‖ := by linarith
    exact lt_of_lt_of_le hpos hden_lower
  have hnum : ‖ξ + w‖ ≤ 1 + ‖w‖ := by
    calc
      ‖ξ + w‖ ≤ ‖ξ‖ + ‖w‖ := norm_add_le ξ w
      _ = 1 + ‖w‖ := by rw [hξnorm]
  unfold unitDiskCaratheodoryKernel
  rw [norm_div]
  have h₁ :
      ‖ξ + w‖ / ‖ξ - w‖ ≤ (1 + ‖w‖) / ‖ξ - w‖ :=
    div_le_div_of_nonneg_right hnum (norm_nonneg _)
  have h₂ :
      (1 + ‖w‖) / ‖ξ - w‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) hden_lower
  exact h₁.trans h₂

private theorem unitDiskCaratheodoryKernel_integrable_of_circle_support_restrict
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    {w : ℂ} (hw : ‖w‖ < 1) (s : Set ℂ) :
    Integrable (fun ξ : ℂ => unitDiskCaratheodoryKernel ξ w)
      ((circle.boundaryMeasure : Measure ℂ).restrict s) :=
  (unitDiskCaratheodoryKernel_integrable_of_circle_support circle hw).mono_measure
    Measure.restrict_le_self

/-- The atom at `1` contributes exactly the Herglotz slope term. -/
theorem unitDiskBoundaryCayley_atom_integral
    (μ : FiniteMeasure ℂ) {z : ℂ} (hz : 0 < z.im) :
    (∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ (upperToDiskCayley z)
        ∂((μ : Measure ℂ).restrict ({1} : Set ℂ))) =
      ((unitDiskBoundaryCayleySlope μ : ℝ≥0) : ℂ) * (-Complex.I * z) := by
  rw [integral_singleton, unitDiskCaratheodoryKernel_one_cayley hz]
  unfold unitDiskBoundaryCayleySlope
  rw [FiniteMeasure.self_eq_mass_mul_normalize]
  simp only [FiniteMeasure.measureReal_eq_coe_coeFn, NNReal.coe_mul]
  conv_lhs =>
    rw [FiniteMeasure.self_eq_mass_mul_normalize]
  change (((μ.mass * μ.normalize {1} : ℝ≥0) : ℂ) • (-Complex.I * z)) =
    ((μ.mass * μ.normalize {1} : ℝ≥0) : ℂ) * (-Complex.I * z)
  rw [smul_eq_mul]

/-- Integrating over the Cayley pushforward is the restricted boundary integral. -/
theorem unitDiskBoundaryCayley_pushforward_integral
    (μ : FiniteMeasure ℂ) {z : ℂ} :
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ)) =
      ∫ ξ : ℂ,
        unitDiskCaratheodoryKernel
          (upperToDiskCayley (unitDiskBoundaryCayleyReal ξ : ℂ))
          (upperToDiskCayley z)
        ∂((μ : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1}) := by
  rw [unitDiskBoundaryCayleyPushforwardMeasure, FiniteMeasure.toMeasure_map]
  exact integral_map unitDiskBoundaryCayleyReal_measurable.aemeasurable (by
    have hOfReal :
        Measurable (fun y : ℝ => (y : ℂ)) := Complex.measurable_ofReal
    have hUpper :
        Measurable (fun y : ℝ => upperToDiskCayley (y : ℂ)) := by
      unfold upperToDiskCayley
      exact
        ((hOfReal.sub measurable_const).div
          (hOfReal.add measurable_const))
    have h :
        Measurable (fun y : ℝ =>
          unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
            (upperToDiskCayley z)) := by
      unfold unitDiskCaratheodoryKernel
      exact
        ((hUpper.add measurable_const).div
          (hUpper.sub measurable_const))
    simpa using h.aestronglyMeasurable)

/-- The non-exceptional boundary integral equals the Cayley-pushforward integral. -/
theorem unitDiskBoundaryCayley_complement_integral_eq_pushforward
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    {z : ℂ} :
    (∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ (upperToDiskCayley z)
        ∂((circle.boundaryMeasure : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1})) =
      ∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure :
          Measure ℝ) := by
  rw [unitDiskBoundaryCayley_pushforward_integral circle.boundaryMeasure]
  have hae_boundary :
      ∀ᵐ ξ ∂((circle.boundaryMeasure : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1}),
        ξ ∈ unitDiskBoundary := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simpa using circle.boundary_support
  have hae_ne :
      ∀ᵐ ξ ∂((circle.boundaryMeasure : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1}),
        ξ ≠ 1 := by
    exact ae_restrict_mem (measurableSet_singleton (1 : ℂ)).compl
  refine integral_congr_ae ?_
  filter_upwards [hae_boundary, hae_ne] with ξ hξ hξ_ne
  exact (unitDiskCaratheodoryKernel_boundaryCayleyReal_eq
    (z := upperToDiskCayley z) hξ hξ_ne).symm

/-- Split the boundary circle integral into the slope atom and Cayley pushforward parts. -/
theorem unitDiskBoundaryCayley_circle_integral_eq
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    {z : ℂ} (hz : 0 < z.im) :
    (∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ (upperToDiskCayley z)
        ∂(circle.boundaryMeasure : Measure ℂ)) =
      ((unitDiskBoundaryCayleySlope circle.boundaryMeasure : ℝ≥0) : ℂ) *
          (-Complex.I * z) +
        ∫ y : ℝ,
          unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
            (upperToDiskCayley z)
          ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure :
            Measure ℝ) := by
  have hw : ‖upperToDiskCayley z‖ < 1 :=
    upperToDiskCayley_norm_lt_one_of_im_pos hz
  have hInt_ne :=
    unitDiskCaratheodoryKernel_integrable_of_circle_support_restrict
      circle hw {ξ : ℂ | ξ ≠ 1}
  have hInt_ne_compl :
      Integrable (fun ξ => unitDiskCaratheodoryKernel ξ (upperToDiskCayley z))
        ((circle.boundaryMeasure : Measure ℂ).restrict ({1} : Set ℂ)ᶜ) := by
    change Integrable (fun ξ => unitDiskCaratheodoryKernel ξ (upperToDiskCayley z))
      ((circle.boundaryMeasure : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1})
    exact hInt_ne
  have hInt_atom :=
    unitDiskCaratheodoryKernel_integrable_of_circle_support_restrict
      circle hw ({1} : Set ℂ)
  rw [← Measure.restrict_add_restrict_compl
    (μ := (circle.boundaryMeasure : Measure ℂ))
    (s := ({1} : Set ℂ)) (measurableSet_singleton (1 : ℂ))]
  rw [integral_add_measure hInt_atom hInt_ne_compl]
  rw [unitDiskBoundaryCayley_atom_integral circle.boundaryMeasure hz]
  change
    ↑↑(unitDiskBoundaryCayleySlope circle.boundaryMeasure) * (-Complex.I * z) +
        (∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ (upperToDiskCayley z)
          ∂((circle.boundaryMeasure : Measure ℂ).restrict {ξ : ℂ | ξ ≠ 1})) =
      ↑↑(unitDiskBoundaryCayleySlope circle.boundaryMeasure) * (-Complex.I * z) +
        ∫ y : ℝ,
          unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
            (upperToDiskCayley z)
          ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure :
            Measure ℝ)
  rw [unitDiskBoundaryCayley_complement_integral_eq_pushforward circle]

/--
Convert disk circle Herglotz data plus the outside-support input into the
real-line Cayley Herglotz data used by the upper-half-plane bridge.
-/
def unitDiskCaratheodoryHerglotzData_of_circleCayleyOutsideData
    {G : ℂ → ℂ} (data : UnitDiskHerglotzCircleCayleyOutsideData G) :
    UnitDiskCaratheodoryHerglotzData G where
  constant := - (G 0).im
  slope := unitDiskBoundaryCayleySlope data.circle.boundaryMeasure
  outsideMeasure := unitDiskBoundaryCayleyPushforwardMeasure data.circle.boundaryMeasure
  outside_support := data.outside_support
  formula := by
    intro z hz
    have hw : upperToDiskCayley z ∈ (unitDiskDomain : Set ℂ) := by
      have hnorm := upperToDiskCayley_norm_lt_one_of_im_pos hz
      simpa [unitDiskDomain, dist_eq_norm] using hnorm
    have hform := data.circle.formula hw
    have hsplit := unitDiskBoundaryCayley_circle_integral_eq data.circle hz
    rw [hform, hsplit]
    ring_nf
    simp
    ring

/--
Producer interface for the boundary Cayley pushforward plus the Corollary 3.6
outside-support input, starting from a disk Carathéodory input.
-/
structure UnitDiskCircleCayleyOutsideProducerFromCaratheodoryInput where
  produce :
    ∀ {G : ℂ → ℂ}, UnitDiskCaratheodoryInput G →
      UnitDiskHerglotzCircleCayleyOutsideData G

/-- The circle Cayley outside producer supplies the disk Herglotz producer. -/
def unitDiskCaratheodoryHerglotzProducer_of_circleCayleyOutsideProducer
    (producer : UnitDiskCircleCayleyOutsideProducerFromCaratheodoryInput) :
    UnitDiskCaratheodoryHerglotzProducerFromPickInput where
  produce := by
    intro f pick hG
    exact unitDiskCaratheodoryHerglotzData_of_circleCayleyOutsideData
      (producer.produce hG)

/--
Reverse Theorem 3.8 from a Pick extension, assuming the disk circle Herglotz
data has been pushed forward by the boundary Cayley map and satisfies the
outside-support input.
-/
def integralRepOnUnitInterval_of_pickExtension_of_circleCayleyOutsideProducer
    (producer : UnitDiskCircleCayleyOutsideProducerFromCaratheodoryInput)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_pickInputDiskHerglotzProducer
    (unitDiskCaratheodoryHerglotzProducer_of_circleCayleyOutsideProducer producer)
    pick

end

end Quantum.TraceInequality.Loewner
