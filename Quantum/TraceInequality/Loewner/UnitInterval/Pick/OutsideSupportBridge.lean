import Quantum.TraceInequality.Loewner.UnitInterval.Pick.BoundaryPushforward
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.ConcreteRadialMeasures

/-!
# Chapter 3 Corollary 3.6 outside-support bridge

This module records the outside-support producer contract from Corollary 3.6
and the bridge from Proposition 3.5 inversion to the reverse Pick/integral
correspondence input.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Corollary 3.6 outside-support producer contract -/

/--
The Corollary 3.6 outside-support input specialized to a Pick extension.

This is deliberately Pick-specific: the vanishing of the interval arc is a
consequence of analytic continuation through `(-1,1)` with real boundary values,
not of an arbitrary disk Carathéodory input.
-/
structure UnitDiskCorollary36OutsideSupportProducerFromPickInput where
  interval_arc_zero :
    ∀ {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
      (_hG : UnitDiskCaratheodoryInput (pickToDiskCaratheodory pick))
      (circle : UnitDiskHerglotzCircleData (pickToDiskCaratheodory pick)),
        ((circle.boundaryMeasure.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
          (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) = 0

/-- Package circle data with the interval-arc vanishing input required by boundary pushforward. -/
def unitDiskHerglotzCircleCayleyOutsideData_of_circle_of_intervalArcZero
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    (hzero :
      ((circle.boundaryMeasure.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
        (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) = 0) :
    UnitDiskHerglotzCircleCayleyOutsideData G where
  circle := circle
  interval_arc_zero := hzero

/--
The concrete Theorem 3.1 / Theorem 3.2 disk-circle producer, together with the
Corollary 3.6 outside-support producer, supplies the disk Herglotz data in
Cayley real-line coordinates.
-/
def unitDiskCaratheodoryHerglotzProducer_of_theorem31ConcreteFormula_and_corollary36
    (producer : UnitDiskCorollary36OutsideSupportProducerFromPickInput) :
    UnitDiskCaratheodoryHerglotzProducerFromPickInput where
  produce := by
    intro f pick hG
    let circle : UnitDiskHerglotzCircleData (pickToDiskCaratheodory pick) :=
      unitDiskHerglotzCircleProducer_of_theorem31ConcreteFormula.produce hG
    exact unitDiskCaratheodoryHerglotzData_of_circleCayleyOutsideData
      (unitDiskHerglotzCircleCayleyOutsideData_of_circle_of_intervalArcZero circle
        (producer.interval_arc_zero pick hG circle))

/--
Reverse Theorem 3.8 from a Pick extension, assuming the Corollary 3.6
outside-support producer.  The producer is the book Theorem 3.4 /
Corollary 3.6 input; a concrete one is
`unitDiskCorollary36OutsideSupportProducer_concrete` (`PublicCorrespondence.lean`).
-/
def integralRepOnUnitInterval_of_pickExtension_of_corollary36OutsideSupportProducer
    (producer : UnitDiskCorollary36OutsideSupportProducerFromPickInput)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_pickInputDiskHerglotzProducer
    (unitDiskCaratheodoryHerglotzProducer_of_theorem31ConcreteFormula_and_corollary36
      producer) pick

/-! ### Corollary 3.6 via Proposition 3.5 inversion -/

/--
Upper-half-plane raw Herglotz data before Corollary 3.6 removes the mass on
`(-1,1)`.

This is the same book formula as `UnitIntervalPickHerglotzUpperRawOutsideData`,
but without the outside-support field.  Proposition 3.5 is responsible for
deducing that field from the real boundary values.
-/
structure UnitIntervalPickHerglotzUpperRawData (f : ℝ → ℝ) where
  pick : PickExtensionOnUnitInterval f
  constant : ℝ
  slope : ℝ≥0
  measure : FiniteMeasure ℝ
  upper_formula :
    ∀ ⦃z : ℂ⦄, 0 < z.im →
      pick.F z =
        (constant : ℂ) + ((slope : ℝ) : ℂ) * z +
          ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
            ∂(measure : Measure ℝ)

/-- The circle Cayley pushforward integral is the raw upper-half-plane integral. -/
theorem unitDiskBoundaryCayley_pushforward_integral_eq_raw
    (μ : FiniteMeasure ℂ) {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ)) =
      -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ) := by
  calc
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ))
        = ∫ y : ℝ, -Complex.I * unitIntervalHerglotzRawKernel z y
            ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ) := by
          exact integral_congr_ae <|
            Eventually.of_forall fun y =>
              unitDiskCaratheodoryKernel_cayley_eq_raw hz y
    _ = -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ) := by
          exact MeasureTheory.integral_const_mul (μ := unitDiskBoundaryCayleyPushforwardMeasure μ)
            (r := -Complex.I) (f := fun y : ℝ => unitIntervalHerglotzRawKernel z y)

/--
The disk circle Herglotz output gives the raw real-line upper-half-plane
Herglotz formula before Corollary 3.6 proves the outside-support condition.
-/
def unitIntervalPickHerglotzUpperRawData_of_circleData
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    (circle : UnitDiskHerglotzCircleData (pickToDiskCaratheodory pick)) :
    UnitIntervalPickHerglotzUpperRawData f where
  pick := pick
  constant := -((pickToDiskCaratheodory pick 0).im)
  slope := unitDiskBoundaryCayleySlope circle.boundaryMeasure
  measure := unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure
  upper_formula := by
    intro z hz
    let A : ℂ :=
      (-((pickToDiskCaratheodory pick 0).im) : ℝ) +
        ((unitDiskBoundaryCayleySlope circle.boundaryMeasure : ℝ) : ℂ) * z
    let R : ℂ :=
      ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
        ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure :
          Measure ℝ)
    have hw : upperToDiskCayley z ∈ (unitDiskDomain : Set ℂ) := by
      have hnorm := upperToDiskCayley_norm_lt_one_of_im_pos hz
      simpa [unitDiskDomain, dist_eq_norm] using hnorm
    have hform := circle.formula hw
    have hsplit := unitDiskBoundaryCayley_circle_integral_eq circle hz
    have hbridge :=
      unitDiskBoundaryCayley_pushforward_integral_eq_raw
        circle.boundaryMeasure hz
    have hinv :
        diskToUpperCayley (upperToDiskCayley z) = z :=
      diskToUpperCayley_upperToDiskCayley
        (upperToDiskCayley_den_ne_zero_of_im_pos hz)
    have hmul :
        -Complex.I * pick.F z = -Complex.I * (A + R) := by
      simpa [pickToDiskCaratheodory, hinv, A, R, hsplit, hbridge, mul_add,
        add_assoc, mul_assoc, mul_comm, mul_left_comm]
        using hform
    have hcancel :
        pick.F z = A + R := by
      calc
        pick.F z = Complex.I * (-Complex.I * pick.F z) := by
          ring_nf
          simp [Complex.I_sq]
        _ = Complex.I * (-Complex.I * (A + R)) := by rw [hmul]
        _ = A + R := by
          ring_nf
          simp [Complex.I_sq]
    simpa [A, R, add_assoc] using hcancel

/--
The output of book Proposition 3.5 for a raw Herglotz representation.

It records only the consequence used in Corollary 3.6: if the upper boundary
imaginary parts tend to zero on `(-1,1)`, then the representing measure has no
mass on that interval.
-/
structure UnitIntervalPickHerglotzProposition35Input
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f) where
  measure_Ioo_eq_zero :
    (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Tendsto
        (fun n : ℕ => (data.pick.F (unitIntervalUpperBoundarySeq x n)).im)
        atTop (𝓝 0)) →
      (data.measure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0

/-- Producer interface for the Proposition 3.5 inversion input. -/
structure UnitIntervalPickHerglotzProposition35Producer where
  produce :
    ∀ {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f),
      UnitIntervalPickHerglotzProposition35Input data

/-- Boundary imaginary parts of a Pick extension vanish along the vertical approach. -/
theorem pickExtension_boundary_im_tendsto_zero_on_Ioo
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n : ℕ => (pick.F (unitIntervalUpperBoundarySeq x n)).im)
      atTop (𝓝 0) := by
  have hcont := pick.continuousAt_real hx
  have hF :
      Tendsto (fun n : ℕ => pick.F (unitIntervalUpperBoundarySeq x n))
        atTop (𝓝 (f x : ℂ)) := by
    simpa [pick.agreesOnReal hx] using
      hcont.tendsto.comp (unitIntervalUpperBoundarySeq_tendsto_ofReal x)
  simpa using (Complex.continuous_im.tendsto (f x : ℂ)).comp hF

/-- Zero pushforward mass gives zero mass on the corresponding boundary arc. -/
theorem unitDiskBoundaryCayley_intervalArcZero_of_pushforward_zero
    (μ : FiniteMeasure ℂ)
    (hzero :
      (unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ)
        (Set.Ioo (-1 : ℝ) 1) = 0) :
    ((μ.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
      (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) = 0 := by
  have hmap :
      (unitDiskBoundaryCayleyPushforwardMeasure μ : Measure ℝ)
        (Set.Ioo (-1 : ℝ) 1) =
        ((μ.restrict {ξ : ℂ | ξ ≠ 1}) : Measure ℂ)
          (unitDiskBoundaryCayleyReal ⁻¹' Set.Ioo (-1 : ℝ) 1) := by
    rw [unitDiskBoundaryCayleyPushforwardMeasure, FiniteMeasure.toMeasure_map]
    rw [Measure.map_apply_of_aemeasurable
      unitDiskBoundaryCayleyReal_measurable.aemeasurable measurableSet_Ioo]
  simpa [hmap] using hzero

/--
Proposition 3.5 inversion supplies the Corollary 3.6 outside-support producer
used in the outside-support producer contract.
-/
def unitDiskCorollary36OutsideSupportProducer_of_proposition35Producer
    (producer : UnitIntervalPickHerglotzProposition35Producer) :
    UnitDiskCorollary36OutsideSupportProducerFromPickInput where
  interval_arc_zero := by
    intro f pick hG circle
    let data := unitIntervalPickHerglotzUpperRawData_of_circleData pick circle
    have hpush :
        (data.measure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 :=
      (producer.produce data).measure_Ioo_eq_zero
        (fun x hx => pickExtension_boundary_im_tendsto_zero_on_Ioo pick hx)
    exact unitDiskBoundaryCayley_intervalArcZero_of_pushforward_zero
      circle.boundaryMeasure (by simpa [data] using hpush)

/--
Reverse Theorem 3.8 from a Pick extension, assuming Proposition 3.5 inversion.
-/
def integralRepOnUnitInterval_of_pickExtension_of_proposition35Producer
    (producer : UnitIntervalPickHerglotzProposition35Producer)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_corollary36OutsideSupportProducer
    (unitDiskCorollary36OutsideSupportProducer_of_proposition35Producer producer)
    pick

end

end Quantum.TraceInequality.Loewner
