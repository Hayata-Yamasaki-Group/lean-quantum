/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.UpperHalfPlane.Nevanlinna
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CauchyApproxIdentity
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.ConcreteRadialMeasures
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.BoundaryPushforward

/-!
# Pick construction for upper-half-plane Poisson boundary data

Source correspondence: the Nevanlinna/Pick representation stage, from Pick
functions through disk Caratheodory data, the Cayley bridge, and the finite
Nevanlinna representation.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open MeasureTheory Set
open Filter
open scoped UpperHalfPlane Topology Manifold ContDiff
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Pick functions as disk Caratheodory inputs -/

/-- The disk Caratheodory function obtained from an upper-half-plane Pick function. -/
def upperHalfPlanePickToDiskCaratheodory (F : ℍ → ℂ) (w : ℂ) : ℂ :=
  -Complex.I * F (UpperHalfPlane.ofComplex (diskToUpperCayley w))

/-- The disk Carathéodory function of an upper-half-plane Pick function is differentiable on the
unit disk. [simon2019] -/
theorem upperHalfPlanePickToDiskCaratheodory_differentiableOn_unitDisk
    {F : ℍ → ℂ} (hF : MDiff F) :
    DifferentiableOn ℂ (upperHalfPlanePickToDiskCaratheodory F) unitDiskDomain := by
  intro w hw
  have hUpperDiff :
      DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
    exact UpperHalfPlane.mdifferentiable_iff.mp hF
  have hz : 0 < (diskToUpperCayley w).im :=
    diskToUpperCayley_im_pos_of_mem_unitDisk hw
  have hF_at : DifferentiableAt ℂ (F ∘ UpperHalfPlane.ofComplex) (diskToUpperCayley w) :=
    hUpperDiff.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hT : DifferentiableAt ℂ diskToUpperCayley w :=
    diskToUpperCayley_differentiableAt_of_ne_one
      (diskToUpperCayley_ne_one_of_mem_unitDisk hw)
  unfold upperHalfPlanePickToDiskCaratheodory
  exact ((differentiableAt_const (-Complex.I)).mul
    (hF_at.comp w hT)).differentiableWithinAt

/-- The disk Carathéodory function of a Pick function is analytic on the unit disk. [simon2019] -/
theorem upperHalfPlanePickToDiskCaratheodory_analyticOn_unitDisk
    {F : ℍ → ℂ} (hF : MDiff F) :
    AnalyticOn ℂ (upperHalfPlanePickToDiskCaratheodory F) unitDiskDomain :=
  (upperHalfPlanePickToDiskCaratheodory_differentiableOn_unitDisk hF).analyticOn
    unitDiskDomain_isOpen

/-- The disk Carathéodory function of a Pick function has nonnegative real part on the unit disk.
[simon2019] -/
theorem upperHalfPlanePickToDiskCaratheodory_re_nonneg_of_mem_unitDisk
    {F : ℍ → ℂ} (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im)
    {w : ℂ} (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    0 ≤ (upperHalfPlanePickToDiskCaratheodory F w).re := by
  have _hz : 0 < (diskToUpperCayley w).im :=
    diskToUpperCayley_im_pos_of_mem_unitDisk hw
  simpa [upperHalfPlanePickToDiskCaratheodory] using
    hF_nonneg (UpperHalfPlane.ofComplex (diskToUpperCayley w))

/-- Upper-half-plane Pick hypotheses supply the disk-side Caratheodory input. -/
def unitDiskCaratheodoryInput_of_upperHalfPlanePick
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    UnitDiskCaratheodoryInput (upperHalfPlanePickToDiskCaratheodory F) where
  analyticOn := upperHalfPlanePickToDiskCaratheodory_analyticOn_unitDisk hF
  real_nonneg := by
    intro w hw
    exact upperHalfPlanePickToDiskCaratheodory_re_nonneg_of_mem_unitDisk hF_nonneg hw

/-- The concrete disk Herglotz circle data attached to an upper-half-plane Pick function. -/
def upperHalfPlanePickCircleData
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    UnitDiskHerglotzCircleData (upperHalfPlanePickToDiskCaratheodory F) :=
  unitDiskHerglotzCircleProducer_of_theorem31ConcreteFormula.produce
    (unitDiskCaratheodoryInput_of_upperHalfPlanePick hF hF_nonneg)

/-! ### Cayley bridge to finite Nevanlinna data -/

/-- Cayley bridge: the disk Carathéodory-kernel integral against the pushforward boundary measure
equals `-i` times the raw unit-interval Herglotz-kernel integral. [simon2019] -/
theorem upperHalfPlanePick_disk_integral_eq_raw
    {G : ℂ → ℂ} (circle : UnitDiskHerglotzCircleData G)
    {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure : Measure ℝ)) =
      -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure : Measure ℝ) := by
  calc
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure : Measure ℝ)) =
        ∫ y : ℝ, -Complex.I * unitIntervalHerglotzRawKernel z y
          ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure : Measure ℝ) := by
          exact integral_congr_ae <|
            Eventually.of_forall fun y =>
              unitDiskCaratheodoryKernel_cayley_eq_raw hz y
    _ = -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure : Measure ℝ) := by
          exact MeasureTheory.integral_const_mul
            (μ := unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure)
            (r := -Complex.I) (f := fun y : ℝ => unitIntervalHerglotzRawKernel z y)

/-- A concrete finite-measure Nevanlinna representation for an upper-half-plane Pick function. -/
def nevanlinnaRep_of_pick
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    NevanlinnaRep F where
  alpha := - (upperHalfPlanePickToDiskCaratheodory F 0).im
  beta := unitDiskBoundaryCayleySlope
    (upperHalfPlanePickCircleData hF hF_nonneg).boundaryMeasure
  ν := unitDiskBoundaryCayleyPushforwardMeasure
    (upperHalfPlanePickCircleData hF hF_nonneg).boundaryMeasure
  formula := by
    intro z
    let circle := upperHalfPlanePickCircleData hF hF_nonneg
    let ν := unitDiskBoundaryCayleyPushforwardMeasure circle.boundaryMeasure
    let zc : ℂ := (z : ℂ)
    have hz : 0 < zc.im := by
      simpa [zc] using z.coe_im_pos
    have hw : upperToDiskCayley zc ∈ (unitDiskDomain : Set ℂ) := by
      have hnorm := upperToDiskCayley_norm_lt_one_of_im_pos hz
      simpa [unitDiskDomain, dist_eq_norm] using hnorm
    have hform := circle.formula hw
    have hsplit := unitDiskBoundaryCayley_circle_integral_eq circle hz
    have hbridge := upperHalfPlanePick_disk_integral_eq_raw circle hz
    have hinv : diskToUpperCayley (upperToDiskCayley zc) = zc :=
      diskToUpperCayley_upperToDiskCayley
        (upperToDiskCayley_den_ne_zero_of_im_pos hz)
    have hleft :
        upperHalfPlanePickToDiskCaratheodory F (upperToDiskCayley zc) =
          -Complex.I * F z := by
      unfold upperHalfPlanePickToDiskCaratheodory
      rw [hinv]
      simp [zc, UpperHalfPlane.ofComplex_apply z]
    let R : ℂ :=
      ∫ y : ℝ, unitIntervalHerglotzRawKernel zc y ∂(ν : Measure ℝ)
    let A : ℂ :=
      (-(upperHalfPlanePickToDiskCaratheodory F 0).im : ℝ) +
        (((unitDiskBoundaryCayleySlope circle.boundaryMeasure : ℝ≥0) : ℝ) : ℂ) * zc + R
    have hmul : -Complex.I * F z = -Complex.I * A := by
      calc
        -Complex.I * F z = upperHalfPlanePickToDiskCaratheodory F (upperToDiskCayley zc) :=
          hleft.symm
        _ = Complex.I * (((upperHalfPlanePickToDiskCaratheodory F) 0).im : ℂ) +
              ((unitDiskBoundaryCayleySlope circle.boundaryMeasure : ℝ≥0) : ℂ) *
                (-Complex.I * zc) +
              (-Complex.I * R) := by
            rw [hform, hsplit, hbridge]
            simp [R, ν, add_assoc]
        _ = -Complex.I * A := by
            simp [A]
            ring_nf
    have hcancel : F z = A := by
      calc
        F z = Complex.I * (-Complex.I * F z) := by
          ring_nf
          simp [Complex.I_sq]
        _ = Complex.I * (-Complex.I * A) := by rw [hmul]
        _ = A := by
          ring_nf
          simp [Complex.I_sq]
    simpa [A, R, ν, circle, zc, unitIntervalHerglotzRawKernel, nevanlinnaKernel] using hcancel

end

end Loewner
end TraceInequality
end Quantum
