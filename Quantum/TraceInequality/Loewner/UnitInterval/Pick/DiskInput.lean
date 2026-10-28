import Quantum.TraceInequality.Loewner.UnitInterval.Pick.DiskCayley

/-!
# Chapter 3 disk Carathéodory input from Pick extensions

This module packages the Cayley reduction from a Pick extension on the normalized
interval to the disk-side Carathéodory input used by the disk Herglotz theorem.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Pick extensions as disk Carathéodory inputs -/

/-- The unit disk, used as the disk-side domain in book Theorem 3.2. -/
def unitDiskDomain : Set ℂ :=
  Metric.ball (0 : ℂ) 1

/--
Disk-side Carathéodory input for the Herglotz representation theorem.

This is deliberately only the input predicate for book Theorem 3.2.  The
measure-producing Herglotz theorem is kept as a separate producer contract.
-/
structure UnitDiskCaratheodoryInput (G : ℂ → ℂ) where
  analyticOn : AnalyticOn ℂ G unitDiskDomain
  real_nonneg : ∀ ⦃w : ℂ⦄, w ∈ unitDiskDomain → 0 ≤ (G w).re

/-- The disk-side domain for Theorem 3.2 is open. -/
theorem unitDiskDomain_isOpen :
    IsOpen (unitDiskDomain : Set ℂ) := by
  simp [unitDiskDomain]

/-- A point of the open unit disk is not the boundary point `1`. -/
theorem diskToUpperCayley_ne_one_of_mem_unitDisk {w : ℂ}
    (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    w ≠ 1 := by
  intro h
  have hlt : ‖w‖ < 1 := by
    simpa [unitDiskDomain, dist_eq_norm] using hw
  have hone : ‖w‖ = 1 := by simp [h]
  linarith

/-- Imaginary part of the disk-to-upper Cayley transform. -/
theorem diskToUpperCayley_im_eq (w : ℂ) :
    (diskToUpperCayley w).im =
      (1 - Complex.normSq w) / Complex.normSq (w - 1) := by
  by_cases hw : w = 1
  · subst hw
    simp [diskToUpperCayley, Complex.normSq_apply]
  · unfold diskToUpperCayley
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    ring

/-- The disk-to-upper Cayley transform has positive imaginary part on the unit disk. -/
theorem diskToUpperCayley_im_pos_of_mem_unitDisk {w : ℂ}
    (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    0 < (diskToUpperCayley w).im := by
  have hwne : w ≠ 1 := diskToUpperCayley_ne_one_of_mem_unitDisk hw
  have hnorm : ‖w‖ < 1 := by
    simpa [unitDiskDomain, dist_eq_norm] using hw
  rw [diskToUpperCayley_im_eq]
  have hnum : 0 < 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w, hnorm]
  have hden : 0 < Complex.normSq (w - 1) := by
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hwne)
  positivity

/-- The disk-to-upper Cayley image of the unit disk lies in the Pick domain. -/
theorem diskToUpperCayley_mem_pickDomain_of_mem_unitDisk {w : ℂ}
    (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    diskToUpperCayley w ∈ (unitIntervalPickDomain : Set ℂ) :=
  mem_unitIntervalPickDomain_of_im_ne_zero
    (ne_of_gt (diskToUpperCayley_im_pos_of_mem_unitDisk hw))

/-- The disk-to-upper Cayley transform is differentiable away from `1`. -/
theorem diskToUpperCayley_differentiableAt_of_ne_one {w : ℂ}
    (hw : w ≠ 1) :
    DifferentiableAt ℂ diskToUpperCayley w := by
  have hden : Complex.I * (w - 1) ≠ 0 :=
    diskToUpperCayley_den_ne_zero_of_ne_one hw
  unfold diskToUpperCayley
  exact (differentiableAt_id.add (differentiableAt_const (1 : ℂ))).div
    ((differentiableAt_const Complex.I).mul
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))) hden

/-- The disk-to-upper Cayley transform is differentiable on the unit disk. -/
theorem diskToUpperCayley_differentiableOn_unitDisk :
    DifferentiableOn ℂ diskToUpperCayley (unitDiskDomain : Set ℂ) := by
  intro w hw
  exact (diskToUpperCayley_differentiableAt_of_ne_one
    (diskToUpperCayley_ne_one_of_mem_unitDisk hw)).differentiableWithinAt

/-- The Pick-to-disk Carathéodory transform is differentiable on the unit disk. -/
theorem pickToDiskCaratheodory_differentiableOn_unitDisk
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    DifferentiableOn ℂ (pickToDiskCaratheodory pick) unitDiskDomain := by
  intro w hw
  have hw_domain :
      diskToUpperCayley w ∈ (unitIntervalPickDomain : Set ℂ) :=
    diskToUpperCayley_mem_pickDomain_of_mem_unitDisk hw
  have hF :
      DifferentiableAt ℂ pick.F (diskToUpperCayley w) :=
    pick.analyticOn.differentiableOn.differentiableAt
      (unitIntervalPickDomain_isOpen.mem_nhds hw_domain)
  have hT :
      DifferentiableAt ℂ diskToUpperCayley w :=
    diskToUpperCayley_differentiableAt_of_ne_one
      (diskToUpperCayley_ne_one_of_mem_unitDisk hw)
  unfold pickToDiskCaratheodory
  exact ((differentiableAt_const (-Complex.I)).mul
    (hF.comp w hT)).differentiableWithinAt

/-- The Pick-to-disk Carathéodory transform is analytic on the unit disk. -/
theorem pickToDiskCaratheodory_analyticOn_unitDisk
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    AnalyticOn ℂ (pickToDiskCaratheodory pick) unitDiskDomain :=
  (pickToDiskCaratheodory_differentiableOn_unitDisk pick).analyticOn
    unitDiskDomain_isOpen

/-- The Pick-to-disk Carathéodory transform has nonnegative real part on the disk. -/
theorem pickToDiskCaratheodory_re_nonneg_of_mem_unitDisk
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    {w : ℂ} (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    0 ≤ (pickToDiskCaratheodory pick w).re := by
  have hz : 0 < (diskToUpperCayley w).im :=
    diskToUpperCayley_im_pos_of_mem_unitDisk hw
  have hmap := pick.mapsUpper hz
  simpa [pickToDiskCaratheodory] using hmap

/-- A Pick extension gives the disk-side Carathéodory input required by Theorem 3.2. -/
def unitDiskCaratheodoryInput_of_pick
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    UnitDiskCaratheodoryInput (pickToDiskCaratheodory pick) where
  analyticOn := pickToDiskCaratheodory_analyticOn_unitDisk pick
  real_nonneg := by
    intro w hw
    exact pickToDiskCaratheodory_re_nonneg_of_mem_unitDisk pick hw

/--
Producer interface for book Theorem 3.2 after the Cayley reduction has supplied
the disk-side Carathéodory input.
-/
structure UnitDiskCaratheodoryHerglotzProducerFromPickInput where
  produce :
    ∀ {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f),
      UnitDiskCaratheodoryInput (pickToDiskCaratheodory pick) →
        UnitDiskCaratheodoryHerglotzData (pickToDiskCaratheodory pick)

/-- A disk Herglotz producer for Carathéodory inputs gives the disk-Cayley producer. -/
def unitDiskCaratheodoryHerglotzProducer_of_pickInputProducer
    (producer : UnitDiskCaratheodoryHerglotzProducerFromPickInput) :
    UnitDiskCaratheodoryHerglotzProducer where
  produce := by
    intro f pick
    exact producer.produce pick (unitDiskCaratheodoryInput_of_pick pick)

/--
Reverse Theorem 3.8 from Pick extension, assuming the disk Herglotz producer
for the Carathéodory input supplied by the Cayley reduction.
-/
def integralRepOnUnitInterval_of_pickExtension_of_pickInputDiskHerglotzProducer
    (producer : UnitDiskCaratheodoryHerglotzProducerFromPickInput)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_diskHerglotzProducer
    (unitDiskCaratheodoryHerglotzProducer_of_pickInputProducer producer) pick

end

end Quantum.TraceInequality.Loewner
