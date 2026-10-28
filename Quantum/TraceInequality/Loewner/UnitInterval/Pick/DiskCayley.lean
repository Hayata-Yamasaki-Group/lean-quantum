import Quantum.TraceInequality.Loewner.UnitInterval.Pick.RawOutside

/-!
# Chapter 3 Cayley bridge for disk Herglotz data

This module contains the Cayley bridge from upper-half-plane raw outside
Herglotz data to disk-side Carathéodory Herglotz data.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Cayley bridge for the upper-half-plane Herglotz representation -/

/-- Book Cayley map from the upper half-plane to the unit disk. -/
def upperToDiskCayley (z : ℂ) : ℂ :=
  (z - Complex.I) / (z + Complex.I)

/-- Inverse book Cayley map from the unit disk to the upper half-plane. -/
def diskToUpperCayley (w : ℂ) : ℂ :=
  (w + 1) / (Complex.I * (w - 1))

/-- Disk Herglotz/Carathéodory kernel in the normalization used in Chapter 3. -/
def unitDiskCaratheodoryKernel (ξ w : ℂ) : ℂ :=
  (ξ + w) / (ξ - w)

/-- The disk-side Carathéodory function attached to a Pick extension. -/
def pickToDiskCaratheodory {f : ℝ → ℝ}
    (pick : PickExtensionOnUnitInterval f) (w : ℂ) : ℂ :=
  -Complex.I * pick.F (diskToUpperCayley w)

/-- An upper-half-plane point does not hit the denominator pole of the Cayley map. -/
theorem upperToDiskCayley_den_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    z + Complex.I ≠ 0 := by
  intro h
  have him : (z + Complex.I).im = 0 := by simp [h]
  simp at him
  linarith

/-- A disk point different from `1` gives a nonzero inverse Cayley denominator. -/
theorem diskToUpperCayley_den_ne_zero_of_ne_one {w : ℂ} (hw : w ≠ 1) :
    Complex.I * (w - 1) ≠ 0 := by
  exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hw)

/-- The upper-to-disk Cayley map sends `Complex.I` to `0`. -/
theorem upperToDiskCayley_I :
    upperToDiskCayley Complex.I = 0 := by
  simp [upperToDiskCayley]

/-- The disk-to-upper Cayley map sends `0` to `Complex.I`. -/
theorem diskToUpperCayley_zero :
    diskToUpperCayley 0 = Complex.I := by
  unfold diskToUpperCayley
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  norm_num

/-- The disk-to-upper Cayley map is a left inverse off the upper Cayley pole. -/
theorem diskToUpperCayley_upperToDiskCayley
    {z : ℂ} (hz : z + Complex.I ≠ 0) :
    diskToUpperCayley (upperToDiskCayley z) = z := by
  unfold diskToUpperCayley upperToDiskCayley
  field_simp [hz, Complex.I_ne_zero]
  ring_nf
  rw [Complex.inv_I]
  ring

/-- The upper-to-disk Cayley map is a left inverse off the disk Cayley pole. -/
theorem upperToDiskCayley_diskToUpperCayley
    {w : ℂ} (hw : w ≠ 1) :
    upperToDiskCayley (diskToUpperCayley w) = w := by
  have hden : Complex.I * (w - 1) ≠ 0 :=
    diskToUpperCayley_den_ne_zero_of_ne_one hw
  unfold upperToDiskCayley diskToUpperCayley
  field_simp [hden, Complex.I_ne_zero, sub_ne_zero.mpr hw]
  rw [Complex.I_sq]
  ring_nf

/-- The Cayley image of an upper-half-plane point has norm square below one. -/
theorem upperToDiskCayley_normSq_lt_one_of_im_pos
    {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (upperToDiskCayley z) < 1 := by
  have hden : z + Complex.I ≠ 0 :=
    upperToDiskCayley_den_ne_zero_of_im_pos hz
  have hlt :
      Complex.normSq (z - Complex.I) < Complex.normSq (z + Complex.I) := by
    simp [Complex.normSq_apply]
    nlinarith [hz]
  rw [upperToDiskCayley, Complex.normSq_div]
  exact (div_lt_one (Complex.normSq_pos.mpr hden)).mpr hlt

/-- The Cayley image of an upper-half-plane point lies in the unit disk. -/
theorem upperToDiskCayley_norm_lt_one_of_im_pos
    {z : ℂ} (hz : 0 < z.im) :
    ‖upperToDiskCayley z‖ < 1 := by
  have hsq := upperToDiskCayley_normSq_lt_one_of_im_pos hz
  rw [Complex.normSq_eq_norm_sq, sq_lt_one_iff₀ (norm_nonneg _)] at hsq
  exact hsq

/-- Real boundary points under the upper-to-disk Cayley map are never `1`. -/
theorem upperToDiskCayley_ofReal_ne_one (x : ℝ) :
    upperToDiskCayley (x : ℂ) ≠ 1 := by
  intro h
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him : ((x : ℂ) + Complex.I).im = 0 := by simp [hzero]
    norm_num at him
  have hmul : (x : ℂ) - Complex.I = (x : ℂ) + Complex.I := by
    calc
      (x : ℂ) - Complex.I =
          upperToDiskCayley (x : ℂ) * ((x : ℂ) + Complex.I) := by
            unfold upperToDiskCayley
            field_simp [hden]
      _ = 1 * ((x : ℂ) + Complex.I) := by rw [h]
      _ = (x : ℂ) + Complex.I := by simp
  have him := congrArg Complex.im hmul
  norm_num at him

/-- The Cayley maps compose to the identity on real boundary points. -/
theorem diskToUpperCayley_upperToDiskCayley_ofReal (x : ℝ) :
    diskToUpperCayley (upperToDiskCayley (x : ℂ)) = (x : ℂ) := by
  apply diskToUpperCayley_upperToDiskCayley
  intro hzero
  have him : ((x : ℂ) + Complex.I).im = 0 := by simp [hzero]
  norm_num at him

/-- Under Cayley change of variables, the disk kernel becomes the raw interval kernel. -/
theorem unitDiskCaratheodoryKernel_cayley_eq_raw
    {z : ℂ} (hz : 0 < z.im) (y : ℝ) :
    unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
        (upperToDiskCayley z) =
      -Complex.I * unitIntervalHerglotzRawKernel z y := by
  have hzden : z + Complex.I ≠ 0 :=
    upperToDiskCayley_den_ne_zero_of_im_pos hz
  have hyden : (y : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((y : ℂ) + Complex.I).im = 0 := by simp [h]
    norm_num at him
  have hyz : (y : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hdiff :
      upperToDiskCayley (y : ℂ) - upperToDiskCayley z ≠ 0 := by
    intro h
    have hyinv :
        diskToUpperCayley (upperToDiskCayley (y : ℂ)) = (y : ℂ) :=
      diskToUpperCayley_upperToDiskCayley hyden
    have hzinv :
        diskToUpperCayley (upperToDiskCayley z) = z :=
      diskToUpperCayley_upperToDiskCayley hzden
    have heqT :
        upperToDiskCayley (y : ℂ) = upperToDiskCayley z :=
      sub_eq_zero.mp h
    have hyz_eq : (y : ℂ) = z := by
      rw [← hyinv, heqT, hzinv]
    have him := congrArg Complex.im hyz_eq
    simp at him
    linarith
  have hD : (y : ℂ) * Complex.I * 2 - Complex.I * z * 2 ≠ 0 := by
    have hfactor :
        (y : ℂ) * Complex.I * 2 - Complex.I * z * 2 =
          2 * Complex.I * ((y : ℂ) - z) := by
      ring
    rw [hfactor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hyz
  unfold unitDiskCaratheodoryKernel upperToDiskCayley unitIntervalHerglotzRawKernel
  field_simp [hzden, hyden, hyz, hdiff, Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  field_simp [hD]
  rw [Complex.I_sq]
  ring_nf

/--
Disk-side Herglotz data after the boundary measure has been written in the
real-line Cayley coordinate of book Theorem 3.4.

This data is produced from the concrete Theorem 3.1 disk-circle formula and the
Corollary 3.6 outside-support producer by
`unitDiskCaratheodoryHerglotzProducer_of_theorem31ConcreteFormula_and_corollary36`
(`OutsideSupportBridge.lean`).  This structure only records the disk kernel
formula needed for the Cayley bridge.
-/
structure UnitDiskCaratheodoryHerglotzData (G : ℂ → ℂ) where
  constant : ℝ
  slope : ℝ≥0
  outsideMeasure : FiniteMeasure ℝ
  outside_support :
    (outsideMeasure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0
  formula :
    ∀ ⦃z : ℂ⦄, 0 < z.im →
      G (upperToDiskCayley z) =
        -Complex.I * ((constant : ℂ) + ((slope : ℝ) : ℂ) * z) +
          ∫ y : ℝ,
            unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
              (upperToDiskCayley z)
            ∂(outsideMeasure : Measure ℝ)

/-- The disk-kernel integral is `-Complex.I` times the raw interval-kernel integral. -/
theorem UnitDiskCaratheodoryHerglotzData.disk_integral_eq_raw
    {G : ℂ → ℂ} (data : UnitDiskCaratheodoryHerglotzData G)
    {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(data.outsideMeasure : Measure ℝ)) =
      -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(data.outsideMeasure : Measure ℝ) := by
  calc
    (∫ y : ℝ,
        unitDiskCaratheodoryKernel (upperToDiskCayley (y : ℂ))
          (upperToDiskCayley z)
        ∂(data.outsideMeasure : Measure ℝ))
        = ∫ y : ℝ, -Complex.I * unitIntervalHerglotzRawKernel z y
            ∂(data.outsideMeasure : Measure ℝ) := by
          exact integral_congr_ae <|
            Eventually.of_forall fun y =>
              unitDiskCaratheodoryKernel_cayley_eq_raw hz y
    _ = -Complex.I *
        ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
          ∂(data.outsideMeasure : Measure ℝ) := by
          exact MeasureTheory.integral_const_mul (μ := data.outsideMeasure)
            (r := -Complex.I) (f := fun y : ℝ => unitIntervalHerglotzRawKernel z y)

/--
Convert disk Herglotz data, after the Chapter 3 Cayley coordinate change, into
the upper-half-plane raw outside Herglotz data used by the Pick representation bridge.
-/
def unitIntervalPickHerglotzUpperRawOutsideData_of_diskHerglotzData
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    (data : UnitDiskCaratheodoryHerglotzData (pickToDiskCaratheodory pick)) :
    UnitIntervalPickHerglotzUpperRawOutsideData f where
  pick := pick
  constant := data.constant
  slope := data.slope
  outsideMeasure := data.outsideMeasure
  outside_support := data.outside_support
  upper_formula := by
    intro z hz
    let A : ℂ := (data.constant : ℂ) + ((data.slope : ℝ) : ℂ) * z
    let R : ℂ :=
      ∫ y : ℝ, unitIntervalHerglotzRawKernel z y
        ∂(data.outsideMeasure : Measure ℝ)
    have hform := data.formula hz
    have hbridge := data.disk_integral_eq_raw hz
    have hinv :
        diskToUpperCayley (upperToDiskCayley z) = z :=
      diskToUpperCayley_upperToDiskCayley
        (upperToDiskCayley_den_ne_zero_of_im_pos hz)
    have hmul :
        -Complex.I * pick.F z = -Complex.I * (A + R) := by
      simpa [pickToDiskCaratheodory, hinv, A, R, hbridge, mul_add] using hform
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
    simpa [A, R] using hcancel

/-- Producer interface for the disk Herglotz representation in Cayley coordinates. -/
structure UnitDiskCaratheodoryHerglotzProducer where
  produce :
    ∀ {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f),
      UnitDiskCaratheodoryHerglotzData (pickToDiskCaratheodory pick)

/-- Disk-side Herglotz producer gives the upper raw outside Herglotz producer. -/
def unitIntervalPickHerglotzUpperRawOutsideProducer_of_diskHerglotzProducer
    (producer : UnitDiskCaratheodoryHerglotzProducer) :
    UnitIntervalPickHerglotzUpperRawOutsideProducer where
  produce := by
    intro f pick
    exact unitIntervalPickHerglotzUpperRawOutsideData_of_diskHerglotzData pick
      (producer.produce pick)

/-- Reverse Theorem 3.8 from Pick extension, assuming the disk Herglotz producer. -/
def integralRepOnUnitInterval_of_pickExtension_of_diskHerglotzProducer
    (producer : UnitDiskCaratheodoryHerglotzProducer)
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_upperRawHerglotzOutsideProducer
    (unitIntervalPickHerglotzUpperRawOutsideProducer_of_diskHerglotzProducer producer) pick

end

end Quantum.TraceInequality.Loewner
