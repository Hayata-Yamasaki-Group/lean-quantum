import Quantum.TraceInequality.Loewner.UpperHalfPlane.PickNevanlinnaCorrespondence

/-!
# Elementary ingredients for Cauer response functions

This file supplies the reflection, measure, denominator, and kernel lemmas used
by the Cauer representation theorem.  It deliberately depends only on the
upper-half-plane Nevanlinna layer.
-/

namespace Quantum.TraceInequality.Loewner.ResponseFunctions

open Set MeasureTheory
open scoped UpperHalfPlane

noncomputable section

/-- Reflection in the imaginary axis preserves the upper half-plane. -/
def upperHalfPlaneReflection (z : ℍ) : ℍ :=
  ⟨-(starRingEnd ℂ) (z : ℂ), by simpa using z.coe_im_pos⟩

@[simp]
theorem coe_upperHalfPlaneReflection (z : ℍ) :
    (upperHalfPlaneReflection z : ℂ) = -(starRingEnd ℂ) (z : ℂ) :=
  rfl

/-- Reflection in the imaginary axis preserves the imaginary part. -/
@[simp]
theorem upperHalfPlaneReflection_im (z : ℍ) :
    (upperHalfPlaneReflection z : ℂ).im = (z : ℂ).im := by
  simp [upperHalfPlaneReflection]

/-- Reflection in the imaginary axis is an involution on the upper half-plane. -/
@[simp]
theorem upperHalfPlaneReflection_involutive (z : ℍ) :
    upperHalfPlaneReflection (upperHalfPlaneReflection z) = z := by
  apply UpperHalfPlane.ext
  simp [upperHalfPlaneReflection]

/-- Positive-real symmetry in the upper-half-plane convention.

This is the identity `N(z)̅ = -N(-z̅)`, written without an auxiliary
extension to the lower half-plane.
-/
def IsPositiveReal (F : ℍ → ℂ) : Prop :=
  ∀ z : ℍ,
    F (upperHalfPlaneReflection z) = -(starRingEnd ℂ) (F z)

theorem isPositiveReal_iff (F : ℍ → ℂ) :
    IsPositiveReal F ↔
      ∀ z : ℍ,
        F (upperHalfPlaneReflection z) = -(starRingEnd ℂ) (F z) :=
  Iff.rfl

/-- Push a finite measure forward by sign reversal. -/
def reflectedFiniteMeasure (ν : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ν.map fun t : ℝ => -t

@[simp]
theorem reflectedFiniteMeasure_toMeasure (ν : FiniteMeasure ℝ) :
    (reflectedFiniteMeasure ν : Measure ℝ) =
      Measure.map (fun t : ℝ => -t) (ν : Measure ℝ) :=
  rfl

/-- Reversing the sign twice recovers a finite measure. -/
@[simp]
theorem reflectedFiniteMeasure_reflectedFiniteMeasure
    (ν : FiniteMeasure ℝ) :
    reflectedFiniteMeasure (reflectedFiniteMeasure ν) = ν := by
  apply FiniteMeasure.toMeasure_injective
  change Measure.map (fun t : ℝ => -t)
      (Measure.map (fun t : ℝ => -t) (ν : Measure ℝ)) =
    (ν : Measure ℝ)
  rw [Measure.map_map measurable_neg measurable_neg]
  simp

/-- Average a finite measure with its reflection. -/
def symmetrizedFiniteMeasure (ν : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  (2 : NNReal)⁻¹ • (ν + reflectedFiniteMeasure ν)

/-- The averaged finite measure is invariant under sign reversal. -/
@[simp]
theorem reflectedFiniteMeasure_symmetrizedFiniteMeasure
    (ν : FiniteMeasure ℝ) :
    reflectedFiniteMeasure (symmetrizedFiniteMeasure ν) =
      symmetrizedFiniteMeasure ν := by
  unfold symmetrizedFiniteMeasure
  change (((2 : NNReal)⁻¹ • (ν + reflectedFiniteMeasure ν)).map
      (fun t : ℝ => -t)) =
    (2 : NNReal)⁻¹ • (ν + reflectedFiniteMeasure ν)
  rw [FiniteMeasure.map_smul, FiniteMeasure.map_add measurable_neg]
  change (2 : NNReal)⁻¹ •
      (reflectedFiniteMeasure ν +
        reflectedFiniteMeasure (reflectedFiniteMeasure ν)) =
    (2 : NNReal)⁻¹ • (ν + reflectedFiniteMeasure ν)
  rw [reflectedFiniteMeasure_reflectedFiniteMeasure]
  rw [add_comm]

/-- A denominator of the form `t + z` does not vanish in the upper half-plane. -/
theorem cauer_add_den_ne_zero (t : ℝ) (z : ℍ) :
    ((t : ℂ) + (z : ℂ)) ≠ 0 := by
  have h := Loewner.nevanlinna_den_ne_zero (-t) z
  intro hzero
  apply h
  calc
    ((-t : ℝ) : ℂ) - (z : ℂ) =
        -((t : ℂ) + (z : ℂ)) := by
          push_cast
          ring
    _ = 0 := by rw [hzero]; simp

/-- The quadratic Cauer denominator does not vanish in the upper half-plane. -/
theorem cauer_sq_den_ne_zero (t : ℝ) (z : ℍ) :
    ((t : ℂ) ^ (2 : ℕ) - (z : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  rw [sq_sub_sq]
  exact mul_ne_zero (cauer_add_den_ne_zero t z)
    (Loewner.nevanlinna_den_ne_zero t z)

/-- The even Cauer kernel `z(1+t²)/(t²-z²)`. -/
def cauerKernel (t : ℝ) (z : ℍ) : ℂ :=
  (z : ℂ) * (1 + (t : ℂ) ^ (2 : ℕ)) /
    ((t : ℂ) ^ (2 : ℕ) - (z : ℂ) ^ (2 : ℕ))

/-- The explicit Cauer kernel identity. -/
theorem cauerKernel_eq_half_difference (t : ℝ) (z : ℍ) :
    cauerKernel t z =
      (2 : ℂ)⁻¹ *
        ((1 + (t : ℂ) * (z : ℂ)) / ((t : ℂ) - (z : ℂ)) -
          (1 - (t : ℂ) * (z : ℂ)) / ((t : ℂ) + (z : ℂ))) := by
  have hminus := Loewner.nevanlinna_den_ne_zero t z
  have hplus := cauer_add_den_ne_zero t z
  have hsq := cauer_sq_den_ne_zero t z
  unfold cauerKernel
  field_simp [hminus, hplus, hsq]
  ring

/-- The Cauer kernel is the average of a Nevanlinna kernel and its reflection. -/
theorem cauerKernel_eq_half_add_nevanlinnaKernel (t : ℝ) (z : ℍ) :
    cauerKernel t z =
      (2 : ℂ)⁻¹ *
        (Loewner.nevanlinnaKernel t z + Loewner.nevanlinnaKernel (-t) z) := by
  rw [cauerKernel_eq_half_difference]
  unfold Loewner.nevanlinnaKernel
  congr 1
  push_cast
  have hminus := Loewner.nevanlinna_den_ne_zero t z
  have hplus := cauer_add_den_ne_zero t z
  have hnegplus : (-(t : ℂ) - (z : ℂ)) ≠ 0 := by
    rw [show -(t : ℂ) - (z : ℂ) = -((t : ℂ) + (z : ℂ)) by ring]
    exact neg_ne_zero.mpr hplus
  field_simp [hminus, hplus, hnegplus]
  ring

/-- The reflected Nevanlinna kernel is integrable against every finite measure. -/
theorem reflected_nevanlinnaKernel_integrable
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    Integrable (fun t : ℝ => Loewner.nevanlinnaKernel (-t) z)
      (ν : Measure ℝ) := by
  have h := Loewner.nevanlinnaKernel_integrable (reflectedFiniteMeasure ν) z
  have hcomp := h.comp_measurable measurable_neg
  simpa only [reflectedFiniteMeasure_toMeasure, Function.comp_apply, neg_neg]
    using hcomp

/-- The Cauer kernel is integrable against every finite measure. -/
theorem cauerKernel_integrable
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    Integrable (fun t : ℝ => cauerKernel t z) (ν : Measure ℝ) := by
  have hadd :=
    (Loewner.nevanlinnaKernel_integrable ν z).add
      (reflected_nevanlinnaKernel_integrable ν z)
  have hmul := hadd.const_mul (2 : ℂ)⁻¹
  refine hmul.congr ?_
  exact ae_of_all _ fun t => (cauerKernel_eq_half_add_nevanlinnaKernel t z).symm

end

end Quantum.TraceInequality.Loewner.ResponseFunctions
