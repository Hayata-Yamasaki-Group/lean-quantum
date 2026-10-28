/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo.Forward

/-!
# Transform operations for positive-ray Kubo--Ando means

Source correspondence: half-line representation theory of Kubo--Ando means.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-! ### Transform Operations on Positive-Ray Means -/
/-- Open-ray transpose transform `x ↦ x h(x⁻¹)`.

This is a function-level version used to state the algebraic core of Hiai
Proposition 2.32. Endpoint completion on `[0,∞)` is handled by
`positiveRayKuboAndoTransposeOfRep`, which uses the representation data. -/
def positiveRayKuboAndoTransposeTransform (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => x * h x⁻¹

/-- Open-ray adjoint transform `x ↦ h(x⁻¹)⁻¹`.

The intended domain is `(0,∞)`. Positivity hypotheses are attached to the
theorems that use this transform, rather than built into the total function. -/
def positiveRayKuboAndoAdjointTransform (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (h x⁻¹)⁻¹

/-- Open-ray dual transform `x ↦ x / h(x)`. -/
def positiveRayKuboAndoDualTransform (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => x / h x

/-- The adjoint transform is involutive on the positive ray. -/
theorem positiveRayKuboAndoAdjointTransform_involutive
    {h : ℝ → ℝ} {x : ℝ} (_hx : 0 < x) (_hpos : 0 < h x) :
    positiveRayKuboAndoAdjointTransform
        (positiveRayKuboAndoAdjointTransform h) x = h x := by
  simp [positiveRayKuboAndoAdjointTransform]

/-- The dual transform is the adjoint of the transpose transform on the positive ray. -/
theorem positiveRayKuboAndoDualTransform_eq_adjoint_transpose
    {h : ℝ → ℝ} {x : ℝ} (_hx : 0 < x) (_hpos : 0 < h x) :
    positiveRayKuboAndoDualTransform h x =
      positiveRayKuboAndoAdjointTransform
        (positiveRayKuboAndoTransposeTransform h) x := by
  simp [positiveRayKuboAndoDualTransform, positiveRayKuboAndoAdjointTransform,
    positiveRayKuboAndoTransposeTransform, div_eq_mul_inv, mul_comm]

/-! ### Transpose Measures and Representation Closure -/
private def positiveRayKuboAndoTransposeParam (t : ℝ) : ℝ :=
  t⁻¹

private theorem measurable_positiveRayKuboAndoTransposeParam :
    Measurable positiveRayKuboAndoTransposeParam := by
  unfold positiveRayKuboAndoTransposeParam
  measurability

private theorem positiveRayKuboAndoTransposeParam_mem_Ioi_of_pos
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayKuboAndoTransposeParam t ∈ Set.Ioi (0 : ℝ) := by
  have htpos : 0 < t := by simpa using ht
  unfold positiveRayKuboAndoTransposeParam
  exact inv_pos.mpr htpos

private def positiveRayKuboAndoTransposeMeasure (ν : FiniteMeasure ℝ) :
    FiniteMeasure ℝ :=
  ν.map positiveRayKuboAndoTransposeParam

private theorem positiveRayKuboAndoTransposeMeasure_support_Ioi
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ)
      (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Ioi (0 : ℝ))ᶜ) := measurableSet_Ioi.compl
  calc
    (positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ)
        (Set.Ioi (0 : ℝ))ᶜ =
        (rep.ν : Measure ℝ)
          (positiveRayKuboAndoTransposeParam ⁻¹' (Set.Ioi (0 : ℝ))ᶜ) := by
          rw [positiveRayKuboAndoTransposeMeasure, FiniteMeasure.toMeasure_map,
            Measure.map_apply measurable_positiveRayKuboAndoTransposeParam hS]
    _ = 0 := by
          rw [measure_eq_zero_iff_ae_notMem]
          filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht hbad
          exact hbad (positiveRayKuboAndoTransposeParam_mem_Ioi_of_pos ht)

private theorem positiveRayKuboAndoKernel_transpose_eq
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayKuboAndoKernel x (positiveRayKuboAndoTransposeParam t) =
      x * positiveRayKuboAndoKernel x⁻¹ t := by
  have hxpos : 0 < x := by simpa using hx
  have htpos : 0 < t := by simpa using ht
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have htne : t ≠ 0 := ne_of_gt htpos
  have hden1 : x + t⁻¹ ≠ 0 := by
    have htinv_pos : 0 < t⁻¹ := inv_pos.mpr htpos
    exact ne_of_gt (by linarith)
  have hden2 : x⁻¹ + t ≠ 0 := by
    have hxinv_pos : 0 < x⁻¹ := inv_pos.mpr hxpos
    exact ne_of_gt (by linarith)
  unfold positiveRayKuboAndoKernel positiveRayKuboAndoTransposeParam
  field_simp [hxne, htne, hden1, hden2]
  ring

private theorem positiveRayKuboAndoTransposeMeasure_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ s : ℝ, positiveRayKuboAndoKernel x s
        ∂(positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ)) =
      x * ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ) := by
  have hmap :
      (∫ s : ℝ, positiveRayKuboAndoKernel x s
          ∂(positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayKuboAndoKernel x (positiveRayKuboAndoTransposeParam t)
          ∂(rep.ν : Measure ℝ) := by
    have hf :
        AEStronglyMeasurable (fun s : ℝ => positiveRayKuboAndoKernel x s)
          (Measure.map positiveRayKuboAndoTransposeParam (rep.ν : Measure ℝ)) := by
      exact (measurable_positiveRayKuboAndoKernel_right x).aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := (rep.ν : Measure ℝ))
        (φ := positiveRayKuboAndoTransposeParam)
        measurable_positiveRayKuboAndoTransposeParam.aemeasurable
        (f := fun s : ℝ => positiveRayKuboAndoKernel x s) hf
    simpa [positiveRayKuboAndoTransposeMeasure] using h
  have hkernel :
      (fun t : ℝ => positiveRayKuboAndoKernel x (positiveRayKuboAndoTransposeParam t))
        =ᵐ[(rep.ν : Measure ℝ)]
        fun t : ℝ => x * positiveRayKuboAndoKernel x⁻¹ t := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayKuboAndoKernel_transpose_eq hx ht
  calc
    (∫ s : ℝ, positiveRayKuboAndoKernel x s
        ∂(positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayKuboAndoKernel x (positiveRayKuboAndoTransposeParam t)
          ∂(rep.ν : Measure ℝ) := hmap
    _ = ∫ t : ℝ, x * positiveRayKuboAndoKernel x⁻¹ t
          ∂(rep.ν : Measure ℝ) := integral_congr_ae hkernel
    _ = x * ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t
          ∂(rep.ν : Measure ℝ) := by
          rw [integral_const_mul]

/--
Endpoint-completed transpose of a Kubo--Ando representation.

For `x > 0` this is `x * h x⁻¹`; at `0` the value is supplied by the
linear coefficient of the representation, as in Hiai Proposition 2.32.
-/
def positiveRayKuboAndoTransposeOfRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) : ℝ → ℝ :=
  fun x => if x = 0 then (rep.b : ℝ) else x * h x⁻¹

/--
The Kubo--Ando representation class is closed under transpose at the
representation level.  The nonnegativity of `h 0` is explicit because it
becomes the new `NNReal` linear coefficient.
-/
noncomputable def positiveRayKuboAndoRep_transpose
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0) :
    PositiveRayKuboAndoRep (positiveRayKuboAndoTransposeOfRep rep) where
  b := ⟨h 0, h0⟩
  ν := positiveRayKuboAndoTransposeMeasure rep.ν
  support := positiveRayKuboAndoTransposeMeasure_support_Ioi rep
  formula := by
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      simp [positiveRayKuboAndoTransposeOfRep, positiveRayKuboAndoKernel]
    · have hxpos : 0 < x := lt_of_le_of_ne' hx hxzero
      have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hxpos
      have hxinv_nonneg : x⁻¹ ∈ Set.Ici (0 : ℝ) := by
        exact le_of_lt (inv_pos.mpr hxpos)
      have hformula := rep.formula hxinv_nonneg
      have hInt := positiveRayKuboAndoTransposeMeasure_integral_kernel rep hxIoi
      have hxmul : x * ((rep.b : ℝ) * x⁻¹) = (rep.b : ℝ) := by
        have hxne : x ≠ 0 := ne_of_gt hxpos
        field_simp [hxne]
      calc
        positiveRayKuboAndoTransposeOfRep rep x = x * h x⁻¹ := by
          simp [positiveRayKuboAndoTransposeOfRep, hxzero]
        _ = x * (h 0 + (rep.b : ℝ) * x⁻¹ +
              ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ)) := by
          rw [hformula]
        _ = (rep.b : ℝ) + h 0 * x +
              x * ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t
                ∂(rep.ν : Measure ℝ) := by
          rw [mul_add, mul_add, hxmul]
          ring
        _ = (rep.b : ℝ) + (⟨h 0, h0⟩ : NNReal) * x +
              ∫ t : ℝ, positiveRayKuboAndoKernel x t
                ∂(positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ) := by
          rw [hInt]
        _ = positiveRayKuboAndoTransposeOfRep rep 0 + (⟨h 0, h0⟩ : NNReal) * x +
              ∫ t : ℝ, positiveRayKuboAndoKernel x t
                ∂(positiveRayKuboAndoTransposeMeasure rep.ν : Measure ℝ) := by
          simp [positiveRayKuboAndoTransposeOfRep]


end

end Loewner
end TraceInequality
end Quantum
