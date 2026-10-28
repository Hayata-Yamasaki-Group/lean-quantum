/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.ReciprocalTransport

/-!
# Positive-ray decreasing representations: resolvent and Kubo-Ando transport

This module is the representation-measure stage of the Simon-style half-line
decreasing-function theory, transporting reciprocal Kubo--Ando and convex
representations back to finite resolvent representations.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Reciprocal transport of representation measures -/

private def positiveRayReciprocalParam (t : ℝ) : ℝ :=
  t⁻¹

private theorem measurable_positiveRayReciprocalParam :
    Measurable positiveRayReciprocalParam := by
  unfold positiveRayReciprocalParam
  measurability

private theorem positiveRayReciprocalParam_mem_Ici_of_pos
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayReciprocalParam t ∈ Set.Ici (0 : ℝ) := by
  have htpos : 0 < t := by simpa using ht
  unfold positiveRayReciprocalParam
  exact le_of_lt (inv_pos.mpr htpos)

private theorem positiveRayReciprocalParam_mem_Ioi_of_pos
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayReciprocalParam t ∈ Set.Ioi (0 : ℝ) := by
  have htpos : 0 < t := by simpa using ht
  unfold positiveRayReciprocalParam
  exact inv_pos.mpr htpos

private def positiveRayResolventDiracZero : FiniteMeasure ℝ :=
  ⟨Measure.dirac (0 : ℝ), inferInstance⟩

private theorem positiveRayResolventDiracZero_support_Ici :
    (positiveRayResolventDiracZero : Measure ℝ)
      (Set.Ici (0 : ℝ))ᶜ = 0 := by
  simp [positiveRayResolventDiracZero]

private theorem positiveRayResolventDiracZero_Iio_zero :
    (positiveRayResolventDiracZero : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
  simpa using positiveRayResolventDiracZero_support_Ici

private def positiveRayResolventPushforward (ν : FiniteMeasure ℝ) :
    FiniteMeasure ℝ :=
  ν.map positiveRayReciprocalParam

private theorem positiveRayResolventPushforward_support_Ici
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (positiveRayResolventPushforward rep.ν : Measure ℝ)
      (Set.Ici (0 : ℝ))ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Ici (0 : ℝ))ᶜ) :=
    isClosed_Ici.measurableSet.compl
  calc
    (positiveRayResolventPushforward rep.ν : Measure ℝ)
        (Set.Ici (0 : ℝ))ᶜ =
        (rep.ν : Measure ℝ)
          (positiveRayReciprocalParam ⁻¹' (Set.Ici (0 : ℝ))ᶜ) := by
          rw [positiveRayResolventPushforward, FiniteMeasure.toMeasure_map,
            Measure.map_apply measurable_positiveRayReciprocalParam hS]
    _ = 0 := by
          rw [measure_eq_zero_iff_ae_notMem]
          filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht hbad
          exact hbad (positiveRayReciprocalParam_mem_Ici_of_pos ht)

private def positiveRayResolventMeasure
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    FiniteMeasure ℝ :=
  (rep.b • positiveRayResolventDiracZero) +
    positiveRayResolventPushforward rep.ν

private theorem positiveRayResolventMeasure_support_Ici
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (positiveRayResolventMeasure rep : Measure ℝ)
      (Set.Ici (0 : ℝ))ᶜ = 0 := by
  have hpush :
      (positiveRayResolventPushforward rep.ν : Measure ℝ)
        (Set.Iio (0 : ℝ)) = 0 := by
    simpa using positiveRayResolventPushforward_support_Ici rep
  simp [positiveRayResolventMeasure, positiveRayResolventDiracZero_Iio_zero, hpush]

private theorem positiveRayResolventKernel_zero
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    positiveRayResolventKernel x 0 = x⁻¹ := by
  have hxpos : 0 < x := by simpa using hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  unfold positiveRayResolventKernel
  field_simp [hxne]
  ring

private theorem positiveRayResolventKernel_nonneg_and_le_const
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ici (0 : ℝ)) :
    0 ≤ positiveRayResolventKernel x t ∧
      positiveRayResolventKernel x t ≤ 1 + x⁻¹ := by
  have hxpos : 0 < x := by simpa using hx
  have ht0 : 0 ≤ t := by simpa using ht
  have hden_pos : 0 < x + t := by linarith
  constructor
  · unfold positiveRayResolventKernel
    positivity
  · have hnum_le : 1 + t ≤ (1 + x⁻¹) * (x + t) := by
      have hxinvg0 : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr hxpos)
      have hrest : 0 ≤ x + x⁻¹ * t :=
        add_nonneg (le_of_lt hxpos) (mul_nonneg hxinvg0 ht0)
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have heq : (1 + x⁻¹) * (x + t) = 1 + t + (x + x⁻¹ * t) := by
        field_simp [hxne]
        ring
      rw [heq]
      linarith
    unfold positiveRayResolventKernel
    rw [div_le_iff₀ hden_pos]
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hnum_le

private theorem positiveRayResolventKernel_norm_le_const
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ici (0 : ℝ)) :
    ‖positiveRayResolventKernel x t‖ ≤ 1 + x⁻¹ := by
  have hbound := positiveRayResolventKernel_nonneg_and_le_const hx ht
  rw [Real.norm_of_nonneg hbound.1]
  exact hbound.2

private theorem positiveRayResolventKernel_integrable_of_support_Ici
    (m : FiniteMeasure ℝ)
    (hm : (m : Measure ℝ) (Set.Ici (0 : ℝ))ᶜ = 0)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => positiveRayResolventKernel x t)
      (m : Measure ℝ) := by
  refine Integrable.of_bound
    (measurable_positiveRayResolventKernel_right x).aestronglyMeasurable
    (1 + x⁻¹) ?_
  have hae : ∀ᵐ t ∂(m : Measure ℝ), t ∈ Set.Ici (0 : ℝ) := by
    rw [ae_iff]
    exact hm
  filter_upwards [hae] with t ht
  have hxpos : 0 < x := by simpa using hx
  have hconst_nonneg : 0 ≤ 1 + x⁻¹ := by positivity
  simpa [Real.norm_of_nonneg hconst_nonneg] using
    positiveRayResolventKernel_norm_le_const hx ht

private theorem positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_sq_mul_resolvent
    (x t : ℝ) :
    positiveRayOperatorConvexFiniteRightDerivativeKernel x t =
      x ^ 2 * positiveRayResolventKernel x t := by
  unfold positiveRayOperatorConvexFiniteRightDerivativeKernel positiveRayResolventKernel
  ring

private theorem positiveRayOperatorConvexFiniteRightDerivativeKernel_integral_eq_resolvent
    (ν : FiniteMeasure ℝ) (x : ℝ) :
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
        ∂(ν : Measure ℝ)) =
      x ^ 2 * ∫ t : ℝ, positiveRayResolventKernel x t ∂(ν : Measure ℝ) := by
  calc
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
        ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, x ^ 2 * positiveRayResolventKernel x t
          ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_sq_mul_resolvent x t
    _ = x ^ 2 * ∫ t : ℝ, positiveRayResolventKernel x t
        ∂(ν : Measure ℝ) := by
          rw [integral_const_mul]

private theorem positiveRayOperatorConvexFiniteRightDerivativeRep_support_Ici
    {h₀ : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepFiniteRightDerivative h₀) :
    (rep.ν : Measure ℝ) (Set.Ici (0 : ℝ))ᶜ = 0 := by
  refine measure_mono_null ?_ rep.support
  intro t ht hpos
  have ht0 : 0 ≤ t := le_of_lt (by simpa using hpos)
  exact ht ht0

/-! ### Resolvent representations as Kubo-Ando witnesses -/

/-- A decreasing resolvent representation is nonnegative on `(0,∞)`. -/
theorem PositiveRayOperatorMonotoneDecreasingRep.nonneg_on_Ioi
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x := by
  intro x hx
  rw [rep.formula hx]
  refine add_nonneg (NNReal.coe_nonneg _) ?_
  have hae : ∀ᵐ t ∂(rep.μ : Measure ℝ), t ∈ Set.Ici (0 : ℝ) := by
    rw [ae_iff]
    exact rep.support
  refine integral_nonneg_of_ae ?_
  filter_upwards [hae] with t ht
  exact (positiveRayResolventKernel_nonneg_and_le_const hx ht).1

/-- Reciprocal witness attached to a decreasing resolvent representation. -/
noncomputable def positiveRayKuboAndoOfOperatorMonotoneDecreasingRep
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) : ℝ → ℝ :=
  fun y => if y = 0 then (rep.a : ℝ) else g y⁻¹

private noncomputable def positiveRayKuboAndoMeasureOfResolvent
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    FiniteMeasure ℝ :=
  (rep.μ.restrict (Set.Ioi (0 : ℝ))).map positiveRayReciprocalParam

private theorem positiveRayKuboAndoMeasureOfResolvent_support_Ioi
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    (positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ)
      (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Ioi (0 : ℝ))ᶜ) := measurableSet_Ioi.compl
  have hpre :
      MeasurableSet
        (positiveRayReciprocalParam ⁻¹' (Set.Ioi (0 : ℝ))ᶜ) :=
    measurable_positiveRayReciprocalParam hS
  have hempty :
      positiveRayReciprocalParam ⁻¹' (Set.Ioi (0 : ℝ))ᶜ ∩
          Set.Ioi (0 : ℝ) = ∅ := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨htbad, htpos_mem⟩
      have htpos : 0 < t := by simpa using htpos_mem
      have hrecip_pos :
          positiveRayReciprocalParam t ∈ Set.Ioi (0 : ℝ) := by
        exact positiveRayReciprocalParam_mem_Ioi_of_pos htpos_mem
      exact False.elim (htbad hrecip_pos)
    · intro ht
      cases ht
  calc
    (positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ)
        (Set.Ioi (0 : ℝ))ᶜ =
        (rep.μ.restrict (Set.Ioi (0 : ℝ)) : Measure ℝ)
          (positiveRayReciprocalParam ⁻¹' (Set.Ioi (0 : ℝ))ᶜ) := by
          rw [positiveRayKuboAndoMeasureOfResolvent, FiniteMeasure.toMeasure_map,
            Measure.map_apply measurable_positiveRayReciprocalParam hS]
    _ = (rep.μ : Measure ℝ)
        (positiveRayReciprocalParam ⁻¹' (Set.Ioi (0 : ℝ))ᶜ ∩
          Set.Ioi (0 : ℝ)) := by
          rw [FiniteMeasure.restrict_measure_eq, Measure.restrict_apply hpre]
    _ = 0 := by
          rw [hempty, measure_empty]

private theorem positiveRayResolventKernel_inv_eq_kubo_reciprocal
    {y t : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayResolventKernel y⁻¹ t =
      positiveRayKuboAndoKernel y (positiveRayReciprocalParam t) := by
  have hypos : 0 < y := by simpa using hy
  have htpos : 0 < t := by simpa using ht
  have hyne : y ≠ 0 := ne_of_gt hypos
  have htne : t ≠ 0 := ne_of_gt htpos
  have hden1 : y⁻¹ + t ≠ 0 := by
    have hyinv_pos : 0 < y⁻¹ := inv_pos.mpr hypos
    exact ne_of_gt (by linarith)
  have hden2 : y + t⁻¹ ≠ 0 := by
    have htinv_pos : 0 < t⁻¹ := inv_pos.mpr htpos
    exact ne_of_gt (by linarith)
  unfold positiveRayResolventKernel positiveRayKuboAndoKernel
    positiveRayReciprocalParam
  field_simp [hyne, htne, hden1, hden2]
  ring

private theorem positiveRayResolventKernel_inv_zero
    {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) :
    positiveRayResolventKernel y⁻¹ 0 = y := by
  have hypos : 0 < y := by simpa using hy
  have hyinv_pos : 0 < y⁻¹ := inv_pos.mpr hypos
  have h := positiveRayResolventKernel_zero
    (x := y⁻¹) (by simpa using hyinv_pos)
  simpa [inv_inv] using h

private theorem positiveRayResolvent_measure_split
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    (rep.μ : Measure ℝ).restrict ({0} : Set ℝ) +
        (rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ)) =
      (rep.μ : Measure ℝ) := by
  have hIci_self :
      (rep.μ : Measure ℝ).restrict (Set.Ici (0 : ℝ)) =
        (rep.μ : Measure ℝ) := by
    have hae : ∀ᵐ t ∂(rep.μ : Measure ℝ), t ∈ Set.Ici (0 : ℝ) := by
      rw [ae_iff]
      exact rep.support
    exact Measure.restrict_eq_self_of_ae_mem hae
  have hIci :
      Set.Ici (0 : ℝ) = ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · intro ht
      rcases lt_or_eq_of_le (by simpa using ht) with htpos | rfl
      · exact Or.inr (by simpa using htpos)
      · exact Or.inl (by simp)
    · intro ht
      rcases ht with ht0 | htpos
      · rcases ht0 with rfl
        simp
      · exact le_of_lt (by simpa using htpos)
  have hdisj : Disjoint ({0} : Set ℝ) (Set.Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro t ht0 htpos
    rcases ht0 with rfl
    change (0 : ℝ) < 0 at htpos
    exact lt_irrefl (0 : ℝ) htpos
  calc
    (rep.μ : Measure ℝ).restrict ({0} : Set ℝ) +
        (rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ)) =
        (rep.μ : Measure ℝ).restrict
          (({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ)) := by
          rw [Measure.restrict_union hdisj measurableSet_Ioi]
    _ = (rep.μ : Measure ℝ).restrict (Set.Ici (0 : ℝ)) := by
          rw [← hIci]
    _ = (rep.μ : Measure ℝ) := hIci_self

private theorem positiveRayResolventRestrictSingleton_integral_kernel
    (μ : FiniteMeasure ℝ) {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
        ∂((μ : Measure ℝ).restrict ({0} : Set ℝ))) =
      (μ {0} : ℝ) * y := by
  rw [MeasureTheory.integral_singleton]
  rw [positiveRayResolventKernel_inv_zero hy]
  simp [smul_eq_mul]

private theorem positiveRayKuboAndoMeasureOfResolvent_integral_kernel
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g)
    {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) :
    (∫ s : ℝ, positiveRayKuboAndoKernel y s
        ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ)) =
      ∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
        ∂((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
  have hmeas_kernel :
      Measurable fun s : ℝ => positiveRayKuboAndoKernel y s := by
    unfold positiveRayKuboAndoKernel
    measurability
  have hmap :
      (∫ s : ℝ, positiveRayKuboAndoKernel y s
          ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ)) =
        ∫ t : ℝ, positiveRayKuboAndoKernel y
          (positiveRayReciprocalParam t)
          ∂((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have hf :
        AEStronglyMeasurable (fun s : ℝ => positiveRayKuboAndoKernel y s)
          (Measure.map positiveRayReciprocalParam
            ((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :=
      hmeas_kernel.aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map
        (μ := (rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
        (φ := positiveRayReciprocalParam)
        measurable_positiveRayReciprocalParam.aemeasurable
        (f := fun s : ℝ => positiveRayKuboAndoKernel y s) hf
    simpa [positiveRayKuboAndoMeasureOfResolvent] using h
  have hkernel :
      (fun t : ℝ =>
          positiveRayKuboAndoKernel y (positiveRayReciprocalParam t))
        =ᵐ[((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))]
        fun t : ℝ => positiveRayResolventKernel y⁻¹ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (positiveRayResolventKernel_inv_eq_kubo_reciprocal hy ht).symm
  calc
    (∫ s : ℝ, positiveRayKuboAndoKernel y s
        ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ)) =
        ∫ t : ℝ, positiveRayKuboAndoKernel y
          (positiveRayReciprocalParam t)
          ∂((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := hmap
    _ = ∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
        ∂((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
        integral_congr_ae hkernel

private theorem positiveRayResolvent_integral_eq_atom_add_kubo
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g)
    {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
        ∂(rep.μ : Measure ℝ)) =
      (rep.μ {0} : ℝ) * y +
        ∫ s : ℝ, positiveRayKuboAndoKernel y s
          ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ) := by
  have hypos : 0 < y := by simpa using hy
  have hyinv_pos : 0 < y⁻¹ := inv_pos.mpr hypos
  have hxin : y⁻¹ ∈ Set.Ioi (0 : ℝ) := by simpa using hyinv_pos
  have hInt :
      Integrable (fun t : ℝ => positiveRayResolventKernel y⁻¹ t)
        (rep.μ : Measure ℝ) :=
    positiveRayResolventKernel_integrable_of_support_Ici rep.μ
      rep.support hxin
  have hInt0 :
      Integrable (fun t : ℝ => positiveRayResolventKernel y⁻¹ t)
        ((rep.μ : Measure ℝ).restrict ({0} : Set ℝ)) :=
    hInt.mono_measure Measure.restrict_le_self
  have hIntPos :
      Integrable (fun t : ℝ => positiveRayResolventKernel y⁻¹ t)
        ((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) :=
    hInt.mono_measure Measure.restrict_le_self
  calc
    (∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
        ∂(rep.μ : Measure ℝ)) =
        ∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
          ∂((rep.μ : Measure ℝ).restrict ({0} : Set ℝ) +
              (rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
          rw [positiveRayResolvent_measure_split rep]
    _ = (∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
            ∂((rep.μ : Measure ℝ).restrict ({0} : Set ℝ))) +
          ∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
            ∂((rep.μ : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
          exact integral_add_measure hInt0 hIntPos
    _ = (rep.μ {0} : ℝ) * y +
        ∫ s : ℝ, positiveRayKuboAndoKernel y s
          ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ) := by
          rw [positiveRayResolventRestrictSingleton_integral_kernel rep.μ hy,
            positiveRayKuboAndoMeasureOfResolvent_integral_kernel rep hy]

/--
The reciprocal function associated to a decreasing resolvent representation has
a Kubo--Ando finite-measure representation.
-/
noncomputable def positiveRayKuboAndoRep_of_operatorMonotoneDecreasingRep
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    PositiveRayKuboAndoRep
      (positiveRayKuboAndoOfOperatorMonotoneDecreasingRep rep) where
  b := rep.μ {0}
  ν := positiveRayKuboAndoMeasureOfResolvent rep
  support := positiveRayKuboAndoMeasureOfResolvent_support_Ioi rep
  formula := by
    intro y hy
    rcases eq_or_lt_of_le (by simpa using hy) with rfl | hypos
    · have hzero_kernel :
          (fun s : ℝ => positiveRayKuboAndoKernel 0 s) =
            fun _s : ℝ => (0 : ℝ) := by
        funext s
        simp [positiveRayKuboAndoKernel]
      rw [hzero_kernel, integral_zero]
      simp [positiveRayKuboAndoOfOperatorMonotoneDecreasingRep]
    · have hyIoi : y ∈ Set.Ioi (0 : ℝ) := by simpa using hypos
      have hyinv_pos : 0 < y⁻¹ := inv_pos.mpr hypos
      have hyinv_Ioi : y⁻¹ ∈ Set.Ioi (0 : ℝ) := by simpa using hyinv_pos
      have hformula := rep.formula hyinv_Ioi
      have hintegral :=
        positiveRayResolvent_integral_eq_atom_add_kubo rep hyIoi
      calc
        positiveRayKuboAndoOfOperatorMonotoneDecreasingRep rep y =
            g y⁻¹ := by
              simp [positiveRayKuboAndoOfOperatorMonotoneDecreasingRep,
                ne_of_gt hypos]
        _ = (rep.a : ℝ) +
            ∫ t : ℝ, positiveRayResolventKernel y⁻¹ t
              ∂(rep.μ : Measure ℝ) := hformula
        _ = positiveRayKuboAndoOfOperatorMonotoneDecreasingRep rep 0 +
            (rep.μ {0} : ℝ) * y +
              ∫ s : ℝ, positiveRayKuboAndoKernel y s
                ∂(positiveRayKuboAndoMeasureOfResolvent rep : Measure ℝ) := by
              rw [hintegral]
              simp [positiveRayKuboAndoOfOperatorMonotoneDecreasingRep,
                add_assoc]

/-! ### Kubo-Ando and convex representations back to resolvents -/

private theorem positiveRayResolventKernel_eq_kubo_inverse
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayResolventKernel x (positiveRayReciprocalParam t) =
      positiveRayKuboAndoKernel x⁻¹ t := by
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
  unfold positiveRayResolventKernel positiveRayReciprocalParam positiveRayKuboAndoKernel
  field_simp [hxne, htne, hden1, hden2]
  ring

private theorem positiveRayResolventPushforward_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ s : ℝ, positiveRayResolventKernel x s
        ∂(positiveRayResolventPushforward rep.ν : Measure ℝ)) =
      ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ) := by
  have hmap :
      (∫ s : ℝ, positiveRayResolventKernel x s
          ∂(positiveRayResolventPushforward rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayResolventKernel x (positiveRayReciprocalParam t)
          ∂(rep.ν : Measure ℝ) := by
    have hf :
        AEStronglyMeasurable (fun s : ℝ => positiveRayResolventKernel x s)
          (Measure.map positiveRayReciprocalParam (rep.ν : Measure ℝ)) := by
      exact (measurable_positiveRayResolventKernel_right x).aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := (rep.ν : Measure ℝ))
        (φ := positiveRayReciprocalParam)
        measurable_positiveRayReciprocalParam.aemeasurable
        (f := fun s : ℝ => positiveRayResolventKernel x s) hf
    simpa [positiveRayResolventPushforward] using h
  have hkernel :
      (fun t : ℝ => positiveRayResolventKernel x (positiveRayReciprocalParam t))
        =ᵐ[(rep.ν : Measure ℝ)]
        fun t : ℝ => positiveRayKuboAndoKernel x⁻¹ t := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayResolventKernel_eq_kubo_inverse hx ht
  calc
    (∫ s : ℝ, positiveRayResolventKernel x s
        ∂(positiveRayResolventPushforward rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayResolventKernel x (positiveRayReciprocalParam t)
          ∂(rep.ν : Measure ℝ) := hmap
    _ = ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ) :=
        integral_congr_ae hkernel

private theorem positiveRayResolventDiracZero_integral_kernel
    (c : ℝ≥0) {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayResolventKernel x t
        ∂(c • positiveRayResolventDiracZero : FiniteMeasure ℝ)) =
      (c : ℝ) * x⁻¹ := by
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  change (c : ℝ≥0) •
      (∫ t : ℝ, positiveRayResolventKernel x t ∂Measure.dirac (0 : ℝ)) =
    (c : ℝ) * x⁻¹
  rw [MeasureTheory.integral_dirac]
  simp [positiveRayResolventKernel_zero hx, NNReal.smul_def]

/--
Divide a finite-right-derivative representation of `h₀ = x ^ 2 * g` by `x ^ 2`.

The finite-right-derivative structure stores its linear coefficient as a real
number, so the nonnegativity of this coefficient is an explicit hypothesis.
-/
noncomputable def positiveRayOperatorMonotoneDecreasingRep_of_xsq_finiteRightDerivativeRep
    {g h₀ : ℝ → ℝ}
    (hxsq : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → h₀ x = x ^ 2 * g x)
    (hzero : h₀ 0 = 0)
    (rep : PositiveRayOperatorConvexRepFiniteRightDerivative h₀)
    (ha : 0 ≤ rep.a) :
    PositiveRayOperatorMonotoneDecreasingRep g where
  a := rep.b
  μ := (Real.toNNReal rep.a • positiveRayResolventDiracZero) + rep.ν
  support := by
    have hν := positiveRayOperatorConvexFiniteRightDerivativeRep_support_Ici rep
    have hνIio : (rep.ν : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
      simpa using hν
    have hdirac :
        (((Real.toNNReal rep.a • positiveRayResolventDiracZero) : FiniteMeasure ℝ) :
          Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
      rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply,
        positiveRayResolventDiracZero_Iio_zero]
      simp
    rw [show (Set.Ici (0 : ℝ))ᶜ = Set.Iio (0 : ℝ) by ext t; simp]
    rw [FiniteMeasure.toMeasure_add, Measure.add_apply, hdirac, hνIio]
    simp
  formula := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxIci : x ∈ Set.Ici (0 : ℝ) := le_of_lt hxpos
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hν := positiveRayOperatorConvexFiniteRightDerivativeRep_support_Ici rep
    have hInt0 :
        Integrable (fun t : ℝ => positiveRayResolventKernel x t)
          (Real.toNNReal rep.a • positiveRayResolventDiracZero : FiniteMeasure ℝ) :=
      positiveRayResolventKernel_integrable_of_support_Ici
        (Real.toNNReal rep.a • positiveRayResolventDiracZero)
        (by simp [positiveRayResolventDiracZero_Iio_zero]) hx
    have hIntν :
        Integrable (fun t : ℝ => positiveRayResolventKernel x t)
          (rep.ν : Measure ℝ) :=
      positiveRayResolventKernel_integrable_of_support_Ici rep.ν hν hx
    have hμ_int :
        (∫ t : ℝ, positiveRayResolventKernel x t
            ∂(((Real.toNNReal rep.a • positiveRayResolventDiracZero) + rep.ν) :
                FiniteMeasure ℝ)) =
          rep.a * x⁻¹ +
            ∫ t : ℝ, positiveRayResolventKernel x t ∂(rep.ν : Measure ℝ) := by
      calc
        (∫ t : ℝ, positiveRayResolventKernel x t
            ∂(((Real.toNNReal rep.a • positiveRayResolventDiracZero) + rep.ν) :
                FiniteMeasure ℝ)) =
            (∫ t : ℝ, positiveRayResolventKernel x t
                ∂(Real.toNNReal rep.a • positiveRayResolventDiracZero :
                    FiniteMeasure ℝ)) +
              ∫ t : ℝ, positiveRayResolventKernel x t ∂(rep.ν : Measure ℝ) := by
              exact integral_add_measure hInt0 hIntν
        _ = rep.a * x⁻¹ +
            ∫ t : ℝ, positiveRayResolventKernel x t ∂(rep.ν : Measure ℝ) := by
              rw [positiveRayResolventDiracZero_integral_kernel
                (Real.toNNReal rep.a) hx, Real.coe_toNNReal _ ha]
    have hkernel :=
      positiveRayOperatorConvexFiniteRightDerivativeKernel_integral_eq_resolvent
        rep.ν x
    have hsq_formula :
        x ^ 2 * g x =
          rep.a * x + (rep.b : ℝ) * x ^ 2 +
            x ^ 2 * ∫ t : ℝ, positiveRayResolventKernel x t
              ∂(rep.ν : Measure ℝ) := by
      calc
        x ^ 2 * g x = h₀ x := by
          rw [hxsq hx]
        _ = h₀ 0 + rep.a * x + (rep.b : ℝ) * x ^ 2 +
              ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
                ∂(rep.ν : Measure ℝ) := rep.formula hxIci
        _ = rep.a * x + (rep.b : ℝ) * x ^ 2 +
            x ^ 2 * ∫ t : ℝ, positiveRayResolventKernel x t
              ∂(rep.ν : Measure ℝ) := by
              rw [hzero, hkernel]
              ring
    calc
      g x = (x ^ 2 * g x) / x ^ 2 := by
        field_simp [hxne]
      _ = (rep.a * x + (rep.b : ℝ) * x ^ 2 +
            x ^ 2 * ∫ t : ℝ, positiveRayResolventKernel x t
              ∂(rep.ν : Measure ℝ)) / x ^ 2 := by
            rw [hsq_formula]
      _ = (rep.b : ℝ) +
            (rep.a * x⁻¹ +
              ∫ t : ℝ, positiveRayResolventKernel x t ∂(rep.ν : Measure ℝ)) := by
            field_simp [hxne]
            ring
      _ = (rep.b : ℝ) +
            ∫ t : ℝ, positiveRayResolventKernel x t
              ∂(((Real.toNNReal rep.a • positiveRayResolventDiracZero) + rep.ν) :
                  FiniteMeasure ℝ) := by
            rw [hμ_int]

/-- Existence form of
`positiveRayOperatorMonotoneDecreasingRep_of_xsq_finiteRightDerivativeRep`. -/
theorem nonempty_positiveRayOperatorMonotoneDecreasingRep_of_xsq_finiteRightDerivativeRep
    {g h₀ : ℝ → ℝ}
    (hxsq : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → h₀ x = x ^ 2 * g x)
    (hzero : h₀ 0 = 0)
    (rep : PositiveRayOperatorConvexRepFiniteRightDerivative h₀)
    (ha : 0 ≤ rep.a) :
    Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  ⟨positiveRayOperatorMonotoneDecreasingRep_of_xsq_finiteRightDerivativeRep
    hxsq hzero rep ha⟩

private theorem positiveRayResolventMeasure_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayResolventKernel x t
        ∂(positiveRayResolventMeasure rep : Measure ℝ)) =
      (rep.b : ℝ) * x⁻¹ +
        ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ) := by
  have hInt0 :
      Integrable (fun t : ℝ => positiveRayResolventKernel x t)
        (rep.b • positiveRayResolventDiracZero : FiniteMeasure ℝ) :=
    positiveRayResolventKernel_integrable_of_support_Ici
      (rep.b • positiveRayResolventDiracZero)
      (by simp [positiveRayResolventDiracZero_Iio_zero]) hx
  have hIntPush :
      Integrable (fun t : ℝ => positiveRayResolventKernel x t)
        (positiveRayResolventPushforward rep.ν : Measure ℝ) :=
    positiveRayResolventKernel_integrable_of_support_Ici
      (positiveRayResolventPushforward rep.ν)
      (positiveRayResolventPushforward_support_Ici rep) hx
  calc
    (∫ t : ℝ, positiveRayResolventKernel x t
        ∂(positiveRayResolventMeasure rep : Measure ℝ)) =
        ∫ t : ℝ, positiveRayResolventKernel x t
          ∂((rep.b • positiveRayResolventDiracZero : FiniteMeasure ℝ) +
              positiveRayResolventPushforward rep.ν) := by
          simp [positiveRayResolventMeasure]
    _ = (∫ t : ℝ, positiveRayResolventKernel x t
            ∂(rep.b • positiveRayResolventDiracZero : FiniteMeasure ℝ)) +
          ∫ t : ℝ, positiveRayResolventKernel x t
            ∂(positiveRayResolventPushforward rep.ν : Measure ℝ) := by
          exact integral_add_measure hInt0 hIntPush
    _ = (rep.b : ℝ) * x⁻¹ +
        ∫ t : ℝ, positiveRayKuboAndoKernel x⁻¹ t ∂(rep.ν : Measure ℝ) := by
          rw [positiveRayResolventDiracZero_integral_kernel rep.b hx,
            positiveRayResolventPushforward_integral_kernel rep hx]

/--
Convert a Kubo--Ando representation of `h` into the resolvent representation
of the reciprocal pullback `x ↦ h x⁻¹`.

This is the representation-level part of Hiai Proposition 2.28.  The full
equivalence with operator monotone decreasing functions is
`positiveCFC_iff_nonempty_rep` in `CFCBridgeReciprocalClosure.lean`.
-/
noncomputable def
    positiveRayOperatorMonotoneDecreasingRep_of_positiveRayKuboAndoRep_inverse
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0) :
    PositiveRayOperatorMonotoneDecreasingRep (fun x : ℝ => h x⁻¹) where
  a := Real.toNNReal (h 0)
  μ := positiveRayResolventMeasure rep
  support := positiveRayResolventMeasure_support_Ici rep
  formula := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxinv_nonneg : x⁻¹ ∈ Set.Ici (0 : ℝ) := by
      exact le_of_lt (inv_pos.mpr hxpos)
    have hformula := rep.formula hxinv_nonneg
    rw [positiveRayResolventMeasure_integral_kernel rep hx]
    simpa [Real.coe_toNNReal _ h0, add_assoc] using hformula

/--
Monotonicity from a reciprocal Kubo--Ando representation: if `h` is given by a
Kubo--Ando representation, then `x ↦ h x⁻¹` is operator monotone decreasing on
the positive ray in the reciprocal-transport sense.
-/
theorem operatorMonotoneDecreasingOnPositive_of_positiveRayKuboAndoRep_inverse
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    (h_nonneg_inverse : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ h x⁻¹) :
    OperatorMonotoneDecreasingOnPositive.{u} (fun x : ℝ => h x⁻¹) := by
  exact
    { nonneg := h_nonneg_inverse
      reciprocal_witness :=
        ⟨h, operatorMonotoneOnPositive_of_positiveRayKuboAndoRep rep, by
          intro x hx
          rfl⟩ }

/--
If the reciprocal witness of `g` has a Kubo--Ando representation, then `g`
has the decreasing resolvent representation.
-/
noncomputable def positiveRayOperatorMonotoneDecreasingRep_of_reciprocalKuboAndoRep
    {g h : ℝ → ℝ}
    (h_formula : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹)
    (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0) :
    PositiveRayOperatorMonotoneDecreasingRep g :=
  PositiveRayOperatorMonotoneDecreasingRep.congr_on_Ioi
    (positiveRayOperatorMonotoneDecreasingRep_of_positiveRayKuboAndoRep_inverse rep h0)
    h_formula

/--
Forward bridge: a decreasing resolvent representation gives the
reciprocal-transport monotonicity predicate once a positive-ray monotone
reciprocal witness is supplied.
-/
theorem operatorMonotoneDecreasingOnPositive_of_rep_of_reciprocalMonotone
    {g h : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g)
    (hh : OperatorMonotoneOnPositive.{u} h)
    (h_formula : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) :
    OperatorMonotoneDecreasingOnPositive.{u} g := by
  exact
    { nonneg := rep.nonneg_on_Ioi
      reciprocal_witness := ⟨h, hh, h_formula⟩ }

end

end Quantum.TraceInequality.Loewner
