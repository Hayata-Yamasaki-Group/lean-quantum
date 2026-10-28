import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo

/-!
# Hansen finite-measure representation on the positive ray

This module records the Hansen form of Hiai's positive-ray finite-measure
representation.  It is obtained from the Kubo--Ando representation by the
change of variables `s = t / (1 + t)`, with the constant and linear terms
represented by atoms at `0` and `1`.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory

open scoped NNReal

noncomputable section

/--
Hansen kernel on `[0,∞) × [0,1]`.

At `s = 0` we use the continuous-extension value `1`, so that an atom at
`0` represents the constant term.
-/
def positiveRayHansenKernel (x s : ℝ) : ℝ :=
  if s = 0 then 1 else x / ((1 - s) * x + s)

private theorem measurable_positiveRayHansenKernel_right (x : ℝ) :
    Measurable fun s : ℝ => positiveRayHansenKernel x s := by
  unfold positiveRayHansenKernel
  exact Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const (by measurability)

/--
Hansen finite-measure representation on `[0,∞)`.

The finite measure is represented as a measure on `ℝ` supported on `[0,1]`.
-/
structure PositiveRayHansenRep (h : ℝ → ℝ) where
  m : FiniteMeasure ℝ
  support : (m : Measure ℝ) (Set.Icc (0 : ℝ) 1)ᶜ = 0
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ici (0 : ℝ) →
      h x = ∫ s : ℝ, positiveRayHansenKernel x s ∂(m : Measure ℝ)

private def positiveRayHansenParam (t : ℝ) : ℝ :=
  t / (1 + t)

private theorem measurable_positiveRayHansenParam :
    Measurable positiveRayHansenParam := by
  unfold positiveRayHansenParam
  measurability

private theorem positiveRayHansenParam_mem_Icc_of_pos
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayHansenParam t ∈ Set.Icc (0 : ℝ) 1 := by
  have htpos : 0 < t := by simpa using ht
  have hden_pos : 0 < 1 + t := by linarith
  constructor
  · unfold positiveRayHansenParam
    positivity
  · unfold positiveRayHansenParam
    rw [div_le_iff₀ hden_pos]
    linarith

private def positiveRayHansenDiracZero : FiniteMeasure ℝ :=
  ⟨Measure.dirac (0 : ℝ), inferInstance⟩

private def positiveRayHansenDiracOne : FiniteMeasure ℝ :=
  ⟨Measure.dirac (1 : ℝ), inferInstance⟩

private theorem positiveRayHansenDiracZero_support_Icc :
    (positiveRayHansenDiracZero : Measure ℝ)
      (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  simp [positiveRayHansenDiracZero, h0]

private theorem positiveRayHansenDiracOne_support_Icc :
    (positiveRayHansenDiracOne : Measure ℝ)
      (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  simp [positiveRayHansenDiracOne, h1]

private def positiveRayHansenPushforward (ν : FiniteMeasure ℝ) :
    FiniteMeasure ℝ :=
  ν.map positiveRayHansenParam

private theorem positiveRayHansenPushforward_support_Icc
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (positiveRayHansenPushforward rep.ν : Measure ℝ)
      (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Icc (0 : ℝ) 1)ᶜ) :=
    isClosed_Icc.measurableSet.compl
  calc
    (positiveRayHansenPushforward rep.ν : Measure ℝ)
        (Set.Icc (0 : ℝ) 1)ᶜ =
        (rep.ν : Measure ℝ)
          (positiveRayHansenParam ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) := by
          rw [positiveRayHansenPushforward, FiniteMeasure.toMeasure_map,
            Measure.map_apply measurable_positiveRayHansenParam hS]
    _ = 0 := by
          rw [measure_eq_zero_iff_ae_notMem]
          filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht hbad
          exact hbad (positiveRayHansenParam_mem_Icc_of_pos ht)

private def positiveRayHansenMeasure
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (_h0 : 0 ≤ h 0) :
    FiniteMeasure ℝ :=
  (Real.toNNReal (h 0) • positiveRayHansenDiracZero) +
    (rep.b • positiveRayHansenDiracOne +
      positiveRayHansenPushforward rep.ν)

private theorem positiveRayHansenMeasure_support_Icc
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0) :
    (positiveRayHansenMeasure rep h0 : Measure ℝ)
      (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  simp [positiveRayHansenMeasure, positiveRayHansenDiracZero_support_Icc,
    positiveRayHansenDiracOne_support_Icc,
    positiveRayHansenPushforward_support_Icc rep]

private theorem positiveRayHansenKernel_zero (x : ℝ) :
    positiveRayHansenKernel x 0 = 1 := by
  simp [positiveRayHansenKernel]

private theorem positiveRayHansenKernel_one (x : ℝ) :
    positiveRayHansenKernel x 1 = x := by
  simp [positiveRayHansenKernel]

private theorem positiveRayHansenKernel_nonneg_and_le_max
    {x s : ℝ} (hx : 0 ≤ x) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ positiveRayHansenKernel x s ∧
      positiveRayHansenKernel x s ≤ max x 1 := by
  by_cases hs0 : s = 0
  · subst s
    constructor
    · simp [positiveRayHansenKernel]
    · simp [positiveRayHansenKernel]
  · have hspos : 0 < s := lt_of_le_of_ne' hs.1 hs0
    have h1ms : 0 ≤ 1 - s := by linarith [hs.2]
    have hden_pos : 0 < (1 - s) * x + s := by
      nlinarith [mul_nonneg h1ms hx]
    have hkernel :
        positiveRayHansenKernel x s = x / ((1 - s) * x + s) := by
      unfold positiveRayHansenKernel
      simp only [hs0, ↓reduceIte]
    have hnonneg : 0 ≤ positiveRayHansenKernel x s := by
      rw [hkernel]
      positivity
    constructor
    · exact hnonneg
    · by_cases hxle : x ≤ 1
      · have hnum_le : x ≤ (1 - s) * x + s := by
          nlinarith
        have hle_one : positiveRayHansenKernel x s ≤ 1 := by
          rw [hkernel]
          rw [div_le_iff₀ hden_pos]
          simpa using hnum_le
        exact le_trans hle_one (le_max_right x 1)
      · have hxge : 1 ≤ x := le_of_not_ge hxle
        have hden_ge_one : 1 ≤ (1 - s) * x + s := by
          nlinarith
        have hle_x : positiveRayHansenKernel x s ≤ x := by
          rw [hkernel]
          rw [div_le_iff₀ hden_pos]
          nlinarith
        exact le_trans hle_x (le_max_left x 1)

private theorem positiveRayHansenKernel_norm_le_const
    {x s : ℝ} (hx : 0 ≤ x) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖positiveRayHansenKernel x s‖ ≤ max x 1 := by
  have hbound := positiveRayHansenKernel_nonneg_and_le_max hx hs
  rw [Real.norm_of_nonneg hbound.1]
  exact hbound.2

private theorem positiveRayHansenKernel_integrable_of_support_Icc
    (m : FiniteMeasure ℝ)
    (hm : (m : Measure ℝ) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun s : ℝ => positiveRayHansenKernel x s) (m : Measure ℝ) := by
  refine Integrable.of_bound
    (measurable_positiveRayHansenKernel_right x).aestronglyMeasurable
    (max x 1) ?_
  have hae : ∀ᵐ s ∂(m : Measure ℝ), s ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hm
  filter_upwards [hae] with s hs
  have hmax_nonneg : 0 ≤ max x 1 := le_trans zero_le_one (le_max_right x 1)
  simpa [Real.norm_of_nonneg hmax_nonneg] using
    positiveRayHansenKernel_norm_le_const hx hs

private theorem positiveRayHansenKernel_eq_kubo_of_pos
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayHansenKernel x (positiveRayHansenParam t) =
      positiveRayKuboAndoKernel x t := by
  have htpos : 0 < t := by simpa using ht
  have hden1 : 1 + t ≠ 0 := by linarith
  have ht_ne : t ≠ 0 := ne_of_gt htpos
  have hparam_ne_zero : positiveRayHansenParam t ≠ 0 := by
    unfold positiveRayHansenParam
    exact div_ne_zero ht_ne hden1
  have hden2 : x + t ≠ 0 := by linarith
  unfold positiveRayHansenKernel positiveRayHansenParam positiveRayKuboAndoKernel
  simp [ht_ne, hden1]
  field_simp [hden1, hden2]
  ring_nf

private theorem positiveRayHansenPushforward_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(positiveRayHansenPushforward rep.ν : Measure ℝ)) =
      ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
  have hmap :
      (∫ s : ℝ, positiveRayHansenKernel x s
          ∂(positiveRayHansenPushforward rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayHansenKernel x (positiveRayHansenParam t)
          ∂(rep.ν : Measure ℝ) := by
    have hf :
        AEStronglyMeasurable (fun s : ℝ => positiveRayHansenKernel x s)
          (Measure.map positiveRayHansenParam (rep.ν : Measure ℝ)) := by
      exact (measurable_positiveRayHansenKernel_right x).aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := (rep.ν : Measure ℝ))
        (φ := positiveRayHansenParam)
        measurable_positiveRayHansenParam.aemeasurable
        (f := fun s : ℝ => positiveRayHansenKernel x s) hf
    simpa [positiveRayHansenPushforward] using h
  have hkernel :
      (fun t : ℝ => positiveRayHansenKernel x (positiveRayHansenParam t))
        =ᵐ[(rep.ν : Measure ℝ)]
        fun t : ℝ => positiveRayKuboAndoKernel x t := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayHansenKernel_eq_kubo_of_pos hx ht
  calc
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(positiveRayHansenPushforward rep.ν : Measure ℝ)) =
        ∫ t : ℝ, positiveRayHansenKernel x (positiveRayHansenParam t)
          ∂(rep.ν : Measure ℝ) := hmap
    _ = ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) :=
        integral_congr_ae hkernel

private theorem positiveRayHansenDiracZero_integral_kernel
    (c : ℝ≥0) (x : ℝ) :
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(c • positiveRayHansenDiracZero : FiniteMeasure ℝ)) =
      (c : ℝ) := by
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  change (c : ℝ≥0) •
      (∫ s : ℝ, positiveRayHansenKernel x s ∂Measure.dirac (0 : ℝ)) =
    (c : ℝ)
  rw [MeasureTheory.integral_dirac]
  simp [positiveRayHansenKernel_zero, NNReal.smul_def]

private theorem positiveRayHansenDiracOne_integral_kernel
    (c : ℝ≥0) (x : ℝ) :
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(c • positiveRayHansenDiracOne : FiniteMeasure ℝ)) =
      (c : ℝ) * x := by
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  change (c : ℝ≥0) •
      (∫ s : ℝ, positiveRayHansenKernel x s ∂Measure.dirac (1 : ℝ)) =
    (c : ℝ) * x
  rw [MeasureTheory.integral_dirac]
  simp [positiveRayHansenKernel_one, NNReal.smul_def]

private theorem positiveRayHansenMeasure_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0)
    {x : ℝ} (hx : x ∈ Set.Ici (0 : ℝ)) :
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(positiveRayHansenMeasure rep h0 : Measure ℝ)) =
      h 0 + (rep.b : ℝ) * x +
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
  let c0 : ℝ≥0 := Real.toNNReal (h 0)
  have hx0 : 0 ≤ x := by simpa using hx
  have hInt0 :
      Integrable (fun s : ℝ => positiveRayHansenKernel x s)
        (c0 • positiveRayHansenDiracZero : FiniteMeasure ℝ) :=
    positiveRayHansenKernel_integrable_of_support_Icc
      (c0 • positiveRayHansenDiracZero)
      (by simp [positiveRayHansenDiracZero_support_Icc]) hx0
  have hInt1 :
      Integrable (fun s : ℝ => positiveRayHansenKernel x s)
        (rep.b • positiveRayHansenDiracOne : FiniteMeasure ℝ) :=
    positiveRayHansenKernel_integrable_of_support_Icc
      (rep.b • positiveRayHansenDiracOne)
      (by simp [positiveRayHansenDiracOne_support_Icc]) hx0
  have hIntPush :
      Integrable (fun s : ℝ => positiveRayHansenKernel x s)
        (positiveRayHansenPushforward rep.ν : Measure ℝ) :=
    positiveRayHansenKernel_integrable_of_support_Icc
      (positiveRayHansenPushforward rep.ν)
      (positiveRayHansenPushforward_support_Icc rep) hx0
  calc
    (∫ s : ℝ, positiveRayHansenKernel x s
        ∂(positiveRayHansenMeasure rep h0 : Measure ℝ)) =
        ∫ s : ℝ, positiveRayHansenKernel x s
          ∂((c0 • positiveRayHansenDiracZero : FiniteMeasure ℝ) +
              (rep.b • positiveRayHansenDiracOne +
                positiveRayHansenPushforward rep.ν : FiniteMeasure ℝ)) := by
          simp [positiveRayHansenMeasure, c0]
    _ = (∫ s : ℝ, positiveRayHansenKernel x s
            ∂(c0 • positiveRayHansenDiracZero : FiniteMeasure ℝ)) +
          ∫ s : ℝ, positiveRayHansenKernel x s
            ∂(rep.b • positiveRayHansenDiracOne +
                positiveRayHansenPushforward rep.ν : FiniteMeasure ℝ) := by
          exact integral_add_measure hInt0 (hInt1.add_measure hIntPush)
    _ = (∫ s : ℝ, positiveRayHansenKernel x s
            ∂(c0 • positiveRayHansenDiracZero : FiniteMeasure ℝ)) +
          ((∫ s : ℝ, positiveRayHansenKernel x s
              ∂(rep.b • positiveRayHansenDiracOne : FiniteMeasure ℝ)) +
            ∫ s : ℝ, positiveRayHansenKernel x s
              ∂(positiveRayHansenPushforward rep.ν : Measure ℝ)) := by
          exact congrArg
            (fun y =>
              (∫ s : ℝ, positiveRayHansenKernel x s
                ∂(c0 • positiveRayHansenDiracZero : FiniteMeasure ℝ)) + y)
            (integral_add_measure hInt1 hIntPush)
    _ = h 0 + (rep.b : ℝ) * x +
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
          rw [positiveRayHansenDiracZero_integral_kernel,
            positiveRayHansenDiracOne_integral_kernel,
            positiveRayHansenPushforward_integral_kernel rep hx0]
          simp [c0, Real.coe_toNNReal _ h0, add_assoc]

/--
Convert a Kubo--Ando finite-measure representation with nonnegative endpoint
value into Hansen's finite-measure representation.
-/
noncomputable def positiveRayHansenRep_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (h0 : 0 ≤ h 0) :
    PositiveRayHansenRep h where
  m := positiveRayHansenMeasure rep h0
  support := positiveRayHansenMeasure_support_Icc rep h0
  formula := by
    intro x hx
    rw [positiveRayHansenMeasure_integral_kernel rep h0 hx]
    exact rep.formula hx

end

end Quantum.TraceInequality.Loewner
