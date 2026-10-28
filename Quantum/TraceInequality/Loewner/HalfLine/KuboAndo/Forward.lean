/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Uniqueness
import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFC

/-!
# Kubo--Ando positive-ray forward representation

Source correspondence: half-line representation theory of Kubo--Ando means.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

universe u

/-! ### Positive-Ray Kubo--Ando Data -/
/-- Kernel in the Kubo--Ando finite-measure representation on `[0,∞)`. -/
def positiveRayKuboAndoKernel (x t : ℝ) : ℝ :=
  x * (1 + t) / (x + t)

/-- The Kubo--Ando positive-ray kernel is measurable in the measure variable. -/
theorem measurable_positiveRayKuboAndoKernel_right (x : ℝ) :
    Measurable fun t : ℝ => positiveRayKuboAndoKernel x t := by
  unfold positiveRayKuboAndoKernel
  measurability

/--
Hiai--Matsumoto Theorem 2.27 type finite-measure representation.

The finite measure is represented as a measure on `ℝ` supported on `(0,∞)`.
The formula is stated on `[0,∞)`, matching the book's positive-ray
normalization.
-/
structure PositiveRayKuboAndoRep (h : ℝ → ℝ) where
  b : NNReal
  ν : FiniteMeasure ℝ
  support : (ν : Measure ℝ) (Set.Ioi (0 : ℝ))ᶜ = 0
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ici (0 : ℝ) →
      h x =
        h 0 + (b : ℝ) * x +
          ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(ν : Measure ℝ)

/-! ### Change of Measure to the Half-Line Kernel -/
private def positiveRayKuboAndoToHalfLineDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal t

private theorem measurable_positiveRayKuboAndoToHalfLineDensity :
    Measurable positiveRayKuboAndoToHalfLineDensity := by
  exact ENNReal.measurable_ofReal.comp measurable_id

private def halfLineMeasureOfPositiveRayKuboAndo (ν : FiniteMeasure ℝ) : Measure ℝ :=
  (ν : Measure ℝ).withDensity positiveRayKuboAndoToHalfLineDensity

/-- The representing measure in a positive-ray Kubo--Ando representation is a.e. positive. -/
theorem positiveRayKuboAndoRep_ae_mem_Ioi
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    ∀ᵐ t ∂(rep.ν : Measure ℝ), t ∈ Set.Ioi (0 : ℝ) := by
  exact (mem_ae_iff).mpr rep.support

private theorem halfLineMeasureOfPositiveRayKuboAndo_support_Ici
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    halfLineMeasureOfPositiveRayKuboAndo rep.ν (Set.Ici (0 : ℝ))ᶜ = 0 := by
  have hac :
      halfLineMeasureOfPositiveRayKuboAndo rep.ν ≪ (rep.ν : Measure ℝ) := by
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hsubset : (Set.Ici (0 : ℝ))ᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ := by
    intro t ht hpos
    have htici : t ∈ Set.Ici (0 : ℝ) := by
      exact le_of_lt (by simpa using hpos)
    exact ht htici
  exact hac (measure_mono_null hsubset rep.support)

private theorem positiveRayKuboAndo_density_mul_weight_le_one
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayKuboAndoToHalfLineDensity t * halfLineWeight t ≤ 1 := by
  have htpos : 0 < t := by simpa using ht
  have ht0 : 0 ≤ t := le_of_lt htpos
  have hden_pos : 0 < 1 + t := by linarith
  have hreal : t * (1 + t)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hden_pos]
    linarith
  calc
    positiveRayKuboAndoToHalfLineDensity t * halfLineWeight t =
        ENNReal.ofReal t * ENNReal.ofReal ((1 + t)⁻¹) := by
          rfl
    _ = ENNReal.ofReal (t * (1 + t)⁻¹) := by
          rw [ENNReal.ofReal_mul ht0]
    _ ≤ 1 := by
          exact ENNReal.ofReal_le_one.mpr hreal

private theorem halfLineMeasureOfPositiveRayKuboAndo_weight_lintegral_lt_top
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (∫⁻ t : ℝ, halfLineWeight t ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν) < ⊤ := by
  have hrewrite :
      (∫⁻ t : ℝ, halfLineWeight t ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν) =
        ∫⁻ t : ℝ,
          positiveRayKuboAndoToHalfLineDensity t * halfLineWeight t
            ∂(rep.ν : Measure ℝ) := by
    have h :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul
        (rep.ν : Measure ℝ)
        measurable_positiveRayKuboAndoToHalfLineDensity
        measurable_halfLineWeight
    simpa [halfLineMeasureOfPositiveRayKuboAndo,
      positiveRayKuboAndoToHalfLineDensity] using h
  have hbound :
      ∀ᵐ t ∂(rep.ν : Measure ℝ),
        positiveRayKuboAndoToHalfLineDensity t * halfLineWeight t ≤ 1 := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayKuboAndo_density_mul_weight_le_one ht
  rw [hrewrite]
  calc
    (∫⁻ t : ℝ,
        positiveRayKuboAndoToHalfLineDensity t * halfLineWeight t
          ∂(rep.ν : Measure ℝ)) ≤
        ∫⁻ _t : ℝ, (1 : ENNReal) ∂(rep.ν : Measure ℝ) :=
          lintegral_mono_ae hbound
    _ = (rep.ν : Measure ℝ) Set.univ := by simp
    _ < ⊤ := measure_lt_top (rep.ν : Measure ℝ) Set.univ

private theorem positiveRayKuboAndoKernel_one_of_pos
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayKuboAndoKernel 1 t = 1 := by
  have htpos : 0 < t := by simpa using ht
  have hden : (1 : ℝ) + t ≠ 0 := by linarith
  unfold positiveRayKuboAndoKernel
  field_simp [hden]

private theorem positiveRayKuboAndoKernel_sub_one_eq_density_halfLineKernel
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayKuboAndoKernel x t - 1 = t * halfLineKernel x t := by
  have hxpos : 0 < x := by simpa using hx
  have htpos : 0 < t := by simpa using ht
  have hden : x + t ≠ 0 := by linarith
  unfold positiveRayKuboAndoKernel halfLineKernel
  field_simp [hden]
  ring_nf
private theorem positiveRayKuboAndoKernel_nonneg_and_le_max
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ positiveRayKuboAndoKernel x t ∧
      positiveRayKuboAndoKernel x t ≤ max x 1 := by
  have htpos : 0 < t := by simpa using ht
  by_cases hxzero : x = 0
  · subst x
    constructor <;> simp [positiveRayKuboAndoKernel]
  · have hxpos : 0 < x := lt_of_le_of_ne' hx hxzero
    have hden_pos : 0 < x + t := by linarith
    have hkernel_nonneg :
        0 ≤ positiveRayKuboAndoKernel x t := by
      unfold positiveRayKuboAndoKernel
      positivity
    constructor
    · exact hkernel_nonneg
    · by_cases hxle : x ≤ 1
      · have hnum_le : x * (1 + t) ≤ 1 * (x + t) := by
          nlinarith
        have hle_one : positiveRayKuboAndoKernel x t ≤ 1 := by
          unfold positiveRayKuboAndoKernel
          rw [div_le_iff₀ hden_pos]
          simpa using hnum_le
        exact le_trans hle_one (le_max_right x 1)
      · have hxge : 1 ≤ x := le_of_not_ge hxle
        have hnum_le : x * (1 + t) ≤ x * (x + t) := by
          nlinarith
        have hle_x : positiveRayKuboAndoKernel x t ≤ x := by
          unfold positiveRayKuboAndoKernel
          rw [div_le_iff₀ hden_pos]
          simpa [mul_add, add_comm, add_left_comm, add_assoc] using hnum_le
        exact le_trans hle_x (le_max_left x 1)

/--
On the support `(0,∞)`, the Kubo--Ando kernel has norm bounded by
`max x 1` for nonnegative `x`.
-/
theorem positiveRayKuboAndoKernel_norm_le_const
    {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    ‖positiveRayKuboAndoKernel x t‖ ≤ max x 1 := by
  have hbound := positiveRayKuboAndoKernel_nonneg_and_le_max hx ht
  rw [Real.norm_of_nonneg hbound.1]
  exact hbound.2

private theorem positiveRayKuboAndoKernel_integrable
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => positiveRayKuboAndoKernel x t)
      (rep.ν : Measure ℝ) := by
  refine Integrable.mono (integrable_const (max x 1))
    (measurable_positiveRayKuboAndoKernel_right x).aestronglyMeasurable ?_
  filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
  have hmax_nonneg : 0 ≤ max x 1 := le_trans zero_le_one (le_max_right x 1)
  simpa [Real.norm_of_nonneg hmax_nonneg] using
    positiveRayKuboAndoKernel_norm_le_const hx ht

private theorem halfLineMeasureOfPositiveRayKuboAndo_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, halfLineKernel x t
        ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν) =
      ∫ t : ℝ, positiveRayKuboAndoKernel x t - 1
        ∂(rep.ν : Measure ℝ) := by
  have hwd :
      (∫ t : ℝ, halfLineKernel x t
          ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν) =
        ∫ t : ℝ,
          (positiveRayKuboAndoToHalfLineDensity t).toReal • halfLineKernel x t
            ∂(rep.ν : Measure ℝ) := by
    have htop :
        ∀ᵐ t ∂(rep.ν : Measure ℝ),
          positiveRayKuboAndoToHalfLineDensity t < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun _ => by simp [positiveRayKuboAndoToHalfLineDensity])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_positiveRayKuboAndoToHalfLineDensity htop
      (fun t : ℝ => halfLineKernel x t)
  have hkernel :
      (fun t : ℝ =>
          (positiveRayKuboAndoToHalfLineDensity t).toReal • halfLineKernel x t)
        =ᵐ[(rep.ν : Measure ℝ)]
        fun t : ℝ => positiveRayKuboAndoKernel x t - 1 := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    have htpos : 0 < t := by simpa using ht
    have htoReal :
        (positiveRayKuboAndoToHalfLineDensity t).toReal = t := by
      rw [positiveRayKuboAndoToHalfLineDensity, ENNReal.toReal_ofReal]
      exact le_of_lt htpos
    calc
      (positiveRayKuboAndoToHalfLineDensity t).toReal • halfLineKernel x t =
          t * halfLineKernel x t := by
            simp [htoReal]
      _ = positiveRayKuboAndoKernel x t - 1 := by
            rw [positiveRayKuboAndoKernel_sub_one_eq_density_halfLineKernel hx ht]
  calc
    (∫ t : ℝ, halfLineKernel x t
        ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν) =
        ∫ t : ℝ,
          (positiveRayKuboAndoToHalfLineDensity t).toReal • halfLineKernel x t
            ∂(rep.ν : Measure ℝ) := hwd
    _ = ∫ t : ℝ, positiveRayKuboAndoKernel x t - 1
        ∂(rep.ν : Measure ℝ) := integral_congr_ae hkernel

/-! ### Forward Half-Line Representation -/
/--
Convert a Kubo--Ando finite-measure representation into the half-line
representation of Theorem 2.26 by setting `dμ(t) = t dν(t)`.
-/
noncomputable def halfLineIntegralRep_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    HalfLineIntegralRep h where
  b := rep.b
  μ := halfLineMeasureOfPositiveRayKuboAndo rep.ν
  support := halfLineMeasureOfPositiveRayKuboAndo_support_Ici rep
  weight_lintegral_lt_top :=
    halfLineMeasureOfPositiveRayKuboAndo_weight_lintegral_lt_top rep
  formula := by
    intro x hx
    let νm : Measure ℝ := (rep.ν : Measure ℝ)
    let Ix : ℝ := ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂νm
    let I1 : ℝ := ∫ t : ℝ, positiveRayKuboAndoKernel 1 t ∂νm
    let Ih : ℝ := ∫ t : ℝ, halfLineKernel x t
      ∂halfLineMeasureOfPositiveRayKuboAndo rep.ν
    have hx0 : 0 < x := by simpa using hx
    have hxIci : x ∈ Set.Ici (0 : ℝ) := by exact le_of_lt hx0
    have h1Ici : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := by norm_num
    have hxformula := rep.formula hxIci
    have h1formula := rep.formula h1Ici
    have hK1 :
        I1 = ∫ _t : ℝ, (1 : ℝ) ∂νm := by
      have hae :
          (fun t : ℝ => positiveRayKuboAndoKernel 1 t) =ᵐ[νm]
            fun _t : ℝ => (1 : ℝ) := by
        filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
        exact positiveRayKuboAndoKernel_one_of_pos ht
      simpa [I1, νm] using integral_congr_ae hae
    have hsub :
        (∫ t : ℝ, positiveRayKuboAndoKernel x t - 1 ∂νm) =
          Ix - ∫ _t : ℝ, (1 : ℝ) ∂νm := by
      have hxint :
          Integrable (fun t : ℝ => positiveRayKuboAndoKernel x t) νm :=
        positiveRayKuboAndoKernel_integrable rep (le_of_lt hx0)
      have h1int : Integrable (fun _t : ℝ => (1 : ℝ)) νm :=
        integrable_const (1 : ℝ)
      simpa [Ix, νm] using
        (integral_sub hxint h1int :
          (∫ t : ℝ, positiveRayKuboAndoKernel x t - 1 ∂νm) =
            (∫ t : ℝ, positiveRayKuboAndoKernel x t ∂νm) -
              ∫ _t : ℝ, (1 : ℝ) ∂νm)
    have hhalf : Ih = Ix - I1 := by
      calc
        Ih =
            ∫ t : ℝ, positiveRayKuboAndoKernel x t - 1 ∂νm := by
              simpa [Ih, νm] using
                halfLineMeasureOfPositiveRayKuboAndo_integral_kernel rep hx
        _ = Ix - ∫ _t : ℝ, (1 : ℝ) ∂νm := hsub
        _ = Ix - I1 := by rw [← hK1]
    calc
      h x = h 0 + (rep.b : ℝ) * x + Ix := by
        simpa [Ix, νm] using hxformula
      _ = (h 0 + (rep.b : ℝ) * 1 + I1) +
          (rep.b : ℝ) * (x - 1) + (Ix - I1) := by
        ring_nf
      _ = (h 0 + (rep.b : ℝ) * 1 + I1) +
          (rep.b : ℝ) * (x - 1) + Ih := by
        rw [hhalf]
      _ = h 1 + (rep.b : ℝ) * (x - 1) + Ih := by
        rw [h1formula]

/-- The easy direction of the Kubo--Ando finite-measure representation. -/
theorem operatorMonotoneOnPositive_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    OperatorMonotoneOnPositive.{u} h :=
  operatorMonotoneOnPositive_of_halfLineIntegralRep
    (halfLineIntegralRep_of_positiveRayKuboAndoRep rep)

/-! ### Endpoint Continuity for the Forward Direction -/
private theorem positiveRayKuboAndoKernel_tendsto_zero_nhdsGT
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => positiveRayKuboAndoKernel x t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum :
      Tendsto (fun x : ℝ => x * (1 + t)) (𝓝[>] (0 : ℝ))
        (𝓝 (0 * (1 + t))) :=
    hx.mul tendsto_const_nhds
  have hden :
      Tendsto (fun x : ℝ => x + t) (𝓝[>] (0 : ℝ)) (𝓝 (0 + t)) :=
    hx.add tendsto_const_nhds
  have htne : 0 + t ≠ 0 := by linarith
  simpa [positiveRayKuboAndoKernel] using hnum.div hden htne

private theorem positiveRayKuboAndoKernel_norm_le_one_on_unit_right
    {x t : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    ‖positiveRayKuboAndoKernel x t‖ ≤ 1 := by
  have hbound := positiveRayKuboAndoKernel_norm_le_const (le_of_lt hx.1) ht
  have hmax : max x 1 = 1 := max_eq_right (le_of_lt hx.2)
  simpa [hmax] using hbound

private theorem positiveRayKuboAndoRep_integral_tendsto_zero_nhdsGT
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    Tendsto
      (fun x : ℝ =>
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hF_meas :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (fun t : ℝ => positiveRayKuboAndoKernel x t)
          (rep.ν : Measure ℝ) :=
    Eventually.of_forall fun x =>
      (measurable_positiveRayKuboAndoKernel_right x).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        ∀ᵐ t ∂(rep.ν : Measure ℝ),
          ‖positiveRayKuboAndoKernel x t‖ ≤ (fun _ : ℝ => (1 : ℝ)) t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayKuboAndoKernel_norm_le_one_on_unit_right hx ht
  have h_bound_integrable :
      Integrable (fun _ : ℝ => (1 : ℝ)) (rep.ν : Measure ℝ) :=
    integrable_const (1 : ℝ)
  have h_lim :
      ∀ᵐ t ∂(rep.ν : Measure ℝ),
        Tendsto (fun x : ℝ => positiveRayKuboAndoKernel x t)
          (𝓝[>] (0 : ℝ)) (𝓝 ((fun _ : ℝ => (0 : ℝ)) t)) := by
    filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
    exact positiveRayKuboAndoKernel_tendsto_zero_nhdsGT (by simpa using ht)
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (rep.ν : Measure ℝ))
      (F := fun x t => positiveRayKuboAndoKernel x t)
      (f := fun _ : ℝ => (0 : ℝ))
      (fun _ : ℝ => (1 : ℝ))
      hF_meas h_bound h_bound_integrable h_lim
  simpa using hDCT

private theorem positiveRayKuboAndoRep_tendsto_nhdsGT_zero
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) := by
  have hx :
      Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlinear :
      Tendsto (fun x : ℝ => (rep.b : ℝ) * x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hx :
        Tendsto (fun x : ℝ => (rep.b : ℝ) * x)
          (𝓝[>] (0 : ℝ)) (𝓝 ((rep.b : ℝ) * 0)))
  have hintegral := positiveRayKuboAndoRep_integral_tendsto_zero_nhdsGT rep
  have hsum :
      Tendsto
        (fun x : ℝ =>
          h 0 + (rep.b : ℝ) * x +
            ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) := by
    simpa [add_assoc] using
      (tendsto_const_nhds.add (hlinear.add hintegral))
  have heq :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        h x =
          h 0 + (rep.b : ℝ) * x +
            ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hxpos
    exact rep.formula (le_of_lt (by simpa using hxpos))
  exact hsum.congr' (heq.mono fun _ hx => hx.symm)

/--
Endpoint version of the Kubo--Ando easy direction: the finite-measure
representation gives open positive monotonicity and right-continuity at `0`.
-/
theorem operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    OperatorMonotoneOnClosedPositive h where
  to_open := operatorMonotoneOnPositive_of_positiveRayKuboAndoRep rep
  right_continuous_at_zero := positiveRayKuboAndoRep_tendsto_nhdsGT_zero rep

/-- Direct CFC monotonicity from a Kubo--Ando finite-measure representation. -/
theorem operatorMonotoneOnClosedPositiveCFC_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    OperatorMonotoneOnClosedPositiveCFC h :=
  operatorMonotoneOnClosedPositiveCFC_of_endpoint
    (operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep rep)

/--
gcongr form of Kubo--Ando representation monotonicity after Cayley pullback.
It delegates through `operatorMonotoneOnPositive_of_positiveRayKuboAndoRep`.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) b :=
  (operatorMonotoneOnPositive_of_positiveRayKuboAndoRep rep).to_unitInterval.cfc_monotone
    ⟨ha, hqa⟩ ⟨hb, hqb⟩ hab

/--
gcongr form of direct closed-positive CFC monotonicity from a Kubo--Ando representation.
It delegates through `operatorMonotoneOnClosedPositiveCFC_of_positiveRayKuboAndoRep`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cfcₙ (fun x : ℝ => h x - h 0) a ≤ cfcₙ (fun x : ℝ => h x - h 0) b :=
  (operatorMonotoneOnClosedPositiveCFC_of_positiveRayKuboAndoRep rep).cfc_monotone
    ha hb hab

/--
gcongr form of strict-positive CFC monotonicity from a Kubo--Ando representation.
It delegates through `positiveCayley_cfc_transport_of_strictPositive`.
-/
@[gcongr]
theorem cfc_sub_le_cfc_sub_of_le_of_positiveRayKuboAndoRep
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    cfc (fun x : ℝ => h x - h 0) a ≤ cfc (fun x : ℝ => h x - h 0) b :=
  positiveCayley_cfc_transport_of_strictPositive
    (operatorMonotoneOnPositive_of_positiveRayKuboAndoRep rep) ha hb hab

end

end Loewner
end TraceInequality
end Quantum
