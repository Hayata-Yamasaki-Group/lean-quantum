/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo.Forward

/-!
# Kubo--Ando reconstruction from half-line measures

Source correspondence: half-line representation theory of Kubo--Ando means.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-! ### Inverse Density from Half-Line Data -/
/--
Density `t⁻¹` used to convert a half-line representation measure into the
Kubo--Ando positive-ray measure.
-/
def halfLineToKuboAndoDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal t⁻¹

private theorem measurable_halfLineToKuboAndoDensity :
    Measurable halfLineToKuboAndoDensity := by
  unfold halfLineToKuboAndoDensity
  measurability

/-- The inverse density vanishes outside the positive ray. -/
theorem halfLineToKuboAndoDensity_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) :
    halfLineToKuboAndoDensity t = 0 := by
  rw [halfLineToKuboAndoDensity, ENNReal.ofReal_eq_zero]
  exact inv_nonpos'.mpr ht

/-- On positive `t`, the `toReal` value of the inverse density is `t⁻¹`. -/
theorem halfLineToKuboAndoDensity_toReal_of_pos
    {t : ℝ} (ht : 0 < t) :
    (halfLineToKuboAndoDensity t).toReal = t⁻¹ := by
  rw [halfLineToKuboAndoDensity, ENNReal.toReal_ofReal]
  exact inv_nonneg.mpr ht.le

private theorem halfLineToKuboAndoDensity_support_Ioi
    (μ : Measure ℝ) :
    (μ.withDensity halfLineToKuboAndoDensity) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  rw [withDensity_apply _ measurableSet_Ioi.compl]
  have hzero :
      halfLineToKuboAndoDensity =ᵐ[μ.restrict (Set.Ioi (0 : ℝ))ᶜ]
        fun _t : ℝ => (0 : ENNReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi.compl] with t ht
    have hnonpos : t ≤ 0 := not_lt.mp (by simpa [Set.mem_Ioi] using ht)
    exact halfLineToKuboAndoDensity_eq_zero_of_nonpos hnonpos
  rw [lintegral_congr_ae hzero, lintegral_zero]

private noncomputable def positiveRayMeasureOfHalfLine
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤) :
    FiniteMeasure ℝ :=
  ⟨rep.μ.withDensity halfLineToKuboAndoDensity,
    MeasureTheory.isFiniteMeasure_withDensity hInv.ne⟩

private theorem positiveRayMeasureOfHalfLine_support
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤) :
    (positiveRayMeasureOfHalfLine rep hInv : Measure ℝ)
      (Set.Ioi (0 : ℝ))ᶜ = 0 :=
  halfLineToKuboAndoDensity_support_Ioi rep.μ

private theorem positiveRayMeasureOfHalfLine_ae_mem_Ioi
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤) :
    ∀ᵐ t ∂(positiveRayMeasureOfHalfLine rep hInv : Measure ℝ),
      t ∈ Set.Ioi (0 : ℝ) := by
  exact (mem_ae_iff).mpr (positiveRayMeasureOfHalfLine_support rep hInv)

private theorem halfLineToKuboAndoDensity_ne_top_ae
    (μ : Measure ℝ) :
    ∀ᵐ t ∂μ, halfLineToKuboAndoDensity t < (⊤ : ENNReal) := by
  exact ae_of_all _ fun t => by
    rw [halfLineToKuboAndoDensity]
    exact ENNReal.ofReal_lt_top

/--
Finiteness of the inverse-density `lintegral` makes its real-valued version
Bochner integrable.
-/
theorem halfLineToKuboAndoDensity_toReal_integrable
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤) :
    Integrable (fun t : ℝ => (halfLineToKuboAndoDensity t).toReal) rep.μ :=
  integrable_toReal_of_lintegral_ne_top
    measurable_halfLineToKuboAndoDensity.aemeasurable hInv.ne

private theorem positiveRayKuboAndoKernel_integrable_of_support
    (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Set.Ioi (0 : ℝ))ᶜ = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => positiveRayKuboAndoKernel x t)
      (ν : Measure ℝ) := by
  refine Integrable.mono (integrable_const (max x 1))
    (measurable_positiveRayKuboAndoKernel_right x).aestronglyMeasurable ?_
  have hae : ∀ᵐ t ∂(ν : Measure ℝ), t ∈ Set.Ioi (0 : ℝ) :=
    (mem_ae_iff).mpr hν
  filter_upwards [hae] with t ht
  have hmax_nonneg : 0 ≤ max x 1 := le_trans zero_le_one (le_max_right x 1)
  simpa [Real.norm_of_nonneg hmax_nonneg] using
    positiveRayKuboAndoKernel_norm_le_const hx ht

private theorem positiveRayMeasureOfHalfLine_integral_kernel
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    {x : ℝ} :
    (∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(positiveRayMeasureOfHalfLine rep hInv : Measure ℝ)) =
      ∫ t : ℝ,
        (halfLineToKuboAndoDensity t).toReal •
          positiveRayKuboAndoKernel x t ∂rep.μ := by
  exact integral_withDensity_eq_integral_toReal_smul
    measurable_halfLineToKuboAndoDensity
    (halfLineToKuboAndoDensity_ne_top_ae rep.μ)
    (fun t : ℝ => positiveRayKuboAndoKernel x t)

private theorem halfLineKernel_add_density_eq_density_kubo
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    halfLineKernel x t + (halfLineToKuboAndoDensity t).toReal =
      (halfLineToKuboAndoDensity t).toReal * positiveRayKuboAndoKernel x t := by
  have htpos : 0 < t := by simpa using ht
  have htoReal := halfLineToKuboAndoDensity_toReal_of_pos htpos
  have hxpos : 0 < x := by simpa using hx
  have hden : x + t ≠ 0 := by linarith
  rw [htoReal]
  unfold halfLineKernel positiveRayKuboAndoKernel
  field_simp [hden, htpos.ne']
  ring_nf

private theorem halfLineKernel_integrable_of_kubo
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    (hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ))
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => halfLineKernel x t) rep.μ := by
  let ν : FiniteMeasure ℝ := positiveRayMeasureOfHalfLine rep hInv
  have hx_nonneg : 0 ≤ x := le_of_lt (by simpa using hx)
  have hkubo_int :
      Integrable (fun t : ℝ => positiveRayKuboAndoKernel x t)
        (ν : Measure ℝ) :=
    positiveRayKuboAndoKernel_integrable_of_support ν
      (positiveRayMeasureOfHalfLine_support rep hInv) hx_nonneg
  have hmul_int :
      Integrable
        (fun t : ℝ =>
          (halfLineToKuboAndoDensity t).toReal •
            positiveRayKuboAndoKernel x t) rep.μ := by
    exact (integrable_withDensity_iff_integrable_smul'
      measurable_halfLineToKuboAndoDensity
      (halfLineToKuboAndoDensity_ne_top_ae rep.μ)).1 hkubo_int
  have hdens_int := halfLineToKuboAndoDensity_toReal_integrable rep hInv
  have hsub_int :
      Integrable
        (fun t : ℝ =>
          (halfLineToKuboAndoDensity t).toReal •
            positiveRayKuboAndoKernel x t -
              (halfLineToKuboAndoDensity t).toReal) rep.μ :=
    hmul_int.sub hdens_int
  refine hsub_int.congr ?_
  filter_upwards [hpos] with t ht
  have hrewrite := halfLineKernel_add_density_eq_density_kubo hx ht
  calc
    (halfLineToKuboAndoDensity t).toReal •
          positiveRayKuboAndoKernel x t -
        (halfLineToKuboAndoDensity t).toReal =
        halfLineKernel x t := by
          rw [smul_eq_mul, ← hrewrite]
          ring

private theorem positiveRayMeasureOfHalfLine_integral_kernel_eq_halfLine_add
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    (hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ))
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(positiveRayMeasureOfHalfLine rep hInv : Measure ℝ)) =
      ∫ t : ℝ, halfLineKernel x t ∂rep.μ +
        ∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ := by
  have hwd := positiveRayMeasureOfHalfLine_integral_kernel rep hInv (x := x)
  have hhalf_int := halfLineKernel_integrable_of_kubo rep hInv hpos hx
  have hdens_int := halfLineToKuboAndoDensity_toReal_integrable rep hInv
  have hsum_int := hhalf_int.add hdens_int
  have hae :
      (fun t : ℝ =>
        (halfLineToKuboAndoDensity t).toReal •
          positiveRayKuboAndoKernel x t) =ᵐ[rep.μ]
        fun t : ℝ =>
          halfLineKernel x t + (halfLineToKuboAndoDensity t).toReal := by
    filter_upwards [hpos] with t ht
    rw [smul_eq_mul, ← halfLineKernel_add_density_eq_density_kubo hx ht]
  calc
    (∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(positiveRayMeasureOfHalfLine rep hInv : Measure ℝ)) =
        ∫ t : ℝ,
          (halfLineToKuboAndoDensity t).toReal •
            positiveRayKuboAndoKernel x t ∂rep.μ := hwd
    _ = ∫ t : ℝ,
          halfLineKernel x t + (halfLineToKuboAndoDensity t).toReal ∂rep.μ :=
        integral_congr_ae hae
    _ = ∫ t : ℝ, halfLineKernel x t ∂rep.μ +
        ∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ := by
          exact integral_add hhalf_int hdens_int

/-! ### Conditional Reconstruction from Half-Line Data -/
/--
Reconstruct the Kubo--Ando positive-ray finite-measure representation from a
half-line representation with integrable inverse density and positive support.
-/
noncomputable def positiveRayKuboAndoRep_of_halfLineIntegralRep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    (hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ))
    (hzero :
      h 0 =
        h 1 - (rep.b : ℝ) -
          ∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ) :
    PositiveRayKuboAndoRep h where
  b := rep.b
  ν := positiveRayMeasureOfHalfLine rep hInv
  support := positiveRayMeasureOfHalfLine_support rep hInv
  formula := by
    intro x hx
    rcases eq_or_lt_of_le (by simpa using hx) with rfl | hxpos
    · have hzero_kernel :
          (fun t : ℝ => positiveRayKuboAndoKernel 0 t) =
            fun _t : ℝ => (0 : ℝ) := by
        funext t
        simp [positiveRayKuboAndoKernel]
      rw [hzero_kernel, integral_zero]
      ring
    · have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hxpos
      have hrep := rep.formula hxIoi
      have hk :=
        positiveRayMeasureOfHalfLine_integral_kernel_eq_halfLine_add
          rep hInv hpos hxIoi
      calc
        h x =
            h 1 + (rep.b : ℝ) * (x - 1) +
              ∫ t : ℝ, halfLineKernel x t ∂rep.μ := hrep
        _ =
            h 0 + (rep.b : ℝ) * x +
              ∫ t : ℝ, positiveRayKuboAndoKernel x t
                ∂(positiveRayMeasureOfHalfLine rep hInv : Measure ℝ) := by
              rw [hzero, hk]
              ring


end

end Loewner
end TraceInequality
end Quantum
