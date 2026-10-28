/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo.FromHalfLineMeasure

/-!
# Endpoint reconstruction from Kubo--Ando half-line data

Source correspondence: half-line representation theory of Kubo--Ando means.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-! ### Endpoint Kernel Approximation -/
private def halfLineEndpointKernel (x t : ℝ) : ℝ :=
  (1 - x) / (x + t)

private theorem measurable_halfLineEndpointKernel_right (x : ℝ) :
    Measurable fun t : ℝ => halfLineEndpointKernel x t := by
  unfold halfLineEndpointKernel
  measurability

private theorem halfLineEndpointKernel_eq_neg_halfLineKernel
    (x t : ℝ) :
    halfLineEndpointKernel x t = -halfLineKernel x t := by
  unfold halfLineEndpointKernel halfLineKernel
  ring

private theorem halfLineEndpointKernel_nonneg
    {x t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (ht : t ∈ Set.Ici (0 : ℝ)) :
    0 ≤ halfLineEndpointKernel x t := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hnum : 0 ≤ 1 - x := by linarith
  have hden : 0 ≤ x + t := by linarith
  unfold halfLineEndpointKernel
  exact div_nonneg hnum hden

private theorem halfLineWeight_toReal_integrable_of_rep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    Integrable (fun t : ℝ => (halfLineWeight t).toReal) rep.μ :=
  integrable_toReal_of_lintegral_ne_top measurable_halfLineWeight.aemeasurable
    rep.weight_lintegral_lt_top.ne

private theorem halfLineEndpointKernel_norm_le_inv_weight
    {x t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (ht : t ∈ Set.Ici (0 : ℝ)) :
    ‖halfLineEndpointKernel x t‖ ≤
      x⁻¹ * (halfLineWeight t).toReal := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hnonneg := halfLineEndpointKernel_nonneg hx0 hx1 ht
  have hden_pos : 0 < x + t := by linarith
  have hweight : (halfLineWeight t).toReal = (1 + t)⁻¹ := by
    rw [halfLineWeight, ENNReal.toReal_ofReal]
    exact inv_nonneg.mpr (by linarith)
  have hineq : (1 - x) / (x + t) ≤ x⁻¹ * (1 + t)⁻¹ := by
    have hnum_le_one : 1 - x ≤ 1 := by linarith
    have hfrac_nonneg : 0 ≤ (1 - x) / (x + t) :=
      div_nonneg (by linarith) hden_pos.le
    have hbase : (1 - x) / (x + t) ≤ 1 / (x + t) := by
      exact div_le_div_of_nonneg_right hnum_le_one hden_pos.le
    have hden2 : 0 < 1 + t := by linarith
    have hbase2 : 1 / (x + t) ≤ x⁻¹ * (1 + t)⁻¹ := by
      rw [one_div]
      have hprod_pos : 0 < x * (1 + t) := mul_pos hx0 hden2
      have hden_le : x * (1 + t) ≤ x + t := by
        nlinarith [mul_le_mul_of_nonneg_right hx1 ht0]
      calc
        (x + t)⁻¹ ≤ (x * (1 + t))⁻¹ :=
          (inv_le_inv₀ hden_pos hprod_pos).2 hden_le
        _ = x⁻¹ * (1 + t)⁻¹ := by rw [mul_inv]
    exact le_trans hbase hbase2
  rw [Real.norm_of_nonneg hnonneg, hweight]
  exact hineq

private theorem halfLineEndpointKernel_integrable
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Integrable (fun t : ℝ => halfLineEndpointKernel x t) rep.μ := by
  have hweight_int := halfLineWeight_toReal_integrable_of_rep rep
  have hbound_int :
      Integrable (fun t : ℝ => x⁻¹ * (halfLineWeight t).toReal) rep.μ :=
    hweight_int.const_mul x⁻¹
  refine Integrable.mono hbound_int
    (measurable_halfLineEndpointKernel_right x).aestronglyMeasurable ?_
  filter_upwards [rep.ae_mem_Ici] with t ht
  have hnonneg :
      0 ≤ x⁻¹ * (halfLineWeight t).toReal := by
    exact mul_nonneg (inv_nonneg.mpr hx0.le) ENNReal.toReal_nonneg
  simpa [Real.norm_of_nonneg hnonneg] using
    halfLineEndpointKernel_norm_le_inv_weight hx0 hx1 ht

private theorem halfLineEndpointKernel_integral_eq
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx0 : 0 < x) (_hx1 : x ≤ 1) :
    (∫ t : ℝ, halfLineEndpointKernel x t ∂rep.μ) =
      h 1 + (rep.b : ℝ) * (x - 1) - h x := by
  have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hx0
  have hrep := rep.formula hxIoi
  have hneg :
      (∫ t : ℝ, halfLineEndpointKernel x t ∂rep.μ) =
        -∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
    calc
      (∫ t : ℝ, halfLineEndpointKernel x t ∂rep.μ) =
          ∫ t : ℝ, -halfLineKernel x t ∂rep.μ := by
            refine integral_congr_ae ?_
            exact ae_of_all _ fun t => halfLineEndpointKernel_eq_neg_halfLineKernel x t
      _ = -∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
            rw [integral_neg]
  calc
    (∫ t : ℝ, halfLineEndpointKernel x t ∂rep.μ) =
        -∫ t : ℝ, halfLineKernel x t ∂rep.μ := hneg
    _ = h 1 + (rep.b : ℝ) * (x - 1) - h x := by
        linarith

private def positiveRayEndpointApprox (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

private theorem positiveRayEndpointApprox_pos (n : ℕ) :
    0 < positiveRayEndpointApprox n := by
  unfold positiveRayEndpointApprox
  positivity

private theorem positiveRayEndpointApprox_le_one (n : ℕ) :
    positiveRayEndpointApprox n ≤ 1 := by
  unfold positiveRayEndpointApprox
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  exact inv_le_one_of_one_le₀ hden

private theorem positiveRayEndpointApprox_tendsto_nhdsGT :
    Tendsto positiveRayEndpointApprox atTop (𝓝[>] (0 : ℝ)) := by
  have hnhds :
      Tendsto positiveRayEndpointApprox atTop (𝓝 (0 : ℝ)) := by
    simpa [positiveRayEndpointApprox, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hpos : ∀ᶠ n in atTop, positiveRayEndpointApprox n ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun n => positiveRayEndpointApprox_pos n
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩

private theorem positiveRayEndpointApprox_antitone :
    Antitone positiveRayEndpointApprox := by
  intro m n hmn
  unfold positiveRayEndpointApprox
  exact inv_anti₀
    (by
      have hm : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      linarith)
    (by
      have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith)

private theorem halfLineEndpointKernel_mono_left
    {x y t : ℝ} (hy0 : 0 < y) (hyx : y ≤ x)
    (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineEndpointKernel x t ≤ halfLineEndpointKernel y t := by
  have ht0 : 0 ≤ t := by simpa using ht
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hyx
  have hdenx : 0 < x + t := by linarith
  have hdeny : 0 < y + t := by linarith
  unfold halfLineEndpointKernel
  rw [div_le_div_iff₀ hdenx hdeny]
  have hone_t : 0 ≤ 1 + t := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hyx) hone_t]

private theorem halfLineEndpointKernel_tendsto_inv_nhdsGT
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => halfLineEndpointKernel x t)
      (𝓝[>] (0 : ℝ)) (𝓝 t⁻¹) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum :
      Tendsto (fun x : ℝ => 1 - x) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hx
  have hden :
      Tendsto (fun x : ℝ => x + t) (𝓝[>] (0 : ℝ)) (𝓝 (0 + t)) :=
    hx.add tendsto_const_nhds
  have htne : 0 + t ≠ 0 := by linarith
  simpa [halfLineEndpointKernel, one_div] using hnum.div hden htne

private theorem halfLineEndpointKernel_approx_tendsto_inv
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => halfLineEndpointKernel (positiveRayEndpointApprox n) t)
      atTop (𝓝 t⁻¹) :=
  (halfLineEndpointKernel_tendsto_inv_nhdsGT ht).comp
    positiveRayEndpointApprox_tendsto_nhdsGT

private theorem halfLineEndpointKernel_approx_mono
    {t : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) :
    Monotone fun n : ℕ =>
      ENNReal.ofReal (halfLineEndpointKernel (positiveRayEndpointApprox n) t) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal
    (halfLineEndpointKernel_mono_left
      (positiveRayEndpointApprox_pos n)
      (positiveRayEndpointApprox_antitone hmn)
      ht)

private def halfLineEndpointLimitKernel (t : ℝ) : ENNReal :=
  ⨆ n : ℕ, ENNReal.ofReal
    (halfLineEndpointKernel (positiveRayEndpointApprox n) t)

private theorem measurable_halfLineEndpointLimitKernel :
    Measurable halfLineEndpointLimitKernel := by
  unfold halfLineEndpointLimitKernel
  exact Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp
      (measurable_halfLineEndpointKernel_right (positiveRayEndpointApprox n))

private theorem halfLineEndpointLimitKernel_tendsto
    {t : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (halfLineEndpointKernel (positiveRayEndpointApprox n) t))
      atTop (𝓝 (halfLineEndpointLimitKernel t)) := by
  exact tendsto_atTop_iSup (halfLineEndpointKernel_approx_mono ht)

private theorem halfLineEndpointLimitKernel_eq_inv_of_pos
    {t : ℝ} (ht : 0 < t) :
    halfLineEndpointLimitKernel t = ENNReal.ofReal t⁻¹ := by
  have htIci : t ∈ Set.Ici (0 : ℝ) := le_of_lt ht
  have h₁ := halfLineEndpointLimitKernel_tendsto htIci
  have h₂ :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (halfLineEndpointKernel (positiveRayEndpointApprox n) t))
        atTop (𝓝 (ENNReal.ofReal t⁻¹)) := by
    exact ENNReal.tendsto_ofReal
      (halfLineEndpointKernel_approx_tendsto_inv ht)
  exact tendsto_nhds_unique h₁ h₂

private theorem halfLineToKuboAndoDensity_le_endpointLimitKernel
    {t : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) :
    halfLineToKuboAndoDensity t ≤ halfLineEndpointLimitKernel t := by
  rcases eq_or_lt_of_le (by simpa using ht) with rfl | htpos
  · rw [halfLineToKuboAndoDensity_eq_zero_of_nonpos (le_refl 0)]
    exact bot_le
  · rw [halfLineToKuboAndoDensity, halfLineEndpointLimitKernel_eq_inv_of_pos htpos]

/-! ### Monotone Convergence and the Inverse Moment -/
private theorem halfLineEndpointKernel_lintegral_eq_ofReal_integral
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∫⁻ t : ℝ, ENNReal.ofReal (halfLineEndpointKernel x t) ∂rep.μ) =
      ENNReal.ofReal (∫ t : ℝ, halfLineEndpointKernel x t ∂rep.μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (halfLineEndpointKernel_integrable rep hx0 hx1)]
  filter_upwards [rep.ae_mem_Ici] with t ht
  exact halfLineEndpointKernel_nonneg hx0 hx1 ht

private theorem halfLineEndpointKernel_lintegral_tendsto
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ t : ℝ,
          ENNReal.ofReal
            (halfLineEndpointKernel (positiveRayEndpointApprox n) t) ∂rep.μ)
      atTop (𝓝 (ENNReal.ofReal (h 1 - (rep.b : ℝ) - h 0))) := by
  have hx_tendsto := positiveRayEndpointApprox_tendsto_nhdsGT
  have hh_tendsto : Tendsto (fun n : ℕ => h (positiveRayEndpointApprox n))
      atTop (𝓝 (h 0)) :=
    hzero.comp hx_tendsto
  have hx_nhds :
      Tendsto positiveRayEndpointApprox atTop (𝓝 (0 : ℝ)) :=
    hx_tendsto.mono_right nhdsWithin_le_nhds
  have hreal :
      Tendsto
        (fun n : ℕ =>
          ∫ t : ℝ, halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ)
        atTop (𝓝 (h 1 - (rep.b : ℝ) - h 0)) := by
    have hformula :
        (fun n : ℕ =>
          ∫ t : ℝ, halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ)
          =
        fun n : ℕ =>
          h 1 + (rep.b : ℝ) * (positiveRayEndpointApprox n - 1) -
            h (positiveRayEndpointApprox n) := by
      funext n
      exact halfLineEndpointKernel_integral_eq rep
        (positiveRayEndpointApprox_pos n)
        (positiveRayEndpointApprox_le_one n)
    rw [hformula]
    have hb :
        Tendsto
          (fun n : ℕ => (rep.b : ℝ) * (positiveRayEndpointApprox n - 1))
          atTop (𝓝 (-(rep.b : ℝ))) := by
      have hsub :
          Tendsto (fun n : ℕ => positiveRayEndpointApprox n - 1)
            atTop (𝓝 (0 - 1)) :=
        hx_nhds.sub tendsto_const_nhds
      simpa using
        (tendsto_const_nhds.mul hsub :
          Tendsto
            (fun n : ℕ => (rep.b : ℝ) * (positiveRayEndpointApprox n - 1))
            atTop (𝓝 ((rep.b : ℝ) * (0 - 1))))
    have hsum :
        Tendsto
          (fun n : ℕ =>
            h 1 + (rep.b : ℝ) * (positiveRayEndpointApprox n - 1) -
              h (positiveRayEndpointApprox n))
          atTop (𝓝 (h 1 - (rep.b : ℝ) - h 0)) := by
      convert ((tendsto_const_nhds.add hb).sub hh_tendsto) using 1
    exact hsum
  have hlintegral_congr :
      (fun n : ℕ =>
        ∫⁻ t : ℝ,
          ENNReal.ofReal
            (halfLineEndpointKernel (positiveRayEndpointApprox n) t) ∂rep.μ)
      =
      fun n : ℕ =>
        ENNReal.ofReal
          (∫ t : ℝ,
            halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ) := by
    funext n
    exact halfLineEndpointKernel_lintegral_eq_ofReal_integral rep
      (positiveRayEndpointApprox_pos n)
      (positiveRayEndpointApprox_le_one n)
  rw [hlintegral_congr]
  exact ENNReal.tendsto_ofReal hreal

private theorem halfLineEndpointLimitKernel_lintegral_lt_top
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    (∫⁻ t : ℝ, halfLineEndpointLimitKernel t ∂rep.μ) < ⊤ := by
  have hmeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun t : ℝ =>
            ENNReal.ofReal
              (halfLineEndpointKernel (positiveRayEndpointApprox n) t)) rep.μ := by
    intro n
    exact (ENNReal.measurable_ofReal.comp
      (measurable_halfLineEndpointKernel_right
        (positiveRayEndpointApprox n))).aemeasurable
  have hmono :
      ∀ᵐ t ∂rep.μ,
        Monotone fun n : ℕ =>
          ENNReal.ofReal
            (halfLineEndpointKernel (positiveRayEndpointApprox n) t) := by
    filter_upwards [rep.ae_mem_Ici] with t ht
    exact halfLineEndpointKernel_approx_mono ht
  have htend :
      ∀ᵐ t ∂rep.μ,
        Tendsto
          (fun n : ℕ =>
            ENNReal.ofReal
              (halfLineEndpointKernel (positiveRayEndpointApprox n) t))
          atTop (𝓝 (halfLineEndpointLimitKernel t)) := by
    filter_upwards [rep.ae_mem_Ici] with t ht
    exact halfLineEndpointLimitKernel_tendsto ht
  have hmono_conv :=
    lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  have hreal_conv :=
    halfLineEndpointKernel_lintegral_tendsto rep hzero
  have hunique :
      (∫⁻ t : ℝ, halfLineEndpointLimitKernel t ∂rep.μ) =
        ENNReal.ofReal (h 1 - (rep.b : ℝ) - h 0) :=
    tendsto_nhds_unique hmono_conv hreal_conv
  rw [hunique]
  exact ENNReal.ofReal_lt_top

private theorem halfLineIntegralRep_inv_lintegral_lt_top_of_right_continuous
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤ := by
  calc
    (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) ≤
        ∫⁻ t : ℝ, halfLineEndpointLimitKernel t ∂rep.μ :=
          lintegral_mono_ae
            (by
              filter_upwards [rep.ae_mem_Ici] with t ht
              exact halfLineToKuboAndoDensity_le_endpointLimitKernel ht)
    _ < ⊤ := halfLineEndpointLimitKernel_lintegral_lt_top rep hzero

/-! ### Zero-Atom Removal and Endpoint Identity -/
private theorem halfLineEndpointLimitKernel_zero :
    halfLineEndpointLimitKernel 0 = ⊤ := by
  have hterm :
      (fun n : ℕ =>
        ENNReal.ofReal
          (halfLineEndpointKernel (positiveRayEndpointApprox n) 0))
        =
      fun n : ℕ => (n : ENNReal) := by
    funext n
    have hden : (positiveRayEndpointApprox n : ℝ) ≠ 0 :=
      (positiveRayEndpointApprox_pos n).ne'
    rw [halfLineEndpointKernel, positiveRayEndpointApprox]
    have hreal :
        (1 - ((n : ℝ) + 1)⁻¹) / (((n : ℝ) + 1)⁻¹ + 0) = n := by
      field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [hreal]
    simp
  unfold halfLineEndpointLimitKernel
  rw [hterm]
  exact ENNReal.iSup_natCast

private theorem halfLineIntegralRep_no_atom_zero_of_right_continuous
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    rep.μ ({0} : Set ℝ) = 0 := by
  have hfin := halfLineEndpointLimitKernel_lintegral_lt_top rep hzero
  by_contra hne
  have hsingleton :
      (∫⁻ t : ℝ in ({0} : Set ℝ), halfLineEndpointLimitKernel t ∂rep.μ) =
        ⊤ := by
    rw [lintegral_singleton, halfLineEndpointLimitKernel_zero]
    exact ENNReal.top_mul hne
  have hle :
      (∫⁻ t : ℝ in ({0} : Set ℝ), halfLineEndpointLimitKernel t ∂rep.μ) ≤
        ∫⁻ t : ℝ, halfLineEndpointLimitKernel t ∂rep.μ :=
    setLIntegral_le_lintegral _ _
  have htop :
      (∫⁻ t : ℝ, halfLineEndpointLimitKernel t ∂rep.μ) = ⊤ := by
    rw [hsingleton] at hle
    exact top_unique hle
  exact (ne_of_lt hfin) htop

private theorem halfLineIntegralRep_ae_mem_Ioi_of_right_continuous
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ) := by
  have hno := halfLineIntegralRep_no_atom_zero_of_right_continuous rep hzero
  have hici := rep.ae_mem_Ici
  have hnot0 : ∀ᵐ t ∂rep.μ, t ≠ 0 := by
    rw [ae_iff]
    simpa using hno
  filter_upwards [hici, hnot0] with t ht hne
  exact lt_of_le_of_ne (by simpa using ht) (Ne.symm hne)

private theorem halfLineEndpointKernel_norm_le_density
    {x t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    ‖halfLineEndpointKernel x t‖ ≤
      (halfLineToKuboAndoDensity t).toReal := by
  have htpos : 0 < t := by simpa using ht
  have htIci : t ∈ Set.Ici (0 : ℝ) := le_of_lt htpos
  have hnonneg := halfLineEndpointKernel_nonneg hx0 hx1 htIci
  have hden_pos : 0 < x + t := by linarith
  have htoReal := halfLineToKuboAndoDensity_toReal_of_pos htpos
  rw [Real.norm_of_nonneg hnonneg, htoReal]
  unfold halfLineEndpointKernel
  rw [div_le_iff₀ hden_pos]
  have hnonneg_prod : 0 ≤ x * (1 + t) := by positivity
  rw [le_inv_mul_iff₀ htpos]
  nlinarith

private theorem halfLineEndpointKernel_integral_tendsto_density
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    (hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ, halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ)
      atTop
      (𝓝 (∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ)) := by
  have hF_meas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable
          (fun t : ℝ =>
            halfLineEndpointKernel (positiveRayEndpointApprox n) t) rep.μ :=
    Eventually.of_forall fun n =>
      (measurable_halfLineEndpointKernel_right
        (positiveRayEndpointApprox n)).aestronglyMeasurable
  have hbound :
      ∀ᶠ n in atTop,
        ∀ᵐ t ∂rep.μ,
          ‖halfLineEndpointKernel (positiveRayEndpointApprox n) t‖ ≤
            (fun t : ℝ => (halfLineToKuboAndoDensity t).toReal) t := by
    refine Eventually.of_forall ?_
    intro n
    filter_upwards [hpos] with t ht
    exact halfLineEndpointKernel_norm_le_density
      (positiveRayEndpointApprox_pos n)
      (positiveRayEndpointApprox_le_one n) ht
  have hbound_int :
      Integrable (fun t : ℝ => (halfLineToKuboAndoDensity t).toReal) rep.μ :=
    halfLineToKuboAndoDensity_toReal_integrable rep hInv
  have hlim :
      ∀ᵐ t ∂rep.μ,
        Tendsto
          (fun n : ℕ =>
            halfLineEndpointKernel (positiveRayEndpointApprox n) t)
          atTop
          (𝓝 ((fun t : ℝ => (halfLineToKuboAndoDensity t).toReal) t)) := by
    filter_upwards [hpos] with t ht
    have htpos : 0 < t := by simpa using ht
    simpa [halfLineToKuboAndoDensity_toReal_of_pos htpos] using
      halfLineEndpointKernel_approx_tendsto_inv htpos
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := rep.μ)
    (F := fun n t => halfLineEndpointKernel (positiveRayEndpointApprox n) t)
    (f := fun t : ℝ => (halfLineToKuboAndoDensity t).toReal)
    (fun t : ℝ => (halfLineToKuboAndoDensity t).toReal)
    hF_meas hbound hbound_int hlim

private theorem halfLineIntegralRep_endpoint_zero_identity
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    (hzero : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)))
    (hInv : (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤)
    (hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ)) :
    h 0 =
      h 1 - (rep.b : ℝ) -
        ∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ := by
  have hlimit₁ :=
    halfLineEndpointKernel_lintegral_tendsto (rep := rep) hzero
  have hreal₁ :
      Tendsto
        (fun n : ℕ =>
          ∫ t : ℝ, halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ)
        atTop (𝓝 (h 1 - (rep.b : ℝ) - h 0)) := by
    have hformula :
        (fun n : ℕ =>
          ∫ t : ℝ, halfLineEndpointKernel (positiveRayEndpointApprox n) t ∂rep.μ)
          =
        fun n : ℕ =>
          h 1 + (rep.b : ℝ) * (positiveRayEndpointApprox n - 1) -
            h (positiveRayEndpointApprox n) := by
      funext n
      exact halfLineEndpointKernel_integral_eq rep
        (positiveRayEndpointApprox_pos n)
        (positiveRayEndpointApprox_le_one n)
    have hx_tendsto := positiveRayEndpointApprox_tendsto_nhdsGT
    have hx_nhds :
        Tendsto positiveRayEndpointApprox atTop (𝓝 (0 : ℝ)) :=
      hx_tendsto.mono_right nhdsWithin_le_nhds
    have hh_tendsto : Tendsto (fun n : ℕ => h (positiveRayEndpointApprox n))
        atTop (𝓝 (h 0)) :=
      hzero.comp hx_tendsto
    rw [hformula]
    have hb :
        Tendsto
          (fun n : ℕ => (rep.b : ℝ) * (positiveRayEndpointApprox n - 1))
          atTop (𝓝 (-(rep.b : ℝ))) := by
      have hsub :
          Tendsto (fun n : ℕ => positiveRayEndpointApprox n - 1)
            atTop (𝓝 (0 - 1)) :=
        hx_nhds.sub tendsto_const_nhds
      simpa using
        (tendsto_const_nhds.mul hsub :
          Tendsto
            (fun n : ℕ => (rep.b : ℝ) * (positiveRayEndpointApprox n - 1))
            atTop (𝓝 ((rep.b : ℝ) * (0 - 1))))
    convert ((tendsto_const_nhds.add hb).sub hh_tendsto) using 1
  have hreal₂ :=
    halfLineEndpointKernel_integral_tendsto_density rep hInv hpos
  have hid :
      (∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ) =
        h 1 - (rep.b : ℝ) - h 0 :=
    tendsto_nhds_unique hreal₂ hreal₁
  linarith


/-! ### Endpoint Package Theorem -/
/--
The endpoint package version of the Kubo--Ando representation theorem.

Right-continuity at `0` turns the half-line representation measure into a
finite Kubo--Ando measure by forcing integrability of `t⁻¹`.
-/
noncomputable def positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive h) :
    PositiveRayKuboAndoRep h := by
  let rep : HalfLineIntegralRep h :=
    halfLineIntegralRep_of_operatorMonotoneOnPositive hh.to_open
  have hInv :
      (∫⁻ t : ℝ, halfLineToKuboAndoDensity t ∂rep.μ) < ⊤ :=
    halfLineIntegralRep_inv_lintegral_lt_top_of_right_continuous rep
      hh.right_continuous_at_zero
  have hpos : ∀ᵐ t ∂rep.μ, t ∈ Set.Ioi (0 : ℝ) :=
    halfLineIntegralRep_ae_mem_Ioi_of_right_continuous rep
      hh.right_continuous_at_zero
  have hzero :
      h 0 =
        h 1 - (rep.b : ℝ) -
          ∫ t : ℝ, (halfLineToKuboAndoDensity t).toReal ∂rep.μ :=
    halfLineIntegralRep_endpoint_zero_identity rep
      hh.right_continuous_at_zero hInv hpos
  exact positiveRayKuboAndoRep_of_halfLineIntegralRep rep hInv hpos hzero

/--
Existence form of the Kubo--Ando representation: operator monotonicity on the
closed positive ray implies a positive-ray Kubo--Ando representation exists.
-/
theorem positiveRayKuboAndoRep_nonempty_of_operatorMonotoneOnClosedPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive h) :
    Nonempty (PositiveRayKuboAndoRep h) :=
  ⟨positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hh⟩


end

end Loewner
end TraceInequality
end Quantum
