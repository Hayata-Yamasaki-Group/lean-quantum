import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Gamma
import Quantum.TraceInequality.Loewner.HalfLine.ConvexRep
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo

/-!
# The Kubo--Ando representation for `x ↦ x ^ p`

This module contains the finite Kubo--Ando measure and operator monotonicity
wrappers for `x ↦ x ^ p`, `0 < p < 1`.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-- Density in the finite Kubo--Ando representation of `x ↦ x ^ p`, `0 < p < 1`. -/
def positiveRayRpowKuboAndoDensity (p t : ℝ) : ℝ :=
  Real.sin (p * Real.pi) / Real.pi * (t ^ (p - 1) / (1 + t))

private theorem measurable_positiveRayRpowKuboAndoDensity (p : ℝ) :
    Measurable fun t : ℝ => positiveRayRpowKuboAndoDensity p t := by
  unfold positiveRayRpowKuboAndoDensity
  measurability

private theorem measurable_positiveRayRpowKuboAndoDensity_ennreal (p : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t) := by
  exact ENNReal.measurable_ofReal.comp
    (measurable_positiveRayRpowKuboAndoDensity p)

private theorem positiveRayRpowKuboAndoDensity_nonneg
    {p t : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ positiveRayRpowKuboAndoDensity p t := by
  have hp_pos : 0 < p := hp.1
  have hp_lt : p < 1 := hp.2
  have ht_pos : 0 < t := by simpa using ht
  have hsin_pos : 0 < Real.sin (p * Real.pi) := by
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_nonneg : 0 ≤ Real.sin (p * Real.pi) / Real.pi := by
    exact le_of_lt (div_pos hsin_pos Real.pi_pos)
  have hk_nonneg : 0 ≤ t ^ (p - 1) / (1 + t) := by
    positivity
  unfold positiveRayRpowKuboAndoDensity
  positivity

private theorem positiveRayRpowKuboAndoDensity_integrable
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Integrable (fun t : ℝ => positiveRayRpowKuboAndoDensity p t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hbase :
      Integrable (fun t : ℝ => Real.rpowIntegrand₀₁ p t 1)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using
      Real.integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one
  have hEq :
      (fun t : ℝ => Real.rpowIntegrand₀₁ p t 1)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t : ℝ => t ^ (p - 1) / (1 + t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa using ht)
    have h := Real.rpowIntegrand₀₁_eq_pow_div hp ht0 zero_le_one
    simpa [add_comm, mul_one] using h
  have hkernel :
      Integrable (fun t : ℝ => t ^ (p - 1) / (1 + t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hbase.congr hEq
  simpa [positiveRayRpowKuboAndoDensity] using
    hkernel.const_mul (Real.sin (p * Real.pi) / Real.pi)

/-- The finite measure in the Kubo--Ando representation of `x ↦ x ^ p`. -/
noncomputable def positiveRayRpowKuboAndoMeasure
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)),
    MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (positiveRayRpowKuboAndoDensity_integrable hp).hasFiniteIntegral⟩

private theorem positiveRayRpowKuboAndoMeasure_support
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (positiveRayRpowKuboAndoMeasure hp : Measure ℝ)
      (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  have hac :
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t))) ≪
          volume.restrict (Set.Ioi (0 : ℝ)) := by
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hbase : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioi.compl]
    rw [compl_Ioi, Iic_inter_Ioi]
    simp
  exact hac hbase

private theorem positiveRayRpowKuboAndoMeasure_support_Ici
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (positiveRayRpowKuboAndoMeasure hp : Measure ℝ)
      (Set.Ici (0 : ℝ))ᶜ = 0 := by
  refine measure_mono_null ?_ (positiveRayRpowKuboAndoMeasure_support hp)
  intro t ht
  simp only [mem_compl_iff, mem_Ici] at ht ⊢
  intro htpos
  exact ht (le_of_lt htpos)

private theorem positiveRayRpow_density_mul_kernel_eq_stieltjes
    {p x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    positiveRayRpowKuboAndoDensity p t * positiveRayKuboAndoKernel x t =
      (Real.sin (p * Real.pi) / Real.pi) *
        (x * t ^ (p - 1) / (x + t)) := by
  have hden1 : 1 + t ≠ 0 := by linarith
  have hden2 : x + t ≠ 0 := by linarith
  unfold positiveRayRpowKuboAndoDensity positiveRayKuboAndoKernel
  field_simp [hden1, hden2]

private theorem positiveRay_rpow_eq_integral_stieltjes
    {p : ℝ} (hp : 0 < p ∧ p < 1) (x : ℝ) (hx : 0 < x) :
    x ^ p =
      Real.sin (p * Real.pi) / Real.pi *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := by
  have h_integral :
      x ^ p =
        (Real.sin (p * Real.pi) / Real.pi) *
          ∫ t in Set.Ioi 0, x * t ^ (p - 1) / (x + t) := by
    have h_subst :
        ∫ t in Set.Ioi 0, x * t ^ (p - 1) / (x + t) =
          x ^ p * ∫ t in Set.Ioi 0, t ^ (p - 1) / (1 + t) := by
      have h_subst :
          ∀ {f : ℝ → ℝ}, ∫ t in Set.Ioi 0, f t =
            ∫ u in Set.Ioi 0, f (x * u) * x := by
        intro f
        rw [MeasureTheory.integral_mul_const]
        rw [MeasureTheory.integral_comp_mul_left_Ioi]
        · rw [mul_zero, smul_eq_mul]
          rw [mul_assoc, mul_comm (∫ t in Set.Ioi (0 : ℝ), f t), ← mul_assoc,
            inv_mul_cancel₀ hx.ne', one_mul]
        · exact RCLike.ofReal_pos.mp hx
      rw [h_subst, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [Real.mul_rpow (by positivity) (by linarith [hu.out])]
      rw [show p = p - 1 + 1 by ring_nf, Real.rpow_add hx, Real.rpow_one]
      ring_nf
      grind
    have h_integral_value :
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (1 + t) =
          Real.pi / Real.sin (p * Real.pi) := by
      have h_integral :
          ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (1 + t) =
            Real.Gamma p * Real.Gamma (1 - p) := by
        have h_integral_kernel :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (1 + t) =
              ∫ t in Set.Ioi (0 : ℝ),
                t ^ (p - 1) *
                  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u * (1 + t)) := by
          field_simp
          have h_integral :
              ∀ t > 0,
                ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u * (1 + t))) =
                  1 / (1 + t) := by
            intro t ht
            have h_exp :
                ∀ t > 0,
                  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u * (1 + t))) =
                    1 / (1 + t) := by
              intro t ht
              have :
                  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u * (1 + t))) =
                    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u * (1 + t)) := by
                norm_num
              rw [this]
              exact (by
                convert integral_exp_neg_mul_rpow zero_lt_one (add_pos zero_lt_one ht) using 1 <;>
                  norm_num [Real.rpow_neg_one]
                exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => by ring_nf)
            exact h_exp t ht
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
            rw [h_integral t ht, mul_one_div]
        have h_integral_swap :
            ∫ t in Set.Ioi (0 : ℝ),
                t ^ (p - 1) *
                  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u * (1 + t)) =
              ∫ u in Set.Ioi (0 : ℝ),
                ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) := by
          rw [MeasureTheory.integral_integral_swap]
          · simp +decide only [MeasureTheory.integral_const_mul]
          · have h_gamma :
                ∀ u > 0,
                  ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
                    Real.exp (-u) * Real.Gamma p * u ^ (-p) := by
              intro u hu
              have h_gamma :
                  ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * t) =
                    Real.Gamma p * u ^ (-p) := by
                have := @integral_rpow_mul_exp_neg_mul_rpow
                convert @this 1 (p - 1) u one_pos (by linarith) hu using 1 <;> norm_num
                ring_nf
              convert congr_arg (fun y => Real.exp (-u) * y) h_gamma using 1 <;> ring_nf
              rw [← MeasureTheory.integral_const_mul]
              congr
              ext
              rw [mul_left_comm]
              rw [← Real.exp_add]
              ring_nf
            have h_integrable_gamma :
                MeasureTheory.IntegrableOn
                  (fun u => Real.exp (-u) * Real.Gamma p * u ^ (-p))
                  (Set.Ioi (0 : ℝ)) := by
              have h_integrable_base :
                  MeasureTheory.IntegrableOn
                    (fun u => Real.exp (-u) * u ^ (-p)) (Set.Ioi (0 : ℝ)) := by
                have h_integral :
                    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-p) =
                      Real.Gamma (1 - p) := by
                  rw [Real.Gamma_eq_integral (by linarith : 0 < 1 - p)]
                  congr
                  ext
                  ring_nf
                exact (by
                  contrapose! h_integral
                  rw [MeasureTheory.integral_undef h_integral]
                  linarith [Real.Gamma_pos_of_pos (by linarith : 0 < 1 - p)])
              simpa only [mul_assoc, mul_comm, mul_left_comm] using
                h_integrable_base.const_mul (Real.Gamma p)
            rw [MeasureTheory.integrable_prod_iff]
            · have h_integrable_fibers :
                  ∀ᵐ u ∂MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0),
                    MeasureTheory.Integrable
                      (fun t => t ^ (p - 1) * Real.exp (-u * (1 + t)))
                      (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0)) := by
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
                exact (by
                  by_contra h
                  exact absurd
                    (h_gamma u hu ▸ MeasureTheory.integral_undef h)
                    (ne_of_gt (mul_pos (mul_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hp.1))
                      (Real.rpow_pos_of_pos hu _))))
              simp +zetaDelta only [neg_mul, Function.uncurry_apply_pair, measurableSet_Ioi,
                ae_restrict_eq, norm_mul, Real.norm_eq_abs, Real.abs_exp] at *
              refine ⟨h_integrable_fibers, ?_⟩
              refine MeasureTheory.Integrable.congr h_integrable_gamma ?_
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
              rw [← h_gamma u hu]
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
                rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht) _)]
            · exact Measurable.aestronglyMeasurable
                (by
                  exact Measurable.mul (measurable_snd.pow_const _)
                    (Real.continuous_exp.measurable.comp
                      (measurable_neg.comp measurable_fst |> Measurable.mul <|
                        measurable_const.add measurable_snd)))
        have h_integral_gamma :
            ∀ u ∈ Set.Ioi (0 : ℝ),
              ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
                Real.exp (-u) * Real.Gamma p * u ^ (-p) := by
          intro u hu
          have h_subst :
              ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
                Real.exp (-u) *
                  ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * t) := by
            rw [← MeasureTheory.integral_const_mul]
            congr
            ext t
            rw [mul_left_comm]
            rw [← Real.exp_add]
            ring_nf
          have h_gamma :
              ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * t) =
                Real.Gamma p * u ^ (-p) := by
            have := @integral_rpow_mul_exp_neg_mul_rpow
            convert @this 1 (p - 1) u one_pos (by linarith) hu using 1 <;> norm_num
            ring_nf
          rw [h_subst, h_gamma]
          ring_nf
        have h_integral_gamma_one_sub :
            ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-p) =
              Real.Gamma (1 - p) := by
          rw [Real.Gamma_eq_integral (by linarith : 0 < 1 - p)]
          congr
          ext
          ring_nf
        rw [h_integral_kernel, h_integral_swap]
        calc
          ∫ u in Set.Ioi (0 : ℝ),
              ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
            ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * Real.Gamma p * u ^ (-p) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu =>
                h_integral_gamma u hu
          _ = Real.Gamma p * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-p) := by
            rw [← MeasureTheory.integral_const_mul]
            exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => by
              ring_nf
          _ = Real.Gamma p * Real.Gamma (1 - p) := by
            rw [h_integral_gamma_one_sub]
      rw [h_integral, Real.Gamma_mul_Gamma_one_sub]
      field_simp
    rw [h_subst, h_integral_value, mul_comm]
    rw [mul_assoc,
      div_mul_div_cancel₀
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))),
      div_self (ne_of_gt Real.pi_pos), mul_one]
  exact h_integral

private theorem positiveRay_rpow_stieltjes_formula
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 < x) :
    x ^ p =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) :=
  positiveRay_rpow_eq_integral_stieltjes ⟨hp.1, hp.2⟩ x hx

/-- The Stieltjes integral formula for `x ↦ x ^ p`, `0 < p < 1`. -/
theorem positiveRay_rpow_stieltjes_formula_of_mem_Ioo_zero_one
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 < x) :
    x ^ p =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) :=
  positiveRay_rpow_stieltjes_formula hp hx

/-- The resolvent Stieltjes formula for `x ↦ x ^ (p - 1)`, `0 < p < 1`. -/
theorem positiveRay_rpow_sub_one_resolvent_formula_of_mem_Ioo_zero_one
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 < x) :
    x ^ (p - 1) =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := by
  have hformula := positiveRay_rpow_stieltjes_formula hp hx
  have hintegral :
      (∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t)) =
        x * ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ht => ?_
    ring
  have hpow : x ^ p = x * x ^ (p - 1) := by
    calc
      x ^ p = x ^ (1 + (p - 1)) := by congr 1; ring
      _ = x ^ (1 : ℝ) * x ^ (p - 1) := by rw [Real.rpow_add hx]
      _ = x * x ^ (p - 1) := by rw [Real.rpow_one]
  have hxne : x ≠ 0 := ne_of_gt hx
  calc
    x ^ (p - 1) = x⁻¹ * x ^ p := by
      rw [hpow]
      field_simp [hxne]
    _ = x⁻¹ * ((Real.sin (p * Real.pi) / Real.pi) *
          ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t)) := by
      rw [hformula]
    _ = (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := by
      rw [hintegral]
      field_simp [hxne]

private theorem positiveRayRpowKuboAndoMeasure_integral_kernel
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 < x) :
    (∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := by
  let μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hwd :
      (∫ t : ℝ, positiveRayKuboAndoKernel x t
          ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
        ∫ t : ℝ,
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayKuboAndoKernel x t ∂μ0 := by
    have htop :
        ∀ᵐ t ∂μ0,
          ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t) < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun _ => by simp)
    simpa [positiveRayRpowKuboAndoMeasure, μ0] using
      integral_withDensity_eq_integral_toReal_smul
        (μ := μ0)
        (measurable_positiveRayRpowKuboAndoDensity_ennreal p)
        htop
        (fun t : ℝ => positiveRayKuboAndoKernel x t)
  have htoReal :
      (fun t : ℝ =>
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayKuboAndoKernel x t)
        =ᵐ[μ0]
      fun t : ℝ =>
        positiveRayRpowKuboAndoDensity p t * positiveRayKuboAndoKernel x t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hdens_nonneg := positiveRayRpowKuboAndoDensity_nonneg hp ht
    rw [ENNReal.toReal_ofReal hdens_nonneg]
    simp
  calc
    (∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
        ∫ t : ℝ,
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayKuboAndoKernel x t ∂μ0 := hwd
    _ = ∫ t : ℝ,
        positiveRayRpowKuboAndoDensity p t * positiveRayKuboAndoKernel x t ∂μ0 := by
          exact integral_congr_ae htoReal
    _ = ∫ t in Set.Ioi (0 : ℝ),
        positiveRayRpowKuboAndoDensity p t * positiveRayKuboAndoKernel x t := by
          rfl
    _ = ∫ t in Set.Ioi (0 : ℝ),
        (Real.sin (p * Real.pi) / Real.pi) *
          (x * t ^ (p - 1) / (x + t)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          exact positiveRayRpow_density_mul_kernel_eq_stieltjes hx (by simpa using ht)
    _ = (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := by
          rw [integral_const_mul]

private theorem positiveRayRpow_density_mul_resolvent_eq_stieltjes
    {p x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    positiveRayRpowKuboAndoDensity p t * positiveRayResolventKernel x t =
      (Real.sin (p * Real.pi) / Real.pi) *
        (t ^ (p - 1) / (x + t)) := by
  have hden1 : 1 + t ≠ 0 := by linarith
  have hden2 : x + t ≠ 0 := by linarith
  unfold positiveRayRpowKuboAndoDensity positiveRayResolventKernel
  field_simp [hden1, hden2]

private theorem positiveRayRpowKuboAndoMeasure_integral_resolvent_kernel
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 < x) :
    (∫ t : ℝ, positiveRayResolventKernel x t
        ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := by
  let μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hwd :
      (∫ t : ℝ, positiveRayResolventKernel x t
          ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
        ∫ t : ℝ,
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayResolventKernel x t ∂μ0 := by
    have htop :
        ∀ᵐ t ∂μ0,
          ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t) < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun _ => by simp)
    simpa [positiveRayRpowKuboAndoMeasure, μ0] using
      integral_withDensity_eq_integral_toReal_smul
        (μ := μ0)
        (measurable_positiveRayRpowKuboAndoDensity_ennreal p)
        htop
        (fun t : ℝ => positiveRayResolventKernel x t)
  have htoReal :
      (fun t : ℝ =>
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayResolventKernel x t)
        =ᵐ[μ0]
      fun t : ℝ =>
        positiveRayRpowKuboAndoDensity p t * positiveRayResolventKernel x t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hdens_nonneg := positiveRayRpowKuboAndoDensity_nonneg hp ht
    rw [ENNReal.toReal_ofReal hdens_nonneg]
    simp
  calc
    (∫ t : ℝ, positiveRayResolventKernel x t
        ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ)) =
        ∫ t : ℝ,
          (ENNReal.ofReal (positiveRayRpowKuboAndoDensity p t)).toReal •
            positiveRayResolventKernel x t ∂μ0 := hwd
    _ = ∫ t : ℝ,
        positiveRayRpowKuboAndoDensity p t * positiveRayResolventKernel x t ∂μ0 := by
          exact integral_congr_ae htoReal
    _ = ∫ t in Set.Ioi (0 : ℝ),
        positiveRayRpowKuboAndoDensity p t * positiveRayResolventKernel x t := by
          rfl
    _ = ∫ t in Set.Ioi (0 : ℝ),
        (Real.sin (p * Real.pi) / Real.pi) *
          (t ^ (p - 1) / (x + t)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          exact positiveRayRpow_density_mul_resolvent_eq_stieltjes hx (by simpa using ht)
    _ = (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := by
          rw [integral_const_mul]

/-- The Kubo--Ando finite-measure representation of `x ↦ x ^ p`, for `0 < p < 1`. -/
noncomputable def positiveRayKuboAndoRep_rpow_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    PositiveRayKuboAndoRep (fun x : ℝ => x ^ p) where
  b := 0
  ν := positiveRayRpowKuboAndoMeasure hp
  support := positiveRayRpowKuboAndoMeasure_support hp
  formula := by
    intro x hx
    rcases eq_or_lt_of_le (by simpa using hx) with rfl | hxpos
    · simp [positiveRayKuboAndoKernel, Real.zero_rpow hp.1.ne']
    · have hintegral :=
        positiveRayRpowKuboAndoMeasure_integral_kernel hp hxpos
      have hformula := positiveRay_rpow_stieltjes_formula hp hxpos
      calc
        x ^ p =
            (Real.sin (p * Real.pi) / Real.pi) *
              ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := hformula
        _ = 0 ^ p + ((0 : NNReal) : ℝ) * x +
            ∫ t : ℝ, positiveRayKuboAndoKernel x t
              ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ) := by
              rw [hintegral]
              simp [Real.zero_rpow hp.1.ne']

/--
The resolvent representation of `x ↦ x ^ (p - 1)`, obtained from the same
finite measure as the Kubo--Ando representation of `x ↦ x ^ p`.
-/
noncomputable def positiveRayOperatorMonotoneDecreasingRep_rpow_sub_one_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    PositiveRayOperatorMonotoneDecreasingRep (fun x : ℝ => x ^ (p - 1)) where
  a := 0
  μ := positiveRayRpowKuboAndoMeasure hp
  support := positiveRayRpowKuboAndoMeasure_support_Ici hp
  formula := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hintegral :=
      positiveRayRpowKuboAndoMeasure_integral_resolvent_kernel hp hxpos
    have hformula :=
      positiveRay_rpow_sub_one_resolvent_formula_of_mem_Ioo_zero_one hp hxpos
    calc
      x ^ (p - 1) =
          (Real.sin (p * Real.pi) / Real.pi) *
            ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (x + t) := hformula
      _ = ((0 : NNReal) : ℝ) +
          ∫ t : ℝ, positiveRayResolventKernel x t
            ∂(positiveRayRpowKuboAndoMeasure hp : Measure ℝ) := by
            rw [hintegral]
            simp

/-- The finite-right-derivative integral formula for `x ↦ x ^ (p + 1)`. -/
theorem positiveRay_rpow_add_one_finiteRightDerivative_formula_of_mem_Ioo_zero_one
    {p x : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 ≤ x) :
    x ^ (p + 1) =
      (Real.sin (p * Real.pi) / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ), x^2 * t ^ (p - 1) / (x + t) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hp1_ne : p + 1 ≠ 0 := by
      exact ne_of_gt (by linarith [hp.1])
    simp [Real.zero_rpow hp1_ne]
  · have hformula := positiveRay_rpow_stieltjes_formula hp hxpos
    have hintegral :
        (∫ t in Set.Ioi (0 : ℝ), x^2 * t ^ (p - 1) / (x + t)) =
          x * ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ht => ?_
      ring
    have hpow : x ^ (p + 1) = x * x ^ p := by
      rw [show p + 1 = 1 + p by ring]
      rw [Real.rpow_add hxpos, Real.rpow_one]
    calc
      x ^ (p + 1) = x * x ^ p := hpow
      _ = x * ((Real.sin (p * Real.pi) / Real.pi) *
            ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t)) := by
            rw [hformula]
      _ = (Real.sin (p * Real.pi) / Real.pi) *
          ∫ t in Set.Ioi (0 : ℝ), x^2 * t ^ (p - 1) / (x + t) := by
            rw [hintegral]
            ring

/--
The finite-right-derivative operator-convex representation of
`x ↦ x ^ (p + 1)`, obtained by multiplying the Kubo--Ando representation of
`x ↦ x ^ p` by `x`.
-/
noncomputable def positiveRayOperatorConvexRepFiniteRightDerivative_rpow_add_one_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    PositiveRayOperatorConvexRepFiniteRightDerivative (fun x : ℝ => x ^ (p + 1)) :=
  positiveRayOperatorConvexRepFiniteRightDerivative_of_positiveRayKuboAndoRep
    (h := fun x : ℝ => x ^ p)
    (by
      intro x hx
      have hxpos : 0 < x := by simpa using hx
      have hp1_ne : p + 1 ≠ 0 := by
        exact ne_of_gt (by linarith [hp.1])
      have hpow : x ^ (p + 1) = x * x ^ p := by
        rw [show p + 1 = 1 + p by ring]
        rw [Real.rpow_add hxpos, Real.rpow_one]
      rw [hpow, Real.zero_rpow hp1_ne]
      ring)
    (positiveRayKuboAndoRep_rpow_of_mem_Ioo_zero_one hp)

/-- The Löwner-theorem proof that `x ↦ x ^ p` is operator monotone on the positive half-line. -/
theorem operatorMonotoneOnPositive_rpow_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    OperatorMonotoneOnPositive (fun x : ℝ => x ^ p) :=
  operatorMonotoneOnPositive_of_positiveRayKuboAndoRep
    (positiveRayKuboAndoRep_rpow_of_mem_Ioo_zero_one hp)

/-- Endpoint version of the Löwner-theorem proof for `x ↦ x ^ p`, `0 < p < 1`. -/
theorem operatorMonotoneOnClosedPositive_rpow_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    OperatorMonotoneOnClosedPositive (fun x : ℝ => x ^ p) :=
  operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep
    (positiveRayKuboAndoRep_rpow_of_mem_Ioo_zero_one hp)

/-- Direct CFC version of the Löwner-theorem proof for `x ↦ x ^ p`, `0 < p < 1`. -/
theorem operatorMonotoneOnClosedPositiveCFC_rpow_of_mem_Ioo_zero_one
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    OperatorMonotoneOnClosedPositiveCFC (fun x : ℝ => x ^ p) :=
  operatorMonotoneOnClosedPositiveCFC_of_endpoint
    (operatorMonotoneOnClosedPositive_rpow_of_mem_Ioo_zero_one hp)

end

end Loewner
end TraceInequality
end Quantum
