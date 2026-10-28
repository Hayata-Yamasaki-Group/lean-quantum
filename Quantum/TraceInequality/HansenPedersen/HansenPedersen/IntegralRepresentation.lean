/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Quantum.TraceInequality.LaterConsequencesRetained
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Integral representations in the Hansen--Pedersen chapter

This file isolates the proved Stieltjes-integral calculation from the main
`HansenPedersen` dependency cone. Downstream Hiai--Petz files only need
`LaterConsequences` and should not import this file transitively; the
Gamma-function and improper-integral dependencies remain local to this
example file.  The unproved conjunction of both displayed formulas is kept in
the separate `HansenPedersen.Frontier` import surface.

## Main results

* `rpow_eq_integral_stieltjes_hp`: the proved first displayed identity from
  Example 5.1.18 (kept private to this calculation file).

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Example 5.1.18.
-/

namespace HansenPedersen

open MeasureTheory

/-- Source: Hiai–Yanagi, Example 5.1.18 (1). -/
private theorem rpow_eq_integral_stieltjes_hp {p : ℝ} (hp : 0 < p ∧ p < 1)
    (x : ℝ) (hx : 0 < x) :
    x ^ p = Real.sin (p * Real.pi) / Real.pi *
      ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t) := by
  /- Step 1: Reduce to a normalized Stieltjes integral with the constant separated. -/
  have h_integral : x ^ p = (Real.sin (p * Real.pi) / Real.pi) *
      ∫ t in Set.Ioi 0, x * t ^ (p - 1) / (x + t) := by
    /- Step 2: Change variables t = x * u so the x-dependence factors out as x ^ p. -/
    have h_subst :
        ∫ t in Set.Ioi 0, x * t ^ (p - 1) / (x + t) =
          x ^ p * ∫ t in Set.Ioi 0, t ^ (p - 1) / (1 + t) := by
      have h_subst : ∀ {f : ℝ → ℝ},
          ∫ t in Set.Ioi 0, f t = ∫ u in Set.Ioi 0, f (x * u) * x := by
        intro f
        rw [MeasureTheory.integral_mul_const]
        rw [MeasureTheory.integral_comp_mul_left_Ioi]
        all_goals norm_num [hx.ne']
        · rw [inv_mul_eq_div, div_mul_cancel₀ _ hx.ne']
        · exact RCLike.ofReal_pos.mp hx
      rw [h_subst, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [Real.mul_rpow (by positivity) (by linarith [hu.out])]
      rw [show p = p - 1 + 1 by ring_nf, Real.rpow_add hx, Real.rpow_one]
      have hx_ne : x ≠ 0 := ne_of_gt hx
      have hu_ne : 1 + u ≠ 0 := by nlinarith [hu.out]
      have hden : x + x * u = x * (1 + u) := by ring_nf
      field_simp [hden, hx_ne, hu_ne]
      ring_nf
    /- Step 3: Evaluate the universal integral by rewriting it as a product of Gamma integrals. -/
    have h_integral_value :
        ∫ t in Set.Ioi 0, t ^ (p - 1) / (1 + t) =
          Real.pi / Real.sin (p * Real.pi) := by
      have h_integral :
          ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (1 + t) =
            Real.Gamma p * Real.Gamma (1 - p) := by
        have h_expand :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) / (1 + t) =
              ∫ t in Set.Ioi (0 : ℝ),
                t ^ (p - 1) * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u * (1 + t)) := by
          field_simp
          have h_integral : ∀ t > 0,
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
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
            rw [h_integral t ht, mul_one_div]
        /- Step 4: Justify swapping integrals via Gamma-kernel integrability. -/
        have h_swap :
            ∫ t in Set.Ioi (0 : ℝ),
                t ^ (p - 1) * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u * (1 + t)) =
              ∫ u in Set.Ioi (0 : ℝ),
                ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) := by
          rw [MeasureTheory.integral_integral_swap]
          · simp +decide only [MeasureTheory.integral_const_mul]
          · have h_gamma : ∀ u > 0,
                ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
                  Real.exp (-u) * Real.Gamma p * u ^ (-p) := by
              intro u hu
              have h_gamma :
                  ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * t) =
                    Real.Gamma p * u ^ (-p) := by
                have := @integral_rpow_mul_exp_neg_mul_rpow
                convert @this 1 (p - 1) u one_pos (by linarith) hu using 1 <;>
                  norm_num
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
                  (fun u => Real.exp (-u) * Real.Gamma p * u ^ (-p)) (Set.Ioi (0 : ℝ)) := by
              have h_integrable :
                  MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * u ^ (-p))
                    (Set.Ioi (0 : ℝ)) := by
                have h_integral :
                    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-p) =
                      Real.Gamma (1 - p) := by
                  rw [Real.Gamma_eq_integral (by linarith : 0 < 1 - p)]
                  congr
                  ext
                  ring_nf
                by_contra h_not_integrable
                have h_zero := MeasureTheory.integral_undef h_not_integrable
                rw [h_zero] at h_integral
                linarith [Real.Gamma_pos_of_pos (by linarith : 0 < 1 - p)]
              simpa only [mul_assoc, mul_comm, mul_left_comm] using
                h_integrable.const_mul (Real.Gamma p)
            rw [MeasureTheory.integrable_prod_iff]
            · have h_integrable :
                  ∀ᵐ u ∂MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0),
                  MeasureTheory.Integrable (fun t => t ^ (p - 1) * Real.exp (-u * (1 + t)))
                    (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioi 0)) := by
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu using by
                  by_contra h
                  exact absurd (h_gamma u hu ▸ MeasureTheory.integral_undef h)
                    (ne_of_gt (mul_pos
                      (mul_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hp.1))
                      (Real.rpow_pos_of_pos hu _)))
              simp +zetaDelta only [neg_mul, Function.uncurry_apply_pair,
                measurableSet_Ioi, ae_restrict_eq, norm_mul, Real.norm_eq_abs,
                Real.abs_exp] at h_gamma h_integrable ⊢
              refine ⟨h_integrable, ?_⟩
              refine MeasureTheory.Integrable.congr h_integrable_gamma ?_
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu using by
                rw [← h_gamma u hu]
                exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by
                  rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht) _)]
            · exact Measurable.aestronglyMeasurable (by
                exact Measurable.mul (measurable_snd.pow_const _)
                  (Real.continuous_exp.measurable.comp
                    (measurable_neg.comp measurable_fst |>.mul
                      (measurable_const.add measurable_snd))))
        /- Step 5: Compute u-sections so the swap gives the last Gamma factor. -/
        have h_inner : ∀ u ∈ Set.Ioi (0 : ℝ),
            ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * (1 + t)) =
              Real.exp (-u) * Real.Gamma p * u ^ (-p) := by
          intros u hu
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
          have h_gamma_inner :
              ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * Real.exp (-u * t) =
                Real.Gamma p * u ^ (-p) := by
            have hq : -1 < p - 1 := by linarith
            convert
              @integral_rpow_mul_exp_neg_mul_rpow 1 (p - 1) u one_pos hq hu using 1 <;>
              norm_num
            ring_nf
          rw [h_subst, h_gamma_inner]
          ring_nf
        have h_gamma_one_sub :
            ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-p) =
              Real.Gamma (1 - p) := by
          rw [Real.Gamma_eq_integral (by linarith : 0 < 1 - p)]
          congr
          ext
          ring_nf
        rw [h_expand, h_swap]
        rw [← h_gamma_one_sub, ← MeasureTheory.integral_const_mul]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => by
          rw [h_inner u hu]
          ring_nf
      /- Step 6: Apply the Gamma reflection formula and cancel the normalizing constants. -/
      rw [h_integral, Real.Gamma_mul_Gamma_one_sub]
      field_simp
    rw [h_subst, h_integral_value, mul_comm]
    rw [mul_assoc,
      div_mul_div_cancel₀
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))),
      div_self (ne_of_gt Real.pi_pos), mul_one]
  exact h_integral

end HansenPedersen
