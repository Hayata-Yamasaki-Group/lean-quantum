import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform

import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.OuterMeasure.AE

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped UpperHalfPlane

noncomputable section

/-!
Step 28 (utility): the Stieltjes transform of a finite measure is a Pick function.

This provides a direct proof that `stieltjes μ` has nonnegative imaginary part on the upper
half-plane for any finite measure `μ` on `ℝ`.

This lemma is used to discharge `hpick` hypotheses in later steps when we introduce auxiliary
measures (e.g., support-elimination transforms).
-/

/-- The Stieltjes transform of any finite measure on `ℝ` is a Pick function: it has nonnegative
imaginary part on the upper half-plane. [simon2019] -/
theorem stieltjes_im_nonneg_of_isFiniteMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ z : ℍ, 0 ≤ (stieltjes μ z).im := by
  intro z
  let f : ℝ → ℂ := fun t => 1 / ((t : ℂ) - (z : ℂ))
  have hzpos : 0 < (z : ℂ).im := by
    simpa using z.coe_im_pos
  have hf_meas : AEStronglyMeasurable f μ := by
    -- The integrand is a measurable (in fact continuous) function of `t`.
    have hmeas : Measurable f := by
      -- `fun_prop` handles measurability of rational expressions.
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hf_bound : ∀ᵐ t ∂μ, ‖f t‖ ≤ ((z : ℂ).im)⁻¹ := by
    refine ae_of_all μ ?_
    intro t
    let w : ℂ := (t : ℂ) - (z : ℂ)
    have hw_im : w.im = - (z : ℂ).im := by
      simp [w]
    have hzle : (z : ℂ).im ≤ ‖w‖ := by
      have h0 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      -- `|w.im| = |z.im|` since `w.im = -z.im`.
      have hzabs : |(z : ℂ).im| ≤ ‖w‖ := by
        simpa [hw_im, abs_neg] using h0
      -- Drop the absolute value.
      exact le_trans (le_abs_self ((z : ℂ).im)) hzabs
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hzpos hzle
    have : ‖w‖⁻¹ ≤ ((z : ℂ).im)⁻¹ :=
      (inv_le_inv₀ hwpos hzpos).2 hzle
    -- Convert the bound to the desired form.
    simpa [f, w, one_div, norm_inv] using this
  have hf_integrable : Integrable f μ :=
    Integrable.of_bound (μ := μ) hf_meas ((z : ℂ).im)⁻¹ hf_bound
  -- `Im (∫ f) = ∫ Im(f)` for an integrable complex-valued function.
  have him_eq :
      (stieltjes μ z).im = ∫ t, (f t).im ∂μ := by
    have := (integral_im (μ := μ) (f := f) hf_integrable)
    -- Unfold `stieltjes` and `f`.
    simpa [stieltjes, f] using this.symm
  -- The integrand has nonnegative imaginary part pointwise.
  have him_nonneg : (∀ᵐ t ∂μ, 0 ≤ (f t).im) := by
    refine ae_of_all μ ?_
    intro t
    let w : ℂ := (t : ℂ) - (z : ℂ)
    have hw_im : w.im = - (z : ℂ).im := by
      simp [w]
    have hw_ne : w ≠ 0 := by
      intro hw0
      have : w.im = 0 := by simp [hw0]
      exact (ne_of_gt hzpos) (by simpa [hw_im] using this)
    have hw_pos : 0 < Complex.normSq w := by
      simpa [Complex.normSq_pos] using hw_ne
    -- `Im (w⁻¹) = -Im(w) / normSq(w)`.
    have hEq : (f t).im = (z : ℂ).im / Complex.normSq w := by
      -- `-w.im = z.im` from `w.im = -z.im`.
      simp [f, w, one_div, Complex.inv_im, hw_im]
    -- Conclude nonnegativity.
    have hnonneg : 0 ≤ (z : ℂ).im / Complex.normSq w :=
      div_nonneg (le_of_lt hzpos) (le_of_lt hw_pos)
    simpa [hEq] using hnonneg
  have him_integrable : Integrable (fun t => (f t).im) μ :=
    hf_integrable.im
  have : 0 ≤ ∫ t, (f t).im ∂μ := by
    exact MeasureTheory.integral_nonneg_of_ae (μ := μ) him_nonneg
  simpa [him_eq] using this

end

end Quantum.TraceInequality.Loewner
