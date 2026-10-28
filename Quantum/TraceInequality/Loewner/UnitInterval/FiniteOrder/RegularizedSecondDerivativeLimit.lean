import Quantum.Analysis.Calculus.UniformCauchy
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizedConfluentHankel
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Continuous


/-!
# Chapter 20 regularized second-derivative limit package

This file contains the local uniform-Cauchy transfer and the C3 Taylor limit
arguments that turn the regularized confluent Hankel bounds into the public
C1 pilot regularity handoff.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution
open scoped fwdDiff

noncomputable section

/-- For a `C³` function, the right-shift Taylor remainder of `f'` is `o(h^2)`. -/
lemma deriv_taylor2_remainder_tendsto_C3 {f : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (deriv f (x + h) -
          (deriv f x +
            h * (deriv^[1] (deriv f)) x +
              h ^ 2 / 2 * (deriv^[2] (deriv f)) x)) / h ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hderivC2 :
      ContDiffOn ℝ 2 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC3.deriv_of_isOpen (m := 2) isOpen_Ioo (by decide)
  have ht :=
    Real.taylor_tendsto (f := deriv f) (x₀ := x) (n := 2)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hderivC2
  have htcomp := ht.comp (tendsto_add_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  refine Eventually.of_forall ?_
  intro h
  simp [Function.comp_apply,
    iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDeriv_eq_iterate, sub_eq_add_neg]
  ring_nf

/--
For a `C³` function, the right secant has third-order Taylor remainder
`o(h^2)` after division by `h`.
-/
lemma secant_taylor3_remainder_tendsto_C3 {f : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (((f (x + h) - f x) / h -
          (deriv f x +
            h / 2 * (deriv^[1] (deriv f)) x +
              h ^ 2 / 6 * (deriv^[2] (deriv f)) x)) / h ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht :=
    Real.taylor_tendsto (f := f) (x₀ := x) (n := 3)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hC3
  have htcomp := ht.comp (tendsto_add_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhne : h ≠ 0 := ne_of_gt hh
  simp only [Function.comp_apply]
  rw [taylor3_eval_Ioo (f := f) hx]
  field_simp [hhne]
  ring

/--
The two-point Löwner determinant divided by `h^2` has the expected
Simon Chapter 20 confluent limit.
-/
lemma twoPoint_det_scaled_tendsto_C3 {f : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (deriv f x * deriv f (x + h) -
          ((f (x + h) - f x) / h) ^ 2) / h ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv f x * (deriv^[2] (deriv f)) x / 6 -
        ((deriv^[1] (deriv f)) x) ^ 2 / 4)) := by
  let a : ℝ := deriv f x
  let b : ℝ := (deriv^[1] (deriv f)) x
  let c : ℝ := (deriv^[2] (deriv f)) x
  let R₁ : ℝ → ℝ := fun h =>
    (deriv f (x + h) - (a + h * b + h ^ 2 / 2 * c)) / h ^ 2
  let R₂ : ℝ → ℝ := fun h =>
    (((f (x + h) - f x) / h - (a + h / 2 * b + h ^ 2 / 6 * c)) / h ^ 2)
  have hR₁ : Tendsto R₁ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [R₁, a, b, c, mul_comm, mul_left_comm, mul_assoc] using
      deriv_taylor2_remainder_tendsto_C3 (f := f) hC3 hx
  have hR₂ : Tendsto R₂ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [R₂, a, b, c, mul_comm, mul_left_comm, mul_assoc] using
      secant_taylor3_remainder_tendsto_C3 (f := f) hC3 hx
  have hh : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have htuple :
      Tendsto (fun h : ℝ => ((h, R₁ h), R₂ h))
        (𝓝[>] (0 : ℝ)) (𝓝 (((0 : ℝ), 0), 0)) :=
    (hh.prodMk_nhds hR₁).prodMk_nhds hR₂
  let expanded : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    a * c / 6 - b ^ 2 / 4 -
      b * c / 6 * p.1.1 - c ^ 2 / 36 * p.1.1 ^ 2 +
        a * p.1.2 -
          2 * (a + p.1.1 / 2 * b + p.1.1 ^ 2 / 6 * c) * p.2 -
            p.1.1 ^ 2 * p.2 ^ 2
  have hcont : ContinuousAt expanded (((0 : ℝ), 0), 0) := by
    dsimp [expanded]
    fun_prop
  have hexp :
      Tendsto (fun h : ℝ => expanded ((h, R₁ h), R₂ h))
        (𝓝[>] (0 : ℝ)) (𝓝 (a * c / 6 - b ^ 2 / 4)) := by
    have hlim0 := hcont.tendsto.comp htuple
    have htarget :
        expanded (((0 : ℝ), 0), 0) = a * c / 6 - b ^ 2 / 4 := by
      dsimp [expanded]
      ring
    simpa [htarget] using hlim0
  refine Tendsto.congr' ?_ hexp
  filter_upwards [self_mem_nhdsWithin] with h hhpos
  have hhne : h ≠ 0 := ne_of_gt hhpos
  dsimp [expanded, R₁, R₂, a, b, c]
  field_simp [hhne]
  ring

/--
For a `C³` public Löwner-positive function, the third derivative is nonnegative
at every interior point.
-/
theorem deriv2_deriv_nonneg_of_loewnerPosOnUnitInterval_C3 {f : ℝ → ℝ}
    (hpos : LoewnerPosOnUnitInterval f)
    (hC3 : ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ (deriv^[2] (deriv f)) x := by
  let a : ℝ := deriv f x
  let b : ℝ := (deriv^[1] (deriv f)) x
  let c : ℝ := (deriv^[2] (deriv f)) x
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact deriv_nonneg_on_Ioo_of_loewnerPosOnUnitInterval hpos hx
  have hscaled_nonneg :
      ∀ᶠ h in 𝓝[>] (0 : ℝ),
        0 ≤
          (deriv f x * deriv f (x + h) -
            ((f (x + h) - f x) / h) ^ 2) / h ^ 2 := by
    have hmem :
        ∀ᶠ h in 𝓝[>] (0 : ℝ), x + h ∈ Set.Ioo (-1 : ℝ) 1 :=
      (tendsto_add_right_nhdsWithin_Ioo hx).eventually
        (self_mem_nhdsWithin : Set.Ioo (-1 : ℝ) 1 ∈
          𝓝[Set.Ioo (-1 : ℝ) 1] x)
    filter_upwards [self_mem_nhdsWithin, hmem] with h hhpos hy
    have hhne : h ≠ 0 := ne_of_gt hhpos
    have hxy : x ≠ x + h := by
      intro hxeq
      have : h = 0 := by linarith
      exact hhne this
    have hdet :=
      diffQuot_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
        (f := f) hpos hx hy hxy
    have hden : 0 ≤ h ^ 2 := sq_nonneg h
    exact div_nonneg (by simpa [sub_eq_add_neg] using hdet) hden
  have hscaled_lim :=
    twoPoint_det_scaled_tendsto_C3 (f := f) hC3 hx
  have halpha :
      0 ≤ a * c / 6 - b ^ 2 / 4 := by
    simpa [a, b, c] using ge_of_tendsto hscaled_lim hscaled_nonneg
  by_cases ha_pos : 0 < a
  · have hb_sq_nonneg : 0 ≤ b ^ 2 / 4 := by positivity
    have : 0 ≤ a * c / 6 := by linarith
    have hdivpos : 0 < a / 6 := by positivity
    have : 0 ≤ c := by nlinarith
    simpa [c] using this
  · have ha_zero : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha_nonneg
    have hb_zero : b = 0 := by
      have : 0 ≤ -(b ^ 2 / 4) := by
        simpa [ha_zero] using halpha
      nlinarith [sq_nonneg b]
    have hderiv_scaled_lim :
        Tendsto
          (fun h : ℝ => deriv f (x + h) / h ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (c / 2)) := by
      have hrem := deriv_taylor2_remainder_tendsto_C3 (f := f) hC3 hx
      have hlim0 :
          Tendsto
            (fun h : ℝ =>
              (deriv f (x + h) -
                (deriv f x +
                  h * (deriv^[1] (deriv f)) x +
                    h ^ 2 / 2 * (deriv^[2] (deriv f)) x)) /
                  h ^ 2 + c / 2)
            (𝓝[>] (0 : ℝ)) (𝓝 (c / 2)) :=
        by simpa using hrem.add (tendsto_const_nhds (x := c / 2))
      refine Tendsto.congr' ?_ hlim0
      filter_upwards [self_mem_nhdsWithin] with h hhpos
      have hhne : h ≠ 0 := ne_of_gt hhpos
      dsimp [a, b, c] at ha_zero hb_zero
      dsimp [c]
      rw [ha_zero, hb_zero]
      field_simp [hhne]
      ring_nf
    have hderiv_scaled_nonneg :
        ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ deriv f (x + h) / h ^ 2 := by
      have hmem :
          ∀ᶠ h in 𝓝[>] (0 : ℝ), x + h ∈ Set.Ioo (-1 : ℝ) 1 :=
        (tendsto_add_right_nhdsWithin_Ioo hx).eventually
          (self_mem_nhdsWithin : Set.Ioo (-1 : ℝ) 1 ∈
            𝓝[Set.Ioo (-1 : ℝ) 1] x)
      filter_upwards [hmem] with h hy
      exact div_nonneg
        (deriv_nonneg_on_Ioo_of_loewnerPosOnUnitInterval hpos hy)
        (sq_nonneg h)
    have hc_half : 0 ≤ c / 2 := ge_of_tendsto hderiv_scaled_lim hderiv_scaled_nonneg
    have hc_nonneg : 0 ≤ c := by nlinarith
    simpa [c] using hc_nonneg

/--
The `C³` Simon Chapter 20 pilot turns public Löwner positivity into convexity of
the first derivative on `(-1,1)`.
-/
theorem smoothHiai_C3_deriv_convexOn_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hC3 : ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1)) :
    ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv f) := by
  have hderivC2 :
      ContDiffOn ℝ 2 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC3.deriv_of_isOpen (m := 2) isOpen_Ioo (by decide)
  have hderivderivC1 :
      ContDiffOn ℝ 1 (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hderivC2.deriv_of_isOpen (m := 1) isOpen_Ioo (by decide)
  exact
    convexOn_of_deriv2_nonneg' (convex_Ioo (-1 : ℝ) 1)
      (hderivC2.differentiableOn (by decide))
      (hderivderivC1.differentiableOn (by decide))
      (fun x hx =>
        deriv2_deriv_nonneg_of_loewnerPosOnUnitInterval_C3
          (f := f) hpos hC3 hx)

/--
With a Hiai mollifier available, public Löwner positivity gives continuity of
the first derivative on the open unit interval.
-/
theorem deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_C3SmoothHiai
    smoothHiai_C3_deriv_convexOn_of_loewnerPosOnUnitInterval
    (φ := φ) (f := f) hφ hpos

end

end Quantum.TraceInequality.Loewner
