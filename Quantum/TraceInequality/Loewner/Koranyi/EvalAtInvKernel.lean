import Quantum.TraceInequality.Loewner.Koranyi.SupportElimination
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimKernel
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Evaluation at the inverse point

Steps of the Korányi construction at `z = 1 / x`: the restricted `(1 - z * t)` kernel
integrals are rewritten against `supportElimMeasure`, split, and identified with a Stieltjes
transform minus a `z`-independent constant, so that kernel differences become Stieltjes
differences.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section



section

variable (μ : Measure ℝ) (z : ℂ)

private lemma supportElimWeight_toReal (y : ℝ) :
    (supportElimWeight y).toReal = (y ^ (2 : ℕ))⁻¹ := by
  have h0 : 0 ≤ (y ^ (2 : ℕ))⁻¹ := by
    have : 0 ≤ y ^ (2 : ℕ) := by simpa using (pow_two_nonneg y)
    exact inv_nonneg.2 this
  simpa [supportElimWeight] using (ENNReal.toReal_ofReal h0)

/-- Change of variables for the real-point kernel `t ↦ 1 / (t - z)` after support elimination.

This rewrites the integral against `μ.restrict [-1,1]ᶜ` as an integral against
`supportElimMeasure μ`.
-/
theorem integral_one_div_sub_eq_integral_supportElimMeasure
    (μ : Measure ℝ) (z : ℂ) :
    (∫ y, (1 / ((y : ℂ) - z)) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, (1 / ((t : ℂ) * (1 - z * (t : ℂ)))) ∂(supportElimMeasure μ) := by
  classical
  have hS : MeasurableSet (Set.Icc (-1 : ℝ) 1)ᶜ :=
    (isClosed_Icc.measurableSet).compl
  have hmeas_inv : Measurable supportElimInv := measurable_supportElimInv
  have hmeas_w : Measurable supportElimWeight := measurable_supportElimWeight
  -- Expand `supportElimMeasure` and pull back along inversion.
  have hmap :
      (∫ t, (1 / ((t : ℂ) * (1 - z * (t : ℂ)))) ∂(supportElimMeasure μ)) =
        ∫ y,
          (1 / (((supportElimInv y : ℝ) : ℂ) *
            (1 - z * ((supportElimInv y : ℝ) : ℂ))))
          ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) := by
    set μ0 : Measure ℝ := (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight
    have hφ : AEMeasurable supportElimInv μ0 := hmeas_inv.aemeasurable
    have hf :
        AEStronglyMeasurable
            (fun t : ℝ => (1 / ((t : ℂ) * (1 - z * (t : ℂ)))))
            (Measure.map supportElimInv μ0) :=
      (measurable_const.div
          (Complex.measurable_ofReal.mul
            (measurable_const.sub
              (measurable_const.mul Complex.measurable_ofReal)))).aestronglyMeasurable
    have h :=
      (MeasureTheory.integral_map (μ := μ0) (φ := supportElimInv) hφ
        (f := fun t : ℝ => (1 / ((t : ℂ) * (1 - z * (t : ℂ))))) hf)
    simpa [supportElimMeasure, μ0] using h
  -- Rewrite the `withDensity` integral.
  have hwd :
      (∫ y,
          (1 / (((supportElimInv y : ℝ) : ℂ) *
            (1 - z * ((supportElimInv y : ℝ) : ℂ))))
            ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)) =
        ∫ y,
          (supportElimWeight y).toReal •
              (1 / (((supportElimInv y : ℝ) : ℂ) *
                (1 - z * ((supportElimInv y : ℝ) : ℂ))))
            ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
    have htop :
        (∀ᵐ y ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ),
          supportElimWeight y < (⊤ : ENNReal)) := by
      exact
        MeasureTheory.ae_of_all (μ := μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (fun y => by
          simp [supportElimWeight])
    simpa using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (f := supportElimWeight) hmeas_w htop
        (g := fun y : ℝ =>
          (1 / (((supportElimInv y : ℝ) : ℂ) *
            (1 - z * ((supportElimInv y : ℝ) : ℂ))))))
  -- Replace the integrand pointwise on `[-1,1]ᶜ` by the target kernel.
  have hEq :
      (fun y : ℝ =>
          (supportElimWeight y).toReal •
              (1 / (((supportElimInv y : ℝ) : ℂ) *
                (1 - z * ((supportElimInv y : ℝ) : ℂ))))) =ᵐ[
          μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ]
        fun y : ℝ => (1 / ((y : ℂ) - z)) := by
    filter_upwards [ae_restrict_mem hS] with y hy
    have hy0 : y ≠ 0 := by
      have hyIcc : ¬ y ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [Set.mem_compl_iff] using hy
      intro h0
      apply hyIcc
      simp [h0]
    have hy0C : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    -- Convert the scalar smul into multiplication in `ℂ`, then clear denominators.
    have hmul :
        ((supportElimWeight y).toReal : ℂ) *
              (1 / (((supportElimInv y : ℝ) : ℂ) *
                (1 - z * ((supportElimInv y : ℝ) : ℂ)))) =
            (1 / ((y : ℂ) - z)) := by
      have hwt : (supportElimWeight y).toReal = (y ^ (2 : ℕ))⁻¹ :=
        supportElimWeight_toReal (y := y)
      -- Use `supportElimInv y = 1 / y` to rewrite the RHS to the same denominator.
      have hfactor :
          (((supportElimInv y : ℝ) : ℂ) *
              (1 - z * ((supportElimInv y : ℝ) : ℂ))) =
            ((y : ℂ) ^ (2 : ℕ))⁻¹ * ((y : ℂ) - z) := by
        -- `y⁻¹ * (1 - z*y⁻¹) = y⁻² * (y - z)`.
        have : ((y : ℂ)⁻¹) * (1 - z * (y : ℂ)⁻¹) =
            ((y : ℂ) ^ (2 : ℕ))⁻¹ * ((y : ℂ) - z) := by
          field_simp [hy0C]
        simpa [supportElimInv, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm,
          mul_comm] using this
      -- Now simplify.
      have hy2ne : ((y : ℂ) ^ (2 : ℕ)) ≠ 0 := by
        simpa using pow_ne_zero 2 hy0C
      calc
        ((supportElimWeight y).toReal : ℂ) *
              (1 / (((supportElimInv y : ℝ) : ℂ) *
                (1 - z * ((supportElimInv y : ℝ) : ℂ))))
            = ((y ^ (2 : ℕ))⁻¹ : ℂ) *
                (1 / (((supportElimInv y : ℝ) : ℂ) *
                  (1 - z * ((supportElimInv y : ℝ) : ℂ)))) := by
                simp [hwt]
        _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ *
                (1 / (((supportElimInv y : ℝ) : ℂ) *
                  (1 - z * ((supportElimInv y : ℝ) : ℂ)))) := by
              simp
        _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ *
              (1 / (((y : ℂ) ^ (2 : ℕ))⁻¹ * ((y : ℂ) - z))) := by
              simp [hfactor]
        _ = (1 / ((y : ℂ) - z)) := by
              -- `y⁻²` cancels with the leading `y⁻²` factor.
              field_simp [hy2ne]
    -- Convert back to `•`.
    have : (supportElimWeight y).toReal •
          (1 / (((supportElimInv y : ℝ) : ℂ) *
            (1 - z * ((supportElimInv y : ℝ) : ℂ)))) =
        (1 / ((y : ℂ) - z)) := by
      simpa [Complex.real_smul] using hmul
    simpa using this
  -- Conclude.
  have hR :
      (∫ t, (1 / ((t : ℂ) * (1 - z * (t : ℂ)))) ∂(supportElimMeasure μ)) =
        (∫ y, (1 / ((y : ℂ) - z)) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) := by
    calc
      (∫ t, (1 / ((t : ℂ) * (1 - z * (t : ℂ)))) ∂(supportElimMeasure μ)) =
          ∫ y,
            (1 / (((supportElimInv y : ℝ) : ℂ) *
              (1 - z * ((supportElimInv y : ℝ) : ℂ))))
            ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) := hmap
      _ =
          ∫ y,
            (supportElimWeight y).toReal •
                (1 / (((supportElimInv y : ℝ) : ℂ) *
                  (1 - z * ((supportElimInv y : ℝ) : ℂ))))
            ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := hwd
      _ = ∫ y, (1 / ((y : ℂ) - z)) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
            exact MeasureTheory.integral_congr_ae hEq
  simpa using hR.symm

end

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section



/-- Specialize support elimination for the real-point Stieltjes kernel at `z = 1 / x`. -/
theorem integral_one_div_sub_inv_eq_integral_supportElimMeasure
    (μ : Measure ℝ) (x : ℂ) :
    (∫ t, (1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, (1 / ((t : ℂ) * (1 - (1 / x) * (t : ℂ)))) ∂(supportElimMeasure μ) := by
  simpa using (integral_one_div_sub_eq_integral_supportElimMeasure (μ := μ) (z := (1 / x)))

/-- The same support-elimination identity with a global minus sign in the kernel. -/
theorem integral_neg_one_div_sub_inv_eq_integral_supportElimMeasure
    (μ : Measure ℝ) (x : ℂ) :
    (∫ t, -(1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, -(1 / ((t : ℂ) * (1 - (1 / x) * (t : ℂ)))) ∂(supportElimMeasure μ) := by
  -- Push the minus sign through the change-of-variables identity.
  calc
    (∫ t, -(1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
        - (∫ t, (1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) := by
          simp [MeasureTheory.integral_neg]
    _ =
        - (∫ t, (1 / ((t : ℂ) * (1 - (1 / x) * (t : ℂ)))) ∂(supportElimMeasure μ)) := by
          simpa using
            congrArg Neg.neg
              (integral_one_div_sub_inv_eq_integral_supportElimMeasure (μ := μ) (x := x))
    _ =
        ∫ t, -(1 / ((t : ℂ) * (1 - (1 / x) * (t : ℂ)))) ∂(supportElimMeasure μ) := by
          simp [MeasureTheory.integral_neg]

/-- Simplify the negated inverse kernel after support elimination. -/
theorem integral_neg_one_div_sub_inv_eq_integral_supportElimMeasure_simplify
    (μ : Measure ℝ) (x : ℂ) (hx : x ≠ 0) :
    (∫ t, -(1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, x / ((t : ℂ) * ((t : ℂ) - x)) ∂(supportElimMeasure μ) := by
  -- Simplify `-(1 / (t * (1 - (1/x) * t)))` into `x / (t * (t - x))`.
  -- Use the previous lemma and simplify pointwise under the integral.
  have h :=
    integral_neg_one_div_sub_inv_eq_integral_supportElimMeasure (μ := μ) (x := x)
  refine h.trans ?_
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  -- Work pointwise in `ℂ` by splitting on the potential zero denominators.
  by_cases ht : (t : ℂ) = 0
  · simp [ht]
  by_cases htx : (t : ℂ) = x
  · simp [htx, hx]
  -- Main case: clear denominators.
  have htx' : (t : ℂ) - x ≠ 0 := sub_ne_zero.mpr htx
  have h1 : (1 - (1 / x) * (t : ℂ)) ≠ 0 := by
    intro h1z
    have h' : (1 / x) * (t : ℂ) = (1 : ℂ) := (sub_eq_zero.mp h1z).symm
    have hxmul : x * ((1 / x) * (t : ℂ)) = (t : ℂ) := by
      simp [hx]
    have hxmul' : x * ((1 / x) * (t : ℂ)) = x := by
      -- Multiply the identity `(1 / x) * t = 1` by `x`.
      have := congrArg (fun u : ℂ => x * u) h'
      simpa [mul_assoc] using this
    have : (t : ℂ) = x := by
      -- Compare the two evaluations of `x * ((1 / x) * t)`.
      exact hxmul.symm.trans hxmul'
    exact htx this
  field_simp [ht, htx', hx, h1]
  have hden : x - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htx)
  have hswap : (t : ℂ) - x = - (x - (t : ℂ)) := by
    ring
  -- `t - x = -(x - t)` implies the fraction equals `-1`, hence the outer negation is `1`.
  have hfrac : (- (x - (t : ℂ))) / (x - (t : ℂ)) = (-1 : ℂ) := by
    calc
      (- (x - (t : ℂ))) / (x - (t : ℂ)) =
          (- (x - (t : ℂ))) * (x - (t : ℂ))⁻¹ := by
            simp [div_eq_mul_inv]
      _ = - ((x - (t : ℂ)) * (x - (t : ℂ))⁻¹) := by
            ring
      _ = - (1 : ℂ) := by
            simp [hden]
      _ = (-1 : ℂ) := by simp
  -- Rewrite `t - x` as `-(x - t)` and close using `hfrac`.
  rw [hswap]
  rw [hfrac]
  simp

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section



private lemma neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (x t : ℂ) (hx : x ≠ 0) :
    -(1 / (t - (1 / x))) = x * (1 / (1 - x * t)) := by
  by_cases hden : (1 - x * t) = 0
  · have hxt : x * t = (1 : ℂ) := by
      simpa using (sub_eq_zero.mp hden).symm
    have ht : t = 1 / x := by
      calc
        t = x⁻¹ * (x * t) := by
              simpa [mul_assoc] using (inv_mul_cancel_left₀ hx t).symm
        _ = x⁻¹ * 1 := by simp [hxt]
        _ = 1 / x := by simp [div_eq_mul_inv]
    have ht' : t - x⁻¹ = 0 := by
      simp [one_div, ht]
    simp [hden, ht', one_div]
  · have ht : t - (1 / x) ≠ 0 := by
      intro ht
      have ht' : t = 1 / x := sub_eq_zero.mp ht
      have hxt : x * t = (1 : ℂ) := by
        -- Multiply `t = 1/x` by `x`.
        have := congrArg (fun u : ℂ => x * u) ht'
        simpa [div_eq_mul_inv, mul_assoc, hx] using this
      exact hden (by simpa using (sub_eq_zero.mpr hxt.symm))
    -- Clear denominators.
    field_simp [hx, ht, hden]
    -- `field_simp` leaves a residual `inv_neg`-type simplification.
    have hsub : 1 - t * x = - (t * x - 1) := by ring
    -- Rewrite `1 - t*x` as `-(t*x - 1)` and use `inv_neg`.
    rw [hsub]
    simpa using (inv_neg (a := t * x - 1)).symm

/-- Rewrite the restricted evaluation-at-inv kernel against `supportElimMeasure μ`. -/
theorem integral_mul_one_div_one_sub_mul_eq_integral_supportElimMeasure_simplify
    (μ : Measure ℝ) (x : ℂ) (hx : x ≠ 0) :
    (∫ t, x * (1 / (1 - x * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, x / ((t : ℂ) * ((t : ℂ) - x)) ∂(supportElimMeasure μ) := by
  -- Rewrite the left integrand into Step 69's `-(1 / (t - 1/x))` form.
  have hcongr :
      (fun t : ℝ => x * (1 / (1 - x * (t : ℂ)))) =ᵐ[μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ]
        (fun t : ℝ => -(1 / ((t : ℂ) - (1 / x)))) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    -- Pointwise rewrite in `ℂ`.
    simpa [mul_assoc, one_div] using
      (neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (x := x) (t := (t : ℂ)) hx).symm
  -- Apply Step 69 and finish.
  calc
    (∫ t, x * (1 / (1 - x * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        = ∫ t, -(1 / ((t : ℂ) - (1 / x))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
            exact MeasureTheory.integral_congr_ae hcongr
    _ = ∫ t, x / ((t : ℂ) * ((t : ℂ) - x)) ∂(supportElimMeasure μ) := by
          simpa using
            (integral_neg_one_div_sub_inv_eq_integral_supportElimMeasure_simplify
              (μ := μ) (x := x) hx)

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped UpperHalfPlane

noncomputable section



/-- Rewrite the restricted `(1 - z * t)` kernel as a split support-elimination kernel. -/
theorem integral_mul_one_div_one_sub_mul_eq_integral_supportElimMeasure_kernel_split
    (μ : Measure ℝ) (z : ℍ) :
    (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
        ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      ∫ t, ((1 / ((t : ℂ) - (z : ℂ))) - (1 / (t : ℂ))) ∂(supportElimMeasure μ) := by
  have hzIm : (z : ℂ).im ≠ 0 := ne_of_gt z.coe_im_pos
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hz
    exact hzIm (by simp [hz])
  -- Step 72: rewrite the restricted integral as an integral against `supportElimMeasure`.
  have h72 :
      (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
          ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
        ∫ t, (z : ℂ) / ((t : ℂ) * ((t : ℂ) - (z : ℂ))) ∂(supportElimMeasure μ) := by
    simpa using
      (integral_mul_one_div_one_sub_mul_eq_integral_supportElimMeasure_simplify
        (μ := μ) (x := (z : ℂ)) hz0)
  -- Step 74: split the rational kernel under `supportElimMeasure`.
  have h74 :
      (∫ t : ℝ, (z : ℂ) / ((t : ℂ) * ((t : ℂ) - (z : ℂ))) ∂(supportElimMeasure μ)) =
        ∫ t : ℝ, ((1 / ((t : ℂ) - (z : ℂ))) - (1 / (t : ℂ)))
          ∂(supportElimMeasure μ) := by
    simpa using integral_supportElimMeasure_kernel_split (μ := μ) (x := (z : ℂ)) hzIm
  exact h72.trans h74

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped UpperHalfPlane

noncomputable section


namespace EvalAtInvStieltjesSubConstPrivate

private lemma supportElimWeight_toReal (y : ℝ) :
    (supportElimWeight y).toReal = (y ^ (2 : ℕ))⁻¹ := by
  have h0 : 0 ≤ (y ^ (2 : ℕ))⁻¹ := by
    have : 0 ≤ y ^ (2 : ℕ) := by
      simpa using (pow_two_nonneg y)
    exact inv_nonneg.2 this
  simpa [supportElimWeight] using (ENNReal.toReal_ofReal h0)

end EvalAtInvStieltjesSubConstPrivate
open EvalAtInvStieltjesSubConstPrivate

private lemma kernel_bound_of_im_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖(1 / ((t : ℂ) - z))‖ ≤ 1 / z.im := by
  have hz0 : 0 ≤ z.im := le_of_lt hz
  have him : z.im ≤ |((t : ℂ) - z).im| := by
    have habs : |((t : ℂ) - z).im| = z.im := by
      have : ((t : ℂ) - z).im = -z.im := by simp
      simp [this, abs_neg, abs_of_nonneg hz0]
    exact le_of_eq habs.symm
  have hnorm : z.im ≤ ‖(t : ℂ) - z‖ := le_trans him (Complex.abs_im_le_norm _)
  calc
    ‖(1 / ((t : ℂ) - z))‖ = 1 / ‖(t : ℂ) - z‖ := by
        simp [one_div]
    _ ≤ 1 / z.im := by
        exact one_div_le_one_div_of_le hz hnorm
    _ = 1 / z.im := rfl

private lemma isFiniteMeasure_supportElimMeasure_of_univ_lt_top (μ : Measure ℝ)
    (hμ : μ Set.univ < ⊤) :
    IsFiniteMeasure (supportElimMeasure μ) := by
  refine ⟨lt_of_le_of_lt (supportElimMeasure_univ_le (μ := μ)) hμ⟩

private lemma isFiniteMeasure_restrict_Icc_compl_of_univ_lt_top (μ : Measure ℝ)
    (hμ : μ Set.univ < ⊤) :
    IsFiniteMeasure (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
  refine ⟨?_
  ⟩
  have : (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ ≤ μ Set.univ := by
    simpa using (Measure.restrict_le_self (μ := μ) (s := (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ)
  exact lt_of_le_of_lt this hμ

private lemma integrable_one_div_supportElimMeasure (μ : Measure ℝ) (hμ : μ Set.univ < ⊤) :
    Integrable (fun t : ℝ => (1 / (t : ℂ))) (supportElimMeasure μ) := by
  classical
  -- Reduce integrability on `supportElimMeasure μ` to integrability on the preimage measure via
  -- `integrable_map_measure`, then discharge the `withDensity` using a boundedness estimate.
  let s : Set ℝ := (Set.Icc (-1 : ℝ) 1)ᶜ
  have hs : MeasurableSet s := (isClosed_Icc.measurableSet).compl
  let μ0 : Measure ℝ := μ.restrict s
  haveI : IsFiniteMeasure μ0 := isFiniteMeasure_restrict_Icc_compl_of_univ_lt_top (μ := μ) hμ
  let μ1 : Measure ℝ := μ0.withDensity supportElimWeight
  have hφ : AEMeasurable supportElimInv μ1 := measurable_supportElimInv.aemeasurable
  have hg_meas :
      AEStronglyMeasurable (fun t : ℝ => (1 / (t : ℂ))) (Measure.map supportElimInv μ1) := by
    have hmeas : Measurable (fun t : ℝ => (1 / (t : ℂ))) := by
      have h1 : Measurable (fun t : ℝ => (t : ℂ)) :=
        (Complex.continuous_ofReal.measurable : Measurable fun t : ℝ => (t : ℂ))
      exact measurable_const.div h1
    exact hmeas.aestronglyMeasurable
  have htop :
      (∀ᵐ y ∂μ0, supportElimWeight y < (⊤ : ENNReal)) := by
    exact MeasureTheory.ae_of_all (μ := μ0) (fun y => by simp [supportElimWeight])
  have hInt_pre :
      Integrable (fun y : ℝ => (1 / ((supportElimInv y : ℝ) : ℂ))) μ1 := by
    have hiff :=
      (integrable_withDensity_iff_integrable_smul' (μ := μ0) (E := ℂ)
        (f := supportElimWeight) measurable_supportElimWeight htop
        (g := fun y : ℝ => (1 / ((supportElimInv y : ℝ) : ℂ))))
    -- It suffices to show integrability of the `toReal`-weighted integrand under `μ0`.
    refine (hiff.mpr ?_)
    have hmeas :
        AEStronglyMeasurable
            (fun y : ℝ =>
              (supportElimWeight y).toReal • (1 / ((supportElimInv y : ℝ) : ℂ))) μ0 := by
      have hmeas' :
          Measurable
            (fun y : ℝ =>
              (supportElimWeight y).toReal • (1 / ((supportElimInv y : ℝ) : ℂ))) := by
        have hwt : Measurable fun y : ℝ => (supportElimWeight y).toReal :=
          ENNReal.measurable_toReal.comp measurable_supportElimWeight
        have hwtC : Measurable fun y : ℝ => ((supportElimWeight y).toReal : ℂ) :=
          Complex.continuous_ofReal.measurable.comp hwt
        have hinv : Measurable fun y : ℝ => (1 / ((supportElimInv y : ℝ) : ℂ)) := by
          have h1 : Measurable fun y : ℝ => ((supportElimInv y : ℝ) : ℂ) :=
            (Complex.continuous_ofReal.measurable.comp measurable_supportElimInv)
          exact measurable_const.div h1
        have hmul :
            Measurable fun y : ℝ =>
              ((supportElimWeight y).toReal : ℂ) * (1 / ((supportElimInv y : ℝ) : ℂ)) :=
          hwtC.mul hinv
        simpa [RCLike.real_smul_eq_coe_mul] using hmul
      exact hmeas'.aestronglyMeasurable
    have hconst : Integrable (fun _y : ℝ => (1 : ℝ)) μ0 := integrable_const 1
    refine Integrable.mono' hconst hmeas ?_
    -- Use that `μ0` is a restriction to `[-1,1]ᶜ`, where `|y| ≥ 1`, so the weighted integrand
    -- has norm at most `1`.
    have hmem : ∀ᵐ y ∂μ0, y ∈ s := by
      simpa [μ0] using (ae_restrict_mem (μ := μ) hs)
    filter_upwards [hmem] with y hy
    have hy_abs : (1 : ℝ) ≤ |y| := by
      -- If `|y| ≤ 1`, then `y ∈ [-1,1]`, contradicting `hy`.
      have : ¬ |y| ≤ (1 : ℝ) := by
        intro hle
        have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := by
          have habs : (- (1 : ℝ)) ≤ y ∧ y ≤ 1 := by
            simpa [abs_le] using hle
          exact habs
        exact hy hyIcc
      exact le_of_lt (lt_of_not_ge this)
    have hy2 : (1 : ℝ) ≤ y ^ (2 : ℕ) := by
      -- `|y|^2 = y^2` and `|y| ≥ 1`.
      have hpow : (1 : ℝ) ≤ |y| ^ (2 : ℕ) := by
        simpa using (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by positivity) hy_abs (2 : ℕ))
      simpa [sq_abs] using hpow
    have hden : (y ^ (2 : ℕ))⁻¹ * |y| ≤ (1 : ℝ) := by
      -- Reduce to `|y|⁻¹ ≤ 1` using `y^2 = |y|^2`.
      have hpow : y ^ (2 : ℕ) = |y| ^ (2 : ℕ) := by
        simp [sq_abs]
      have hEq : (y ^ (2 : ℕ))⁻¹ * |y| = (|y|)⁻¹ := by
        rw [hpow]
        by_cases h0 : |y| = 0
        · simp [h0]
        · have ha : |y| ≠ 0 := h0
          -- Clear denominators in `ℝ` (a field).
          field_simp [pow_two, ha]
      -- Now use `1 ≤ |y|`.
      simpa [hEq] using (inv_le_one_of_one_le₀ hy_abs)
    -- Finally bound the norm.
    have hsimps :
        ‖(supportElimWeight y).toReal • (1 / ((supportElimInv y : ℝ) : ℂ))‖ =
          (y ^ (2 : ℕ))⁻¹ * |y| := by
      -- Rewrite `1 / (supportElimInv y)` to `y`.
      have : (1 / ((supportElimInv y : ℝ) : ℂ)) = (y : ℂ) := by
        simp [supportElimInv]
      have hnonneg : 0 ≤ (supportElimWeight y).toReal := by
        have : 0 ≤ y ^ (2 : ℕ) := by
          simpa using (pow_two_nonneg y)
        simpa [supportElimWeight_toReal (y := y)] using (inv_nonneg.2 this)
      -- Rewrite the weight and compute the norm.
      calc
        ‖(supportElimWeight y).toReal • (1 / ((supportElimInv y : ℝ) : ℂ))‖
            = ‖(supportElimWeight y).toReal • (y : ℂ)‖ := by
                simp [this]
        _ = ‖(supportElimWeight y).toReal‖ * ‖(y : ℂ)‖ := by
              simp
        _ = (supportElimWeight y).toReal * |y| := by
              simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, Complex.norm_real, Real.norm_eq_abs]
        _ = (y ^ (2 : ℕ))⁻¹ * |y| := by
              simp [supportElimWeight_toReal (y := y)]
    have hle1 :
        ‖(supportElimWeight y).toReal • (1 / ((supportElimInv y : ℝ) : ℂ))‖ ≤ 1 := by
      -- Use the explicit formula and the bound `≤ 1`.
      -- Rewrite the norm and use the scalar bound.
      rw [hsimps]
      exact hden
    exact hle1
  -- Push integrability forward through the map.
  have hmap :
      Integrable (fun t : ℝ => (1 / (t : ℂ))) (Measure.map supportElimInv μ1) := by
    exact (integrable_map_measure hg_meas hφ).2 hInt_pre
  -- Unfold the definition.
  simpa [supportElimMeasure, μ0, μ1] using hmap

private lemma integrable_stieltjesKernel_supportElimMeasure
    (μ : Measure ℝ) (hμ : μ Set.univ < ⊤) (z : ℍ) :
    Integrable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) (supportElimMeasure μ) := by
  haveI : IsFiniteMeasure (supportElimMeasure μ) :=
    isFiniteMeasure_supportElimMeasure_of_univ_lt_top (μ := μ) hμ
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) (supportElimMeasure μ) := by
    have hmeas' : Measurable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) := by
      have h1 : Measurable (fun t : ℝ => (t : ℂ)) :=
        (Complex.continuous_ofReal.measurable : Measurable fun t : ℝ => (t : ℂ))
      exact measurable_const.div (h1.sub measurable_const)
    exact hmeas'.aestronglyMeasurable
  have hg : Integrable (fun _t : ℝ => (1 / (z : ℂ).im : ℝ)) (supportElimMeasure μ) :=
    integrable_const (1 / (z : ℂ).im)
  refine Integrable.mono' hg hmeas ?_
  refine (Eventually.of_forall fun t : ℝ => ?_)
  simpa [one_div] using kernel_bound_of_im_pos (z := (z : ℂ)) (by simpa using z.coe_im_pos) t

/-- The split support-elimination kernel integral is a Stieltjes transform minus a constant. -/
theorem integral_supportElimMeasure_kernel_split_eq_stieltjes_sub_const
    (μ : Measure ℝ) (hμ : μ Set.univ < ⊤) (z : ℍ) :
    (∫ t : ℝ, ((1 / ((t : ℂ) - (z : ℂ))) - (1 / (t : ℂ))) ∂(supportElimMeasure μ)) =
      stieltjes (supportElimMeasure μ) z -
        ∫ t : ℝ, (1 / (t : ℂ)) ∂(supportElimMeasure μ) := by
  have hInt1 :
      Integrable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) (supportElimMeasure μ) :=
    integrable_stieltjesKernel_supportElimMeasure (μ := μ) hμ z
  have hInt2 : Integrable (fun t : ℝ => (1 / (t : ℂ))) (supportElimMeasure μ) :=
    integrable_one_div_supportElimMeasure (μ := μ) hμ
  -- Expand `stieltjes` and use linearity of the Bochner integral.
  simpa [stieltjes] using (integral_sub hInt1 hInt2)

/-- The restricted `(1 - z * t)` kernel equals Stieltjes minus a `z`-independent constant. -/
theorem integral_mul_one_div_one_sub_mul_eq_stieltjes_sub_const_supportElimMeasure
    (μ : Measure ℝ) (hμ : μ Set.univ < ⊤) (z : ℍ) :
    (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
        ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
      stieltjes (supportElimMeasure μ) z -
        ∫ t : ℝ, (1 / (t : ℂ)) ∂(supportElimMeasure μ) := by
  calc
    (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
        ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        =
        ∫ t : ℝ, ((1 / ((t : ℂ) - (z : ℂ))) - (1 / (t : ℂ)))
          ∂(supportElimMeasure μ) := by
          simpa using
            (integral_mul_one_div_one_sub_mul_eq_integral_supportElimMeasure_kernel_split
              (μ := μ) z)
    _ =
        stieltjes (supportElimMeasure μ) z -
          ∫ t : ℝ, (1 / (t : ℂ)) ∂(supportElimMeasure μ) := by
          simpa using
            integral_supportElimMeasure_kernel_split_eq_stieltjes_sub_const (μ := μ) hμ z

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped UpperHalfPlane

noncomputable section



/-- Kernel differences for the `(1 - z * t)` form equal Stieltjes differences. -/
theorem integral_mul_one_div_one_sub_mul_sub_eq_stieltjes_sub
    (μ : Measure ℝ) (hμ : μ Set.univ < ⊤) (z w : ℍ) :
    (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
        ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) =
      stieltjes (supportElimMeasure μ) z - stieltjes (supportElimMeasure μ) w := by
  have hz :
      (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
        stieltjes (supportElimMeasure μ) z -
          ∫ t : ℝ, (1 / (t : ℂ)) ∂(supportElimMeasure μ) :=
    integral_mul_one_div_one_sub_mul_eq_stieltjes_sub_const_supportElimMeasure (μ := μ) hμ z
  have hw :
      (∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ))) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =
        stieltjes (supportElimMeasure μ) w -
          ∫ t : ℝ, (1 / (t : ℂ)) ∂(supportElimMeasure μ) :=
    integral_mul_one_div_one_sub_mul_eq_stieltjes_sub_const_supportElimMeasure (μ := μ) hμ w
  -- Subtract and cancel the constant term.
  -- Use `rw` to rewrite the two integrals, then simplify.
  rw [hz, hw]
  ring

end

end Quantum.TraceInequality.Loewner
