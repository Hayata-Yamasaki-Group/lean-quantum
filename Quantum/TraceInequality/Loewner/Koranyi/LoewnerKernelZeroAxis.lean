import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelDiffUniformPackage
import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridge


namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 86 (bridge): along the extracted subsequence from the Step 82 full package,
rewrite the evaluation identity

`f(y) = f(0) + y * ∫ 1/(1-y*t) dμ`

into an explicit formula for the divided difference `loewnerKernel f y 0`.

This is a small bookkeeping step used later when comparing real-axis quantities with the
ratio-kernel functional obtained on `ENNReal`.
-/

/-- A `1 - y * t` evaluation formula rewrites to the zero-axis Loewner-kernel integral. -/
lemma loewnerKernel_zero_eq_integral_one_div_one_sub_mul_of_eval
    (f : ℝ → ℝ) (μ : Measure ℝ) {y : ℝ} (hy0 : y ≠ 0)
    (hEval :
      (f y : ℂ) =
        (f 0 : ℂ) + (y : ℂ) * ∫ t, (1 / (1 - (y : ℂ) * (t : ℂ))) ∂μ) :
    (loewnerKernel f y 0 : ℂ) = ∫ t, (1 / (1 - (y : ℂ) * (t : ℂ))) ∂μ := by
  have hk : loewnerKernel f y 0 = (f y - f 0) / y :=
    loewnerKernel_zero_right (f := f) (x := y) hy0
  have hkC : (loewnerKernel f y 0 : ℂ) = ((f y - f 0) / y : ℂ) := by
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hk
  -- Rearrange the evaluation identity into `(f y - f 0) / y = ∫ ...`.
  have hy0C : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
  have hdiv :
      ((f y - f 0) / y : ℂ) = ∫ t, (1 / (1 - (y : ℂ) * (t : ℂ))) ∂μ := by
    -- Subtract `(f 0)` and divide by `y`.
    have hsub :
        (f y : ℂ) - (f 0 : ℂ) =
          (y : ℂ) * ∫ t, (1 / (1 - (y : ℂ) * (t : ℂ))) ∂μ := by
      -- `hEval` already has the needed shape; subtract `(f 0)` from both sides.
      have := congrArg (fun w : ℂ => w - (f 0 : ℂ)) hEval
      -- Simplify `((f 0) + ...) - (f 0)` on the right.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    -- Multiply by `y⁻¹` on the left and cancel.
    have := congrArg (fun w : ℂ => (y : ℂ)⁻¹ * w) hsub
    -- The right side becomes `y⁻¹ * (y * I) = I` in the commutative ring `ℂ`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hy0C] using this
  simpa [hkC] using hdiv


end

end Quantum.TraceInequality.Loewner
