import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridgeAtInv
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra

import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 67 (bridge): rewrite the Step 60' finite-point evaluation at `1 / y` into a
`(1 - y * t)`-denominator form.

This is a purely algebraic rearrangement:
`- 1 / (t - 1/y) = y / (1 - y * t)` (with Lean's `inv` convention).
-/


private lemma neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (y t : ℂ) (hy : y ≠ 0) :
    -(1 / (t - (1 / y))) = y * (1 / (1 - y * t)) := by
  have h :=
    neg_inv_mul_one_div_sub_eq_one_div_one_sub_mul (x := y) (t := t) hy
  -- Multiply the identity by `y` to eliminate the prefactor `-(1/y)`.
  have : y * ((-(1 / y)) * (1 / (t - (1 / y)))) = y * (1 / (1 - y * t)) := by
    simpa [h] using congrArg (fun z : ℂ => y * z) h
  -- Simplify the left-hand side.
  simpa [mul_assoc, div_eq_mul_inv, hy] using this


/--
Build the support-eliminated subsequence package with the `(1 - y * t)` evaluation identity.
-/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulPackage f canonicalPoints) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv
        (f := f) hL with
    ⟨p⟩
  refine ⟨⟨p.toStrictApproxFullPackage, ?_⟩⟩
  intro n i hi0
  have hy0 : (canonicalPoints n i : ℂ) ≠ 0 := by
    rcases pointsHyp_canonicalPoints n with ⟨_h0, _hinj, _hIoo, hne⟩
    exact_mod_cast (hne i hi0)
  -- Start from the Step 60' identity.
  have h0 := p.hEvalInv n i hi0
  -- Finish by algebraic rearrangement under the integral.
  calc
    (f (canonicalPoints n i) : ℂ) =
        (f 0 : ℂ) + ∫ t, -(1 / ((t : ℂ) - (1 / (canonicalPoints n i : ℂ))))
          ∂(p.μn n) := by
          -- Move the minus sign inside the integral.
          have : (f (canonicalPoints n i) : ℂ) =
              (f 0 : ℂ) +
                -(∫ t, (1 / ((t : ℂ) - (1 / (canonicalPoints n i : ℂ))))
                    ∂(p.μn n)) := by
            simpa [sub_eq_add_neg] using h0
          simpa [MeasureTheory.integral_neg] using this
    _ = (f 0 : ℂ) +
        ∫ t,
          (canonicalPoints n i : ℂ) *
            (1 / (1 - (canonicalPoints n i : ℂ) * (t : ℂ)))
            ∂(p.μn n) := by
          refine congrArg (fun z => (f 0 : ℂ) + z) ?_
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun t => ?_)
          -- Pointwise algebraic rewrite.
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (y := (canonicalPoints n i : ℂ))
              (t := (t : ℂ)) hy0)
    _ = (f 0 : ℂ) + (canonicalPoints n i : ℂ) *
        ∫ t, (1 / (1 - (canonicalPoints n i : ℂ) * (t : ℂ))) ∂(p.μn n) := by
          exact congrArg (fun z => (f 0 : ℂ) + z)
            (MeasureTheory.integral_const_mul (μ := p.μn n) (r := (canonicalPoints n i : ℂ))
              (f := fun t : ℝ => 1 / (1 - (canonicalPoints n i : ℂ) * (t : ℂ))))

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 67'' (convenience): restate the `(1 - y * t)` evaluation identity along the extracted
subsequence `φ`.

This is the direct analogue of
`exists_subseq_supportElim_stieltjesDiff_full_of_global_loewnerMatrix_posDef
_canonicalPoints_with_eval_at_inv_subseq`.
-/

/-- Restrict the `(1 - y * t)` evaluation identity to the extracted subsequence. -/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMulSubseq
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqPackage f canonicalPoints) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul
        (f := f) hL with
    ⟨p⟩
  refine ⟨⟨p.toStrictApproxFullPackage, ?_⟩⟩
  intro n i hi
  simpa using p.hOneSubMul (p.φ n) i hi

end

end Quantum.TraceInequality.Loewner
