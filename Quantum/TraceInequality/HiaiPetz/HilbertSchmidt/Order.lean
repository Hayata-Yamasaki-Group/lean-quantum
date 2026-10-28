/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HansenPedersen.HilbertSchmidt.Instances

/-!
# Hilbert-Schmidt order helpers

This file collects order facts for Hilbert-Schmidt operators that are used by
the positive functional calculus and data-processing arguments. The proofs
reuse the C-star algebra structure on `HSOp n` for inverse positivity and the
Hilbert-space quadratic-form characterization for conjugation by an operator.

## Main results

* `ringInverse_nonneg_of_nonneg_isUnit`: the ring inverse of a
  nonnegative unit in `HSOp n` is nonnegative.
* `star_mul_mul_nonneg_of_nonneg`: the positive cone of Hilbert-space
  endomorphisms is stable under the congruence `T ↦ U^* T U`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 Hilbert-Schmidt operator order.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- A nonnegative Hilbert-Schmidt operator that is invertible has a
nonnegative ring inverse, using the C-star algebra inverse-positivity theorem. -/
theorem ringInverse_nonneg_of_nonneg_isUnit
    {n : ℕ} {T : HSOp n}
    (hT0 : 0 ≤ T) (hTu : IsUnit T) :
  0 ≤ Ring.inverse T := by
  lift T to (HSOp n)ˣ using hTu
  letI : CStarAlgebra (HSOp n) := hsOpCStarAlgebra
  letI : ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint := hsOpRealCFC
  simpa using CFC.inv_nonneg_of_nonneg T hT0

/-- Conjugation by an arbitrary Hilbert-space operator preserves positivity:
if `T` is nonnegative, then `U^* T U` is nonnegative. -/
theorem star_mul_mul_nonneg_of_nonneg
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {U T : HansenPedersen.L K}
    (hT : 0 ≤ T) :
    0 ≤ star U * T * U := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT ⊢
  rw [ContinuousLinearMap.isPositive_def'] at hT ⊢
  rcases hT with ⟨hTsa, hTpos⟩
  constructor
  · calc
      star (star U * T * U) = star U * star T * U := by
        simp [mul_assoc]
      _ = star U * T * U := by
        rw [hTsa.star_eq]
  · intro x
    have hx := hTpos (U x)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    rw [show (star U * T * U) x = (star U) (T (U x)) by
      simp]
    rw [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hx

end MatrixScopedInstances

end HiaiPetz
