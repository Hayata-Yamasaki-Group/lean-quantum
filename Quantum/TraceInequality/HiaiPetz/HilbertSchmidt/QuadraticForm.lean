/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.InnerProduct

/-!
# Hilbert-Schmidt quadratic-form order

This file connects order of Hilbert-Schmidt operators with inequalities of
their quadratic forms. The local lemmas are used to move between the
continuous-linear-map order and trace expressions over matrices.

## Main results

* `le_of_quadratic_form_nonneg`: self-adjoint operators ordered by
  nonnegativity of the quadratic form of their difference.
* `hsQForm_le_of_le`: order of Hilbert-Schmidt operators implies pointwise
  order of the corresponding matrix trace quadratic forms.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 Hilbert-Schmidt quadratic forms.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- A self-adjoint difference `T - S` with nonnegative quadratic form witnesses
the order `S ≤ T` for Hilbert-space continuous linear maps. -/
theorem le_of_quadratic_form_nonneg
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {S T : HansenPedersen.L K}
    (hself : IsSelfAdjoint (T - S))
    (hquad : ∀ x : K, 0 ≤ RCLike.re (inner ℂ ((T - S) x) x)) :
    S ≤ T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  refine ⟨?_, hquad x⟩
  have hsymm : (T - S).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  exact Complex.conj_eq_iff_re.mp
    ((LinearMap.isSymmetric_iff_inner_map_self_real _).mp hsymm x)

/-- Order of Hilbert-Schmidt operators gives pointwise monotonicity of their
trace quadratic forms on matrices. -/
theorem hsQForm_le_of_le {n : ℕ}
    {S T : HSOp n}
    (hST : S ≤ T) (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (S X))) ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hnonneg : 0 ≤ Complex.re (inner ℂ ((T - S) X) X) := by
    exact @ContinuousLinearMap.IsPositive.re_inner_nonneg_left ℂ (Mₙ n)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (T - S)
      (((@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (T - S))).1 (by simpa using hST))
      X
  have hinner :
      Complex.re (inner ℂ (S X) X) ≤ Complex.re (inner ℂ (T X) X) := by
    have hrew :
        Complex.re (inner ℂ ((T - S) X) X) =
          Complex.re (inner ℂ (T X) X) - Complex.re (inner ℂ (S X) X) := by
      simp [ContinuousLinearMap.sub_apply, Complex.sub_re]
    rw [hrew] at hnonneg
    linarith
  simpa [hsQForm_real_eq_inner_real] using hinner

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.HilbertSchmidt

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- A nonnegative Hilbert-Schmidt operator has nonnegative quadratic form
against every matrix. -/
theorem hsQForm_nonneg_of_nonneg {n : ℕ} {T : HSOp n}
    (hT : 0 ≤ T) (X : Mₙ n) :
    0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  have hT' : 0 ≤ (T : Mₙ n →L[ℂ] Mₙ n) := by simpa using hT
  have hTpos :
      @ContinuousLinearMap.IsPositive ℂ (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        ((T : Mₙ n →L[ℂ] Mₙ n)) :=
    ((@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ n)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      ((T : Mₙ n →L[ℂ] Mₙ n))).1 hT')
  have hsymm : T.IsSymmetric := by
    simpa using hTpos.1
  have hswap : inner ℂ X (T X) = inner ℂ (T X) X := by
    exact (hsymm X X).symm
  have hinner' : 0 ≤ Complex.re (inner ℂ (T X) X) := by
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hTpos.2 X
  have hinner : 0 ≤ Complex.re (inner ℂ X (T X)) := by
    simpa [hswap] using hinner'
  have htrace : 0 ≤ Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
    simpa [inner] using hinner
  rw [Matrix.trace_mul_comm]
  exact htrace

end

end HiaiPetz.HilbertSchmidt
