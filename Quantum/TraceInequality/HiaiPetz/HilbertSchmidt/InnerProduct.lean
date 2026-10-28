/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Hilbert-Schmidt trace and inner-product forms

This file provides the bridge between matrix trace quadratic forms and the
Hilbert-Schmidt inner product on matrices. It lets later order and adjoint
lemmas move between book-style trace expressions and Lean's inner-product
formulation of positivity.

## Main results

* `hsQForm_real_eq_inner_real`: the real part of
  `Tr(X^* T X)` agrees with the real part of `inner (T X) X`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 Hilbert-Schmidt quadratic forms.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius

noncomputable section MatrixScopedInstances

theorem HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun
    {n : ℕ} (T : Mₙ n → Mₙ n) (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * T X)) =
      Complex.re (inner ℂ (T X) X) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose X * T X)) =
        Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
          rw [Matrix.trace_mul_comm]
    _ = Complex.re (star (Matrix.trace (X * Matrix.conjTranspose (T X)))) := by
          rw [← Matrix.trace_conjTranspose (A := X * Matrix.conjTranspose (T X))]
          simp [Matrix.conjTranspose_mul]
    _ = Complex.re (Matrix.trace (X * Matrix.conjTranspose (T X))) := by
          simp
    _ = Complex.re (inner ℂ (T X) X) := by
          rfl

/-- The real part of the trace quadratic form `Tr(X^* T X)` agrees with the
real part of the Hilbert-Schmidt inner product `inner (T X) X`. -/
theorem hsQForm_real_eq_inner_real {n : ℕ} (T : HSOp n) (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * T X)) =
      Complex.re (inner ℂ (T X) X) := by
  exact HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun T X

end MatrixScopedInstances

end HiaiPetz
