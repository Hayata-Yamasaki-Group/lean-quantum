/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.CarlenKernel.MatrixFactor
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Hilbert--Schmidt adjoint and matrix-order helpers
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section

/-- The trace pairing for `hsAdjoint` agrees with the pushed-forward pairing. -/
theorem trace_hsAdjoint_eq {n m : ℕ} (Φ : HSMap n m) (X : Mₙ n) (Y : Mₙ m) :
    Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y) =
      Matrix.trace (Matrix.conjTranspose (Φ X) * Y) := by
  calc
    Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y)
        = Matrix.trace (hsAdjoint Φ Y * Matrix.conjTranspose X) := by
          rw [Matrix.trace_mul_comm]
    _ = @inner ℂ (Mₙ n) inferInstance X (hsAdjoint Φ Y) := rfl
    _ = @inner ℂ (Mₙ m) inferInstance (Φ X) Y := by
          have hadj :=
            @ContinuousLinearMap.adjoint_inner_right ℂ (Mₙ n) (Mₙ m)
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedAddCommGroup (n := m))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixInnerProductSpace (n := m))
              (instMatrixCompleteSpace (n := n))
              (instMatrixCompleteSpace (n := m))
              Φ X Y
          simpa [hsAdjoint] using hadj
    _ = Matrix.trace (Y * Matrix.conjTranspose (Φ X)) := rfl
    _ = Matrix.trace (Matrix.conjTranspose (Φ X) * Y) := by
          rw [Matrix.trace_mul_comm]

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem matrix_trace_mul_nonneg_of_posSemidef {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self hB
  rw [hY]
  have htrace :
      Matrix.trace (A * (Matrix.conjTranspose Y * Y)) =
        Matrix.trace (Y * A * Matrix.conjTranspose Y) := by
    calc
      Matrix.trace (A * (Matrix.conjTranspose Y * Y)) =
          Matrix.trace ((A * Matrix.conjTranspose Y) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Matrix.conjTranspose Y)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Matrix.conjTranspose Y) := by
        simp [Matrix.mul_assoc]
  rw [htrace]
  exact (hA.mul_mul_conjTranspose_same Y).trace_nonneg

end

end Quantum.TraceInequality.Loewner.HiaiPetz
