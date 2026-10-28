/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.MatrixFactor
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.AdjointHelpers
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

/-- A trace-preserving Hilbert--Schmidt map has a unital Hilbert--Schmidt adjoint. -/
theorem isUnitalMap_hsAdjoint_of_tracePreserving {n m : ℕ} {Φ : HSMap n m}
    (hΦ : _root_.HiaiPetz.TracePreserving Φ) :
    IsUnitalMap (hsAdjoint Φ) := by
  change hsAdjoint Φ (1 : Mₙ m) = (1 : Mₙ n)
  rw [Matrix.ext_iff_trace_mul_left]
  intro X
  calc
    Matrix.trace (X * hsAdjoint Φ (1 : Mₙ m)) =
        Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose X) *
          hsAdjoint Φ (1 : Mₙ m)) := by
      simp
    _ = Matrix.trace (Matrix.conjTranspose (Φ (Matrix.conjTranspose X)) *
          (1 : Mₙ m)) :=
      trace_hsAdjoint_eq Φ (Matrix.conjTranspose X) (1 : Mₙ m)
    _ = Matrix.trace (Matrix.conjTranspose (Φ (Matrix.conjTranspose X))) := by
      simp
    _ = star (Matrix.trace (Φ (Matrix.conjTranspose X))) := by
      rw [Matrix.trace_conjTranspose]
    _ = star (Matrix.trace (Matrix.conjTranspose X)) := by
      rw [hΦ (Matrix.conjTranspose X)]
    _ = Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose X)) := by
      simp [Matrix.trace_conjTranspose]
    _ = Matrix.trace X := by
      simp
    _ = Matrix.trace (X * (1 : Mₙ n)) := by
      simp

/-! ### Lieb--Ruskai and Schwarz Endpoint Inputs -/
/--
Two-positive maps preserve conjugate transpose.  This is extracted from the
Hermitian part of the image of the standard Lieb--Ruskai block with `C = 1`.
-/
theorem map_conjTranspose_of_isTwoPositiveMap {n m : ℕ} {Ψ : HSMap n m}
    (hΨ : IsTwoPositiveMap Ψ) (X : Mₙ n) :
    Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X) := by
  classical
  have hbase : BlockMatrixPosSemidef (liebRuskaiBlock (1 : Mₙ n) X) :=
    liebRuskaiBlock_posSemidef (C := (1 : Mₙ n)) (X := X) Matrix.PosDef.one
  have hout : BlockMatrixPosSemidef ((liebRuskaiBlock (1 : Mₙ n) X).map Ψ) :=
    hΨ (liebRuskaiBlock (1 : Mₙ n) X) hbase
  ext i j
  have hentry := hout.1.apply (Sum.inr i) (Sum.inl j)
  simpa [BlockMatrixPosSemidef, twoBlockMatrixFlatten, liebRuskaiBlock] using hentry.symm

end

end Quantum.TraceInequality.Loewner.HiaiPetz
