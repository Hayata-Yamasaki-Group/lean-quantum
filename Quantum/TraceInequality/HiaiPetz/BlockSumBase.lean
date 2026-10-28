/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Two-block sum map

The block-sum map sends a `2n × 2n` matrix, after the standard two-block
reindexing, to the sum of its diagonal blocks.  This file records its positivity,
trace preservation, value on the identity, and Hilbert--Schmidt adjoint
properties used in the standard compression step.

## Main results

* `blockSumMap_positive`: the block-sum map is positive.
* `blockSumMap_tracePreserving`: the block-sum map preserves trace.
* `blockSumMap_hsAdjointSchwarz`: its Hilbert--Schmidt adjoint satisfies the
  Schwarz inequality.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Section 6.1.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius
open scoped ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section MatrixScopedInstances

private theorem trace_reindexToBlockMatrix {n : ℕ} (X : Mₙ (2 * n)) :
    Matrix.trace (reindexToBlockMatrix n X) = Matrix.trace X := by
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  change ∑ i : Fin n ⊕ Fin n, X (e.symm i) (e.symm i) = ∑ i : Fin (2 * n), X i i
  exact (Fintype.sum_equiv e (fun i : Fin (2 * n) => X i i)
    (fun i : Fin n ⊕ Fin n => X (e.symm i) (e.symm i)) (fun i => by simp)).symm

private theorem reindexToBlockMatrix_nonneg {n : ℕ} {X : Mₙ (2 * n)} (hX : 0 ≤ X) :
    0 ≤ reindexToBlockMatrix n X := by
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  rw [Matrix.nonneg_iff_posSemidef]
  have hX' : X.PosSemidef := by
    simpa [Matrix.nonneg_iff_posSemidef] using hX
  simpa [reindexToBlockMatrix, reindexToBlockEquiv, e, Matrix.reindexLinearEquiv_apply] using
    (Matrix.posSemidef_submatrix_equiv (M := X) e.symm).2 hX'

private theorem mul_fromBlocks_toBlocks11 {n : ℕ}
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (X : Mₙ n) :
    (Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X)).toBlocks₁₁ =
      Y.toBlocks₁₁ * Matrix.conjTranspose X := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply]

private theorem mul_fromBlocks_toBlocks22 {n : ℕ}
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (X : Mₙ n) :
    (Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X)).toBlocks₂₂ =
      Y.toBlocks₂₂ * Matrix.conjTranspose X := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply]

private theorem reindexToBlockMatrix_one {n : ℕ} :
    reindexToBlockMatrix n (1 : Mₙ (2 * n)) =
      Matrix.fromBlocks (1 : Mₙ n) 0 0 (1 : Mₙ n) := by
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  simp [reindexToBlockMatrix, reindexToBlockEquiv]

private theorem twoBlockDiag_conj_mul {n : ℕ} (X : Mₙ n) :
    Matrix.conjTranspose (twoBlockDiag X X) * twoBlockDiag X X =
      twoBlockDiag (Matrix.conjTranspose X * X) (Matrix.conjTranspose X * X) := by
  apply (reindexToBlockEquiv n).injective
  have hmul :
      reindexToBlockMatrix n (Matrix.conjTranspose (twoBlockDiag X X) * twoBlockDiag X X) =
        Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) *
          Matrix.fromBlocks X 0 0 X := by
    let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    have hreindexDiag :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag X X) = Matrix.fromBlocks X 0 0 X := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks X 0 0 X))
    have hconj :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.conjTranspose (twoBlockDiag X X)) =
          Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) := by
      simpa [Matrix.fromBlocks_conjTranspose] using congrArg Matrix.conjTranspose hreindexDiag
    change
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (Matrix.conjTranspose (twoBlockDiag X X) * twoBlockDiag X X) = _
    calc
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
          (Matrix.conjTranspose (twoBlockDiag X X) * twoBlockDiag X X)
          = (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.conjTranspose (twoBlockDiag X X)) *
              (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag X X) := by
                simp
      _ = Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) *
            Matrix.fromBlocks X 0 0 X := by rw [hconj, hreindexDiag]
  calc
    reindexToBlockMatrix n (Matrix.conjTranspose (twoBlockDiag X X) * twoBlockDiag X X)
        = Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) *
            Matrix.fromBlocks X 0 0 X := hmul
    _ = Matrix.fromBlocks (Matrix.conjTranspose X * X) 0 0 (Matrix.conjTranspose X * X) := by
          simp [Matrix.fromBlocks_multiply]
    _ = reindexToBlockMatrix n
          (twoBlockDiag (Matrix.conjTranspose X * X) (Matrix.conjTranspose X * X)) := by
          simp

/-- The block-sum map preserves Loewner nonnegativity by taking the two
positive diagonal blocks of the reindexed positive block matrix and adding them. -/
theorem blockSumMap_positive (n : ℕ) :
    IsPositiveMap (blockSumMap n) := by
  intro A hA
  change 0 ≤ (reindexToBlockMatrix n A).toBlocks₁₁ + (reindexToBlockMatrix n A).toBlocks₂₂
  have hreindex : 0 ≤ reindexToBlockMatrix n A :=
    reindexToBlockMatrix_nonneg (n := n) hA
  refine add_nonneg ?_ ?_
  · rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.toBlocks₁₁] using Matrix.PosSemidef.submatrix
      (by rwa [Matrix.nonneg_iff_posSemidef] at hreindex) Sum.inl
  · rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.toBlocks₂₂] using Matrix.PosSemidef.submatrix
      (by rwa [Matrix.nonneg_iff_posSemidef] at hreindex) Sum.inr

/-- The trace of the block-sum is the trace of the original `2n × 2n` matrix,
because the trace splits over the two diagonal blocks after reindexing. -/
theorem blockSumMap_tracePreserving (n : ℕ) :
    TracePreserving (blockSumMap n) := by
  intro X
  rw [blockSumMap_apply, Matrix.trace_add]
  calc
    Matrix.trace ((reindexToBlockMatrix n X).toBlocks₁₁) +
        Matrix.trace ((reindexToBlockMatrix n X).toBlocks₂₂)
      = Matrix.trace (reindexToBlockMatrix n X) := by
          simp [Matrix.trace, Matrix.diag, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂,
            Fintype.sum_sum_type]
    _ = Matrix.trace X := trace_reindexToBlockMatrix X

/-- On the identity matrix, the block-sum map returns twice the `n × n`
identity. -/
theorem blockSumMap_one (n : ℕ) :
    blockSumMap n (1 : Mₙ (2 * n)) = (2 : ℂ) • (1 : Mₙ n) := by
  rw [blockSumMap_apply, reindexToBlockMatrix_one, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂]
  ext i j
  by_cases hij : i = j
  · subst hij
    norm_num [Matrix.one_apply]
  · simp [hij]

/-- The image of the identity under the block-sum map is positive definite; it
is the positive scalar `2` times the identity. -/
theorem blockSumMap_one_posDef (n : ℕ) :
    Matrix.PosDef (blockSumMap n (1 : Mₙ (2 * n))) := by
  rw [blockSumMap_one]
  have hpos : (((2 : ℂ) • (1 : Mₙ n)) : Mₙ n).PosDef := by
    exact Matrix.PosDef.one.smul (by positivity)
  exact hpos

private theorem hsAdjoint_blockSumMap_apply {n : ℕ} (X : Mₙ n) :
    hsAdjoint (blockSumMap n) X = twoBlockDiag X X := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  apply (@ext_inner_right ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n)))
  intro Y
  have hAdj :
      inner ℂ ((hsAdjoint (blockSumMap n)) X) Y = inner ℂ X ((blockSumMap n) Y) := by
    exact
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (2 * n)) (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := n))
        (blockSumMap n) Y X)
  have htrace :
      Matrix.trace (((Y : Mₙ (2 * n)) * Matrix.conjTranspose (twoBlockDiag X X))) =
        Matrix.trace (((blockSumMap n (Y : Mₙ (2 * n))) * Matrix.conjTranspose X)) := by
    let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    rw [← trace_reindexToBlockMatrix (X := Y * Matrix.conjTranspose (twoBlockDiag X X))]
    have hmul :
        reindexToBlockMatrix n (Y * Matrix.conjTranspose (twoBlockDiag X X)) =
          reindexToBlockMatrix n Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
            (Matrix.conjTranspose X) := by
      have hreindexDiag :
          (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag X X) =
            Matrix.fromBlocks X 0 0 X := by
        simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
          (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks X 0 0 X))
      have hconj :
          (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.conjTranspose (twoBlockDiag X X)) =
            Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) := by
        simpa [Matrix.fromBlocks_conjTranspose] using congrArg Matrix.conjTranspose hreindexDiag
      change (Matrix.reindexLinearEquiv ℂ ℂ e e) (Y * Matrix.conjTranspose (twoBlockDiag X X)) =
        (Matrix.reindexLinearEquiv ℂ ℂ e e) Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
          (Matrix.conjTranspose X)
      calc
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (Y * Matrix.conjTranspose (twoBlockDiag X X)) =
            (Matrix.reindexLinearEquiv ℂ ℂ e e) Y *
              (Matrix.reindexLinearEquiv ℂ ℂ e e)
                (Matrix.conjTranspose (twoBlockDiag X X)) := by
                rw [Matrix.reindexLinearEquiv_mul]
        _ = (Matrix.reindexLinearEquiv ℂ ℂ e e) Y *
              Matrix.fromBlocks (Matrix.conjTranspose X) 0 0 (Matrix.conjTranspose X) := by
                rw [hconj]
    rw [hmul]
    calc
      Matrix.trace
          (reindexToBlockMatrix n Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
            (Matrix.conjTranspose X)) =
        Matrix.trace ((reindexToBlockMatrix n Y).toBlocks₁₁ * Matrix.conjTranspose X) +
          Matrix.trace ((reindexToBlockMatrix n Y).toBlocks₂₂ * Matrix.conjTranspose X) := by
            rw [show Matrix.trace
                (reindexToBlockMatrix n Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
                  (Matrix.conjTranspose X)) =
              Matrix.trace
                  ((reindexToBlockMatrix n Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
                    (Matrix.conjTranspose X)).toBlocks₁₁) +
                Matrix.trace
                  ((reindexToBlockMatrix n Y * Matrix.fromBlocks (Matrix.conjTranspose X) 0 0
                    (Matrix.conjTranspose X)).toBlocks₂₂) by
                  simp [Matrix.trace, Matrix.diag, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂,
                    Fintype.sum_sum_type]]
            rw [mul_fromBlocks_toBlocks11, mul_fromBlocks_toBlocks22]
      _ = Matrix.trace ((blockSumMap n Y) * Matrix.conjTranspose X) := by
            simp [blockSumMap_apply, Matrix.trace_add, Matrix.add_mul]
  have hinner :
      inner ℂ X ((blockSumMap n) Y) = inner ℂ (twoBlockDiag X X) Y := by
    change Matrix.trace (((blockSumMap n (Y : Mₙ (2 * n))) * Matrix.conjTranspose X)) =
      Matrix.trace (((Y : Mₙ (2 * n)) * Matrix.conjTranspose (twoBlockDiag X X)))
    simpa using htrace.symm
  exact hAdj.trans hinner

/-- The Hilbert--Schmidt adjoint of the block-sum map is the diagonal
two-block embedding `X ↦ diag(X, X)`. -/
@[simp] theorem blockDiagMap_apply {n : ℕ} (X : Mₙ n) :
    blockDiagMap n X = twoBlockDiag X X := by
  simpa [blockDiagMap] using hsAdjoint_blockSumMap_apply (n := n) X

/-- The block-sum map satisfies the Hilbert--Schmidt adjoint Schwarz condition;
the adjoint sends `X` to a two-block diagonal copy, whose square is blockwise. -/
theorem blockSumMap_hsAdjointSchwarz (n : ℕ) :
    HSAdjointSchwarz (blockSumMap n) := by
  intro X
  rw [show hsAdjoint (blockSumMap n) = blockDiagMap n by rfl, blockDiagMap_apply,
    blockDiagMap_apply]
  rw [twoBlockDiag_conj_mul]

/-- Named simplification form of the Hilbert--Schmidt adjoint of `blockSumMap`. -/
@[simp] theorem blockSumMap_hsAdjoint (n : ℕ) :
    hsAdjoint (blockSumMap n) = blockDiagMap n := rfl

end MatrixScopedInstances

end HiaiPetz
