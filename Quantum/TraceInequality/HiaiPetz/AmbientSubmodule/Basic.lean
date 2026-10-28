/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Basic ambient block maps

Foundational positivity predicates, two-block matrix maps, and the trace
identities used by the ambient submodule layer.

## Main results

* `twoBlockDiag` and `fourBlockMatrix`: constructors for diagonal and general
  `2 × 2` block matrices in `M_{2n}`.
* `blockSumMap`, `dupBlockMap`, and `blockDiagMap`: block-sum and block-lift
  maps used in the ambient reduction.
* `trace_twoBlockDiag` and `trace_fourBlockMatrix`: trace formulas for block
  matrices.

## References

* Hiai, two-block matrix manipulations used in the ambient submodule
  reduction.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

/-!
Instance supply is centralized in `HiaiPetz/Core.lean` (the four scoped
`instMatrix*` instances, active inside `namespace HiaiPetz`).  The named
definitions below are kept because they are referenced by name throughout the
tree; they merely re-point to the Core instances.
-/

/-- Local alias for the normed additive group structure on matrix spaces. -/
local instance instMatrixNormedAddCommGroupScoped {k : ℕ} : NormedAddCommGroup (Mₙ k) :=
  instMatrixNormedAddCommGroup (n := k)

/-- Local alias for the complex normed-space structure on matrix spaces. -/
local instance instMatrixNormedSpaceScoped {k : ℕ} : NormedSpace ℂ (Mₙ k) :=
  instMatrixNormedSpace (n := k)

/-- Local alias for the Hilbert-space structure on matrix spaces. -/
local instance instMatrixInnerProductSpaceScoped {k : ℕ} : InnerProductSpace ℂ (Mₙ k) :=
  instMatrixInnerProductSpace (n := k)

/-- Local alias for completeness of matrix spaces. -/
local instance instMatrixCompleteSpaceScoped {k : ℕ} : CompleteSpace (Mₙ k) :=
  instMatrixCompleteSpace (n := k)

/-- Local inner-product-space instance for `WithLp` pairs of matrix spaces. -/
noncomputable local instance instWithLpMatrixPairInnerProductSpace {k : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ k × Mₙ k)) :=
  @WithLp.instProdInnerProductSpace ℂ (Mₙ k) (Mₙ k)
    inferInstance
    (instMatrixNormedAddCommGroup (n := k))
    (instMatrixInnerProductSpace (n := k))
    (instMatrixNormedAddCommGroup (n := k))
    (instMatrixInnerProductSpace (n := k))

/-- Local complex normed-space instance for `WithLp` pairs of matrix spaces. -/
noncomputable local instance instWithLpMatrixPairNormedSpace {k : ℕ} :
    NormedSpace ℂ (WithLp 2 (Mₙ k × Mₙ k)) :=
  WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ k) (β := Mₙ k)

/-- Local completeness instance for `WithLp` pairs of matrix spaces. -/
noncomputable local instance instWithLpMatrixPairCompleteSpace {k : ℕ} :
    CompleteSpace (WithLp 2 (Mₙ k × Mₙ k)) :=
  WithLp.instProdCompleteSpace (p := 2) (α := Mₙ k) (β := Mₙ k)

/-- Positivity for matrix-valued maps in the strict-output setting. -/
def IsPositiveMap {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ ⦃A : Mₙ n⦄, 0 ≤ A → 0 ≤ Φ A

/-- Trace preservation for matrix-valued maps. -/
def TracePreserving {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ A : Mₙ n, Matrix.trace (Φ A) = Matrix.trace A

/-- Schwarz-type condition for the Hilbert-Schmidt adjoint of `Φ`. -/
def HSAdjointSchwarz {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ X : Mₙ m,
    Matrix.conjTranspose ((hsAdjoint Φ) X) * ((hsAdjoint Φ) X) ≤
      hsAdjoint Φ (Matrix.conjTranspose X * X)

/-- Reindex `M_{2n}` as a `2 × 2` block matrix with `n × n` blocks. -/
noncomputable def reindexToBlockEquiv (n : ℕ) :
    Mₙ (2 * n) ≃ₗ[ℂ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  Matrix.reindexLinearEquiv ℂ ℂ e e

/-- Reindex `M_{2n}` as a `2 × 2` block matrix with `n × n` blocks. -/
noncomputable def reindexToBlockMatrix (n : ℕ) :
    Mₙ (2 * n) →ₗ[ℂ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (reindexToBlockEquiv n).toLinearMap

/-- Block-sum map used to derive `(iv)` from the output-nondegenerate direct condition. -/
noncomputable def blockSumMap (n : ℕ) : HSMap (2 * n) n :=
  ({ toFun := fun X =>
       (reindexToBlockMatrix n X).toBlocks₁₁ + (reindexToBlockMatrix n X).toBlocks₂₂
     map_add' := by
       intro X Y
       rw [map_add]
       exact add_add_add_comm _ _ _ _
     map_smul' := by
       intro z X
       ext i j
       simp [reindexToBlockMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, mul_add] }
      : Mₙ (2 * n) →ₗ[ℂ] Mₙ n).toContinuousLinearMap

/-- Applying `blockSumMap` adds the two diagonal blocks of the reindexed matrix. -/
@[simp] theorem blockSumMap_apply {n : ℕ} (X : Mₙ (2 * n)) :
    blockSumMap n X =
      (reindexToBlockMatrix n X).toBlocks₁₁ + (reindexToBlockMatrix n X).toBlocks₂₂ := rfl

/-- Two-block diagonal matrix `diag(A₁, A₂)` viewed in `M_{2n}`. -/
noncomputable def twoBlockDiag {n : ℕ} (A₁ A₂ : Mₙ n) : Mₙ (2 * n) :=
  (reindexToBlockEquiv n).symm (Matrix.fromBlocks A₁ 0 0 A₂)

/-- A general `2 × 2` block matrix with `n × n` blocks, viewed in `M_{2n}`. -/
noncomputable def fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) : Mₙ (2 * n) :=
  (reindexToBlockEquiv n).symm (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂)

/-- Reindexing a two-block diagonal matrix gives the corresponding block
matrix with zero off-diagonal blocks. -/
@[simp] theorem reindexToBlockMatrix_twoBlockDiag {n : ℕ} (A₁ A₂ : Mₙ n) :
    reindexToBlockMatrix n (twoBlockDiag A₁ A₂) = Matrix.fromBlocks A₁ 0 0 A₂ := by
  simp [twoBlockDiag, reindexToBlockMatrix]

/-- Reindexing a general four-block matrix recovers its `Matrix.fromBlocks`
form. -/
@[simp] theorem reindexToBlockMatrix_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    reindexToBlockMatrix n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := by
  simp [fourBlockMatrix, reindexToBlockMatrix]

/-- Conjugate transpose of a four-block matrix transposes the block positions
and conjugate-transposes each block. -/
@[simp] theorem conjTranspose_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    Matrix.conjTranspose (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      fourBlockMatrix (Matrix.conjTranspose X₁₁) (Matrix.conjTranspose X₂₁)
        (Matrix.conjTranspose X₁₂) (Matrix.conjTranspose X₂₂) := by
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  have h :
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (Matrix.conjTranspose (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)) =
        Matrix.conjTranspose (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂) := by
    simpa [reindexToBlockEquiv, fourBlockMatrix, e] using
      congrArg Matrix.conjTranspose
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
          (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂))
  apply (reindexToBlockEquiv n).injective
  calc
    reindexToBlockMatrix n (Matrix.conjTranspose (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂))
      = Matrix.conjTranspose (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂) := h
    _ = Matrix.fromBlocks (Matrix.conjTranspose X₁₁) (Matrix.conjTranspose X₂₁)
          (Matrix.conjTranspose X₁₂) (Matrix.conjTranspose X₂₂) := by
            simp [Matrix.fromBlocks_conjTranspose]
    _ = reindexToBlockMatrix n
          (fourBlockMatrix (Matrix.conjTranspose X₁₁) (Matrix.conjTranspose X₂₁)
            (Matrix.conjTranspose X₁₂) (Matrix.conjTranspose X₂₂)) := by
            simp

/-- The `(1,1)` block of a four-block matrix is its first input block. -/
@[simp] theorem toBlocks11_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)).toBlocks₁₁ =
      X₁₁ := by
  simp

/-- The `(1,2)` block of a four-block matrix is its second input block. -/
@[simp] theorem toBlocks12_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)).toBlocks₁₂ =
      X₁₂ := by
  simp

/-- The `(2,1)` block of a four-block matrix is its third input block. -/
@[simp] theorem toBlocks21_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)).toBlocks₂₁ =
      X₂₁ := by
  simp

/-- The `(2,2)` block of a four-block matrix is its fourth input block. -/
@[simp] theorem toBlocks22_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)).toBlocks₂₂ =
      X₂₂ := by
  simp

/-- The block-sum map sends a two-block diagonal matrix to the sum of its
diagonal blocks. -/
@[simp] theorem blockSumMap_twoBlockDiag {n : ℕ} (A₁ A₂ : Mₙ n) :
    blockSumMap n (twoBlockDiag A₁ A₂) = A₁ + A₂ := by
  simp [blockSumMap_apply, reindexToBlockMatrix_twoBlockDiag]

/-- Duplicate a matrix along the diagonal of a `2 × 2` block matrix. -/
noncomputable def dupBlockMap (n : ℕ) : HSMap n (2 * n) :=
  ({ toFun := fun X => twoBlockDiag X X
     map_add' := by
       intro X Y
       apply (reindexToBlockEquiv n).injective
       simp [twoBlockDiag, Matrix.fromBlocks_add]
     map_smul' := by
       intro z X
       apply (reindexToBlockEquiv n).injective
       simp [twoBlockDiag, Matrix.fromBlocks_smul] }
    : Mₙ n →ₗ[ℂ] Mₙ (2 * n)).toContinuousLinearMap

/-- Applying `dupBlockMap` duplicates its input on the two diagonal blocks. -/
@[simp] theorem dupBlockMap_apply {n : ℕ} (X : Mₙ n) :
    dupBlockMap n X = twoBlockDiag X X := rfl

/-- Block-diagonal lift used to derive `(iv)` from the output-nondegenerate direct condition. -/
noncomputable abbrev blockDiagMap (n : ℕ) : HSMap n (2 * n) :=
  hsAdjoint (blockSumMap n)

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
  simp [reindexToBlockMatrix, reindexToBlockEquiv, Matrix.reindexLinearEquiv_apply,
    Matrix.posSemidef_submatrix_equiv, hX']

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

/-- Trace of a two-block diagonal matrix is the sum of the traces of its
diagonal blocks. -/
theorem trace_twoBlockDiag {n : ℕ} (A₁ A₂ : Mₙ n) :
    Matrix.trace (twoBlockDiag A₁ A₂) = Matrix.trace A₁ + Matrix.trace A₂ := by
  rw [← trace_reindexToBlockMatrix]
  simp [reindexToBlockMatrix_twoBlockDiag, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- Trace of a four-block matrix is the sum of the traces of its two diagonal
blocks. -/
theorem trace_fourBlockMatrix {n : ℕ} (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    Matrix.trace (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      Matrix.trace X₁₁ + Matrix.trace X₂₂ := by
  rw [← trace_reindexToBlockMatrix]
  simp [reindexToBlockMatrix_fourBlockMatrix, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

end MatrixScopedInstances

end HiaiPetz
