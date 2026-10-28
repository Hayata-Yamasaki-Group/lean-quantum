/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities

/-!
# Two-block diagonal algebra

Block multiplication, `jArg` block formulas, and orthogonality identities for
diagonal and off-diagonal block matrices.

## Main results

* `twoBlockDiag_mul`, `twoBlockDiag_mul_fourBlockMatrix`, and
  `fourBlockMatrix_mul_twoBlockDiag`: block multiplication formulas.
* `jArg_twoBlockDiag` and `jArg_fourBlockMatrix`: componentwise action of the
  ambient `J`-argument on diagonal and four-block matrices.
* `inner_twoBlockDiag_offDiag_eq_zero` and
  `inner_offDiag_twoBlockDiag_eq_zero`: Hilbert-Schmidt orthogonality of the
  diagonal and off-diagonal block subspaces.

## References

* Internal finite-dimensional block-matrix algebra for the Hiai-Petz
  two-block construction.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

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
    _ =
        reindexToBlockMatrix n
          (twoBlockDiag (Matrix.conjTranspose X * X) (Matrix.conjTranspose X * X)) := by
          simp

/-- Multiplying two two-block diagonal matrices is componentwise multiplication
of the diagonal blocks. -/
theorem twoBlockDiag_mul {n : ℕ} (A₁ A₂ B₁ B₂ : Mₙ n) :
    twoBlockDiag A₁ A₂ * twoBlockDiag B₁ B₂ = twoBlockDiag (A₁ * B₁) (A₂ * B₂) := by
  apply (reindexToBlockEquiv n).injective
  have hmul :
      reindexToBlockMatrix n (twoBlockDiag A₁ A₂ * twoBlockDiag B₁ B₂) =
        Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks B₁ 0 0 B₂ := by
    let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    have hA :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂) =
          Matrix.fromBlocks A₁ 0 0 A₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks A₁ 0 0 A₂))
    have hB :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag B₁ B₂) =
          Matrix.fromBlocks B₁ 0 0 B₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks B₁ 0 0 B₂))
    change
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (twoBlockDiag A₁ A₂ * twoBlockDiag B₁ B₂) = _
    calc
      (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂ * twoBlockDiag B₁ B₂)
          = (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂) *
              (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag B₁ B₂) := by
                simp
      _ = Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks B₁ 0 0 B₂ := by
            rw [hA, hB]
  calc
    reindexToBlockMatrix n (twoBlockDiag A₁ A₂ * twoBlockDiag B₁ B₂)
        = Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks B₁ 0 0 B₂ := hmul
    _ = Matrix.fromBlocks (A₁ * B₁) 0 0 (A₂ * B₂) := by
          simp [Matrix.fromBlocks_multiply]
    _ = reindexToBlockMatrix n (twoBlockDiag (A₁ * B₁) (A₂ * B₂)) := by
          simp

/-- Multiplication by a two-block diagonal matrix on the left acts on each row
block of an explicit four-block matrix by the corresponding diagonal block. -/
theorem twoBlockDiag_mul_fourBlockMatrix {n : ℕ}
    (A₁ A₂ X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    twoBlockDiag A₁ A₂ * fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ =
      fourBlockMatrix (A₁ * X₁₁) (A₁ * X₁₂) (A₂ * X₂₁) (A₂ * X₂₂) := by
  apply (reindexToBlockEquiv n).injective
  have hmul :
      reindexToBlockMatrix n
          (twoBlockDiag A₁ A₂ * fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
        Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := by
    let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    have hA :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂) =
          Matrix.fromBlocks A₁ 0 0 A₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks A₁ 0 0 A₂))
    have hX :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
          Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, fourBlockMatrix] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
          (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂))
    change (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (twoBlockDiag A₁ A₂ * fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) = _
    calc
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
          (twoBlockDiag A₁ A₂ * fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)
          =
            (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂) *
              (Matrix.reindexLinearEquiv ℂ ℂ e e)
                (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) := by
                  simp
      _ = Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := by
            rw [hA, hX]
  calc
    reindexToBlockMatrix n
        (twoBlockDiag A₁ A₂ * fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)
        = Matrix.fromBlocks A₁ 0 0 A₂ *
          Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := hmul
    _ = Matrix.fromBlocks (A₁ * X₁₁) (A₁ * X₁₂) (A₂ * X₂₁) (A₂ * X₂₂) := by
          simp [Matrix.fromBlocks_multiply]
    _ = reindexToBlockMatrix n
          (fourBlockMatrix
            (A₁ * X₁₁) (A₁ * X₁₂) (A₂ * X₂₁) (A₂ * X₂₂)) := by
          simp

/-- Conjugate transpose of a two-block diagonal matrix is computed
componentwise on the diagonal blocks. -/
@[simp] theorem conjTranspose_twoBlockDiag {n : ℕ} (A₁ A₂ : Mₙ n) :
    Matrix.conjTranspose (twoBlockDiag A₁ A₂) =
      twoBlockDiag (Matrix.conjTranspose A₁) (Matrix.conjTranspose A₂) := by
  apply (reindexToBlockEquiv n).injective
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  have hreindexDiag :
      (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag A₁ A₂) =
        Matrix.fromBlocks A₁ 0 0 A₂ := by
    simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
      (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks A₁ 0 0 A₂))
  have hconj :
      (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.conjTranspose (twoBlockDiag A₁ A₂)) =
        Matrix.fromBlocks (Matrix.conjTranspose A₁) 0 0 (Matrix.conjTranspose A₂) := by
    simpa [Matrix.fromBlocks_conjTranspose] using congrArg Matrix.conjTranspose hreindexDiag
  have hrhs :
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (twoBlockDiag (Matrix.conjTranspose A₁) (Matrix.conjTranspose A₂)) =
          Matrix.fromBlocks (Matrix.conjTranspose A₁) 0 0 (Matrix.conjTranspose A₂) := by
    simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
      (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
        (Matrix.fromBlocks (Matrix.conjTranspose A₁) 0 0 (Matrix.conjTranspose A₂)))
  exact hconj.trans hrhs.symm

/-- Multiplication by a two-block diagonal matrix on the right acts on each
column block of an explicit four-block matrix by the corresponding block. -/
theorem fourBlockMatrix_mul_twoBlockDiag {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ B₁ B₂ : Mₙ n) :
    fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ * twoBlockDiag B₁ B₂ =
      fourBlockMatrix (X₁₁ * B₁) (X₁₂ * B₂) (X₂₁ * B₁) (X₂₂ * B₂) := by
  apply (reindexToBlockEquiv n).injective
  have hmul :
      reindexToBlockMatrix n
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ * twoBlockDiag B₁ B₂) =
        Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ * Matrix.fromBlocks B₁ 0 0 B₂ := by
    let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    have hX :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
          Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, fourBlockMatrix] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
          (Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂))
    have hB :
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag B₁ B₂) =
          Matrix.fromBlocks B₁ 0 0 B₂ := by
      simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, twoBlockDiag] using
        (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks B₁ 0 0 B₂))
    change (Matrix.reindexLinearEquiv ℂ ℂ e e)
        (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ * twoBlockDiag B₁ B₂) = _
    calc
      (Matrix.reindexLinearEquiv ℂ ℂ e e)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ * twoBlockDiag B₁ B₂)
          =
            (Matrix.reindexLinearEquiv ℂ ℂ e e)
              (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) *
              (Matrix.reindexLinearEquiv ℂ ℂ e e) (twoBlockDiag B₁ B₂) := by
                  simp
      _ = Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ * Matrix.fromBlocks B₁ 0 0 B₂ := by
            rw [hX, hB]
  calc
    reindexToBlockMatrix n
        (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ * twoBlockDiag B₁ B₂)
        = Matrix.fromBlocks X₁₁ X₁₂ X₂₁ X₂₂ *
          Matrix.fromBlocks B₁ 0 0 B₂ := hmul
    _ = Matrix.fromBlocks (X₁₁ * B₁) (X₁₂ * B₂) (X₂₁ * B₁) (X₂₂ * B₂) := by
          simp [Matrix.fromBlocks_multiply]
    _ = reindexToBlockMatrix n
          (fourBlockMatrix
            (X₁₁ * B₁) (X₁₂ * B₂) (X₂₁ * B₁) (X₂₂ * B₂)) := by
          simp

/-- The product of an off-diagonal block matrix with the conjugate transpose of
another off-diagonal block matrix is two-block diagonal. -/
theorem offDiag_fourBlock_mul_conjTranspose {n : ℕ}
    (X₁₂ X₂₁ Y₁₂ Y₂₁ : Mₙ n) :
    fourBlockMatrix 0 X₁₂ X₂₁ 0 *
        Matrix.conjTranspose (fourBlockMatrix 0 Y₁₂ Y₂₁ 0) =
      twoBlockDiag
        (X₁₂ * Matrix.conjTranspose Y₁₂) (X₂₁ * Matrix.conjTranspose Y₂₁) := by
  have hconj :
      Matrix.conjTranspose (fourBlockMatrix 0 Y₁₂ Y₂₁ 0) =
        fourBlockMatrix 0 (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0 := by
    simp
  rw [hconj]
  apply (reindexToBlockEquiv n).injective
  calc
    (reindexToBlockEquiv n)
        (fourBlockMatrix 0 X₁₂ X₂₁ 0 * fourBlockMatrix 0 (Matrix.conjTranspose Y₂₁)
          (Matrix.conjTranspose Y₁₂) 0)
      = Matrix.fromBlocks 0 X₁₂ X₂₁ 0 *
          Matrix.fromBlocks 0 (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0 := by
            let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
              (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
            have hX :
                (Matrix.reindexLinearEquiv ℂ ℂ e e) (fourBlockMatrix 0 X₁₂ X₂₁ 0) =
                  Matrix.fromBlocks 0 X₁₂ X₂₁ 0 := by
                simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, fourBlockMatrix] using
                  (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
                    (Matrix.fromBlocks 0 X₁₂ X₂₁ 0))
            have hY :
                (Matrix.reindexLinearEquiv ℂ ℂ e e)
                    (fourBlockMatrix 0
                      (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0) =
                  Matrix.fromBlocks 0
                    (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0 := by
                simpa [reindexToBlockEquiv, reindexToBlockMatrix, e, fourBlockMatrix] using
                  (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
                    (Matrix.fromBlocks 0
                      (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0))
            change (Matrix.reindexLinearEquiv ℂ ℂ e e)
                (fourBlockMatrix 0 X₁₂ X₂₁ 0 *
                  fourBlockMatrix 0
                    (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0) = _
            calc
              (Matrix.reindexLinearEquiv ℂ ℂ e e)
                  (fourBlockMatrix 0 X₁₂ X₂₁ 0 *
                    fourBlockMatrix 0
                      (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0)
                = (Matrix.reindexLinearEquiv ℂ ℂ e e) (fourBlockMatrix 0 X₁₂ X₂₁ 0) *
                    (Matrix.reindexLinearEquiv ℂ ℂ e e)
                      (fourBlockMatrix 0
                        (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0) := by
                        simp
              _ = Matrix.fromBlocks 0 X₁₂ X₂₁ 0 *
                    Matrix.fromBlocks 0
                      (Matrix.conjTranspose Y₂₁) (Matrix.conjTranspose Y₁₂) 0 := by
                      rw [hX, hY]
    _ =
        Matrix.fromBlocks
          (X₁₂ * Matrix.conjTranspose Y₁₂) 0 0
          (X₂₁ * Matrix.conjTranspose Y₂₁) := by
          simp [Matrix.fromBlocks_multiply]
    _ = (reindexToBlockEquiv n)
          (twoBlockDiag
            (X₁₂ * Matrix.conjTranspose Y₁₂) (X₂₁ * Matrix.conjTranspose Y₂₁)) := by
            simp [twoBlockDiag]

/-- Left multiplication by a two-block diagonal matrix acts componentwise on a
two-block diagonal test matrix. -/
theorem leftMul_twoBlockDiag {n : ℕ} (A₁ A₂ X₁ X₂ : Mₙ n) :
    leftMul (twoBlockDiag A₁ A₂) (twoBlockDiag X₁ X₂) =
      twoBlockDiag (A₁ * X₁) (A₂ * X₂) := by
  simpa [leftMul] using twoBlockDiag_mul A₁ A₂ X₁ X₂

/-- Right multiplication by a two-block diagonal matrix acts componentwise on a
two-block diagonal test matrix. -/
theorem rightMul_twoBlockDiag {n : ℕ} (B₁ B₂ X₁ X₂ : Mₙ n) :
    rightMul (twoBlockDiag B₁ B₂) (twoBlockDiag X₁ X₂) =
      twoBlockDiag (X₁ * B₁) (X₂ * B₂) := by
  simpa [rightMul] using twoBlockDiag_mul X₁ X₂ B₁ B₂

/-- The ambient `J`-argument of two two-block diagonal inputs preserves the
diagonal test subspace and acts componentwise by `jArg Aᵢ Bᵢ`. -/
theorem jArg_twoBlockDiag {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X₁ X₂ : Mₙ n) :
    jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiag X₁ X₂) =
      twoBlockDiag (jArg A₁ B₁ X₁) (jArg A₂ B₂ X₂) := by
  rw [jArg_apply, twoBlockDiag_inv hB₁ hB₂, twoBlockDiag_mul, twoBlockDiag_mul]
  simp [jArg_apply, mul_assoc]

/-- The ambient `J`-argument of two two-block diagonal inputs acts on a general
four-block matrix by the four expected componentwise `jArg` operators. -/
theorem jArg_fourBlockMatrix {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
        (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      fourBlockMatrix
        (jArg A₁ B₁ X₁₁)
        (jArg A₁ B₂ X₁₂)
        (jArg A₂ B₁ X₂₁)
        (jArg A₂ B₂ X₂₂) := by
  rw [jArg_apply, twoBlockDiag_inv hB₁ hB₂, twoBlockDiag_mul_fourBlockMatrix,
    fourBlockMatrix_mul_twoBlockDiag]
  simp [jArg_apply, mul_assoc]

/-- The ambient `J`-argument preserves the predicate of being two-block
diagonal when the input test matrix is two-block diagonal. -/
theorem jArg_preserves_twoBlockDiagonal {n : ℕ} {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    Matrix.IsTwoBlockDiagonal
      (reindexToBlockMatrix n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiag X₁ X₂))) := by
  rw [jArg_twoBlockDiag hB₁ hB₂ X₁ X₂]
  simp [Matrix.IsTwoBlockDiagonal]

/-- The `(1,1)` block of the ambient `J`-argument on a four-block matrix is
`jArg A₁ B₁` applied to the `(1,1)` block. -/
theorem jArg_fourBlockMatrix_toBlocks11 {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂))).toBlocks₁₁ =
      jArg A₁ B₁ X₁₁ := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simp

/-- The `(1,2)` block of the ambient `J`-argument on a four-block matrix is
`jArg A₁ B₂` applied to the `(1,2)` block. -/
theorem jArg_fourBlockMatrix_toBlocks12 {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂))).toBlocks₁₂ =
      jArg A₁ B₂ X₁₂ := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simp

/-- The `(2,1)` block of the ambient `J`-argument on a four-block matrix is
`jArg A₂ B₁` applied to the `(2,1)` block. -/
theorem jArg_fourBlockMatrix_toBlocks21 {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂))).toBlocks₂₁ =
      jArg A₂ B₁ X₂₁ := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simp

/-- The `(2,2)` block of the ambient `J`-argument on a four-block matrix is
`jArg A₂ B₂` applied to the `(2,2)` block. -/
theorem jArg_fourBlockMatrix_toBlocks22 {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    (reindexToBlockMatrix n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂))).toBlocks₂₂ =
      jArg A₂ B₂ X₂₂ := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simp

/-- The Hilbert-Schmidt trace pairing between a two-block diagonal matrix and
an off-diagonal block matrix vanishes at the matrix-trace level. -/
theorem trace_mul_twoBlockDiag_offDiag {n : ℕ} (A₁ A₂ X₁₂ X₂₁ : Mₙ n) :
    Matrix.trace
      (Matrix.conjTranspose (twoBlockDiag A₁ A₂) *
        fourBlockMatrix 0 X₁₂ X₂₁ 0) = 0 := by
  rw [conjTranspose_twoBlockDiag, twoBlockDiag_mul_fourBlockMatrix, trace_fourBlockMatrix]
  simp

/-- Diagonal and off-diagonal block matrices are orthogonal for the
Hilbert-Schmidt inner product, with the diagonal matrix on the left. -/
theorem inner_twoBlockDiag_offDiag_eq_zero {n : ℕ} (A₁ A₂ X₁₂ X₂₁ : Mₙ n) :
    inner ℂ (twoBlockDiag A₁ A₂) (fourBlockMatrix 0 X₁₂ X₂₁ 0) = 0 := by
  change
    Matrix.trace
      (fourBlockMatrix 0 X₁₂ X₂₁ 0 * Matrix.conjTranspose (twoBlockDiag A₁ A₂)) = 0
  rw [Matrix.trace_mul_comm, trace_mul_twoBlockDiag_offDiag]

/-- Diagonal and off-diagonal block matrices are orthogonal for the
Hilbert-Schmidt inner product, with the off-diagonal matrix on the left. -/
theorem inner_offDiag_twoBlockDiag_eq_zero {n : ℕ} (X₁₂ X₂₁ A₁ A₂ : Mₙ n) :
    inner ℂ (fourBlockMatrix 0 X₁₂ X₂₁ 0) (twoBlockDiag A₁ A₂) = 0 := by
  have h :=
    inner_twoBlockDiag_offDiag_eq_zero
      (A₁ := A₁) (A₂ := A₂) (X₁₂ := X₁₂) (X₂₁ := X₂₁)
  simpa [InnerProductSpace.conj_inner_symm] using congrArg star h

/-- Reassembling the four blocks of the reindexed form of a matrix gives back
the original ambient matrix. -/
@[simp] theorem fourBlockMatrix_reindex_blocks {n : ℕ} (X : Mₙ (2 * n)) :
    fourBlockMatrix
        (reindexToBlockMatrix n X).toBlocks₁₁
        (reindexToBlockMatrix n X).toBlocks₁₂
        (reindexToBlockMatrix n X).toBlocks₂₁
        (reindexToBlockMatrix n X).toBlocks₂₂ = X := by
  apply (reindexToBlockEquiv n).injective
  simpa [reindexToBlockMatrix, fourBlockMatrix] using
    (Matrix.fromBlocks_toBlocks ((reindexToBlockEquiv n) X))

end MatrixScopedInstances

end HiaiPetz
