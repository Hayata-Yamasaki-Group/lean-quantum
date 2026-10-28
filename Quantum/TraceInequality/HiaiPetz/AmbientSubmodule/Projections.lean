/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.BlockDiagonal

/-!
# Diagonal and off-diagonal projections

Continuous projections onto the diagonal and off-diagonal block parts, together
with their Hilbert-space adjoint and symmetry properties.

## Main results

* `twoBlockDiagProj` and `offDiagProj`: continuous projections onto the
  diagonal and off-diagonal block summands.
* `twoBlockDiagProj_add_offDiagProj`: the two projections add to the identity.
* `twoBlockDiagProj_isSymmetricProjection` and
  `offDiagProj_isSymmetricProjection`: both projections are symmetric
  idempotents for the Hilbert-Schmidt inner product.

## References

* Internal finite-dimensional two-block decomposition for the Hiai-Petz
  construction.
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

/-- Orthogonal projection onto the `2 × 2` block-diagonal subspace of `M_{2n}`. -/
noncomputable def twoBlockDiagProj (n : ℕ) : HSOp (2 * n) :=
  ({ toFun := fun X =>
       fourBlockMatrix
         (reindexToBlockMatrix n X).toBlocks₁₁ 0 0
         (reindexToBlockMatrix n X).toBlocks₂₂
     map_add' := by
       intro X Y
       apply (reindexToBlockEquiv n).injective
       ext i j
       cases i <;> cases j <;>
         simp [reindexToBlockMatrix, fourBlockMatrix, map_add,
           Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
     map_smul' := by
       intro z X
       apply (reindexToBlockEquiv n).injective
       ext i j
       cases i <;> cases j <;>
         simp [reindexToBlockMatrix, fourBlockMatrix, map_smul,
           Matrix.toBlocks₁₁, Matrix.toBlocks₂₂] }
    : Mₙ (2 * n) →ₗ[ℂ] Mₙ (2 * n)).toContinuousLinearMap

/-- Orthogonal projection onto the off-diagonal `2 × 2` block subspace of `M_{2n}`. -/
noncomputable def offDiagProj (n : ℕ) : HSOp (2 * n) :=
  ({ toFun := fun X =>
       fourBlockMatrix
         0 (reindexToBlockMatrix n X).toBlocks₁₂
         (reindexToBlockMatrix n X).toBlocks₂₁ 0
     map_add' := by
       intro X Y
       apply (reindexToBlockEquiv n).injective
       ext i j
       cases i <;> cases j <;>
         simp [reindexToBlockMatrix, fourBlockMatrix, map_add,
           Matrix.toBlocks₁₂, Matrix.toBlocks₂₁]
     map_smul' := by
       intro z X
       apply (reindexToBlockEquiv n).injective
       ext i j
       cases i <;> cases j <;>
         simp [reindexToBlockMatrix, fourBlockMatrix, map_smul,
           Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] }
    : Mₙ (2 * n) →ₗ[ℂ] Mₙ (2 * n)).toContinuousLinearMap

/-- The diagonal projection keeps only the `(1,1)` and `(2,2)` blocks of a
matrix after reindexing to `2 × 2` block form. -/
@[simp] theorem twoBlockDiagProj_apply {n : ℕ} (X : Mₙ (2 * n)) :
    twoBlockDiagProj n X =
      fourBlockMatrix
        (reindexToBlockMatrix n X).toBlocks₁₁ 0 0
        (reindexToBlockMatrix n X).toBlocks₂₂ := rfl

/-- The off-diagonal projection keeps only the `(1,2)` and `(2,1)` blocks of a
matrix after reindexing to `2 × 2` block form. -/
@[simp] theorem offDiagProj_apply {n : ℕ} (X : Mₙ (2 * n)) :
    offDiagProj n X =
      fourBlockMatrix
        0 (reindexToBlockMatrix n X).toBlocks₁₂
        (reindexToBlockMatrix n X).toBlocks₂₁ 0 := rfl

/-- A matrix already in two-block diagonal form is fixed by the diagonal
projection. -/
@[simp] theorem twoBlockDiagProj_twoBlockDiag {n : ℕ} (X₁ X₂ : Mₙ n) :
    twoBlockDiagProj n (twoBlockDiag X₁ X₂) = twoBlockDiag X₁ X₂ := by
  rw [twoBlockDiagProj_apply, reindexToBlockMatrix_twoBlockDiag]
  rfl

/-- The off-diagonal projection annihilates every two-block diagonal matrix. -/
@[simp] theorem offDiagProj_twoBlockDiag {n : ℕ} (X₁ X₂ : Mₙ n) :
    offDiagProj n (twoBlockDiag X₁ X₂) = 0 := by
  rw [offDiagProj_apply, reindexToBlockMatrix_twoBlockDiag]
  simp [fourBlockMatrix]

/-- On an explicit four-block matrix, the diagonal projection returns the
two-block diagonal matrix made from the diagonal blocks. -/
@[simp] theorem twoBlockDiagProj_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    twoBlockDiagProj n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      twoBlockDiag X₁₁ X₂₂ := by
  rw [twoBlockDiagProj_apply, reindexToBlockMatrix_fourBlockMatrix]
  rfl

/-- On an explicit four-block matrix, the off-diagonal projection returns the
matrix made from the off-diagonal blocks and zero diagonal blocks. -/
@[simp] theorem offDiagProj_fourBlockMatrix {n : ℕ}
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    offDiagProj n (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂) =
      fourBlockMatrix 0 X₁₂ X₂₁ 0 := by
  rw [offDiagProj_apply, reindexToBlockMatrix_fourBlockMatrix]
  rfl

/-- The diagonal and off-diagonal projections form a direct decomposition of
the ambient matrix space, adding to the identity operator. -/
theorem twoBlockDiagProj_add_offDiagProj {n : ℕ} :
    twoBlockDiagProj n + offDiagProj n = 1 := by
  apply ContinuousLinearMap.ext
  intro X
  rw [ContinuousLinearMap.one_apply]
  let X₁₁ := (reindexToBlockMatrix n X).toBlocks₁₁
  let X₁₂ := (reindexToBlockMatrix n X).toBlocks₁₂
  let X₂₁ := (reindexToBlockMatrix n X).toBlocks₂₁
  let X₂₂ := (reindexToBlockMatrix n X).toBlocks₂₂
  calc
    (twoBlockDiagProj n + offDiagProj n) X
        = fourBlockMatrix X₁₁ 0 0 X₂₂ + fourBlockMatrix 0 X₁₂ X₂₁ 0 := by
            simp [X₁₁, X₁₂, X₂₁, X₂₂]
    _ = fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ := by
          apply (reindexToBlockEquiv n).injective
          simp [fourBlockMatrix, X₁₁, X₁₂, X₂₁, X₂₂,
            Matrix.fromBlocks_add, add_comm]
    _ = X := by
          simp [X₁₁, X₁₂, X₂₁, X₂₂]

/-- The diagonal block projection is idempotent as an operator. -/
theorem twoBlockDiagProj_idempotent (n : ℕ) :
    twoBlockDiagProj n * twoBlockDiagProj n = twoBlockDiagProj n := by
  apply ContinuousLinearMap.ext
  intro X
  simp [twoBlockDiagProj_apply]

/-- The off-diagonal block projection is idempotent as an operator. -/
theorem offDiagProj_idempotent (n : ℕ) :
    offDiagProj n * offDiagProj n = offDiagProj n := by
  apply ContinuousLinearMap.ext
  intro X
  simp [offDiagProj_apply]

/-- The off-diagonal projection is the complement of the diagonal projection
with respect to the identity map. -/
theorem offDiagProj_eq_one_sub_twoBlockDiagProj (n : ℕ) :
    offDiagProj n = 1 - twoBlockDiagProj n := by
  apply ContinuousLinearMap.ext
  intro X
  have h :=
    congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h))

/-- The Hilbert-Schmidt adjoint of the diagonal projection is itself; the proof
uses the orthogonality of diagonal and off-diagonal block matrices. -/
theorem hsAdjoint_twoBlockDiagProj (n : ℕ) :
    hsAdjoint (twoBlockDiagProj n) = twoBlockDiagProj n := by
  letI := instMatrixNormedAddCommGroup (n := 2 * n)
  letI := instMatrixNormedSpace (n := 2 * n)
  letI := instMatrixInnerProductSpace (n := 2 * n)
  letI := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply (@ext_inner_right ℂ (Mₙ (2 * n)) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n)))
  intro Y
  let PX := twoBlockDiagProj n X
  let QX := offDiagProj n X
  let PY := twoBlockDiagProj n Y
  let QY := offDiagProj n Y
  have hX : PX + QX = X := by
    dsimp [PX, QX]
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
  have hY : PY + QY = Y := by
    dsimp [PY, QY]
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : HSOp (2 * n) => T Y) (twoBlockDiagProj_add_offDiagProj (n := n))
  have hAdj :
      inner ℂ ((hsAdjoint (twoBlockDiagProj n)) X) Y = inner ℂ X (twoBlockDiagProj n Y) := by
    simpa [hsAdjoint] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (2 * n)) (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := 2 * n))
        (twoBlockDiagProj n) Y X)
  have hcross_left : inner ℂ QX PY = 0 := by
    dsimp [QX, PY]
    simpa [twoBlockDiag, fourBlockMatrix] using
      (inner_offDiag_twoBlockDiag_eq_zero
        ((reindexToBlockMatrix n X).toBlocks₁₂)
        ((reindexToBlockMatrix n X).toBlocks₂₁)
        ((reindexToBlockMatrix n Y).toBlocks₁₁)
        ((reindexToBlockMatrix n Y).toBlocks₂₂))
  have hcross_right : inner ℂ PX QY = 0 := by
    dsimp [PX, QY]
    simpa [twoBlockDiag, fourBlockMatrix] using
      (inner_twoBlockDiag_offDiag_eq_zero
        ((reindexToBlockMatrix n X).toBlocks₁₁)
        ((reindexToBlockMatrix n X).toBlocks₂₂)
        ((reindexToBlockMatrix n Y).toBlocks₁₂)
        ((reindexToBlockMatrix n Y).toBlocks₂₁))
  calc
    inner ℂ ((hsAdjoint (twoBlockDiagProj n)) X) Y = inner ℂ X (twoBlockDiagProj n Y) := hAdj
    _ = inner ℂ (PX + QX) PY := by simp [hX, PY]
    _ = inner ℂ PX PY + inner ℂ QX PY := by simp
    _ = inner ℂ PX PY := by rw [hcross_left, add_zero]
    _ = inner ℂ PX (PY + QY) := by
          rw [inner_add_right, hcross_right, add_zero]
    _ = inner ℂ (twoBlockDiagProj n X) Y := by simp [PX, hY]

/-- The diagonal projection is a symmetric projection for the Hilbert-Schmidt
inner product. -/
theorem twoBlockDiagProj_isSymmetricProjection (n : ℕ) :
    (twoBlockDiagProj n).toLinearMap.IsSymmetricProjection := by
  letI := instMatrixNormedAddCommGroup (n := 2 * n)
  letI := instMatrixNormedSpace (n := 2 * n)
  letI := instMatrixInnerProductSpace (n := 2 * n)
  letI := instMatrixCompleteSpace (n := 2 * n)
  refine ⟨?_, ?_⟩
  · change (twoBlockDiagProj n).toLinearMap * (twoBlockDiagProj n).toLinearMap =
        (twoBlockDiagProj n).toLinearMap
    ext X
    simp
  · intro X Y
    have hAdj :
        inner ℂ ((hsAdjoint (twoBlockDiagProj n)) X) Y =
          inner ℂ X (twoBlockDiagProj n Y) := by
      simpa [hsAdjoint] using
        (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (2 * n)) (Mₙ (2 * n))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (instMatrixCompleteSpace (n := 2 * n))
          (instMatrixCompleteSpace (n := 2 * n))
          (twoBlockDiagProj n) Y X)
    simpa [hsAdjoint_twoBlockDiagProj n] using hAdj

/-- The Hilbert-Schmidt adjoint of the off-diagonal projection is itself; this
is the companion self-adjointness result to `hsAdjoint_twoBlockDiagProj`. -/
theorem hsAdjoint_offDiagProj (n : ℕ) :
    hsAdjoint (offDiagProj n) = offDiagProj n := by
  letI := instMatrixNormedAddCommGroup (n := 2 * n)
  letI := instMatrixNormedSpace (n := 2 * n)
  letI := instMatrixInnerProductSpace (n := 2 * n)
  letI := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply (@ext_inner_right ℂ (Mₙ (2 * n)) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n)))
  intro Y
  let PX := twoBlockDiagProj n X
  let QX := offDiagProj n X
  let PY := twoBlockDiagProj n Y
  let QY := offDiagProj n Y
  have hX : PX + QX = X := by
    dsimp [PX, QX]
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
  have hY : PY + QY = Y := by
    dsimp [PY, QY]
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : HSOp (2 * n) => T Y) (twoBlockDiagProj_add_offDiagProj (n := n))
  have hAdj :
      inner ℂ ((hsAdjoint (offDiagProj n)) X) Y =
        inner ℂ X (offDiagProj n Y) := by
    simpa [hsAdjoint] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (2 * n)) (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := 2 * n))
        (offDiagProj n) Y X)
  have hcross_left : inner ℂ QX PY = 0 := by
    dsimp [QX, PY]
    simpa [twoBlockDiag, fourBlockMatrix] using
      (inner_offDiag_twoBlockDiag_eq_zero
        ((reindexToBlockMatrix n X).toBlocks₁₂)
        ((reindexToBlockMatrix n X).toBlocks₂₁)
        ((reindexToBlockMatrix n Y).toBlocks₁₁)
        ((reindexToBlockMatrix n Y).toBlocks₂₂))
  have hcross_right : inner ℂ PX QY = 0 := by
    dsimp [PX, QY]
    simpa [twoBlockDiag, fourBlockMatrix] using
      (inner_twoBlockDiag_offDiag_eq_zero
        ((reindexToBlockMatrix n X).toBlocks₁₁)
        ((reindexToBlockMatrix n X).toBlocks₂₂)
        ((reindexToBlockMatrix n Y).toBlocks₁₂)
        ((reindexToBlockMatrix n Y).toBlocks₂₁))
  calc
    inner ℂ ((hsAdjoint (offDiagProj n)) X) Y = inner ℂ X (offDiagProj n Y) := hAdj
    _ = inner ℂ (PX + QX) QY := by simp [hX, QY]
    _ = inner ℂ PX QY + inner ℂ QX QY := by simp
    _ = inner ℂ QX QY := by rw [hcross_right, zero_add]
    _ = inner ℂ QX (PY + QY) := by
          rw [inner_add_right, hcross_left, zero_add]
    _ = inner ℂ (offDiagProj n X) Y := by simp [QX, hY]

/-- The off-diagonal projection is a symmetric projection for the
Hilbert-Schmidt inner product. -/
theorem offDiagProj_isSymmetricProjection (n : ℕ) :
    (offDiagProj n).toLinearMap.IsSymmetricProjection := by
  letI := instMatrixNormedAddCommGroup (n := 2 * n)
  letI := instMatrixNormedSpace (n := 2 * n)
  letI := instMatrixInnerProductSpace (n := 2 * n)
  letI := instMatrixCompleteSpace (n := 2 * n)
  refine ⟨?_, ?_⟩
  · change (offDiagProj n).toLinearMap * (offDiagProj n).toLinearMap =
        (offDiagProj n).toLinearMap
    ext X
    simp
  · intro X Y
    have hAdj :
        inner ℂ ((hsAdjoint (offDiagProj n)) X) Y =
          inner ℂ X (offDiagProj n Y) := by
      simpa [hsAdjoint] using
        (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (2 * n)) (Mₙ (2 * n))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (instMatrixCompleteSpace (n := 2 * n))
          (instMatrixCompleteSpace (n := 2 * n))
          (offDiagProj n) Y X)
    simpa [hsAdjoint_offDiagProj n] using hAdj

end MatrixScopedInstances

end HiaiPetz
