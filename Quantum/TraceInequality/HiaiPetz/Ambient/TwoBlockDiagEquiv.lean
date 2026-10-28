/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
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
# Two-block diagonal and off-diagonal block equivalences

This file identifies the diagonal and off-diagonal block submodules of `M_{2n}`
with `WithLp 2 (M_n × M_n)`.  The constructions supply continuous linear
equivalences, isometric forms, and conjugation star-algebra equivalences used to
transport CFC calculations out of the ambient matrix algebra.

## Main results

* `twoBlockDiagSubmoduleEquiv` and `twoBlockDiagSubmoduleIsometry`: the
  diagonal block submodule as a Hilbert-space pair.
* `offDiagSubmoduleEquiv` and `offDiagSubmoduleIsometry`: the off-diagonal
  block submodule as a Hilbert-space pair.
* `twoBlockDiagSubmoduleConjStarAlgEquiv` and
  `offDiagSubmoduleConjStarAlgEquiv`: conjugation star-algebra equivalences on
  endomorphism algebras.

## References

* Hiai, matrix block decompositions used in the proof of operator
  convexity and monotonicity equivalences.
-/

namespace HiaiPetz


open scoped ComplexOrder

open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Extract the two diagonal `n × n` blocks of an element of `M_{2n}` as a
pair. -/
noncomputable def twoBlockDiagToPair (n : ℕ) : Mₙ (2 * n) →L[ℂ] (Mₙ n × Mₙ n) :=
  ({ toFun := fun X =>
       ((reindexToBlockMatrix n X).toBlocks₁₁, (reindexToBlockMatrix n X).toBlocks₂₂)
     map_add' := by
       intro X Y
       ext <;> simp [reindexToBlockMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, map_add]
     map_smul' := by
       intro z X
       ext <;> simp [reindexToBlockMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, map_smul] }
    : Mₙ (2 * n) →ₗ[ℂ] (Mₙ n × Mₙ n)).toContinuousLinearMap

/-- Build a diagonal `2 × 2` block matrix from a pair of blocks. -/
noncomputable def pairToTwoBlockDiag (n : ℕ) : (Mₙ n × Mₙ n) →L[ℂ] Mₙ (2 * n) :=
  ({ toFun := fun X => twoBlockDiag X.1 X.2
     map_add' := by
       intro X Y
       apply (reindexToBlockEquiv n).injective
       simp [twoBlockDiag, Matrix.fromBlocks_add]
     map_smul' := by
       intro z X
       apply (reindexToBlockEquiv n).injective
       simp [twoBlockDiag, Matrix.fromBlocks_smul] }
    : (Mₙ n × Mₙ n) →ₗ[ℂ] Mₙ (2 * n)).toContinuousLinearMap

/-- Encode the diagonal block pair as an element of `WithLp 2 (M_n × M_n)`. -/
noncomputable def twoBlockDiagEncode (n : ℕ) :
    Mₙ (2 * n) →L[ℂ] WithLp 2 (Mₙ n × Mₙ n) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)).symm :
      (Mₙ n × Mₙ n) →L[ℂ] _).comp
    (twoBlockDiagToPair n)

/-- Decode an element of `WithLp 2 (M_n × M_n)` to a diagonal block matrix in `M_{2n}`. -/
noncomputable def twoBlockDiagDecode (n : ℕ) :
    WithLp 2 (Mₙ n × Mₙ n) →L[ℂ] Mₙ (2 * n) :=
  (pairToTwoBlockDiag n).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)) : _ →L[ℂ] (Mₙ n × Mₙ n))

/-- Applying `twoBlockDiagToPair` returns exactly the two diagonal blocks of the
reindexed block matrix. -/
@[simp] theorem twoBlockDiagToPair_apply {n : ℕ} (X : Mₙ (2 * n)) :
    twoBlockDiagToPair n X =
      ((reindexToBlockMatrix n X).toBlocks₁₁, (reindexToBlockMatrix n X).toBlocks₂₂) :=
  rfl

/-- Applying `pairToTwoBlockDiag` forms the corresponding two-block diagonal
matrix. -/
@[simp] theorem pairToTwoBlockDiag_apply {n : ℕ} (X : Mₙ n × Mₙ n) :
    pairToTwoBlockDiag n X = twoBlockDiag X.1 X.2 := rfl

/-- The diagonal encoder is block extraction followed by the `WithLp` product
equivalence. -/
@[simp] theorem twoBlockDiagEncode_apply {n : ℕ} (X : Mₙ (2 * n)) :
    twoBlockDiagEncode n X =
      WithLp.toLp 2
        ((reindexToBlockMatrix n X).toBlocks₁₁,
          (reindexToBlockMatrix n X).toBlocks₂₂) := by
  rfl

/-- The diagonal decoder builds a two-block diagonal matrix from the two
`WithLp` components. -/
@[simp] theorem twoBlockDiagDecode_apply {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    twoBlockDiagDecode n X = twoBlockDiag X.fst X.snd := by
  rfl

/-- Encoding an already diagonal block matrix returns its two diagonal blocks. -/
@[simp] theorem twoBlockDiagEncode_twoBlockDiag {n : ℕ} (X₁ X₂ : Mₙ n) :
    twoBlockDiagEncode n (twoBlockDiag X₁ X₂) = WithLp.toLp 2 (X₁, X₂) := by
  simp [twoBlockDiagEncode_apply, reindexToBlockMatrix_twoBlockDiag]

/-- Decoding a `WithLp` pair returns the corresponding diagonal block matrix. -/
@[simp] theorem twoBlockDiagDecode_toLp {n : ℕ} (X₁ X₂ : Mₙ n) :
    twoBlockDiagDecode n (WithLp.toLp 2 (X₁, X₂)) = twoBlockDiag X₁ X₂ := by
  simp [twoBlockDiagDecode_apply]

/-- The diagonal decoder lands in the two-block diagonal submodule. -/
theorem twoBlockDiagDecode_mem_submodule {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    twoBlockDiagDecode n X ∈ twoBlockDiagSubmodule n := by
  rw [twoBlockDiagDecode_apply]
  exact twoBlockDiag_mem_submodule X.fst X.snd

/-- Encoding after diagonal decoding is the identity on the `WithLp` pair
model. -/
@[simp] theorem twoBlockDiagEncode_decode {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    twoBlockDiagEncode n (twoBlockDiagDecode n X) = X := by
  apply WithLp.ofLp_injective
  ext <;> simp [twoBlockDiagEncode_apply, twoBlockDiagDecode_apply]

/-- Decoding after diagonal encoding gives the orthogonal projection onto the
two-block diagonal submodule. -/
theorem twoBlockDiagDecode_encode {n : ℕ} (X : Mₙ (2 * n)) :
    twoBlockDiagDecode n (twoBlockDiagEncode n X) = twoBlockDiagProj n X := by
  simp [twoBlockDiagDecode_apply, twoBlockDiagEncode_apply, twoBlockDiagProj_apply, fourBlockMatrix,
    twoBlockDiag]

/-- Continuous linear equivalence between diagonal block pairs and the diagonal submodule. -/
noncomputable def twoBlockDiagSubmoduleEquiv (n : ℕ) :
    WithLp 2 (Mₙ n × Mₙ n) ≃L[ℂ] twoBlockDiagSubmodule n where
  toLinearEquiv :=
    { toFun := fun X => ⟨twoBlockDiagDecode n X, twoBlockDiagDecode_mem_submodule (n := n) X⟩
      invFun := fun X => twoBlockDiagEncode n X.1
      map_add' := by
        intro X Y
        apply Subtype.ext
        apply (reindexToBlockEquiv n).injective
        simp [twoBlockDiagDecode_apply, twoBlockDiag, Matrix.fromBlocks_add]
      map_smul' := by
        intro z X
        apply Subtype.ext
        apply (reindexToBlockEquiv n).injective
        simp [twoBlockDiagDecode_apply, twoBlockDiag, Matrix.fromBlocks_smul]
      left_inv := by
        intro X
        simpa using twoBlockDiagEncode_decode (n := n) X
      right_inv := by
        intro X
        apply Subtype.ext
        change twoBlockDiagDecode n (twoBlockDiagEncode n X.1) = X.1
        rw [twoBlockDiagDecode_encode]
        exact mem_twoBlockDiagSubmodule_iff.mp X.2 }
  continuous_toFun := by
    exact (twoBlockDiagDecode n).continuous.subtype_mk _
  continuous_invFun := by
    simpa using (twoBlockDiagEncode n).continuous.comp continuous_subtype_val

/-- Coercing the diagonal submodule equivalence applies the diagonal decoder. -/
@[simp] theorem coe_twoBlockDiagSubmoduleEquiv_apply {n : ℕ}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    ((twoBlockDiagSubmoduleEquiv n X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
      twoBlockDiagDecode n X := rfl

/-- The inverse of the diagonal submodule equivalence applies the diagonal
encoder to the ambient representative. -/
@[simp] theorem twoBlockDiagSubmoduleEquiv_symm_apply {n : ℕ}
    (X : twoBlockDiagSubmodule n) :
    (twoBlockDiagSubmoduleEquiv n).symm X = twoBlockDiagEncode n X.1 := rfl

/-- The Hilbert-Schmidt inner product of two diagonal block matrices is the sum
of the inner products of their diagonal blocks. -/
theorem inner_twoBlockDiag_twoBlockDiag {n : ℕ} (X₁ X₂ Y₁ Y₂ : Mₙ n) :
    inner ℂ (twoBlockDiag X₁ X₂) (twoBlockDiag Y₁ Y₂) =
      inner ℂ X₁ Y₁ + inner ℂ X₂ Y₂ := by
  change Matrix.trace (twoBlockDiag Y₁ Y₂ * Matrix.conjTranspose (twoBlockDiag X₁ X₂)) =
      Matrix.trace (Y₁ * Matrix.conjTranspose X₁) +
        Matrix.trace (Y₂ * Matrix.conjTranspose X₂)
  rw [conjTranspose_twoBlockDiag, twoBlockDiag_mul, trace_twoBlockDiag]

/-- The diagonal decoder preserves the Hilbert-space inner product from the
`WithLp` pair model. -/
theorem inner_twoBlockDiagDecode {n : ℕ} (X Y : WithLp 2 (Mₙ n × Mₙ n)) :
    inner ℂ (twoBlockDiagDecode n X) (twoBlockDiagDecode n Y) = inner ℂ X Y := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  simpa [twoBlockDiagDecode] using
    (inner_twoBlockDiag_twoBlockDiag (n := n) X.fst X.snd Y.fst Y.snd).trans <|
      by simp

/-- Isometric form of `twoBlockDiagSubmoduleEquiv`, used for `conjStarAlgEquiv`. -/
noncomputable def twoBlockDiagSubmoduleIsometry (n : ℕ) :
    WithLp 2 (Mₙ n × Mₙ n) ≃ₗᵢ[ℂ] twoBlockDiagSubmodule n where
  toLinearEquiv := (twoBlockDiagSubmoduleEquiv n).toLinearEquiv
  norm_map' := by
    intro X
    let e := (twoBlockDiagSubmoduleEquiv n).toLinearMap
    have hinner : ∀ X Y : WithLp 2 (Mₙ n × Mₙ n), inner ℂ (e X) (e Y) = inner ℂ X Y := by
      intro X Y
      change inner ℂ ((twoBlockDiagSubmoduleEquiv n X : twoBlockDiagSubmodule n) : Mₙ (2 * n))
          (((twoBlockDiagSubmoduleEquiv n Y : twoBlockDiagSubmodule n) : Mₙ (2 * n))) =
        inner ℂ X Y
      simpa using inner_twoBlockDiagDecode (n := n) X Y
    exact (LinearMap.norm_map_iff_inner_map_map e).2 hinner X

/-- Coercing the diagonal submodule isometry applies the diagonal decoder. -/
@[simp] theorem coe_twoBlockDiagSubmoduleIsometry_apply {n : ℕ}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    (((twoBlockDiagSubmoduleIsometry n) X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
      twoBlockDiagDecode n X := rfl

/-- The inverse of the diagonal isometry applies the diagonal encoder. -/
@[simp] theorem twoBlockDiagSubmoduleIsometry_symm_apply {n : ℕ}
    (X : twoBlockDiagSubmodule n) :
    (twoBlockDiagSubmoduleIsometry n).symm X = twoBlockDiagEncode n X.1 := rfl

/-- Conjugation star-algebra equivalence between diagonal-submodule
endomorphisms and endomorphisms of the `WithLp` pair model. -/
noncomputable def twoBlockDiagSubmoduleConjStarAlgEquiv (n : ℕ) :
    (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) ≃⋆ₐ[ℂ]
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
  letI : CompleteSpace (twoBlockDiagSubmodule n) := instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (twoBlockDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ (twoBlockDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (twoBlockDiagSubmodule n) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairCompleteSpace (k := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  exact
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (twoBlockDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagSubmodule n))
      (instTwoBlockDiagSubtypeCompleteSpace (n := n))
      (WithLp 2 (Mₙ n × Mₙ n))
      (inferInstance : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)))
      (inferInstance : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)))
      (instWithLpMatrixPairCompleteSpace (k := n))
      (twoBlockDiagSubmoduleIsometry n).symm

/-- Extract the off-diagonal block pair as an element of `M_n × M_n`. -/
noncomputable def offDiagToPair (n : ℕ) : Mₙ (2 * n) →L[ℂ] Mₙ n × Mₙ n :=
  ({ toFun := fun X =>
       ((reindexToBlockMatrix n X).toBlocks₁₂, (reindexToBlockMatrix n X).toBlocks₂₁)
     map_add' := by
       intro X Y
       ext <;> simp [reindexToBlockMatrix, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁]
     map_smul' := by
       intro z X
       ext <;> simp [reindexToBlockMatrix, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] }
    : Mₙ (2 * n) →ₗ[ℂ] Mₙ n × Mₙ n).toContinuousLinearMap

/-- Decode an off-diagonal block pair to `M_{2n}`. -/
noncomputable def pairToOffDiag (n : ℕ) : Mₙ n × Mₙ n →L[ℂ] Mₙ (2 * n) :=
  ({ toFun := fun X => fourBlockMatrix 0 X.1 X.2 0
     map_add' := by
       intro X Y
       apply (reindexToBlockEquiv n).injective
       simp [fourBlockMatrix, Matrix.fromBlocks_add]
     map_smul' := by
       intro z X
       apply (reindexToBlockEquiv n).injective
       simp [fourBlockMatrix, Matrix.fromBlocks_smul] }
    : (Mₙ n × Mₙ n) →ₗ[ℂ] Mₙ (2 * n)).toContinuousLinearMap

/-- Encode the off-diagonal block pair as an element of `WithLp 2 (M_n × M_n)`. -/
noncomputable def offDiagEncode (n : ℕ) :
    Mₙ (2 * n) →L[ℂ] WithLp 2 (Mₙ n × Mₙ n) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)).symm :
      (Mₙ n × Mₙ n) →L[ℂ] _).comp
    (offDiagToPair n)

/-- Decode an element of `WithLp 2 (M_n × M_n)` to an off-diagonal block matrix. -/
noncomputable def offDiagDecode (n : ℕ) : WithLp 2 (Mₙ n × Mₙ n) →L[ℂ] Mₙ (2 * n) :=
  (pairToOffDiag n).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)) : _ →L[ℂ] (Mₙ n × Mₙ n))

/-- The off-diagonal encoder extracts the `(1,2)` and `(2,1)` blocks and
places them in the `WithLp` pair model. -/
@[simp] theorem offDiagEncode_apply {n : ℕ} (X : Mₙ (2 * n)) :
    offDiagEncode n X =
      WithLp.toLp 2
        ((reindexToBlockMatrix n X).toBlocks₁₂,
          (reindexToBlockMatrix n X).toBlocks₂₁) := by
  rfl

/-- The off-diagonal decoder builds a block matrix with zero diagonal blocks. -/
@[simp] theorem offDiagDecode_apply {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    offDiagDecode n X = fourBlockMatrix 0 X.fst X.snd 0 := by
  rfl

/-- Encoding an off-diagonal four-block matrix returns its two off-diagonal
blocks. -/
@[simp] theorem offDiagEncode_fourBlockMatrix {n : ℕ} (X₁₂ X₂₁ : Mₙ n) :
    offDiagEncode n (fourBlockMatrix 0 X₁₂ X₂₁ 0) = WithLp.toLp 2 (X₁₂, X₂₁) := by
  simp [offDiagEncode_apply, reindexToBlockMatrix_fourBlockMatrix]

/-- Decoding a `WithLp` pair returns the corresponding off-diagonal block
matrix. -/
@[simp] theorem offDiagDecode_toLp {n : ℕ} (X₁₂ X₂₁ : Mₙ n) :
    offDiagDecode n (WithLp.toLp 2 (X₁₂, X₂₁)) = fourBlockMatrix 0 X₁₂ X₂₁ 0 := by
  simp [offDiagDecode_apply]

/-- The off-diagonal decoder lands in the off-diagonal submodule. -/
theorem offDiagDecode_mem_submodule {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    offDiagDecode n X ∈ offDiagSubmodule n := by
  rw [offDiagDecode_apply]
  exact offDiag_mem_submodule X.fst X.snd

/-- Encoding after off-diagonal decoding is the identity on the `WithLp` pair
model. -/
@[simp] theorem offDiagEncode_decode {n : ℕ} (X : WithLp 2 (Mₙ n × Mₙ n)) :
    offDiagEncode n (offDiagDecode n X) = X := by
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagEncode_apply, offDiagDecode_apply]

/-- Decoding after off-diagonal encoding gives the projection onto the
off-diagonal submodule. -/
theorem offDiagDecode_encode {n : ℕ} (X : Mₙ (2 * n)) :
    offDiagDecode n (offDiagEncode n X) = offDiagProj n X := by
  simp [offDiagDecode_apply, offDiagEncode_apply, offDiagProj_apply, fourBlockMatrix]

/-- Continuous linear equivalence between off-diagonal block pairs and the
off-diagonal submodule. -/
noncomputable def offDiagSubmoduleEquiv (n : ℕ) :
    WithLp 2 (Mₙ n × Mₙ n) ≃L[ℂ] offDiagSubmodule n where
  toLinearEquiv :=
    { toFun := fun X => ⟨offDiagDecode n X, offDiagDecode_mem_submodule (n := n) X⟩
      invFun := fun X => offDiagEncode n X.1
      map_add' := by
        intro X Y
        apply Subtype.ext
        apply (reindexToBlockEquiv n).injective
        simp [offDiagDecode_apply, fourBlockMatrix, Matrix.fromBlocks_add]
      map_smul' := by
        intro z X
        apply Subtype.ext
        apply (reindexToBlockEquiv n).injective
        simp [offDiagDecode_apply, fourBlockMatrix, Matrix.fromBlocks_smul]
      left_inv := by
        intro X
        simpa using offDiagEncode_decode (n := n) X
      right_inv := by
        intro X
        apply Subtype.ext
        change offDiagDecode n (offDiagEncode n X.1) = X.1
        rw [offDiagDecode_encode]
        exact mem_offDiagSubmodule_iff.mp X.2 }
  continuous_toFun := by
    exact (offDiagDecode n).continuous.subtype_mk _
  continuous_invFun := by
    simpa using (offDiagEncode n).continuous.comp continuous_subtype_val

/-- Coercing the off-diagonal submodule equivalence applies the off-diagonal
decoder. -/
@[simp] theorem coe_offDiagSubmoduleEquiv_apply {n : ℕ}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    ((offDiagSubmoduleEquiv n X : offDiagSubmodule n) : Mₙ (2 * n)) =
      offDiagDecode n X := rfl

/-- The inverse of the off-diagonal submodule equivalence applies the
off-diagonal encoder to the ambient representative. -/
@[simp] theorem offDiagSubmoduleEquiv_symm_apply {n : ℕ}
    (X : offDiagSubmodule n) :
    (offDiagSubmoduleEquiv n).symm X = offDiagEncode n X.1 := rfl

/-- The Hilbert-Schmidt inner product of off-diagonal block matrices is the sum
of the inner products of the two off-diagonal blocks. -/
theorem inner_offDiag_fourBlock {n : ℕ} (X₁₂ X₂₁ Y₁₂ Y₂₁ : Mₙ n) :
    inner ℂ (fourBlockMatrix 0 X₁₂ X₂₁ 0) (fourBlockMatrix 0 Y₁₂ Y₂₁ 0) =
      inner ℂ X₁₂ Y₁₂ + inner ℂ X₂₁ Y₂₁ := by
  change Matrix.trace
      (fourBlockMatrix 0 Y₁₂ Y₂₁ 0 *
        Matrix.conjTranspose (fourBlockMatrix 0 X₁₂ X₂₁ 0)) =
    Matrix.trace (Y₁₂ * Matrix.conjTranspose X₁₂) +
      Matrix.trace (Y₂₁ * Matrix.conjTranspose X₂₁)
  rw [offDiag_fourBlock_mul_conjTranspose, trace_twoBlockDiag]

/-- The off-diagonal decoder preserves the Hilbert-space inner product from
the `WithLp` pair model. -/
theorem inner_offDiagDecode {n : ℕ} (X Y : WithLp 2 (Mₙ n × Mₙ n)) :
    inner ℂ (offDiagDecode n X) (offDiagDecode n Y) = inner ℂ X Y := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  simpa [offDiagDecode] using
    (inner_offDiag_fourBlock (n := n) X.fst X.snd Y.fst Y.snd).trans <|
      by simp

/-- Isometric form of `offDiagSubmoduleEquiv`, used for `conjStarAlgEquiv`. -/
noncomputable def offDiagSubmoduleIsometry (n : ℕ) :
    WithLp 2 (Mₙ n × Mₙ n) ≃ₗᵢ[ℂ] offDiagSubmodule n where
  toLinearEquiv := (offDiagSubmoduleEquiv n).toLinearEquiv
  norm_map' := by
    intro X
    let e := (offDiagSubmoduleEquiv n).toLinearMap
    have hinner : ∀ X Y : WithLp 2 (Mₙ n × Mₙ n), inner ℂ (e X) (e Y) = inner ℂ X Y := by
      intro X Y
      change inner ℂ ((offDiagSubmoduleEquiv n X : offDiagSubmodule n) : Mₙ (2 * n))
          (((offDiagSubmoduleEquiv n Y : offDiagSubmodule n) : Mₙ (2 * n))) =
        inner ℂ X Y
      simpa using inner_offDiagDecode (n := n) X Y
    exact (LinearMap.norm_map_iff_inner_map_map e).2 hinner X

/-- Coercing the off-diagonal submodule isometry applies the off-diagonal
decoder. -/
@[simp] theorem coe_offDiagSubmoduleIsometry_apply {n : ℕ}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    (((offDiagSubmoduleIsometry n) X : offDiagSubmodule n) : Mₙ (2 * n)) =
      offDiagDecode n X := rfl

/-- The inverse of the off-diagonal isometry applies the off-diagonal encoder. -/
@[simp] theorem offDiagSubmoduleIsometry_symm_apply {n : ℕ}
    (X : offDiagSubmodule n) :
    (offDiagSubmoduleIsometry n).symm X = offDiagEncode n X.1 := rfl

/-- Conjugation star-algebra equivalence between off-diagonal-submodule
endomorphisms and endomorphisms of the `WithLp` pair model. -/
noncomputable def offDiagSubmoduleConjStarAlgEquiv (n : ℕ) :
    (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairCompleteSpace (k := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  exact
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (offDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
      (instOffDiagSubtypeCompleteSpace (n := n))
      (WithLp 2 (Mₙ n × Mₙ n))
      (inferInstance : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)))
      (inferInstance : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)))
      (instWithLpMatrixPairCompleteSpace (k := n))
      (offDiagSubmoduleIsometry n).symm

end MatrixScopedInstances

end HiaiPetz
