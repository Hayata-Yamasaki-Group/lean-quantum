/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Core
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
# Orthogonal decomposition of two-block diagonal inputs

This module evaluates the ambient orthogonal projection/decomposition maps on
two-block diagonal matrices.  It supplies the bridge used later to identify
restricted `J`-operators and right multiplication with diagonal operators on
the Hilbert-Schmidt pair space.

## Main results

* `twoBlockDiagSubmodule_orthogonalDecomposition_twoBlockDiag`: a diagonal
  block matrix decomposes entirely into the two-block diagonal summand.
* `twoBlockDiagSubmodule_orthogonalDecomposition_jArg_twoBlockDiag` and
  `..._rightMul_twoBlockDiag`: the same decomposition after applying the
  ambient `J`-argument or right multiplication.

## References

* Internal finite-dimensional two-block decomposition for the Hiai-Petz
  construction.
-/

namespace HiaiPetz
open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- The orthogonal projection onto the two-block diagonal submodule fixes a
matrix already written as `twoBlockDiag X₁ X₂`. -/
@[simp] theorem twoBlockDiagSubmodule_orthogonalProjection_twoBlockDiag {n : ℕ}
    (X₁ X₂ : Mₙ n) :
    twoBlockDiagOrthogonalProjection n (twoBlockDiag X₁ X₂) =
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩ := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) :=
    twoBlockDiagSubmodule_hasOrthogonalProjection n
  apply Subtype.ext
  rw [coe_twoBlockDiagSubmodule_orthogonalProjection_apply, twoBlockDiagProj_twoBlockDiag]

/-- The orthogonal complement projection of a two-block diagonal matrix is
zero, so diagonal inputs have no off-diagonal component. -/
@[simp] theorem twoBlockDiagSubmodule_orthogonalComplementProjection_twoBlockDiag {n : ℕ}
    (X₁ X₂ : Mₙ n) :
    twoBlockDiagOrthogonalComplementProjection n (twoBlockDiag X₁ X₂) = 0 := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) :=
    twoBlockDiagSubmodule_hasOrthogonalProjection n
  apply Subtype.ext
  rw [coe_twoBlockDiagOrthogonalProjection_apply, offDiagProj_twoBlockDiag]
  simp

/-- The full orthogonal decomposition of a two-block diagonal matrix is the
matrix itself in the diagonal summand and zero in the orthogonal summand. -/
@[simp] theorem twoBlockDiagSubmodule_orthogonalDecomposition_twoBlockDiag {n : ℕ}
    (X₁ X₂ : Mₙ n) :
    twoBlockDiagOrthogonalDecomposition n (twoBlockDiag X₁ X₂) =
      WithLp.toLp 2
        (⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩, 0) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : NormedAddCommGroup ↥(twoBlockDiagSubmodule n) := by infer_instance
  letI : NormedSpace ℂ ↥(twoBlockDiagSubmodule n) := by infer_instance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := by infer_instance
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) :=
    instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := by infer_instance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := by infer_instance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := by infer_instance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · change ((twoBlockDiagOrthogonalDecomposition n) (twoBlockDiag X₁ X₂)).fst =
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩
    change ((@Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
        (twoBlockDiag X₁ X₂)).fst) =
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩
    exact
      (@Submodule.fst_orthogonalDecomposition_apply ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
        (twoBlockDiag X₁ X₂)).trans
        (twoBlockDiagSubmodule_orthogonalProjection_twoBlockDiag (n := n) X₁ X₂)
  · change ((@Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
        (twoBlockDiag X₁ X₂)).snd) = 0
    exact
      (@Submodule.snd_orthogonalDecomposition_apply ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
        (twoBlockDiag X₁ X₂)).trans
        (twoBlockDiagSubmodule_orthogonalComplementProjection_twoBlockDiag (n := n) X₁ X₂)

/-- Applying the ambient `J`-argument to a two-block diagonal test matrix stays
in the diagonal summand, with componentwise `jArg Aᵢ Bᵢ` action. -/
theorem twoBlockDiagSubmodule_orthogonalDecomposition_jArg_twoBlockDiag {n : ℕ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagOrthogonalDecomposition n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiag X₁ X₂)) =
      WithLp.toLp 2
        (⟨twoBlockDiag (jArg A₁ B₁ X₁) (jArg A₂ B₂ X₂),
          twoBlockDiag_mem_submodule (n := n)
            (jArg A₁ B₁ X₁) (jArg A₂ B₂ X₂)⟩, 0) := by
  rw [jArg_twoBlockDiag hB₁ hB₂]
  simp

/-- Right multiplication by a two-block diagonal matrix preserves the diagonal
summand and acts componentwise by the corresponding right multipliers. -/
theorem twoBlockDiagSubmodule_orthogonalDecomposition_rightMul_twoBlockDiag {n : ℕ}
    {B₁ B₂ X₁ X₂ : Mₙ n} :
    twoBlockDiagOrthogonalDecomposition n
        (rightMul (twoBlockDiag B₁ B₂) (twoBlockDiag X₁ X₂)) =
      WithLp.toLp 2
        (⟨twoBlockDiag (rightMul B₁ X₁) (rightMul B₂ X₂),
          twoBlockDiag_mem_submodule (n := n) (rightMul B₁ X₁) (rightMul B₂ X₂)⟩, 0) := by
  rw [rightMul_twoBlockDiag]
  simp

end MatrixScopedInstances

end HiaiPetz
