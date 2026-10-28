/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagEquiv
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagHilbertSpace
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
# Two-block diagonal `J`-operator restrictions

This file proves that the ambient `jArg` and right-multiplication operators
respect the diagonal and off-diagonal block submodules.  It packages the
restricted operators on the submodules and on the orthogonal complement so that
later CFC transport can split the ambient action into block components.

## Main results

* `twoBlockDiagProj_jArg` and `offDiagProj_jArg`: `jArg` commutes with the
  diagonal and off-diagonal projections for two-block diagonal parameters.
* `twoBlockDiagRestrictedJArg` and `offDiagRestrictedJArg`: submodule
  restrictions of the ambient `jArg`.
* `twoBlockDiagSubmodule_orthogonalDecomposition_jArg` and
  `twoBlockDiagSubmodule_orthogonalDecomposition_rightMul`: blockwise formulas
  for the orthogonal decomposition of the ambient action.

## References

* Hiai, off-diagonal block decomposition of the `J`-operator in the
  operator convexity/monotonicity argument.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Applying `jArg` with two-block diagonal parameters and then projecting to
the diagonal blocks keeps only the two diagonal componentwise `jArg`s. -/
theorem twoBlockDiagProj_jArg_fourBlockMatrix {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    twoBlockDiagProj n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)) =
      twoBlockDiag (jArg A₁ B₁ X₁₁) (jArg A₂ B₂ X₂₂) := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simpa using
    (twoBlockDiagProj_fourBlockMatrix
      (X₁₁ := jArg A₁ B₁ X₁₁) (X₁₂ := jArg A₁ B₂ X₁₂)
      (X₂₁ := jArg A₂ B₁ X₂₁) (X₂₂ := jArg A₂ B₂ X₂₂))

/-- Applying `jArg` with two-block diagonal parameters and then projecting to
the off-diagonal blocks keeps only the two mixed componentwise `jArg`s. -/
theorem offDiagProj_jArg_fourBlockMatrix {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X₁₁ X₁₂ X₂₁ X₂₂ : Mₙ n) :
    offDiagProj n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
          (fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂)) =
      fourBlockMatrix 0 (jArg A₁ B₂ X₁₂) (jArg A₂ B₁ X₂₁) 0 := by
  rw [jArg_fourBlockMatrix hB₁ hB₂]
  simp

/-- For two-block diagonal parameters, the diagonal projection commutes with
the ambient `jArg`. -/
theorem twoBlockDiagProj_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : Mₙ (2 * n)) :
    twoBlockDiagProj n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
        (twoBlockDiagProj n X) := by
  let X₁₁ := (reindexToBlockMatrix n X).toBlocks₁₁
  let X₁₂ := (reindexToBlockMatrix n X).toBlocks₁₂
  let X₂₁ := (reindexToBlockMatrix n X).toBlocks₂₁
  let X₂₂ := (reindexToBlockMatrix n X).toBlocks₂₂
  have hX : fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ = X := by
    simp [X₁₁, X₁₂, X₂₁, X₂₂]
  rw [← hX, twoBlockDiagProj_jArg_fourBlockMatrix hB₁ hB₂, twoBlockDiagProj_fourBlockMatrix,
    jArg_twoBlockDiag hB₁ hB₂]

/-- For two-block diagonal parameters, the off-diagonal projection commutes
with the ambient `jArg`. -/
theorem offDiagProj_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : Mₙ (2 * n)) :
    offDiagProj n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
        (offDiagProj n X) := by
  let X₁₁ := (reindexToBlockMatrix n X).toBlocks₁₁
  let X₁₂ := (reindexToBlockMatrix n X).toBlocks₁₂
  let X₂₁ := (reindexToBlockMatrix n X).toBlocks₂₁
  let X₂₂ := (reindexToBlockMatrix n X).toBlocks₂₂
  have hX : fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ = X := by
    simp [X₁₁, X₁₂, X₂₁, X₂₂]
  rw [← hX, offDiagProj_jArg_fourBlockMatrix hB₁ hB₂, offDiagProj_fourBlockMatrix,
    jArg_fourBlockMatrix hB₁ hB₂]
  simp [jArg_apply]

/-- Diagonal operator on the `WithLp` matrix-pair model, applying `a` to the
first component and `b` to the second. -/
noncomputable def matrixDiagMapCLM {n : ℕ}
    (a b : Mₙ n →L[ℂ] Mₙ n) :
    (WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] WithLp 2 (Mₙ n × Mₙ n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairNormedSpace (k := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
    instWithLpMatrixPairInnerProductSpace (k := n)
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairCompleteSpace (k := n)
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)).symm :
      Mₙ n × Mₙ n →L[ℂ] WithLp 2 (Mₙ n × Mₙ n)).comp <|
    (a.prodMap b).comp ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)) :
      WithLp 2 (Mₙ n × Mₙ n) →L[ℂ] Mₙ n × Mₙ n)

/-- Applying `matrixDiagMapCLM` is componentwise application on the `WithLp`
pair. -/
@[simp] theorem matrixDiagMapCLM_apply {n : ℕ}
    (a b : Mₙ n →L[ℂ] Mₙ n) (X : WithLp 2 (Mₙ n × Mₙ n)) :
    matrixDiagMapCLM (n := n) a b X = WithLp.toLp 2 (a X.fst, b X.snd) := by
  cases X
  rfl

/-- Encoding the diagonal restriction of ambient `jArg` gives the componentwise
diagonal operator on the `WithLp` pair model. -/
theorem twoBlockDiagEncode_jArg_decode {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : WithLp 2 (Mₙ n × Mₙ n)) :
    twoBlockDiagEncode n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiagDecode n X)) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂) X := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  apply WithLp.ofLp_injective
  rw [twoBlockDiagDecode_apply, jArg_twoBlockDiag hB₁ hB₂, twoBlockDiagEncode_apply,
    matrixDiagMapCLM_apply, reindexToBlockMatrix_twoBlockDiag]
  ext i j
  · simp only [jArg_apply, Matrix.toBlocks_fromBlocks₁₁]
    change (A₁ * X.fst * B₁⁻¹) i j = ((rightMul (B₁⁻¹)) ((leftMul A₁) X.fst)) i j
    rw [leftMul_apply, rightMul_apply, Matrix.mul_assoc]
  · simp only [jArg_apply, Matrix.toBlocks_fromBlocks₂₂]
    change (A₂ * X.snd * B₂⁻¹) i j = ((rightMul (B₂⁻¹)) ((leftMul A₂) X.snd)) i j
    rw [leftMul_apply, rightMul_apply, Matrix.mul_assoc]

/-- Encoding the off-diagonal restriction of ambient `jArg` gives the mixed
componentwise operator on the `WithLp` pair model. -/
theorem offDiagEncode_jArg_decode {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : WithLp 2 (Mₙ n × Mₙ n)) :
    offDiagEncode n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (offDiagDecode n X)) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁) X := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  apply WithLp.ofLp_injective
  rw [offDiagDecode_apply, jArg_fourBlockMatrix hB₁ hB₂, offDiagEncode_apply,
    matrixDiagMapCLM_apply, reindexToBlockMatrix_fourBlockMatrix]
  ext i j
  · simp only [jArg_apply, mul_zero, zero_mul, Matrix.toBlocks_fromBlocks₁₂]
    change (A₁ * X.fst * B₂⁻¹) i j = ((rightMul (B₂⁻¹)) ((leftMul A₁) X.fst)) i j
    rw [leftMul_apply, rightMul_apply, Matrix.mul_assoc]
  · simp only [jArg_apply, mul_zero, zero_mul, Matrix.toBlocks_fromBlocks₂₁]
    change (A₂ * X.snd * B₁⁻¹) i j = ((rightMul (B₁⁻¹)) ((leftMul A₂) X.snd)) i j
    rw [leftMul_apply, rightMul_apply, Matrix.mul_assoc]

/-- Encoding right multiplication on the diagonal submodule gives componentwise
right multiplication on the `WithLp` pair model. -/
theorem twoBlockDiagEncode_rightMul_decode {n : ℕ} {B₁ B₂ : Mₙ n}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    twoBlockDiagEncode n
        (rightMul (twoBlockDiag B₁ B₂) (twoBlockDiagDecode n X)) =
      matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) X := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  apply WithLp.ofLp_injective
  rw [twoBlockDiagDecode_apply, rightMul_twoBlockDiag, twoBlockDiagEncode_apply,
    matrixDiagMapCLM_apply, reindexToBlockMatrix_twoBlockDiag]
  ext i j
  · change (X.fst * B₁) i j = (rightMul B₁ X.fst) i j
    rw [rightMul_apply]
  · change (X.snd * B₂) i j = (rightMul B₂ X.snd) i j
    rw [rightMul_apply]

/-- Right multiplication by a two-block diagonal matrix commutes with the
diagonal projection. -/
theorem twoBlockDiagProj_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} (X : Mₙ (2 * n)) :
    twoBlockDiagProj n (rightMul (twoBlockDiag B₁ B₂) X) =
      rightMul (twoBlockDiag B₁ B₂) (twoBlockDiagProj n X) := by
  let X₁₁ := (reindexToBlockMatrix n X).toBlocks₁₁
  let X₁₂ := (reindexToBlockMatrix n X).toBlocks₁₂
  let X₂₁ := (reindexToBlockMatrix n X).toBlocks₂₁
  let X₂₂ := (reindexToBlockMatrix n X).toBlocks₂₂
  have hX : fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ = X := by
    simp [X₁₁, X₁₂, X₂₁, X₂₂]
  rw [← hX, rightMul_apply, fourBlockMatrix_mul_twoBlockDiag, twoBlockDiagProj_fourBlockMatrix,
    twoBlockDiagProj_fourBlockMatrix, rightMul_apply, twoBlockDiag_mul]

/-- Right multiplication by a two-block diagonal matrix commutes with the
off-diagonal projection. -/
theorem offDiagProj_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} (X : Mₙ (2 * n)) :
    offDiagProj n (rightMul (twoBlockDiag B₁ B₂) X) =
      rightMul (twoBlockDiag B₁ B₂) (offDiagProj n X) := by
  let X₁₁ := (reindexToBlockMatrix n X).toBlocks₁₁
  let X₁₂ := (reindexToBlockMatrix n X).toBlocks₁₂
  let X₂₁ := (reindexToBlockMatrix n X).toBlocks₂₁
  let X₂₂ := (reindexToBlockMatrix n X).toBlocks₂₂
  have hX : fourBlockMatrix X₁₁ X₁₂ X₂₁ X₂₂ = X := by
    simp [X₁₁, X₁₂, X₂₁, X₂₂]
  rw [← hX, rightMul_apply, fourBlockMatrix_mul_twoBlockDiag, offDiagProj_fourBlockMatrix,
    offDiagProj_fourBlockMatrix, rightMul_apply, fourBlockMatrix_mul_twoBlockDiag]
  simp

/-- `jArg` restricted to the diagonal block submodule. -/
noncomputable def twoBlockDiagRestrictedJArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n) :=
  (((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)).comp
      (twoBlockDiagSubmodule n).subtypeL).codRestrict
    (twoBlockDiagSubmodule n) (fun X => by
      rw [mem_twoBlockDiagSubmodule_iff]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      calc
        twoBlockDiagProj n ((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) X.1)
            = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiagProj n X.1) :=
              twoBlockDiagProj_jArg hB₁ hB₂ X.1
        _ = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := by
              rw [mem_twoBlockDiagSubmodule_iff.mp X.2]))

/-- `rightMul` by a diagonal block matrix restricted to the diagonal block submodule. -/
noncomputable def twoBlockDiagRestrictedRightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n) :=
  (((rightMul (twoBlockDiag B₁ B₂)).comp (twoBlockDiagSubmodule n).subtypeL).codRestrict
    (twoBlockDiagSubmodule n) (fun X => by
      rw [mem_twoBlockDiagSubmodule_iff]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      calc
        twoBlockDiagProj n ((rightMul (twoBlockDiag B₁ B₂)) X.1)
            = rightMul (twoBlockDiag B₁ B₂) (twoBlockDiagProj n X.1) :=
              twoBlockDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X.1
        _ = rightMul (twoBlockDiag B₁ B₂) X.1 := by
              rw [mem_twoBlockDiagSubmodule_iff.mp X.2]))

/-- `jArg` restricted to the off-diagonal block submodule. -/
noncomputable def offDiagRestrictedJArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n) :=
  (((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)).comp
      (offDiagSubmodule n).subtypeL).codRestrict
    (offDiagSubmodule n) (fun X => by
      rw [mem_offDiagSubmodule_iff]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      calc
        offDiagProj n ((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) X.1)
            = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (offDiagProj n X.1) :=
              offDiagProj_jArg (n := n) hB₁ hB₂ X.1
        _ = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := by
              rw [mem_offDiagSubmodule_iff.mp X.2]))

/-- `rightMul` by a diagonal block matrix restricted to the off-diagonal block
submodule. -/
noncomputable def offDiagRestrictedRightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    ↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n) :=
  (((rightMul (twoBlockDiag B₁ B₂)).comp (offDiagSubmodule n).subtypeL).codRestrict
    (offDiagSubmodule n) (fun X => by
      rw [mem_offDiagSubmodule_iff]
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      calc
        offDiagProj n ((rightMul (twoBlockDiag B₁ B₂)) X.1)
            = rightMul (twoBlockDiag B₁ B₂) (offDiagProj n X.1) :=
              offDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X.1
        _ = rightMul (twoBlockDiag B₁ B₂) X.1 := by
              rw [mem_offDiagSubmodule_iff.mp X.2]))

/-- Coercing `twoBlockDiagRestrictedJArg` to the ambient matrix space recovers
the ambient `jArg` on the representative. -/
@[simp] theorem twoBlockDiagRestrictedJArg_apply {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : twoBlockDiagSubmodule n) :
    ((twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ X :
        twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := rfl

/-- Coercing `twoBlockDiagRestrictedRightMul` to the ambient matrix space
recovers ambient right multiplication on the representative. -/
@[simp] theorem twoBlockDiagRestrictedRightMul_apply {n : ℕ} {B₁ B₂ : Mₙ n}
    (X : twoBlockDiagSubmodule n) :
    ((twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂) X :
        twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
      rightMul (twoBlockDiag B₁ B₂) X.1 := rfl

/-- Coercing `offDiagRestrictedJArg` to the ambient matrix space recovers the
ambient `jArg` on the representative. -/
@[simp] theorem offDiagRestrictedJArg_apply {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) (X : offDiagSubmodule n) :
    ((offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ X :
        offDiagSubmodule n) : Mₙ (2 * n)) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := rfl

/-- Coercing `offDiagRestrictedRightMul` to the ambient matrix space recovers
ambient right multiplication on the representative. -/
@[simp] theorem offDiagRestrictedRightMul_apply {n : ℕ} {B₁ B₂ : Mₙ n}
    (X : offDiagSubmodule n) :
    ((offDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂) X :
        offDiagSubmodule n) : Mₙ (2 * n)) =
      rightMul (twoBlockDiag B₁ B₂) X.1 := rfl

/-- Hilbert-space endomorphism alias for `twoBlockDiagRestrictedJArg`. -/
noncomputable abbrev twoBlockDiagRestrictedJArgL {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(twoBlockDiagSubmodule n) :=
  twoBlockDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Hilbert-space endomorphism alias for `offDiagRestrictedJArg`. -/
noncomputable abbrev offDiagRestrictedJArgL {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(offDiagSubmodule n) :=
  offDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Hilbert-space endomorphism alias for `twoBlockDiagRestrictedRightMul`. -/
noncomputable abbrev twoBlockDiagRestrictedRightMulL {n : ℕ} {B₁ B₂ : Mₙ n} :
    HansenPedersen.L ↥(twoBlockDiagSubmodule n) :=
  twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)

/-- Hilbert-space endomorphism alias for `offDiagRestrictedRightMul`. -/
noncomputable abbrev offDiagRestrictedRightMulL {n : ℕ} {B₁ B₂ : Mₙ n} :
    HansenPedersen.L ↥(offDiagSubmodule n) :=
  offDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)

/-- `jArg` on the off-diagonal block subspace, transported to the orthogonal
complement of the diagonal block subspace. -/
noncomputable def offDiagRestrictedJArgOrth {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ↥(twoBlockDiagOrthogonalSubmodule n) →L[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n) :=
  by
    let od : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
      offDiagOrthogonalEquiv n
    exact od.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) ∘L
      od.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- `rightMul` on the off-diagonal block subspace, transported to the
orthogonal complement of the diagonal block subspace. -/
noncomputable def offDiagRestrictedRightMulOrth {n : ℕ} {B₁ B₂ : Mₙ n} :
    ↥(twoBlockDiagOrthogonalSubmodule n) →L[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n) :=
  by
    let od : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
      offDiagOrthogonalEquiv n
    exact od.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (offDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)) ∘L
      od.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Hilbert-space endomorphism alias for the orthogonal-complement transport of
`offDiagRestrictedJArg`. -/
noncomputable abbrev offDiagRestrictedJArgOrthL {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n) :=
  offDiagRestrictedJArgOrth
    (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Coercing the orthogonal-complement transport of `offDiagRestrictedJArg`
recovers the ambient `jArg` on representatives. -/
@[simp] theorem offDiagRestrictedJArgOrth_apply {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X : twoBlockDiagOrthogonalSubmodule n) :
    ((offDiagRestrictedJArgOrth (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
        hB₁ hB₂ X : twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := by
  change (((offDiagOrthogonalEquiv n) (offDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ ((offDiagOrthogonalEquiv n).symm X)) :
        twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1
  rw [coe_offDiagOrthogonalEquiv_apply, offDiagRestrictedJArg_apply,
    coe_offDiagOrthogonalEquiv_symm_apply]

/-- Coercing the orthogonal-complement transport of `offDiagRestrictedRightMul`
recovers ambient right multiplication on representatives. -/
@[simp] theorem offDiagRestrictedRightMulOrth_apply {n : ℕ} {B₁ B₂ : Mₙ n}
    (X : twoBlockDiagOrthogonalSubmodule n) :
    ((offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂) X :
        twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
      rightMul (twoBlockDiag B₁ B₂) X.1 := by
  change (((offDiagOrthogonalEquiv n) (offDiagRestrictedRightMul (n := n)
      (B₁ := B₁) (B₂ := B₂) ((offDiagOrthogonalEquiv n).symm X)) :
        twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
      rightMul (twoBlockDiag B₁ B₂) X.1
  rw [coe_offDiagOrthogonalEquiv_apply, offDiagRestrictedRightMul_apply,
    coe_offDiagOrthogonalEquiv_symm_apply]

/-- Orthogonal decomposition formula for ambient `jArg`: the diagonal component
uses `twoBlockDiagRestrictedJArg` and the orthogonal component uses the
transported off-diagonal restriction. -/
theorem twoBlockDiagSubmodule_orthogonalDecomposition_jArg {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (X : Mₙ (2 * n)) :
    twoBlockDiagOrthogonalDecomposition n
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) =
      WithLp.toLp 2
        (twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
            (twoBlockDiagOrthogonalProjection n X),
          offDiagRestrictedJArgOrth
            (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂ (twoBlockDiagOrthogonalComplementProjection n X)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : CompleteSpace (twoBlockDiagSubmodule n) := instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  change
    @Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) =
      _
  apply (WithLp.ofLp_injective (p := 2))
  simp only [Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    calc
      ((twoBlockDiagOrthogonalProjection n
          (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) : twoBlockDiagSubmodule n) :
            Mₙ (2 * n))
          = twoBlockDiagProj n (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) := by
              exact coe_twoBlockDiagSubmodule_orthogonalProjection_apply _
      _ = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiagProj n X) := by
            exact twoBlockDiagProj_jArg (n := n) hB₁ hB₂ X
      _ = ((twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
            (twoBlockDiagOrthogonalProjection n X) : twoBlockDiagSubmodule n) :
              Mₙ (2 * n)) := by
            rw [twoBlockDiagRestrictedJArg_apply,
              coe_twoBlockDiagSubmodule_orthogonalProjection_apply]
  · apply Subtype.ext
    calc
      ((twoBlockDiagOrthogonalComplementProjection n
          (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) :
            twoBlockDiagOrthogonalSubmodule n) :
            Mₙ (2 * n))
          = offDiagProj n (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X) := by
              exact coe_twoBlockDiagOrthogonalProjection_apply _
      _ = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (offDiagProj n X) := by
            exact offDiagProj_jArg (n := n) hB₁ hB₂ X
      _ = ((offDiagRestrictedJArgOrth
            (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂ (twoBlockDiagOrthogonalComplementProjection n X) :
              twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) := by
            rw [offDiagRestrictedJArgOrth_apply, coe_twoBlockDiagOrthogonalProjection_apply]

/-- Orthogonal decomposition formula for ambient right multiplication by a
two-block diagonal matrix. -/
theorem twoBlockDiagSubmodule_orthogonalDecomposition_rightMul {n : ℕ}
    {B₁ B₂ : Mₙ n} (X : Mₙ (2 * n)) :
    twoBlockDiagOrthogonalDecomposition n
        (rightMul (twoBlockDiag B₁ B₂) X) =
      WithLp.toLp 2
        (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)
            (twoBlockDiagOrthogonalProjection n X),
          offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂)
            (twoBlockDiagOrthogonalComplementProjection n X)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : CompleteSpace (twoBlockDiagSubmodule n) := instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  change
    @Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      (rightMul (twoBlockDiag B₁ B₂) X) =
      _
  apply (WithLp.ofLp_injective (p := 2))
  simp only [Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    calc
      ((twoBlockDiagOrthogonalProjection n
          (rightMul (twoBlockDiag B₁ B₂) X) : twoBlockDiagSubmodule n) : Mₙ (2 * n))
          = twoBlockDiagProj n (rightMul (twoBlockDiag B₁ B₂) X) := by
              exact coe_twoBlockDiagSubmodule_orthogonalProjection_apply _
      _ = rightMul (twoBlockDiag B₁ B₂) (twoBlockDiagProj n X) := by
            exact twoBlockDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X
      _ = ((twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)
            (twoBlockDiagOrthogonalProjection n X) : twoBlockDiagSubmodule n) :
              Mₙ (2 * n)) := by
            rw [twoBlockDiagRestrictedRightMul_apply,
              coe_twoBlockDiagSubmodule_orthogonalProjection_apply]
  · apply Subtype.ext
    calc
      ((twoBlockDiagOrthogonalComplementProjection n
          (rightMul (twoBlockDiag B₁ B₂) X) : twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n))
          = offDiagProj n (rightMul (twoBlockDiag B₁ B₂) X) := by
            exact coe_twoBlockDiagOrthogonalProjection_apply _
      _ = rightMul (twoBlockDiag B₁ B₂) (offDiagProj n X) := by
            exact offDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X
      _ = ((offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂)
            (twoBlockDiagOrthogonalComplementProjection n X) :
              twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) := by
            rw [offDiagRestrictedRightMulOrth_apply, coe_twoBlockDiagOrthogonalProjection_apply]

end MatrixScopedInstances

end HiaiPetz
