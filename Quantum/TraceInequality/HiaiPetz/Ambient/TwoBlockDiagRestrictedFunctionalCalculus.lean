/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Restricted functional calculus for two-block diagonal `J`-operators

This module connects continuous functional calculus on the ambient
Hilbert-Schmidt space with the CFC operators restricted to the diagonal,
off-diagonal, and orthogonal off-diagonal summands.  The proofs transport
CFC through the block isometries and then identify the resulting operators
with componentwise `jOperator` formulas.

## Main results

* `twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg` and
  `offDiagSubmoduleIsometry_cfcRestrictedJArg`: CFC transport through the
  diagonal and off-diagonal submodule isometries.
* `twoBlockDiagRestrictedCfc`, `offDiagRestrictedOrthCfc`, and
  `offDiagRestrictedCfc`: public restricted CFC operators used by later
  ambient bridges.
* `orthogonalConjDiagCfcOp`: the orthogonally conjugated diagonal CFC operator
  on the ambient two-block Hilbert-Schmidt space.

## References

* Internal CFC transport layer for the finite-dimensional Hiai-Petz
  two-block construction.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private noncomputable def twoBlockDiagRestrictedCfcEarly {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (_hB₁ : Matrix.PosDef B₁) (_hB₂ : Matrix.PosDef B₂) :
    ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  exact (twoBlockDiagSubmoduleConjStarAlgEquiv n).symm
    (HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
      (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)))

private noncomputable def offDiagRestrictedCfcEarly {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (_hB₁ : Matrix.PosDef B₁) (_hB₂ : Matrix.PosDef B₂) :
    ↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  exact (offDiagSubmoduleConjStarAlgEquiv n).symm
    (HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
      (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)))

/-- Transporting the early diagonal restricted CFC through the diagonal
submodule isometry gives the CFC of the diagonal `jArg` block map on the pair
space. -/
theorem twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (_hf : ContinuousOn f
      (spectrum ℝ
        (twoBlockDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (_hA₁ : IsSelfAdjoint A₁) (_hA₂ : IsSelfAdjoint A₂)
    :
    twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedCfcEarly
          (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          hB₁ hB₂) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) := by
  simp [twoBlockDiagRestrictedCfcEarly]

/-- Transporting the early off-diagonal restricted CFC through the off-diagonal
submodule isometry gives the CFC of the crossed `jArg` block map. -/
theorem offDiagSubmoduleIsometry_cfcRestrictedJArg {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (_hf : ContinuousOn f
      (spectrum ℝ
        (offDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (_hA₁ : IsSelfAdjoint A₁) (_hA₂ : IsSelfAdjoint A₂)
    :
    offDiagSubmoduleConjStarAlgEquiv n
        (offDiagRestrictedCfcEarly
          (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          hB₁ hB₂) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) := by
  simp [offDiagRestrictedCfcEarly]

private theorem diagMapCLM_jOperator {n : ℕ} {f : ℝ → ℝ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)))
    (hJ₁ : IsSelfAdjoint (jArg A₁ B₁)) (hJ₂ : IsSelfAdjoint (jArg A₂ B₂)) :
    matrixDiagMapCLM (n := n) (jOperator f A₁ B₁) (jOperator f A₂ B₂) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) *
        matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  calc
    matrixDiagMapCLM (n := n)
        (hsCfcR f (jArg A₁ B₁) * rightMul B₁)
        (hsCfcR f (jArg A₂ B₂) * rightMul B₂)
      =
        matrixDiagMapCLM (n := n)
            (hsCfcR f (jArg A₁ B₁))
            (hsCfcR f (jArg A₂ B₂)) *
          matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) := by
            ext X
            apply WithLp.ofLp_injective
            ext i j <;> rfl
    _ =
        HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) *
        matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) := by
          let R := matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂)
          have h :=
            congrArg (fun T => T * R)
              ((cfcR_diagMapCLM_union (n := n) (g := f) hf hJ₁ hJ₂).symm)
          simpa [R, hsDiagMapCLM_eq_matrixDiagMapCLM] using h

private theorem diagMapCLM_jOperator_offDiag {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (spectrum ℝ (jArg A₁ B₂) ∪ spectrum ℝ (jArg A₂ B₁)))
    (hJ₁ : IsSelfAdjoint (jArg A₁ B₂)) (hJ₂ : IsSelfAdjoint (jArg A₂ B₁)) :
    matrixDiagMapCLM (n := n) (jOperator f A₁ B₂) (jOperator f A₂ B₁) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) *
        matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  calc
    matrixDiagMapCLM (n := n)
        (hsCfcR f (jArg A₁ B₂) * rightMul B₂)
        (hsCfcR f (jArg A₂ B₁) * rightMul B₁)
      =
        matrixDiagMapCLM (n := n)
            (hsCfcR f (jArg A₁ B₂))
            (hsCfcR f (jArg A₂ B₁)) *
          matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) := by
            ext X
            apply WithLp.ofLp_injective
            ext i j <;> rfl
    _ =
        HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) *
        matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) := by
          let R := matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁)
          have h :=
            congrArg (fun T => T * R)
              ((cfcR_diagMapCLM_union (n := n) (g := f) hf hJ₁ hJ₂).symm)
          simpa [R, hsDiagMapCLM_eq_matrixDiagMapCLM] using h

/-- Auxiliary diagonal restricted CFC operator on the two-block diagonal
submodule, exposed for later wrappers under `HansenPedersen.L`. -/
noncomputable def twoBlockDiagRestrictedCfcAux {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(twoBlockDiagSubmodule n) :=
  twoBlockDiagRestrictedCfcEarly (n := n) f
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

private noncomputable def offDiagRestrictedOrthCfcAux {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n) := by
  letI : NormedAddCommGroup (offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n) :=
    inferInstance
  letI : NormedSpace ℂ (twoBlockDiagOrthogonalSubmodule n) :=
    inferInstance
  letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n) :=
    inferInstance
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  let e : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
    offDiagOrthogonalEquiv n
  let Ψ :
      (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (offDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
      (instOffDiagSubtypeCompleteSpace (n := n))
      (twoBlockDiagOrthogonalSubmodule n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n))
      (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
      e
  exact Ψ
    (offDiagRestrictedCfcEarly (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)

/-- Auxiliary off-diagonal restricted CFC operator on the off-diagonal
submodule, before transport to the orthogonal complement model. -/
noncomputable def offDiagRestrictedCfcAux {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(offDiagSubmodule n) :=
  offDiagRestrictedCfcEarly (n := n) f
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

private noncomputable def intrinsicTwoBlockDiagJOperatorAux {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L ↥(twoBlockDiagSubmodule n) :=
  twoBlockDiagRestrictedCfcAux (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ *
    twoBlockDiagRestrictedRightMulL (n := n) (B₁ := B₁) (B₂ := B₂)

private noncomputable def intrinsicOffDiagJOperatorAux {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    offDiagSubmodule n →L[ℂ] offDiagSubmodule n :=
  offDiagRestrictedCfcAux (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ *
    offDiagRestrictedRightMulL (n := n) (B₁ := B₁) (B₂ := B₂)

/-- Multiplicativity of the diagonal-submodule conjugation on the product used by
`intrinsicTwoBlockDiagJOperatorAux` (isolates the instance unification of `map_mul`). -/
private theorem twoBlockDiagSubmoduleConjStarAlgEquiv_mul {n : ℕ}
    (S T : HansenPedersen.L ↥(twoBlockDiagSubmodule n)) :
    twoBlockDiagSubmoduleConjStarAlgEquiv n (S * T) =
      twoBlockDiagSubmoduleConjStarAlgEquiv n S * twoBlockDiagSubmoduleConjStarAlgEquiv n T :=
  map_mul _ S T

/-- Multiplicativity of the off-diagonal-submodule conjugation on the product used by
`intrinsicOffDiagJOperatorAux` (isolates the instance unification of `map_mul`). -/
private theorem offDiagSubmoduleConjStarAlgEquiv_mul {n : ℕ}
    (S T : HansenPedersen.L ↥(offDiagSubmodule n)) :
    offDiagSubmoduleConjStarAlgEquiv n (S * T) =
      offDiagSubmoduleConjStarAlgEquiv n S * offDiagSubmoduleConjStarAlgEquiv n T :=
  map_mul _ S T

private theorem twoBlockDiagSubmoduleIsometry_intrinsicJOperator {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hf_restricted : ContinuousOn f
      (spectrum ℝ
        (twoBlockDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    twoBlockDiagSubmoduleConjStarAlgEquiv n
        (intrinsicTwoBlockDiagJOperatorAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      matrixDiagMapCLM (n := n) (jOperator f A₁ B₁) (jOperator f A₂ B₂) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace (twoBlockDiagSubmodule n) := instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : Star
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
    infer_instance
  have hcfc : twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedCfcAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) := by
    simpa [twoBlockDiagRestrictedCfcAux] using
      (twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg
          (n := n) (A₁ := A₁) (A₂ := A₂)
          (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
          hf_restricted hA₁ hA₂)
  have hright :
      twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedRightMulL (n := n) (B₁ := B₁) (B₂ := B₂)) =
      matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) := by
    simpa [matrixDiagMapCLM] using (@twoBlockDiagSubmoduleIsometry_rightMul n B₁ B₂)
  rw [intrinsicTwoBlockDiagJOperatorAux, twoBlockDiagSubmoduleConjStarAlgEquiv_mul, hcfc, hright]
  simpa using
    (diagMapCLM_jOperator (n := n) (f := f) (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hf_union
      (by simpa [hsAdjoint] using jArg_isSelfAdjoint hA₁ hB₁)
      (by simpa [hsAdjoint] using jArg_isSelfAdjoint hA₂ hB₂)).symm

private theorem offDiagSubmoduleIsometry_intrinsicJOperator {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hf_restricted : ContinuousOn f
      (spectrum ℝ
        (offDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₂) ∪ spectrum ℝ (jArg A₂ B₁)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    offDiagSubmoduleConjStarAlgEquiv n
        (intrinsicOffDiagJOperatorAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      matrixDiagMapCLM (n := n) (jOperator f A₁ B₂) (jOperator f A₂ B₁) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : Star
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
    infer_instance
  have hcfc : offDiagSubmoduleConjStarAlgEquiv n
        (offDiagRestrictedCfcAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) := by
    simpa [offDiagRestrictedCfcAux] using
      (offDiagSubmoduleIsometry_cfcRestrictedJArg (n := n) (A₁ := A₁) (A₂ := A₂)
          (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hf_restricted hA₁ hA₂)
  have hright :
      offDiagSubmoduleConjStarAlgEquiv n
        (offDiagRestrictedRightMulL (n := n) (B₁ := B₁) (B₂ := B₂)) =
      matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) := by
    simpa [matrixDiagMapCLM] using (@offDiagSubmoduleIsometry_rightMul n B₁ B₂)
  rw [intrinsicOffDiagJOperatorAux, offDiagSubmoduleConjStarAlgEquiv_mul, hcfc, hright]
  simpa using
    (diagMapCLM_jOperator_offDiag (n := n) (f := f) (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hf_union
      (by simpa [hsAdjoint] using jArg_isSelfAdjoint hA₁ hB₂)
      (by simpa [hsAdjoint] using jArg_isSelfAdjoint hA₂ hB₁)).symm

private theorem intrinsicJOperator_offDiag {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ X₁₂ X₂₁ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hf_restricted : ContinuousOn f
      (spectrum ℝ
        (offDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₂) ∪ spectrum ℝ (jArg A₂ B₁)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ((intrinsicOffDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨fourBlockMatrix 0 X₁₂ X₂₁ 0,
        offDiag_mem_submodule (n := n) X₁₂ X₂₁⟩ : offDiagSubmodule n) =
      ⟨fourBlockMatrix 0 (jOperator f A₁ B₂ X₁₂) (jOperator f A₂ B₁ X₂₁) 0,
        offDiag_mem_submodule (n := n)
          (jOperator f A₁ B₂ X₁₂) (jOperator f A₂ B₁ X₂₁)⟩ := by
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : Star
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
    infer_instance
  /- Step 1: Transport the off-diagonal operator to expose product action. -/
  have hmap := congrArg
    (fun T =>
      T (WithLp.toLp 2 (X₁₂, X₂₁)))
    (offDiagSubmoduleIsometry_intrinsicJOperator (n := n) (f := f)
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      hB₁ hB₂ hf_restricted hf_union hA₁ hA₂)
  /- Step 2: Decode product action into the two off-diagonal jOperators. -/
  have hpair :
      WithLp.ofLp
          (((offDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicOffDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁₂, X₂₁))) =
        (jOperator f A₁ B₂ X₁₂, jOperator f A₂ B₁ X₂₁) := by
    simpa [matrixDiagMapCLM_apply] using congrArg (WithLp.ofLp (p := 2)) hmap
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  have hdecode := congrArg (offDiagDecode n) hmap
  /- Step 3: Relate the subtype value back to its ambient off-diagonal block encoding. -/
  have hbridge :
      ↑((intrinsicOffDiagJOperatorAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨fourBlockMatrix 0 X₁₂ X₂₁ 0, offDiag_mem_submodule (n := n) X₁₂ X₂₁⟩) =
        offDiagDecode n
          (((offDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicOffDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁₂, X₂₁))) := by
    let Y : offDiagSubmodule n :=
      (intrinsicOffDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨fourBlockMatrix 0 X₁₂ X₂₁ 0, offDiag_mem_submodule (n := n) X₁₂ X₂₁⟩
    have hY : offDiagProj n (Y : Mₙ (2 * n)) = Y := by
      exact (mem_offDiagSubmodule_iff).mp Y.2
    have henc :
        (((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₂,
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₁) =
          (((offDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicOffDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁₂, X₂₁))).ofLp := by
      have hsymm :
          (offDiagSubmoduleIsometry n).symm Y =
            ((offDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicOffDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁₂, X₂₁)) := by
        unfold offDiagSubmoduleConjStarAlgEquiv
        rfl
      calc
        (((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₂,
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₁)
            = (offDiagEncode n (Y : Mₙ (2 * n))).ofLp := by
              simp [offDiagEncode_apply]
        _ = ((offDiagSubmoduleIsometry n).symm Y).ofLp := by
              symm
              simp
        _ = (((offDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicOffDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁₂, X₂₁))).ofLp := by
              simp [hsymm]
    calc
      (Y : Mₙ (2 * n)) = offDiagProj n (Y : Mₙ (2 * n)) := hY.symm
      _ = fourBlockMatrix 0
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₂
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₁ 0 := by
        simp [offDiagProj_apply]
      _ = fourBlockMatrix 0
            ((((offDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicOffDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁₂, X₂₁))).ofLp.1)
            ((((offDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicOffDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁₂, X₂₁))).ofLp.2) 0 := by
        exact congrArg (fun p => fourBlockMatrix 0 p.1 p.2 0) henc
      _ = offDiagDecode n
            (((offDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicOffDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁₂, X₂₁))) := by
        simp [offDiagDecode_apply]
  /- Step 4: Use component identities to identify the ambient off-diagonal matrix. -/
  apply Subtype.ext
  calc
    ↑((intrinsicOffDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨fourBlockMatrix 0 X₁₂ X₂₁ 0,
        offDiag_mem_submodule (n := n) X₁₂ X₂₁⟩)
      = offDiagDecode n
          (((offDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicOffDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁₂, X₂₁))) := hbridge
    _ = fourBlockMatrix 0 (jOperator f A₁ B₂ X₁₂) (jOperator f A₂ B₁ X₂₁) 0 := by
      simpa [offDiagDecode_apply, hfst, hsnd] using hdecode

private theorem intrinsicJOperator_twoBlockDiag {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hf_restricted : ContinuousOn f
      (spectrum ℝ
        (twoBlockDiagRestrictedJArgL
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)))
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ((intrinsicTwoBlockDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨twoBlockDiag X₁ X₂,
        twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩ : twoBlockDiagSubmodule n) =
      ⟨twoBlockDiag (jOperator f A₁ B₁ X₁) (jOperator f A₂ B₂ X₂),
        twoBlockDiag_mem_submodule (n := n)
          (jOperator f A₁ B₁ X₁) (jOperator f A₂ B₂ X₂)⟩ := by
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := by infer_instance
  letI : Star
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
    infer_instance
  /- Step 1: Transport the diagonal operator to expose product action. -/
  have hmap := congrArg
    (fun T =>
      T (WithLp.toLp 2 (X₁, X₂)))
    (twoBlockDiagSubmoduleIsometry_intrinsicJOperator (n := n) (f := f)
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      hB₁ hB₂ hf_restricted hf_union hA₁ hA₂)
  /- Step 2: Decode the transported product action into the two diagonal jOperator components. -/
  have hpair :
      WithLp.ofLp
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) =
        (jOperator f A₁ B₁ X₁, jOperator f A₂ B₂ X₂) := by
    simpa [matrixDiagMapCLM_apply] using congrArg (WithLp.ofLp (p := 2)) hmap
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  have hdecode := congrArg (twoBlockDiagDecode n) hmap
  /- Step 3: Relate the subtype value back to its ambient two-block diagonal encoding. -/
  have hbridge :
      ↑((intrinsicTwoBlockDiagJOperatorAux (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩) =
        twoBlockDiagDecode n
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) := by
    let Y : twoBlockDiagSubmodule n :=
      (intrinsicTwoBlockDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩
    have hY : twoBlockDiagProj n (Y : Mₙ (2 * n)) = Y := by
      exact (mem_twoBlockDiagSubmodule_iff).mp Y.2
    have henc :
        (((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₁,
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₂) =
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))).ofLp := by
      have hsymm :
          (twoBlockDiagSubmoduleIsometry n).symm Y =
            ((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂)) := by
        unfold twoBlockDiagSubmoduleConjStarAlgEquiv
        rfl
      calc
        (((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₁,
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₂)
            = (twoBlockDiagEncode n (Y : Mₙ (2 * n))).ofLp := by
              simp [twoBlockDiagEncode_apply]
        _ = ((twoBlockDiagSubmoduleIsometry n).symm Y).ofLp := by
              symm
              simp
        _ = (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))).ofLp := by
              simp [hsymm]
    calc
      (Y : Mₙ (2 * n)) = twoBlockDiagProj n (Y : Mₙ (2 * n)) := hY.symm
      _ = twoBlockDiag
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₁
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₂ := by
        simp [twoBlockDiagProj_apply, twoBlockDiag, fourBlockMatrix]
      _ = twoBlockDiag
            ((((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))).ofLp.1)
            ((((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))).ofLp.2) := by
        exact congrArg (fun p => twoBlockDiag p.1 p.2) henc
      _ = twoBlockDiagDecode n
            (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))) := by
        simp [twoBlockDiag]
  /- Step 4: Use component identities to identify the ambient two-block diagonal matrix. -/
  apply Subtype.ext
  calc
    ↑((intrinsicTwoBlockDiagJOperatorAux (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩)
      = twoBlockDiagDecode n
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (intrinsicTwoBlockDiagJOperatorAux (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) := hbridge
    _ = twoBlockDiag (jOperator f A₁ B₁ X₁) (jOperator f A₂ B₂ X₂) := by
      simpa [twoBlockDiagDecode_apply, hfst, hsnd] using hdecode

/-- Ambient CFC operator obtained by applying `hsCfcR f` directly to the
ambient `jArg` of the two-block diagonal pair. -/
noncomputable def ambientTwoBlockDiagJArgCfc {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (_hB₁ : Matrix.PosDef B₁) (_hB₂ : Matrix.PosDef B₂) :
    HSOp (2 * n) := by
  exact hsCfcR f (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂))

/-- Public restricted CFC operator on the two-block diagonal submodule,
packaged as a `HansenPedersen.L` operator. -/
noncomputable def twoBlockDiagRestrictedCfc {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L (twoBlockDiagSubmodule n) :=
  twoBlockDiagRestrictedCfcAux (n := n) f
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Restricted CFC operator transported to the orthogonal complement model of
the off-diagonal submodule. -/
noncomputable def offDiagRestrictedOrthCfc {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L (twoBlockDiagOrthogonalSubmodule n) :=
  offDiagRestrictedOrthCfcAux (n := n) f
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Public restricted CFC operator on the explicit off-diagonal submodule. -/
noncomputable def offDiagRestrictedCfc {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HansenPedersen.L (offDiagSubmodule n) :=
  offDiagRestrictedCfcAux (n := n) f
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Ambient operator obtained by conjugating the diagonal pair of restricted
CFC operators through the orthogonal two-block decomposition. -/
noncomputable def orthogonalConjDiagCfcOp {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    HSOp (2 * n) := by
  exact twoBlockDiagOrthogonalConjStarAlgEquiv n
    (HansenPedersen.Internal.diagMapCLM
      (twoBlockDiagRestrictedCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      (offDiagRestrictedOrthCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))


end MatrixScopedInstances

end HiaiPetz
