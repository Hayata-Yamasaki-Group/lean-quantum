/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator

/-!
Evaluation rules for orthogonal-decomposition conjugation on two-block diagonal vectors.
-/

namespace HiaiPetz

open HiaiPetz.AmbientInstances

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instWithLpMatrixPairNormedAddCommGroup
  instWithLpMatrixPairNormedSpace'
  instWithLpMatrixPairInnerProductSpace'
  instWithLpMatrixPairCompleteSpace'

noncomputable section MatrixScopedInstances

-- Applying the orthogonal conjugation to a submodule vector unfolds projection cancellation.
private theorem twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule
    {n : ℕ}
    {u : ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)}
    {v : ↥(twoBlockDiagOrthogonalSubmodule n) →L[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n)}
    (Y : twoBlockDiagSubmodule n) :
    (twoBlockDiagOrthogonalConjStarAlgEquiv n
      (HansenPedersen.Internal.diagMapCLM u v)) Y.1 =
        ((u Y : twoBlockDiagSubmodule n) : Mₙ (2 * n)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : NormedAddCommGroup ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) :=
    instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  change (twoBlockDiagOrthogonalConjStarAlgEquiv n
    (HansenPedersen.Internal.diagMapCLM u v)) Y.1 =
      ((u Y : twoBlockDiagSubmodule n) : Mₙ (2 * n))
  have hprojY :
      (twoBlockDiagOrthogonalProjection n) Y.1 = Y := by
    have hprojY0 : twoBlockDiagProj n Y.1 = Y.1 :=
      mem_twoBlockDiagSubmodule_iff.mp Y.2
    apply Subtype.ext
    simpa [coe_twoBlockDiagSubmodule_orthogonalProjection_apply] using hprojY0
  have hoffY :
      (twoBlockDiagOrthogonalComplementProjection n) Y.1 = 0 := by
    have hsum :=
      congrArg (fun T : HSOp (2 * n) => T Y.1) (twoBlockDiagProj_add_offDiagProj (n := n))
    have hsum' : twoBlockDiagProj n Y.1 + offDiagProj n Y.1 = Y.1 := by
      simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] using hsum
    have hprojY0 : twoBlockDiagProj n Y.1 = Y.1 :=
      mem_twoBlockDiagSubmodule_iff.mp Y.2
    have hoffY0 : offDiagProj n Y.1 = 0 := by
      simpa [hprojY0] using hsum'
    apply Subtype.ext
    simpa [coe_twoBlockDiagOrthogonalProjection_apply] using hoffY0
  have hprojY' : (twoBlockDiagOrthogonalProjection n) Y.1 = Y := by
    simpa using hprojY
  have hoffY' : (twoBlockDiagOrthogonalComplementProjection n) Y.1 = 0 := by
    simpa using hoffY
  rw [orthogonalDecomposition_symm_conj_diag]
  rw [twoBlockDiagLiftComp, twoBlockDiagOrthogonalLiftComp, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    (((u ((twoBlockDiagOrthogonalProjection n) Y.1) : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
        ((v ((twoBlockDiagOrthogonalComplementProjection n) Y.1) :
          twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n))) =
      ((u Y : twoBlockDiagSubmodule n) : Mₙ (2 * n))
  rw [hprojY', hoffY']
  simp

/-- On the two-block diagonal submodule the orthogonal-decomposition conjugation is multiplicative
on block-diagonal lifts: conjugating `diagMapCLM c' d'` and `diagMapCLM r s` and composing the
results agrees with conjugating the single lift `diagMapCLM (c' * r) (d' * s)`, evaluated at any `X`
in the submodule. -/
theorem twoBlockDiagOrthogonalConjDiag_mul_apply_twoBlockDiagSubmodule
    {n : ℕ}
    {c' r : ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)}
    {d' s : ↥(twoBlockDiagOrthogonalSubmodule n) →L[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n)}
    (X : twoBlockDiagSubmodule n) :
    (twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM c' d') *
      twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM r s)) X.1 =
      (twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM (c' * r) (d' * s))) X.1 := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  calc
    (twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM c' d') *
      twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM r s)) X.1
      = (twoBlockDiagOrthogonalConjStarAlgEquiv n
          (HansenPedersen.Internal.diagMapCLM c' d'))
          ((twoBlockDiagOrthogonalConjStarAlgEquiv n
            (HansenPedersen.Internal.diagMapCLM r s)) X.1) := by
            rfl
    _ = (twoBlockDiagOrthogonalConjStarAlgEquiv n
          (HansenPedersen.Internal.diagMapCLM c' d'))
          (((r X : twoBlockDiagSubmodule n) : Mₙ (2 * n))) := by
            rw [twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule (n := n)
              (u := r) (v := s) X]
    _ = ((c' (r X) : twoBlockDiagSubmodule n) : Mₙ (2 * n)) := by
          simpa using
            (twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule (n := n)
              (u := c') (v := d') (Y := r X))
    _ = (twoBlockDiagOrthogonalConjStarAlgEquiv n
          (HansenPedersen.Internal.diagMapCLM (c' * r) (d' * s))) X.1 := by
          symm
          simpa [ContinuousLinearMap.mul_apply] using
            (twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule (n := n)
              (u := c' * r) (v := d' * s) X)

end MatrixScopedInstances

end HiaiPetz
