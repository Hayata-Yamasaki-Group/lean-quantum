/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator.Basic

/-!
# Equivalences for two-block diagonal `J`-operators

This module identifies ambient `J`-argument and right-multiplication operators
with diagonal operators on the orthogonal two-block decomposition.  It also
transports the restricted diagonal and off-diagonal submodule operators to the
Hilbert-Schmidt pair model.

## Main results

* `jArg_eq_orthogonalConjDiag` and `rightMul_eq_orthogonalConjDiag`: ambient
  operators are orthogonal conjugates of diagonal restricted operators.
* `twoBlockDiagSubmoduleEquiv_jArg` and `offDiagSubmoduleEquiv_jArg`: the
  restricted `J`-arguments become componentwise matrix diagonal maps.
* `twoBlockDiagSubmoduleIsometry_jArg` and `offDiagSubmoduleIsometry_jArg`:
  star-algebra-isometry versions of the same transport identities.

## References

* Internal equivalence layer for the finite-dimensional Hiai-Petz two-block
  construction.
-/

namespace HiaiPetz
open scoped MatrixOrder Matrix.Norms.Frobenius
open scoped ComplexOrder
open scoped HiaiPetz.AmbientInstances
noncomputable section MatrixScopedInstances

private theorem orthogonalDecomposition_comp_jArg {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagOrthogonalDecompositionCLM n ∘L
        (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) =
      (HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          (offDiagRestrictedJArgOrth
            (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂)) ∘L
        twoBlockDiagOrthogonalDecompositionCLM n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  ext X
  apply (WithLp.ofLp_injective (p := 2))
  change
    ((twoBlockDiagOrthogonalProjection n)
        ((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) X),
      (twoBlockDiagOrthogonalComplementProjection n)
        ((jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) X)) =
    (((HansenPedersen.Internal.diagMapCLM
      (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      (offDiagRestrictedJArgOrth
        (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
        hB₁ hB₂)).comp
        (twoBlockDiagOrthogonalDecompositionCLM n)) X).ofLp
  refine Prod.ext ?_ ?_
  · simpa [twoBlockDiagOrthogonalDecomposition_fst,
      twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      HansenPedersen.Internal.diagMapCLM_apply, ContinuousLinearMap.comp_apply,
      WithLp.ofLp_toLp] using
      congrArg (fun Y => Y.fst)
        (twoBlockDiagSubmodule_orthogonalDecomposition_jArg (n := n) (A₁ := A₁) (A₂ := A₂)
          (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ X)
  · simpa [twoBlockDiagOrthogonalDecomposition_snd,
      twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      HansenPedersen.Internal.diagMapCLM_apply, ContinuousLinearMap.comp_apply,
      WithLp.ofLp_toLp] using
      congrArg (fun Y => Y.snd)
        (twoBlockDiagSubmodule_orthogonalDecomposition_jArg (n := n) (A₁ := A₁) (A₂ := A₂)
          (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ X)

private theorem orthogonalDecomposition_comp_rightMul {n : ℕ}
    {B₁ B₂ : Mₙ n} :
    twoBlockDiagOrthogonalDecompositionCLM n ∘L
        (rightMul (twoBlockDiag B₁ B₂)) =
      (HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂))
          (offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂))) ∘L
        twoBlockDiagOrthogonalDecompositionCLM n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  ext X
  apply (WithLp.ofLp_injective (p := 2))
  change ((twoBlockDiagOrthogonalProjection n) ((rightMul (twoBlockDiag B₁ B₂)) X),
      (twoBlockDiagOrthogonalComplementProjection n) ((rightMul (twoBlockDiag B₁ B₂)) X)) =
    (((HansenPedersen.Internal.diagMapCLM
      (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂))
      (offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂))).comp
        (twoBlockDiagOrthogonalDecompositionCLM n)) X).ofLp
  refine Prod.ext ?_ ?_
  · simpa [twoBlockDiagOrthogonalDecomposition_fst,
      twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      HansenPedersen.Internal.diagMapCLM_apply, ContinuousLinearMap.comp_apply,
      WithLp.ofLp_toLp] using
      congrArg (fun Y => Y.fst)
        (twoBlockDiagSubmodule_orthogonalDecomposition_rightMul
          (n := n) (B₁ := B₁) (B₂ := B₂) X)
  · simpa [twoBlockDiagOrthogonalDecomposition_snd,
      twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      HansenPedersen.Internal.diagMapCLM_apply, ContinuousLinearMap.comp_apply,
      WithLp.ofLp_toLp] using
      congrArg (fun Y => Y.snd)
        (twoBlockDiagSubmodule_orthogonalDecomposition_rightMul
          (n := n) (B₁ := B₁) (B₂ := B₂) X)

/-- Lift an operator on the two-block diagonal submodule to the ambient
Hilbert-Schmidt space by projecting onto that summand, applying the operator,
and including back. -/
noncomputable def twoBlockDiagLiftComp {n : ℕ}
    (a : HansenPedersen.L ↥(twoBlockDiagSubmodule n)) :
    HSOp (2 * n) := by
  exact (twoBlockDiagSubmodule n).subtypeL ∘L a ∘L twoBlockDiagOrthogonalProjection n

/-- Lift an operator on the orthogonal complement of the two-block diagonal
submodule to the ambient Hilbert-Schmidt space by compression and inclusion. -/
noncomputable def twoBlockDiagOrthogonalLiftComp {n : ℕ}
    (b : HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n)) :
    HSOp (2 * n) := by
  exact (twoBlockDiagOrthogonalSubmodule n).subtypeL ∘L b ∘L
    twoBlockDiagOrthogonalComplementProjection n

/-- Conjugating a diagonal operator on the orthogonal decomposition back to the
ambient space is the sum of its diagonal-summand and orthogonal-summand lifts. -/
theorem orthogonalDecomposition_symm_conj_diag
    {n : ℕ} {a : HansenPedersen.L ↥(twoBlockDiagSubmodule n)}
    {b : HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n)} :
    twoBlockDiagOrthogonalConjStarAlgEquiv n (HansenPedersen.Internal.diagMapCLM a b) =
      twoBlockDiagLiftComp a + twoBlockDiagOrthogonalLiftComp b := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : CompleteSpace (twoBlockDiagSubmodule n) := instTwoBlockDiagSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  ext x i j
  have hdiag :
      (HansenPedersen.Internal.diagMapCLM a b)
          ((twoBlockDiagOrthogonalDecompositionCLM n) x) =
        WithLp.toLp 2
          (a ((twoBlockDiagOrthogonalProjection n) x),
            b ((twoBlockDiagOrthogonalComplementProjection n) x)) := by
    simp [HansenPedersen.Internal.diagMapCLM, twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      ContinuousLinearMap.comp_apply]
  change
    (twoBlockDiagOrthogonalDecompositionSymmCLM n
      ((HansenPedersen.Internal.diagMapCLM a b)
        ((twoBlockDiagOrthogonalDecompositionCLM n) x))) i j =
    (twoBlockDiagLiftComp a + twoBlockDiagOrthogonalLiftComp b) x i j
  rw [hdiag]
  change
    (((a ((twoBlockDiagOrthogonalProjection n) x) :
      twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
      (((b ((twoBlockDiagOrthogonalComplementProjection n) x) :
        twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)))) i j =
    (twoBlockDiagLiftComp a + twoBlockDiagOrthogonalLiftComp b) x i j
  have hlift :
      twoBlockDiagLiftComp a x =
        ((a ((twoBlockDiagOrthogonalProjection n) x) :
          twoBlockDiagSubmodule n) : Mₙ (2 * n)) := by
    rfl
  have horth :
      twoBlockDiagOrthogonalLiftComp b x =
        (((b ((twoBlockDiagOrthogonalComplementProjection n) x) :
          twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n))) := by
    rfl
  rw [ContinuousLinearMap.add_apply, hlift, horth]

private noncomputable def twoBlockDiagCompressionComp {n : ℕ} (T : HSOp (2 * n)) :
    twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n := by
  exact twoBlockDiagOrthogonalProjection n ∘L T ∘L (twoBlockDiagSubmodule n).subtypeL

private noncomputable def twoBlockDiagOrthogonalCompressionComp {n : ℕ} (T : HSOp (2 * n)) :
    twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n := by
  exact twoBlockDiagOrthogonalComplementProjection n ∘L T ∘L
    (twoBlockDiagOrthogonalSubmodule n).subtypeL

/-- The block-diagonal map on two copies of `Mₙ n` is definitionally the local
`matrixDiagMapCLM`.
Source: the Hansen-Pedersen two-block construction underlying `hsDiagMapCLM`. -/
theorem hsDiagMapCLM_eq_matrixDiagMapCLM {n : ℕ} (a b : HSOp n) :
    hsDiagMapCLM a b = matrixDiagMapCLM (n := n) a b := by
  rfl

/-- A block diagonal continuous linear map is self-adjoint when both component
operators are self-adjoint. -/
theorem isSelfAdjoint_matrixDiagMapCLM {n : ℕ}
    {a b : HSOp n}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (matrixDiagMapCLM (n := n) a b) := by
  simpa [hsDiagMapCLM_eq_matrixDiagMapCLM] using
    (@HansenPedersen.Internal.isSelfAdjoint_diagMapCLM (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      a b ha hb)

private theorem twoBlockDiagRestrictedJArg_eq_compression {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
      twoBlockDiagCompressionComp
        (n := n) (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  have hY :
      twoBlockDiagProj n (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1) =
        jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 :=
    (twoBlockDiagProj_jArg
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      hB₁ hB₂ X.1
      |>.trans (by rw [mem_twoBlockDiagSubmodule_iff.mp X.2]))
  have hproj :
      (((twoBlockDiagOrthogonalProjection n)
          (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1) :
            twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
        jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := by
    simpa using (coe_twoBlockDiagSubmodule_orthogonalProjection_apply
      (n := n) (X := jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1)).trans hY
  simpa [twoBlockDiagCompressionComp, ContinuousLinearMap.comp_apply,
    twoBlockDiagRestrictedJArg_apply,
    coe_twoBlockDiagSubmodule_orthogonalProjection_apply] using hproj.symm

private theorem twoBlockDiagRestrictedRightMul_eq_compression {n : ℕ}
    {B₁ B₂ : Mₙ n} :
    twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂) =
      twoBlockDiagCompressionComp (n := n) (rightMul (twoBlockDiag B₁ B₂)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  have hY :
      twoBlockDiagProj n (rightMul (twoBlockDiag B₁ B₂) X.1) =
        rightMul (twoBlockDiag B₁ B₂) X.1 :=
    (twoBlockDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X.1
      |>.trans (by rw [mem_twoBlockDiagSubmodule_iff.mp X.2]))
  have hproj :
      (((twoBlockDiagOrthogonalProjection n) (rightMul (twoBlockDiag B₁ B₂) X.1) :
          twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
        rightMul (twoBlockDiag B₁ B₂) X.1 := by
    simpa using (coe_twoBlockDiagSubmodule_orthogonalProjection_apply
      (n := n) (X := rightMul (twoBlockDiag B₁ B₂) X.1)).trans hY
  simpa [twoBlockDiagCompressionComp, ContinuousLinearMap.comp_apply,
    twoBlockDiagRestrictedRightMul_apply,
    coe_twoBlockDiagSubmodule_orthogonalProjection_apply] using hproj.symm

private theorem offDiagRestrictedJArgOrth_eq_compression {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    offDiagRestrictedJArgOrth
        (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
      twoBlockDiagOrthogonalCompressionComp
        (n := n) (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  have hX : offDiagProj n X.1 = X.1 := by
    have hmem : X.1 ∈ offDiagSubmodule n := by
      simp [offDiagSubmodule_eq_orthogonal (n := n)]
    have hprojX :
        (((twoBlockDiagOrthogonalComplementProjection n) X.1 :
            twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) = X.1 := by
      calc
        (((twoBlockDiagOrthogonalComplementProjection n) X.1 :
            twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) = offDiagProj n X.1 := by
              exact coe_twoBlockDiagOrthogonalProjection_apply (n := n) X.1
        _ = X.1 := mem_offDiagSubmodule_iff.mp hmem
    exact (coe_twoBlockDiagOrthogonalProjection_apply (n := n) X.1).symm.trans hprojX
  have hY :
      offDiagProj n (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1) =
        jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 :=
    (offDiagProj_jArg
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      hB₁ hB₂ X.1
      |>.trans (by rw [hX]))
  have hproj :
      (((twoBlockDiagOrthogonalComplementProjection n)
          (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1) :
            twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
        jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1 := by
    simpa using (coe_twoBlockDiagOrthogonalProjection_apply
      (n := n) (X := jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) X.1)).trans hY
  simpa [twoBlockDiagOrthogonalCompressionComp, ContinuousLinearMap.comp_apply,
    offDiagRestrictedJArgOrth_apply,
    coe_twoBlockDiagOrthogonalProjection_apply] using hproj.symm

private theorem offDiagRestrictedRightMulOrth_eq_compression {n : ℕ}
    {B₁ B₂ : Mₙ n} :
    offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂) =
      twoBlockDiagOrthogonalCompressionComp (n := n) (rightMul (twoBlockDiag B₁ B₂)) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  have hX : offDiagProj n X.1 = X.1 := by
    have hmem : X.1 ∈ offDiagSubmodule n := by
      simp [offDiagSubmodule_eq_orthogonal (n := n)]
    have hprojX :
        (((twoBlockDiagOrthogonalComplementProjection n) X.1 :
            twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) = X.1 := by
      calc
        (((twoBlockDiagOrthogonalComplementProjection n) X.1 :
            twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) = offDiagProj n X.1 := by
              exact coe_twoBlockDiagOrthogonalProjection_apply (n := n) X.1
        _ = X.1 := mem_offDiagSubmodule_iff.mp hmem
    exact (coe_twoBlockDiagOrthogonalProjection_apply (n := n) X.1).symm.trans hprojX
  have hY :
      offDiagProj n (rightMul (twoBlockDiag B₁ B₂) X.1) =
        rightMul (twoBlockDiag B₁ B₂) X.1 :=
    (offDiagProj_rightMul (n := n) (B₁ := B₁) (B₂ := B₂) X.1
      |>.trans (by rw [hX]))
  have hproj :
      (((twoBlockDiagOrthogonalComplementProjection n) (rightMul (twoBlockDiag B₁ B₂) X.1) :
          twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
        rightMul (twoBlockDiag B₁ B₂) X.1 := by
    simpa using (coe_twoBlockDiagOrthogonalProjection_apply
      (n := n) (X := rightMul (twoBlockDiag B₁ B₂) X.1)).trans hY
  simpa [twoBlockDiagOrthogonalCompressionComp, ContinuousLinearMap.comp_apply,
    offDiagRestrictedRightMulOrth_apply,
    coe_twoBlockDiagOrthogonalProjection_apply] using hproj.symm

/-- The ambient `jArg` for two-block diagonal inputs is the orthogonal
conjugate of the diagonal map with the diagonal and off-diagonal restricted
`jArg` operators on the two summands. -/
theorem jArg_eq_orthogonalConjDiag {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          (offDiagRestrictedJArgOrth
            (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂)) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  ext x i j
  have hcomp := congrArg (fun S => S x)
    (orthogonalDecomposition_comp_jArg (n := n) (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
  have hback := congrArg (fun y => twoBlockDiagOrthogonalDecompositionSymmCLM n y) hcomp
  change (twoBlockDiagOrthogonalDecompositionSymmCLM n
      (((HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          (offDiagRestrictedJArgOrth
            (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂)).comp
          (twoBlockDiagOrthogonalDecompositionCLM n)) x)) i j =
    (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) x) i j
  exact (congrArg (fun Y => Y i j) hback.symm).trans <|
    by
      exact congrArg (fun Y => Y i j)
        (twoBlockDiagOrthogonalDecomposition_cancel
          (n := n) (X := (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) x))

/-- Right multiplication by a two-block diagonal matrix is the orthogonal
conjugate of the diagonal map of its restricted right-multiplication operators. -/
theorem rightMul_eq_orthogonalConjDiag {n : ℕ}
    {B₁ B₂ : Mₙ n} :
    twoBlockDiagOrthogonalConjStarAlgEquiv n
        (HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂))
          (offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂))) =
      rightMul (twoBlockDiag B₁ B₂) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  ext x i j
  have hcomp := congrArg (fun S => S x)
    (orthogonalDecomposition_comp_rightMul (n := n) (B₁ := B₁) (B₂ := B₂))
  have hback := congrArg (fun y => twoBlockDiagOrthogonalDecompositionSymmCLM n y) hcomp
  change (twoBlockDiagOrthogonalDecompositionSymmCLM n
      (((HansenPedersen.Internal.diagMapCLM
          (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂))
          (offDiagRestrictedRightMulOrth (n := n) (B₁ := B₁) (B₂ := B₂))).comp
          (twoBlockDiagOrthogonalDecompositionCLM n)) x)) i j =
    (rightMul (twoBlockDiag B₁ B₂) x) i j
  exact (congrArg (fun Y => Y i j) hback.symm).trans <|
    by
      exact congrArg (fun Y => Y i j)
        (twoBlockDiagOrthogonalDecomposition_cancel
          (n := n) (X := (rightMul (twoBlockDiag B₁ B₂)) x))

/-- Under the diagonal submodule equivalence, the restricted `J`-argument
becomes the matrix diagonal map with entries `jArg A₁ B₁` and `jArg A₂ B₂`. -/
theorem twoBlockDiagSubmoduleEquiv_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ((twoBlockDiagSubmoduleEquiv n).symm.toContinuousLinearMap).comp
        ((twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂).comp
          (twoBlockDiagSubmoduleEquiv n).toContinuousLinearMap) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  ext X
  simpa [ContinuousLinearMap.comp_apply, twoBlockDiagRestrictedJArg_apply,
    hsDiagMapCLM_eq_matrixDiagMapCLM] using
    twoBlockDiagEncode_jArg_decode (n := n) hB₁ hB₂ X

/-- Under the off-diagonal submodule equivalence, the restricted `J`-argument
becomes the matrix diagonal map with crossed entries `jArg A₁ B₂` and
`jArg A₂ B₁`. -/
theorem offDiagSubmoduleEquiv_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ((offDiagSubmoduleEquiv n).symm.toContinuousLinearMap).comp
        ((offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂).comp
          (offDiagSubmoduleEquiv n).toContinuousLinearMap) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  ext X
  simpa [ContinuousLinearMap.comp_apply, offDiagRestrictedJArg_apply,
    hsDiagMapCLM_eq_matrixDiagMapCLM] using
    offDiagEncode_jArg_decode (n := n) hB₁ hB₂ X

/-- Encoding the result of right multiplication on a decoded off-diagonal
matrix gives the crossed diagonal map of the two right multipliers. -/
theorem offDiagEncode_rightMul_decode {n : ℕ} {B₁ B₂ : Mₙ n}
    (X : WithLp 2 (Mₙ n × Mₙ n)) :
    offDiagEncode n
        (rightMul (twoBlockDiag B₁ B₂) (offDiagDecode n X)) =
      matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) X := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  apply WithLp.ofLp_injective
  rw [offDiagDecode_apply, matrixDiagMapCLM_apply]
  ext i j
  · simp only [offDiagEncode_apply, rightMul_apply, fourBlockMatrix_mul_twoBlockDiag,
      reindexToBlockMatrix_fourBlockMatrix, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, zero_mul]
    change (X.fst * B₂) i j = (X.fst * B₂) i j
    rfl
  · simp only [offDiagEncode_apply, rightMul_apply, fourBlockMatrix_mul_twoBlockDiag,
      reindexToBlockMatrix_fourBlockMatrix, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, zero_mul]
    change (X.snd * B₁) i j = (X.snd * B₁) i j
    rfl

/-- Under the diagonal submodule equivalence, restricted right multiplication
is the diagonal map with entries `rightMul B₁` and `rightMul B₂`. -/
theorem twoBlockDiagSubmoduleEquiv_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    ((twoBlockDiagSubmoduleEquiv n).symm.toContinuousLinearMap).comp
        ((twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)).comp
          (twoBlockDiagSubmoduleEquiv n).toContinuousLinearMap) =
      matrixDiagMapCLM (n := n) (rightMul B₁) (rightMul B₂) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  ext X
  simpa [ContinuousLinearMap.comp_apply, twoBlockDiagRestrictedRightMul_apply,
    hsDiagMapCLM_eq_matrixDiagMapCLM] using
    twoBlockDiagEncode_rightMul_decode (n := n) (B₁ := B₁) (B₂ := B₂) X

/-- Under the off-diagonal submodule equivalence, restricted right
multiplication is the crossed diagonal map with entries `rightMul B₂` and
`rightMul B₁`. -/
theorem offDiagSubmoduleEquiv_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    ((offDiagSubmoduleEquiv n).symm.toContinuousLinearMap).comp
        ((offDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)).comp
          (offDiagSubmoduleEquiv n).toContinuousLinearMap) =
      matrixDiagMapCLM (n := n) (rightMul B₂) (rightMul B₁) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  ext X
  simpa [ContinuousLinearMap.comp_apply, offDiagRestrictedRightMul_apply,
    hsDiagMapCLM_eq_matrixDiagMapCLM] using
    offDiagEncode_rightMul_decode (n := n) (B₁ := B₁) (B₂ := B₂) X

/-- Star-algebra-isometry form of `twoBlockDiagSubmoduleEquiv_jArg` for the
two-block diagonal restricted `J`-argument. -/
theorem twoBlockDiagSubmoduleIsometry_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂) := by
  simpa [twoBlockDiagSubmoduleConjStarAlgEquiv,
    LinearIsometryEquiv.conjStarAlgEquiv_apply] using
    twoBlockDiagSubmoduleEquiv_jArg
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Star-algebra-isometry form of `offDiagSubmoduleEquiv_jArg` for the
off-diagonal restricted `J`-argument. -/
theorem offDiagSubmoduleIsometry_jArg {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    offDiagSubmoduleConjStarAlgEquiv n
        (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁) := by
  simpa [offDiagSubmoduleConjStarAlgEquiv,
    LinearIsometryEquiv.conjStarAlgEquiv_apply] using
    offDiagSubmoduleEquiv_jArg
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

end MatrixScopedInstances

end HiaiPetz
