/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport
import Quantum.TraceInequality.HiaiPetz.JArgAction
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport
import Quantum.TraceInequality.HiaiPetz.Core.Homogeneity

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private noncomputable def twoBlockDiagLiftComp_hp62 {n : ℕ}
    (a : HansenPedersen.L ↥(twoBlockDiagSubmodule n)) :
    HSOp (2 * n) := by
  exact (twoBlockDiagSubmodule n).subtypeL ∘L a ∘L twoBlockDiagOrthogonalProjection n

private noncomputable def twoBlockDiagOrthogonalLiftComp_hp62 {n : ℕ}
    (b : HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n)) :
    HSOp (2 * n) := by
  exact (twoBlockDiagOrthogonalSubmodule n).subtypeL ∘L b ∘L
    twoBlockDiagOrthogonalComplementProjection n

private theorem orthogonalDecomposition_symm_conj_diag_hp62
    {n : ℕ} {a : HansenPedersen.L ↥(twoBlockDiagSubmodule n)}
    {b : HansenPedersen.L ↥(twoBlockDiagOrthogonalSubmodule n)} :
    twoBlockDiagOrthogonalConjStarAlgEquiv n (HansenPedersen.Internal.diagMapCLM a b) =
      twoBlockDiagLiftComp_hp62 a + twoBlockDiagOrthogonalLiftComp_hp62 b := by
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
      (HansenPedersen.Internal.diagMapCLM a b) ((twoBlockDiagOrthogonalDecompositionCLM n) x) =
        WithLp.toLp 2
          (a ((twoBlockDiagOrthogonalProjection n) x),
            b ((twoBlockDiagOrthogonalComplementProjection n) x)) := by
    simp [HansenPedersen.Internal.diagMapCLM, twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      ContinuousLinearMap.comp_apply]
  change (twoBlockDiagOrthogonalDecompositionSymmCLM n
      ((HansenPedersen.Internal.diagMapCLM a b)
        ((twoBlockDiagOrthogonalDecompositionCLM n) x))) i j =
    (twoBlockDiagLiftComp_hp62 a + twoBlockDiagOrthogonalLiftComp_hp62 b) x i j
  rw [hdiag]
  change (((a ((twoBlockDiagOrthogonalProjection n) x) : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
      (((b ((twoBlockDiagOrthogonalComplementProjection n) x) :
        twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)))) i j =
    (twoBlockDiagLiftComp_hp62 a + twoBlockDiagOrthogonalLiftComp_hp62 b) x i j
  have hlift :
      twoBlockDiagLiftComp_hp62 a x =
        (((a ((twoBlockDiagOrthogonalProjection n) x) : twoBlockDiagSubmodule n) :
          Mₙ (2 * n))) := by
    rfl
  have horth :
      twoBlockDiagOrthogonalLiftComp_hp62 b x =
        (((b ((twoBlockDiagOrthogonalComplementProjection n) x) :
          twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n))) := by
    rfl
  rw [ContinuousLinearMap.add_apply, hlift, horth]

private theorem twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule_hp62
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
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
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
  rw [orthogonalDecomposition_symm_conj_diag_hp62]
  rw [twoBlockDiagLiftComp_hp62, twoBlockDiagOrthogonalLiftComp_hp62, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    (((u ((twoBlockDiagOrthogonalProjection n) Y.1) : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
        ((v ((twoBlockDiagOrthogonalComplementProjection n) Y.1) :
          twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n))) =
      ((u Y : twoBlockDiagSubmodule n) : Mₙ (2 * n))
  rw [hprojY', hoffY']
  simp

@[simp] private theorem hsDiagMapCLM_apply_hp62 {n : ℕ}
    (a b : HSOp n) (X : hsBlockSpace n) :
    hsDiagMapCLM a b X = WithLp.toLp 2 (a X.fst, b X.snd) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  change
    (((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)).symm :
        Mₙ n × Mₙ n →L[ℂ] WithLp 2 (Mₙ n × Mₙ n)).comp
      ((a.prodMap b).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)) :
          WithLp 2 (Mₙ n × Mₙ n) →L[ℂ] Mₙ n × Mₙ n))) X =
      WithLp.toLp 2 (a X.fst, b X.snd)
  cases X
  rfl

private noncomputable def twoBlockDiagRestrictedCfcEarly_hp62 {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (_hB₁ : Matrix.PosDef B₁) (_hB₂ : Matrix.PosDef B₂) :
    ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (hsBlockSpace n) := instHsBlockSpaceNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (hsBlockSpace n) := instHsBlockSpaceNormedSpace (n := n)
  letI : InnerProductSpace ℂ (hsBlockSpace n) := instHsBlockSpaceInnerProductSpace (n := n)
  letI : CompleteSpace (hsBlockSpace n) := instHsBlockSpaceCompleteSpace (n := n)
  exact (twoBlockDiagSubmoduleConjStarAlgEquiv n).symm
    (HansenPedersen.cfcR (ℋ := hsBlockSpace n) f
      (hsDiagMapCLM (jArg A₁ B₁) (jArg A₂ B₂)))

private theorem twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg_hp62 {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedCfcEarly_hp62 (f := f)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      hsDiagMapCLM (hsCfcR f (jArg A₁ B₁)) (hsCfcR f (jArg A₂ B₂)) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (hsBlockSpace n) := instHsBlockSpaceNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (hsBlockSpace n) := instHsBlockSpaceNormedSpace (n := n)
  letI : InnerProductSpace ℂ (hsBlockSpace n) := instHsBlockSpaceInnerProductSpace (n := n)
  letI : CompleteSpace (hsBlockSpace n) := instHsBlockSpaceCompleteSpace (n := n)
  have hJ₁ : IsSelfAdjoint (jArg A₁ B₁) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A₁) (B := B₁) hA₁ hB₁
  have hJ₂ : IsSelfAdjoint (jArg A₂ B₂) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A₂) (B := B₂) hA₂ hB₂
  simpa [twoBlockDiagRestrictedCfcEarly_hp62] using
    (cfcR_diagMapCLM_union (n := n) (g := f) hf_union hJ₁ hJ₂)

private theorem intrinsicTwoBlockDiagCfcEarly_hp62 {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ :
      Matrix.PosDef B₂)
    (hf_union : ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)))
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ((twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩ :
        twoBlockDiagSubmodule n) =
      ⟨twoBlockDiag ((hsCfcR f (jArg A₁ B₁)) X₁) ((hsCfcR f (jArg A₂ B₂)) X₂),
        twoBlockDiag_mem_submodule (n := n)
          ((hsCfcR f (jArg A₁ B₁)) X₁) ((hsCfcR f (jArg A₂ B₂)) X₂)⟩ := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairNormedAddCommGroup
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairNormedSpace'
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
    instWithLpMatrixPairInnerProductSpace'
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := instWithLpMatrixPairCompleteSpace'
  /- Step 1: Apply the conjugated CFC identity on the product space and read off the pair. -/
  have hmap := congrArg
    (fun T => T (WithLp.toLp 2 (X₁, X₂)))
    (twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg_hp62 (n := n) (f := f)
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hf_union hA₁ hA₂)
  have hpair :
      WithLp.ofLp
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) =
        ((hsCfcR f (jArg A₁ B₁)) X₁, (hsCfcR f (jArg A₂ B₂)) X₂) := by
    simpa [hsDiagMapCLM_apply_hp62] using congrArg (WithLp.ofLp (p := 2)) hmap
  /- Step 2: Extract the two block components and decode the raw block image. -/
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  have hdecode := congrArg (twoBlockDiagDecode n) hmap
  /- Step 3: Bridge the restricted-CFC value to its decoded product image via the isometry. -/
  have hbridge :
      ↑((twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩) =
        twoBlockDiagDecode n
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) := by
    let Y : twoBlockDiagSubmodule n :=
      (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩
    have hY : twoBlockDiagProj n (Y : Mₙ (2 * n)) = Y := by
      exact (mem_twoBlockDiagSubmodule_iff).mp Y.2
    have henc :
        (((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₁₁,
            ((reindexToBlockMatrix n) (Y : Mₙ (2 * n))).toBlocks₂₂) =
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))).ofLp := by
      have hsymm :
          (twoBlockDiagSubmoduleIsometry n).symm Y =
            ((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
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
              exact (congrArg (WithLp.ofLp (p := 2))
                (twoBlockDiagSubmoduleIsometry_symm_apply (n := n) Y)).symm
        _ = (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
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
                (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))).ofLp.1)
            ((((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))).ofLp.2) := by
        exact congrArg (fun p => twoBlockDiag p.1 p.2) henc
      _ = twoBlockDiagDecode n
            (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
                (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
              (WithLp.toLp 2 (X₁, X₂))) := by
        simp [twoBlockDiag]
  /- Step 4: Combine the bridge with the component identities to get the block-diagonal equality. -/
  apply Subtype.ext
  calc
    ↑((twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      ⟨twoBlockDiag X₁ X₂, twoBlockDiag_mem_submodule (n := n) X₁ X₂⟩)
      = twoBlockDiagDecode n
          (((twoBlockDiagSubmoduleConjStarAlgEquiv n)
              (twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
                (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
            (WithLp.toLp 2 (X₁, X₂))) := hbridge
    _ = twoBlockDiag ((hsCfcR f (jArg A₁ B₁)) X₁) ((hsCfcR f (jArg A₂ B₂)) X₂) := by
      simpa [twoBlockDiagDecode_apply, hfst, hsnd] using hdecode

private theorem blockSumMap_jOperator_twoBlockDiag_of_posDef {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    blockSumMap n
        (jOperator f (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) (twoBlockDiag X X)) =
      jOperator f A₁ B₁ X + jOperator f A₂ B₂ X := by
  simp only [blockSumMap_apply]
  change
    ((reindexToBlockMatrix n)
          ((ambientTwoBlockDiagJArgCfc (n := n) f
              (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
            (twoBlockDiag X X * twoBlockDiag B₁ B₂))).toBlocks₁₁ +
      ((reindexToBlockMatrix n)
          ((ambientTwoBlockDiagJArgCfc (n := n) f
              (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
            (twoBlockDiag X X * twoBlockDiag B₁ B₂))).toBlocks₂₂ =
    (hsCfcR f (jArg A₁ B₁)) (X * B₁) + (hsCfcR f (jArg A₂ B₂)) (X * B₂)
  rw [cfcJArg_eq_orthogonalConjDiag (n := n) (f := f)
    (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁.1 hA₂.1]
  rw [show twoBlockDiag X X * twoBlockDiag B₁ B₂ = twoBlockDiag (X * B₁) (X * B₂) by
    simpa using twoBlockDiag_mul X X B₁ B₂]
  have hf_union :
      ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)) := by
    apply hf.mono
    intro x hx
    rcases hx with hx | hx
    · exact spectrum_jArg_subset_Ioi_of_posDef hA₁ hB₁ hx
    · exact spectrum_jArg_subset_Ioi_of_posDef hA₂ hB₂ hx
  have hEarly :
      twoBlockDiagRestrictedCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
      twoBlockDiagRestrictedCfcEarly_hp62 (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ := by
    rfl
  have hdiag :
      (orthogonalConjDiagCfcOp (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        (twoBlockDiag (X * B₁) (X * B₂)) =
      twoBlockDiag ((hsCfcR f (jArg A₁ B₁)) (X * B₁))
        ((hsCfcR f (jArg A₂ B₂)) (X * B₂)) := by
    have happly :
        (orthogonalConjDiagCfcOp (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          (twoBlockDiag (X * B₁) (X * B₂)) =
        (((twoBlockDiagRestrictedCfc (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          ⟨twoBlockDiag (X * B₁) (X * B₂),
            twoBlockDiag_mem_submodule (n := n) (X * B₁) (X * B₂)⟩ :
            twoBlockDiagSubmodule n) : Mₙ (2 * n)) := by
      simpa [orthogonalConjDiagCfcOp] using
        twoBlockDiagOrthogonalConjDiag_apply_twoBlockDiagSubmodule_hp62
          (n := n)
          (u := twoBlockDiagRestrictedCfc (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          (v := offDiagRestrictedOrthCfc (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
          ⟨twoBlockDiag (X * B₁) (X * B₂),
            twoBlockDiag_mem_submodule (n := n) (X * B₁) (X * B₂)⟩
    rw [happly, hEarly]
    simpa using
      congrArg (fun Z : twoBlockDiagSubmodule n => (Z : Mₙ (2 * n)))
        (intrinsicTwoBlockDiagCfcEarly_hp62 (n := n) (f := f)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          (X₁ := X * B₁) (X₂ := X * B₂) hB₁ hB₂ hf_union hA₁.1 hA₂.1)
  rw [hdiag]
  simp [reindexToBlockMatrix_twoBlockDiag]

/-- Strict-output direct inequality implies joint concavity.
Source: Hiai, Theorem 6.2, output-nondegenerate condition (iii) implies condition (iv). -/
theorem QuasiEntropyDataProcessing.jointConcavity_of_strictDirectDPI (f : ℝ
  → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality f →
      QuasiEntropyDataProcessing.JointConcavity f := by
  intro hIII n A₁ A₂ B₁ B₂ X t ht0 ht1 hA₁ hA₂ hB₁ hB₂
  /- Step 1: Handle the boundary cases t = 0 and t = 1 collapsing to an endpoint. -/
  by_cases htEq0 : t = 0
  · subst htEq0
    have hA : (0 : ℝ) • A₁ + (1 - (0 : ℝ)) • A₂ = A₂ := by
      ext i j
      change (0 : ℂ) * A₁ i j + (((1 - (0 : ℝ)) : ℝ) : ℂ) * A₂ i j = A₂ i j
      norm_num
    have hB : (0 : ℝ) • B₁ + (1 - (0 : ℝ)) • B₂ = B₂ := by
      ext i j
      change (0 : ℂ) * B₁ i j + (((1 - (0 : ℝ)) : ℝ) : ℂ) * B₂ i j = B₂ i j
      norm_num
    rw [hA, hB]
    rw [sub_zero, zero_mul, one_mul, zero_add]
  by_cases htEq1 : t = 1
  · subst htEq1
    have hA : (1 : ℝ) • A₁ + (1 - (1 : ℝ)) • A₂ = A₁ := by
      ext i j
      change (1 : ℂ) * A₁ i j + (((1 - (1 : ℝ)) : ℝ) : ℂ) * A₂ i j = A₁ i j
      norm_num
    have hB : (1 : ℝ) • B₁ + (1 - (1 : ℝ)) • B₂ = B₁ := by
      ext i j
      change (1 : ℂ) * B₁ i j + (((1 - (1 : ℝ)) : ℝ) : ℂ) * B₂ i j = B₁ i j
      norm_num
    rw [hA, hB]
    rw [sub_self, zero_mul, one_mul, add_zero]
  /- Step 2: In the interior 0 < t < 1, build the block-diagonal interpolants A and B. -/
  have htPos : 0 < t := lt_of_le_of_ne ht0 (by
    intro h
    apply htEq0
    exact h.symm)
  have htLt1 : t < 1 := lt_of_le_of_ne ht1 (by simpa using htEq1)
  have h1tPos : 0 < 1 - t := sub_pos.mpr htLt1
  have hBt₁ : Matrix.PosDef (t • B₁) := matrixPosDef_smul hB₁ htPos
  have hBt₂ : Matrix.PosDef ((1 - t) • B₂) := matrixPosDef_smul hB₂ h1tPos
  let A : Mₙ (2 * n) := twoBlockDiag (t • A₁) ((1 - t) • A₂)
  let B : Mₙ (2 * n) := twoBlockDiag (t • B₁) ((1 - t) • B₂)
  have hA : Matrix.PosDef A := by
    dsimp [A]
    exact twoBlockDiag_posDef (matrixPosDef_smul hA₁ htPos) (matrixPosDef_smul hA₂ h1tPos)
  have hB : Matrix.PosDef B := by
    dsimp [B]
    exact twoBlockDiag_posDef (matrixPosDef_smul hB₁ htPos) (matrixPosDef_smul hB₂ h1tPos)
  /- Step 3: Apply the output-nondegenerate direct inequality to the block-sum map. -/
  have hle :=
    hIII (blockSumMap n) (A := A) (B := B)
      (blockSumMap_positive n) (blockSumMap_tracePreserving n) (blockSumMap_hsAdjointSchwarz n)
      hA hB (blockSumMap_one_posDef n)
  have hXraw := hsQForm_le_of_le hle X
  dsimp [A, B] at hXraw
  have hX := by
    simpa only [reindexToBlockMatrix_twoBlockDiag] using hXraw
  let Y : Mₙ (2 * n) :=
    (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
      (twoBlockDiag (t • B₁) ((1 - t) • B₂)) (twoBlockDiag X X))
  /- Step 4: Identify the block-sum image as the sum of the two endpoint quasi-entropy forms. -/
  have hblock :
      blockSumMap n Y =
        jOperator f (t • A₁) (t • B₁) X +
          jOperator f ((1 - t) • A₂) ((1 - t) • B₂) X := by
    simpa [Y] using
      (blockSumMap_jOperator_twoBlockDiag_of_posDef (n := n) (f := f)
        hf
        (A₁ := t • A₁) (A₂ := (1 - t) • A₂) (B₁ := t • B₁) (B₂ := (1 - t)
          • B₂)
        (X := X)
        hBt₁ hBt₂
        (matrixPosDef_smul hA₁ htPos) (matrixPosDef_smul hA₂ h1tPos))
  have hsrc :
      Complex.re (Matrix.trace (Matrix.conjTranspose X * blockSumMap n Y)) =
        quasiEntropy f (t • A₁) (t • B₁) X + quasiEntropy f ((1 - t) • A₂) ((1 - t)
          • B₂) X := by
    rw [hblock]
    simp [quasiEntropy, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have hblockDiagX : blockDiagMap n X = twoBlockDiag X X := by
    simp [blockDiagMap_apply]
  have hinnerY :
      (ContinuousLinearMap.comp
          (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
            (twoBlockDiag (t • B₁) ((1 - t) • B₂)))
          (blockDiagMap n)) X = Y := by
    rw [ContinuousLinearMap.comp_apply]
    change
      (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
          (twoBlockDiag (t • B₁) ((1 - t) • B₂))) ((blockDiagMap n) X) =
        (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
          (twoBlockDiag (t • B₁) ((1 - t) • B₂))) (twoBlockDiag X X)
    simp [hblockDiagX]
  have hcompY :
      (ContinuousLinearMap.comp (blockSumMap n)
          (ContinuousLinearMap.comp
            (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
              (twoBlockDiag (t • B₁) ((1 - t) • B₂)))
            (blockDiagMap n))) X =
        blockSumMap n Y := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (blockSumMap n) hinnerY
  /- Step 5: Rephrase the operator inequality as the trace-form bound for the mixed operator. -/
  have hX' :
      Complex.re (Matrix.trace (Matrix.conjTranspose X * blockSumMap n Y)) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (jOperator f (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X)))
                := by
    have htraceY :
        Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((ContinuousLinearMap.comp (blockSumMap n)
                    (ContinuousLinearMap.comp
                      (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
                        (twoBlockDiag (t • B₁) ((1 - t) • B₂)))
                (blockDiagMap n))) X))) =
          Complex.re (Matrix.trace (Matrix.conjTranspose X * blockSumMap n Y)) := by
      rw [hcompY]
    calc
      Complex.re (Matrix.trace (Matrix.conjTranspose X * blockSumMap n Y))
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((ContinuousLinearMap.comp (blockSumMap n)
                    (ContinuousLinearMap.comp
                      (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
                        (twoBlockDiag (t • B₁) ((1 - t) • B₂)))
                      (blockDiagMap n))) X))) := htraceY.symm
      _ ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (jOperator f (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X)))
                := by
            have hnonneg' :
                0 ≤
                  Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X *
                        (jOperator f (t • A₁ + (1 - t) • A₂)
                          (t • B₁ + (1 - t) • B₂) X))) -
                  Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X *
                        ((ContinuousLinearMap.comp (blockSumMap n)
                            (ContinuousLinearMap.comp
                              (jOperator f (twoBlockDiag (t • A₁) ((1 - t) • A₂))
                                (twoBlockDiag (t • B₁) ((1 - t) • B₂)))
                              (blockDiagMap n))) X))) := by
              exact sub_nonneg.mpr hX
            exact sub_nonneg.mp hnonneg'
  /- Step 6: Substitute the sum form and apply homogeneity to conclude joint concavity. -/
  rw [hsrc] at hX'
  rw [quasiEntropy_homogeneous (f := f) (A := A₁) (B := B₁) (X := X) htPos,
    quasiEntropy_homogeneous (f := f) (A := A₂) (B := B₂) (X := X) h1tPos] at hX'
  simpa [quasiEntropy] using hX'


end MatrixScopedInstances

end HiaiPetz
