/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.OrthogonalTransport.OrthogonalTransportAlgebra
import Quantum.TraceInequality.HiaiPetz.Ambient.OrthogonalTransport.OrthogonalTransportStarAlgHom
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagHilbertSpace
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagRestrictedFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagPositivity
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.RestrictedContinuity
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagEquiv
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
# CFC equality layer for orthogonal transport

This module contains the final CFC transport equalities after the algebra and
star-algebra hom layers have been isolated.

## Main results

* `ambientTwoBlockDiagJArgCfc_eq_orthogonalTransportCfcImage_core`: the ambient
  two-block `J`-argument CFC agrees with the orthogonal transport CFC image.
* `orthogonalTransportCfcImage_eq_orthogonalConjDiagCfcOp_core`: the transport
  image agrees with the block diagonal CFC operator in the orthogonal
  decomposition.

## References

* Hiai, CFC transport step in the off-diagonal block decomposition of
  the `J`-operator.
-/

namespace HiaiPetz

open HiaiPetz.AmbientInstances

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroupBase
  instTwoBlockDiagOrthogonalPairSpaceNormedSpaceBase
  instTwoBlockDiagOrthogonalPairSpaceInnerProductSpaceBase
  instTwoBlockDiagOrthogonalPairSpaceCompleteSpaceBase
  instWithLpMatrixPairNormedAddCommGroup
  instWithLpMatrixPairNormedSpace'
  instWithLpMatrixPairInnerProductSpace'
  instWithLpMatrixPairCompleteSpace'

noncomputable section MatrixScopedInstances


-- The transported `jArg` equality still leaves a heavy residual kernel after helper splitting.
private theorem twoBlockDiagOrthogonalTransport_jArg_eq {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    let t₁ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)
    let t₂ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)
    twoBlockDiagOrthogonalTransportStarAlgHom n (t₁, t₂) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) := by
  intro K t₁ t₂
  have hE₁t : (twoBlockDiagSubmoduleConjStarAlgEquiv n).symm t₁ =
      twoBlockDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ :=
    (congrArg ((twoBlockDiagSubmoduleConjStarAlgEquiv n).symm)
      (twoBlockDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)).symm.trans
      ((twoBlockDiagSubmoduleConjStarAlgEquiv n).symm_apply_apply _)
  have hOff : (offDiagSubmoduleConjStarAlgEquiv n).symm t₂ =
      offDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ :=
    (congrArg ((offDiagSubmoduleConjStarAlgEquiv n).symm)
      (offDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)).symm.trans
      ((offDiagSubmoduleConjStarAlgEquiv n).symm_apply_apply _)
  have hblock :
      twoBlockDiagOrthogonalBlockProdStarAlgHom n (t₁, t₂) =
        (twoBlockDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂,
          offDiagRestrictedJArgOrth (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
            hB₁ hB₂) :=
    Prod.ext hE₁t (congrArg (twoBlockDiagOrthogonalOffDiagConjStarAlgEquiv n) hOff)
  change twoBlockDiagOrthogonalConjStarAlgHom n
      (twoBlockDiagOrthogonalDiagStarAlgHom n
        (twoBlockDiagOrthogonalBlockProdStarAlgHom n (t₁, t₂))) = _
  rw [hblock]
  exact (twoBlockDiagOrthogonalConjStarAlgHom_apply (n := n)
      (T := HansenPedersen.Internal.diagMapCLM
        (twoBlockDiagRestrictedJArg (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
        (offDiagRestrictedJArgOrth (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          hB₁ hB₂))).trans
    (jArg_eq_orthogonalConjDiag (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)

private theorem twoBlockDiagOrthogonalTransport_cfcJArgWithLpPair_eq {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    twoBlockDiagOrthogonalTransportStarAlgHom n
        (cfcJArgWithLpMatrixPair (n := n) A₁ A₂ B₁ B₂) =
      jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) := by
  simpa [cfcJArgWithLpMatrixPair, cfcJArgWithLpMatrixPairFst, cfcJArgWithLpMatrixPairSnd] using
    twoBlockDiagOrthogonalTransport_jArg_eq
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

-- CFC transport across the left restricted block unfolds several equivalence layers.
private theorem twoBlockDiagOrthogonalTransport_left_cfc_eq {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    let t₁ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)
    let E₁ :
        (K →L[ℂ] K) ≃⋆ₐ[ℂ]
          (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) :=
      (twoBlockDiagSubmoduleConjStarAlgEquiv n).symm
    E₁ (HansenPedersen.cfcR (ℋ := K) f t₁) =
      twoBlockDiagRestrictedCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ := by
  intro K t₁ E₁
  exact
    (congrArg ((twoBlockDiagSubmoduleConjStarAlgEquiv n).symm)
      (twoBlockDiagSubmoduleIsometry_cfcRestrictedJArg (n := n) (f := f)
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
        (continuousOn_twoBlockDiagRestrictedJArgL_of_selfAdjoint
          (n := n) (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          hB₁ hB₂ hA₁ hA₂) hA₁ hA₂)).symm.trans
      ((twoBlockDiagSubmoduleConjStarAlgEquiv n).symm_apply_apply _)

-- CFC transport across the right restricted block unfolds several equivalence layers.
private theorem twoBlockDiagOrthogonalTransport_right_cfc_eq {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    let t₂ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)
    let E₂ :
        (K →L[ℂ] K) ≃⋆ₐ[ℂ]
          (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
      ((offDiagSubmoduleConjStarAlgEquiv n).symm).trans
        (twoBlockDiagOrthogonalOffDiagConjStarAlgEquiv n)
    E₂ (HansenPedersen.cfcR (ℋ := K) f t₂) =
      offDiagRestrictedOrthCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ := by
  intro K t₂ E₂
  have hOff :
      ((offDiagSubmoduleConjStarAlgEquiv n).symm)
          (HansenPedersen.cfcR (ℋ := K) f t₂) =
        offDiagRestrictedCfc (n := n) f
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ :=
    (congrArg ((offDiagSubmoduleConjStarAlgEquiv n).symm)
      (offDiagSubmoduleIsometry_cfcRestrictedJArg (n := n) (f := f)
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
        (continuousOn_offDiagRestrictedJArgL_of_selfAdjoint
          (n := n) (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
          hB₁ hB₂ hA₁ hA₂) hA₁ hA₂)).symm.trans
      ((offDiagSubmoduleConjStarAlgEquiv n).symm_apply_apply _)
  exact congrArg (twoBlockDiagOrthogonalOffDiagConjStarAlgEquiv n) hOff

-- The transported `cfc` equality elaborates through two restricted branches at once.
private theorem twoBlockDiagOrthogonalTransport_cfc_eq {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    let t₁ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)
    let t₂ : K →L[ℂ] K := matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)
    twoBlockDiagOrthogonalTransportStarAlgHom n
      (HansenPedersen.cfcR (ℋ := K) f t₁, HansenPedersen.cfcR (ℋ := K) f t₂) =
      orthogonalConjDiagCfcOp (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ := by
  intro K t₁ t₂
  have hblock :
      twoBlockDiagOrthogonalBlockProdStarAlgHom n
          (HansenPedersen.cfcR (ℋ := K) f t₁, HansenPedersen.cfcR (ℋ := K) f t₂) =
        (twoBlockDiagRestrictedCfc (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂,
          offDiagRestrictedOrthCfc (n := n) f
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) :=
    Prod.ext
      (twoBlockDiagOrthogonalTransport_left_cfc_eq
        (n := n) (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂)
      (twoBlockDiagOrthogonalTransport_right_cfc_eq
        (n := n) (f := f) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂)
  change twoBlockDiagOrthogonalConjStarAlgHom n
      (twoBlockDiagOrthogonalDiagStarAlgHom n
        (twoBlockDiagOrthogonalBlockProdStarAlgHom n
          (HansenPedersen.cfcR (ℋ := K) f t₁, HansenPedersen.cfcR (ℋ := K) f t₂))) = _
  rw [hblock]
  exact twoBlockDiagOrthogonalConjStarAlgHom_apply (n := n)
    (T := HansenPedersen.Internal.diagMapCLM
      (twoBlockDiagRestrictedCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      (offDiagRestrictedOrthCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))

-- The CFC argument pair is kept as a separate declaration to stabilize elaboration.
private noncomputable def cfcJArgWithLpMatrixPair_cfc_arg (n : ℕ)
    (A₁ A₂ B₁ B₂ : Mₙ n) :
    ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
  (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂,
    cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂)

/- Instance caches: the CFC transport bridge below rebuilds the same deep
instance stack (`CStarAlgebra`/`ContinuousFunctionalCalculus` on the
`WithLp`-pair operator algebra, its product, and `HSOp (2 * n)`) inside every
`have` block. Section-level reducible
local instances turn each search into a head-match; in-proof `letI` bindings
keep precedence, so elaborated statements are unchanged where they exist. -/

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the C-star algebra structure on endomorphisms of
the `WithLp` matrix-pair model. -/
@[reducible, local instance]
private noncomputable def instCStarAlgebraWithLpPairCLMScoped {n : ℕ} :
    CStarAlgebra ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (WithLp 2 (Mₙ n × Mₙ n))
    inferInstance inferInstance inferInstance

-- The CFC cache construction still performs one deep instance search.
/-- Local reducible cache for the real CFC on `WithLp` matrix-pair
endomorphisms. -/
@[reducible, local instance]
private noncomputable def instCFCRealWithLpPairCLMScoped {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- The complex CFC cache uses the same transported operator-algebra stack.
/-- Local reducible cache for the complex CFC on `WithLp` matrix-pair
endomorphisms. -/
@[reducible, local instance]
private noncomputable def instCFCComplexWithLpPairCLMScoped {n : ℕ} :
    ContinuousFunctionalCalculus ℂ
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

-- The product CFC cache combines two already-heavy endomorphism searches.
/-- Local reducible cache for the real CFC on pairs of `WithLp` matrix-pair
endomorphisms. -/
@[reducible, local instance]
private noncomputable def instCFCRealWithLpPairCLMProdScoped {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- HS operator CFC inference is cached here to avoid repeated downstream search.
/-- Local reducible cache for the real CFC on Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instCFCRealHSOpTransportScoped {m : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp m) IsSelfAdjoint :=
  inferInstance

-- The complex HS CFC cache has the same one-time instance-search cost.
/-- Local reducible cache for the complex CFC on Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instCFCComplexHSOpTransportScoped {m : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp m) IsStarNormal :=
  inferInstance

-- The real-algebra cache prevents repeated coercion searches in CFC lemmas.
/-- Local reducible real algebra cache for `WithLp` matrix-pair endomorphisms. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealWithLpPairCLMOrthScoped {n : ℕ} :
    Algebra ℝ ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
  NormedAlgebra.complexToReal.toAlgebra

-- HS real-algebra inference is cached once for the transport bridge.
/-- Local reducible real algebra cache for Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpTransportScoped {m : ℕ} :
    Algebra ℝ (HSOp m) :=
  inferInstance

private theorem twoBlockDiagOrthogonalTransport_cfc_arg_eq_jArg
    (n : ℕ)
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
    letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
    letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
    letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
    letI : CStarAlgebra (K →L[ℂ] K) :=
      @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace K inferInstance inferInstance
        inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℝ ((K →L[ℂ] K) × (K →L[ℂ] K)) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    let Ψ : ((K →L[ℂ] K) × (K →L[ℂ] K)) →⋆ₐ[ℂ] HSOp (2 * n) :=
      twoBlockDiagOrthogonalTransportStarAlgHom n
    let t := cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂
    Ψ t = jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) := by
  intros
  exact twoBlockDiagOrthogonalTransport_cfcJArgWithLpPair_eq
    (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂

/-- Self-adjointness and spectral-continuity bundle for the `WithLp`-pair CFC
argument, factored out of the transport bridge so that each piece elaborates
within the default heartbeat budget. -/
private theorem cfcJArgWithLpMatrixPair_phaseBundle_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    (IsSelfAdjoint (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂) ∧
        ContinuousOn f
          (spectrum ℝ (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂))) ∧
      (IsSelfAdjoint (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂) ∧
        IsSelfAdjoint (cfcJArgWithLpMatrixPairSnd A₁ A₂ B₁ B₂)) := by
  have hsa₁ := cfcJArgWithLpMatrixPairFst_isSelfAdjoint hB₁ hB₂ hA₁ hA₂
  have hsa₂ := cfcJArgWithLpMatrixPairSnd_isSelfAdjoint hB₁ hB₂ hA₁ hA₂
  refine ⟨⟨cfcJArgWithLpMatrixPair_isSelfAdjoint hB₁ hB₂ hA₁ hA₂, ?_⟩, hsa₁, hsa₂⟩
  have hfin := (finite_real_spectrum_of_selfAdjoint (K := WithLp 2 (Mₙ n × Mₙ n)) hsa₁).union
    (finite_real_spectrum_of_selfAdjoint (K := WithLp 2 (Mₙ n × Mₙ n)) hsa₂)
  rw [cfcJArgWithLpMatrixPair_cfc_arg, Prod.spectrum_eq]
  exact hfin.continuousOn f

/-- First half of the transport bridge: the ambient two-block CFC equals the
CFC of the transported argument. Factored out of the bridge so that it
elaborates within the default heartbeat budget. -/
private theorem ambientTwoBlockDiagJArgCfc_eq_cfc_transport_hMapBlock
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ambientTwoBlockDiagJArgCfc (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
    cfc f
      ((twoBlockDiagOrthogonalTransportStarAlgHom n)
        (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)) := by
  let K := WithLp 2 (Mₙ n × Mₙ n)
  let EndK := K →L[ℂ] K
  let EndPair := EndK × EndK
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  let t := cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂
  letI : CStarAlgebra EndK := instCStarAlgebraWithLpPairCLMScoped
  letI : ContinuousFunctionalCalculus ℂ EndK IsStarNormal := instCFCComplexWithLpPairCLMScoped
  letI : ContinuousFunctionalCalculus ℝ EndK IsSelfAdjoint := instCFCRealWithLpPairCLMScoped
  letI : ContinuousFunctionalCalculus ℝ EndPair IsSelfAdjoint :=
    instCFCRealWithLpPairCLMProdScoped
  letI : ContinuousFunctionalCalculus ℝ (HSOp (2 * n)) IsSelfAdjoint :=
    instCFCRealHSOpTransportScoped
  letI : ContinuousFunctionalCalculus ℂ (HSOp (2 * n)) IsStarNormal :=
    instCFCComplexHSOpTransportScoped
  let Ψ : EndPair →⋆ₐ[ℂ] HSOp (2 * n) :=
    twoBlockDiagOrthogonalTransportStarAlgHom n
  let A := twoBlockDiag A₁ A₂
  let B := twoBlockDiag B₁ B₂
  have hΨt0 : Ψ t = jArg A B := by
    simpa [t, Ψ, A, B] using
      twoBlockDiagOrthogonalTransport_cfc_arg_eq_jArg (n := n)
        hB₁ hB₂
  exact (congrArg (hsCfcR f) hΨt0).symm

/-- Continuity of the orthogonal-transport star-algebra hom (finite-dimensional
domain); kept separate so that the `map_cfc` steps below stay light. -/
private theorem continuous_twoBlockDiagOrthogonalTransportStarAlgHom (n : ℕ) :
    Continuous (twoBlockDiagOrthogonalTransportStarAlgHom n) :=
  LinearMap.continuous_of_finiteDimensional
    (twoBlockDiagOrthogonalTransportStarAlgHom n).toAlgHom.toLinearMap

/-- CFC commutes with the orthogonal-transport star-algebra hom on the
`WithLp`-pair CFC argument. Factored out of the transport bridge so that the
heavy `map_cfc` elaboration runs in its own declaration. -/
private theorem cfc_transport_starAlgHom_comm_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    cfc f
        ((twoBlockDiagOrthogonalTransportStarAlgHom n)
          (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)) =
      (twoBlockDiagOrthogonalTransportStarAlgHom n)
        (cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)) := by
  have hP := cfcJArgWithLpMatrixPair_phaseBundle_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂
  have hTwoA : IsSelfAdjoint (twoBlockDiag A₁ A₂) :=
    (conjTranspose_twoBlockDiag A₁ A₂).trans (congrArg₂ twoBlockDiag hA₁.star_eq hA₂.star_eq)
  have hsaJ0 : IsSelfAdjoint (jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)) :=
    jArg_isSelfAdjoint hTwoA (twoBlockDiag_posDef hB₁ hB₂)
  have hΨt0 :
      (twoBlockDiagOrthogonalTransportStarAlgHom n)
          (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂) =
        jArg (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂) :=
    twoBlockDiagOrthogonalTransport_cfcJArgWithLpPair_eq hB₁ hB₂
  exact ((twoBlockDiagOrthogonalTransportStarAlgHom n).map_cfc f _ hP.1.2
    (continuous_twoBlockDiagOrthogonalTransportStarAlgHom n) hP.1.1 (hΨt0 ▸ hsaJ0)).symm

/-- First component of the CFC splitting on the `WithLp`-pair CFC argument
(one `map_cfc` per declaration to stay within the default heartbeat budget). -/
private theorem cfc_cfcJArgWithLpMatrixPair_fst_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    (cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)).1 =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂) := by
  have hP := cfcJArgWithLpMatrixPair_phaseBundle_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂
  exact (StarAlgHom.fst ℂ _ _).map_cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)
    hP.1.2 continuous_fst hP.1.1 hP.2.1

/-- Second component of the CFC splitting on the `WithLp`-pair CFC argument
(one `map_cfc` per declaration to stay within the default heartbeat budget). -/
private theorem cfc_cfcJArgWithLpMatrixPair_snd_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    (cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)).2 =
      HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
        (cfcJArgWithLpMatrixPairSnd A₁ A₂ B₁ B₂) := by
  have hP := cfcJArgWithLpMatrixPair_phaseBundle_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂
  exact (StarAlgHom.snd ℂ _ _).map_cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)
    hP.1.2 continuous_snd hP.1.1 hP.2.2

/-- Componentwise CFC splitting on the `WithLp`-pair CFC argument, assembled
from the component lemmas above. -/
private theorem cfc_cfcJArgWithLpMatrixPair_prod_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    cfc f (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂) =
      (HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂),
        HansenPedersen.cfcR (ℋ := WithLp 2 (Mₙ n × Mₙ n)) f
          (cfcJArgWithLpMatrixPairSnd A₁ A₂ B₁ B₂)) := by
  exact Prod.ext
    (cfc_cfcJArgWithLpMatrixPair_fst_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂)
    (cfc_cfcJArgWithLpMatrixPair_snd_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂)

/-- Second half of the transport bridge: the CFC of the transported argument
equals the orthogonal-transport CFC image. Assembled from
`cfc_transport_starAlgHom_comm_hMain` and
`cfc_cfcJArgWithLpMatrixPair_prod_hMain`. -/
private theorem cfc_transport_eq_orthogonalTransportCfcImage_hTransportBlock
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    cfc f
        ((twoBlockDiagOrthogonalTransportStarAlgHom n)
          (cfcJArgWithLpMatrixPair_cfc_arg (n := n) A₁ A₂ B₁ B₂)) =
      orthogonalTransportCfcImage (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) :=
  (cfc_transport_starAlgHom_comm_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂).trans
    (congrArg (twoBlockDiagOrthogonalTransportStarAlgHom n)
      (cfc_cfcJArgWithLpMatrixPair_prod_hMain n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂))

-- The main CFC transport bridge combines star-hom CFC transport and product CFC splitting.
private theorem ambientTwoBlockDiagJArgCfc_eq_orthogonalTransportCfcImage_core_hMain
    (n : ℕ) (f : ℝ → ℝ)
    (A₁ A₂ B₁ B₂ : Mₙ n)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ambientTwoBlockDiagJArgCfc (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
    orthogonalTransportCfcImage (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) := by
  exact
    (ambientTwoBlockDiagJArgCfc_eq_cfc_transport_hMapBlock
      n f A₁ A₂ B₁ B₂ hB₁ hB₂).trans
      (cfc_transport_eq_orthogonalTransportCfcImage_hTransportBlock
        n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂)
/-- The ambient CFC of the two-block `J` argument equals the CFC image obtained
by orthogonal transport to the diagonal/off-diagonal decomposition. -/
theorem ambientTwoBlockDiagJArgCfc_eq_orthogonalTransportCfcImage_core
    (n : ℕ) (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ambientTwoBlockDiagJArgCfc (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
    orthogonalTransportCfcImage (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) := by
  exact ambientTwoBlockDiagJArgCfc_eq_orthogonalTransportCfcImage_core_hMain
    n f A₁ A₂ B₁ B₂ hB₁ hB₂ hA₁ hA₂

/-- The orthogonal transport CFC image is the conjugated block diagonal CFC
operator on the orthogonal decomposition. -/
theorem orthogonalTransportCfcImage_eq_orthogonalConjDiagCfcOp_core
    (n : ℕ) (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    orthogonalTransportCfcImage (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) =
    orthogonalConjDiagCfcOp (n := n) f
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ :=
  twoBlockDiagOrthogonalTransport_cfc_eq
    hB₁ hB₂ hA₁ hA₂

end MatrixScopedInstances

end HiaiPetz
