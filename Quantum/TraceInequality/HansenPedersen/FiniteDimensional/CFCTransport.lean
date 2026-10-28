/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Instances
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.MatrixModel
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.MatrixModel
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.CFCTransport

/-!
# Functional-calculus transport for block extensions

This module transports complex normal functional calculus across the diagonal
block map and the orthogonal decomposition of a closed submodule.  It provides
the block-extension models and monotonicity transport used by the
finite-dimensional approximation layer.

## Main results

* `cfcNormal_diagMapCLM_union`: complex CFC of a diagonal block is diagonal CFC.
* `blockExtensionConjDiag` and `blockExtensionDiag`: two equivalent models of
  the block extension `P A P + t₀ (1 - P)`.
* `blockExtensionDiag_cfc_mono_from_subtype`: CFC monotonicity for compressed
  submodule operators lifts to the ambient block extensions.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology MatrixOrder CStarAlgebra
open Filter
open HansenPedersen.Internal

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

-- simplified facade still reuses the heavy block CFC transport elaboration path
omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Simplified facade for `cfcNormal_blockExtensionDiag_eq_blockConjDiagMap`,
expanding the right-hand side as a `blockConjDiagMap`. -/
theorem cfcNormal_blockExtensionDiag_eq_blockConjDiagMap_simple
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    {g : ℂ → ℂ} (X : L ℋ) (t₀ : ℝ)
    (hXcont :
      ContinuousOn g
        (spectrum ℂ (U.orthogonalProjection ∘L X ∘L U.subtypeL) ∪
          spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))))
    (hXnorm : IsStarNormal (U.orthogonalProjection ∘L X ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) X t₀) =
      blockConjDiagMap (U := U)
        (a := cfc (R := ℂ) g (U.orthogonalProjection ∘L X ∘L U.subtypeL))
        (b := cfc (R := ℂ) g (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))) := by
  simpa [blockExtensionConjDiagCfc, blockConjDiagMap] using
    (cfcNormal_blockExtensionDiag_eq_blockConjDiagMap
      (U := U) (g := g) (X := X) t₀ hXcont hXnorm)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- If the complex CFC comparison holds after compressing `A` and `B` to
`U`, then the same comparison holds for the ambient block extensions with
scalar complement `t₀`. -/
theorem blockExtensionDiag_cfc_mono_from_subtype
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    {g : ℂ → ℂ} {A B : L ℋ} {t₀ : ℝ}
    (hAcont :
      ContinuousOn g
        (spectrum ℂ (U.orthogonalProjection ∘L A ∘L U.subtypeL) ∪
          spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))))
    (hBcont :
      ContinuousOn g
        (spectrum ℂ (U.orthogonalProjection ∘L B ∘L U.subtypeL) ∪
          spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))))
    (hA_norm : IsStarNormal (U.orthogonalProjection ∘L A ∘L U.subtypeL))
    (hB_norm : IsStarNormal (U.orthogonalProjection ∘L B ∘L U.subtypeL))
    (hsub_fcC :
      cfc (R := ℂ) g (U.orthogonalProjection ∘L A ∘L U.subtypeL) ≤
        cfc (R := ℂ) g (U.orthogonalProjection ∘L B ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) A t₀) ≤
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) B t₀) := by
  let cU : Uᗮ →L[ℂ] Uᗮ := (t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)
  have hCA_base :
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) A t₀) =
        blockConjDiagMap (U := U)
          (a := cfc (R := ℂ) g (U.orthogonalProjection ∘L A ∘L U.subtypeL))
          (b := cfc (R := ℂ) g cU) := by
    simpa [cU] using
      (cfcNormal_blockExtensionDiag_eq_blockConjDiagMap_simple
        (U := U) (g := g) (X := A) t₀ hAcont hA_norm)
  have hCB_base :
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) B t₀) =
        blockConjDiagMap (U := U)
          (a := cfc (R := ℂ) g (U.orthogonalProjection ∘L B ∘L U.subtypeL))
          (b := cfc (R := ℂ) g cU) := by
    simpa [cU] using
      (cfcNormal_blockExtensionDiag_eq_blockConjDiagMap_simple
        (U := U) (g := g) (X := B) t₀ hBcont hB_norm)
  rw [hCA_base, hCB_base]
  exact
    blockConjDiagMap_mono
      (U := U)
      (a1 := cfc (R := ℂ) g (U.orthogonalProjection ∘L A ∘L U.subtypeL))
      (a2 := cfc (R := ℂ) g (U.orthogonalProjection ∘L B ∘L U.subtypeL))
      (b := cfc (R := ℂ) g cU)
      hsub_fcC

end NormalCFC514

end HansenPedersen
