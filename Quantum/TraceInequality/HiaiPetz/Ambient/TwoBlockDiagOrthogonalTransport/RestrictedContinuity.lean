/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagRestrictedFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
Restricted-spectrum continuity helpers for the two-block orthogonal transport.

These lemmas isolate the finite-spectrum continuity proof used by the heavier
orthogonal CFC transport bridge.
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

-- The restricted CFC spectrum proof synthesizes a large CStarAlgebra instance bundle.
-- The proof uses finite-spectrum continuity after unfolding the restricted left block.
/-- For self-adjoint blocks `A₁, A₂` and positive-definite `B₁, B₂`, every real function `f`
is continuous on the real spectrum of the left restricted `J`-argument block
`twoBlockDiagRestrictedJArgL`.  The operator is self-adjoint on the finite-dimensional two-block
diagonal submodule, so its real spectrum is finite and continuity on it is automatic. -/
@[fun_prop] theorem continuousOn_twoBlockDiagRestrictedJArgL_of_selfAdjoint {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (_hA₁ : IsSelfAdjoint A₁) (_hA₂ : IsSelfAdjoint A₂) :
    ContinuousOn f
      (spectrum ℝ
        (twoBlockDiagRestrictedJArgL (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
  letI : NormedAddCommGroup ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  letI : FiniteDimensional ℂ ↥(twoBlockDiagSubmodule n) := by infer_instance
  letI : Semiring (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) := by
    infer_instance
  letI : Ring (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) := by
    infer_instance
  letI : NormedRing (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    ContinuousLinearMap.toNormedRing
  letI : Star (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) := by
    infer_instance
  letI : StarRing (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) := by
    infer_instance
  letI : Algebra ℂ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) := by
    infer_instance
  letI : NormedAlgebra ℂ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    ContinuousLinearMap.toNormedAlgebra
  letI : IsScalarTower ℂ ℂ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : SMul ℝ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    NormedAlgebra.complexToReal.toSMul
  letI : Algebra ℝ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    NormedAlgebra.complexToReal.toAlgebra
  letI : NormedAlgebra ℝ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    NormedAlgebra.complexToReal
  letI : IsScalarTower ℝ ℂ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : CStarAlgebra (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
      ↥(twoBlockDiagSubmodule n) inferInstance inferInstance
      (instTwoBlockDiagSubtypeCompleteSpace (n := n))
  letI : ContinuousFunctionalCalculus ℂ
      (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hfin :=
    @finite_real_spectrum_of_selfAdjoint
      ↥(twoBlockDiagSubmodule n)
      inferInstance
      inferInstance
      (instTwoBlockDiagSubtypeCompleteSpace (n := n))
      inferInstance
      (IsStarNormal.instContinuousFunctionalCalculus
        (A := ↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)))
      (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      (twoBlockDiagRestrictedJArg_isSelfAdjoint (n := n) _hA₁ _hA₂ hB₁ hB₂)
  simpa [twoBlockDiagRestrictedJArgL] using hfin.continuousOn f

-- The restricted CFC spectrum proof synthesizes a large CStarAlgebra instance bundle.
-- The proof uses finite-spectrum continuity after unfolding the restricted right block.
/-- For self-adjoint blocks `A₁, A₂` and positive-definite `B₁, B₂`, every real function `f`
is continuous on the real spectrum of the off-diagonal restricted `J`-argument block
`offDiagRestrictedJArgL`.  The operator is self-adjoint on the finite-dimensional off-diagonal
submodule, so its real spectrum is finite and continuity on it is automatic. -/
@[fun_prop] theorem continuousOn_offDiagRestrictedJArgL_of_selfAdjoint {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (_hA₁ : IsSelfAdjoint A₁) (_hA₂ : IsSelfAdjoint A₂) :
    ContinuousOn f
      (spectrum ℝ
        (offDiagRestrictedJArgL (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
  letI : NormedAddCommGroup ↥(offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : FiniteDimensional ℂ ↥(offDiagSubmodule n) := by infer_instance
  letI : Semiring (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) := by
    infer_instance
  letI : Ring (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) := by
    infer_instance
  letI : NormedRing (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    ContinuousLinearMap.toNormedRing
  letI : Star (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) := by
    infer_instance
  letI : StarRing (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) := by
    infer_instance
  letI : Algebra ℂ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) := by
    infer_instance
  letI : NormedAlgebra ℂ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    ContinuousLinearMap.toNormedAlgebra
  letI : IsScalarTower ℂ ℂ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : SMul ℝ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    NormedAlgebra.complexToReal.toSMul
  letI : Algebra ℝ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    NormedAlgebra.complexToReal.toAlgebra
  letI : NormedAlgebra ℝ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    NormedAlgebra.complexToReal
  letI : IsScalarTower ℝ ℂ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : CStarAlgebra (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
      ↥(offDiagSubmodule n) inferInstance inferInstance
      (instOffDiagSubtypeCompleteSpace (n := n))
  letI : ContinuousFunctionalCalculus ℂ
      (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hfin :=
    @finite_real_spectrum_of_selfAdjoint
      ↥(offDiagSubmodule n)
      inferInstance
      inferInstance
      (instOffDiagSubtypeCompleteSpace (n := n))
      inferInstance
      (IsStarNormal.instContinuousFunctionalCalculus
        (A := ↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)))
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)
      (offDiagRestrictedJArg_isSelfAdjoint (n := n) _hA₁ _hA₂ hB₁ hB₂)
  simpa [offDiagRestrictedJArgL] using hfin.continuousOn f

end MatrixScopedInstances

end HiaiPetz
