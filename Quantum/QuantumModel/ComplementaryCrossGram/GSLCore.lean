/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Joint-operator reindexing

`jointOperatorReindex` transports operators on the tensor system to the Hilbert tensor
product; on elementary tensors it agrees with `tensorOperator`
(`jointOperatorReindex_operatorTensorEquiv_tmul`).
-/

noncomputable section

open QuantumState
open scoped TensorProduct

namespace QuantumModel

open CategoryTheory
open scoped MonoidalCategory

/-- Pull a categorical tensor-system operator back to the native Hilbert
tensor carrier. -/
noncomputable def jointOperatorReindex (B E : Sys) :
    Operator (B ⊗ E) →ₗ[ℂ] L (JointSpace B E) :=
  QuantumChannel.conjugateEnd (jointSpaceEquiv B E).symm.toLinearEquiv

private theorem operatorTensorEquiv_eq_tensorOperator
    {B E : Sys} (X : Operator B) (Y : Operator E) :
    operatorTensorEquiv B E (X ⊗ₜ[ℂ] Y) = tensorOperator X Y := by
  apply (operatorEquivMatrix (B ⊗ E)).injective
  exact (operatorTensorEquiv_matrix_tmul X Y).trans
    (tensorOperator_matrix X Y).symm

theorem jointOperatorReindex_operatorTensorEquiv_tmul
    {B E : Sys} (X : Operator B) (Y : Operator E) :
    jointOperatorReindex B E (operatorTensorEquiv B E (X ⊗ₜ[ℂ] Y)) =
      (QuantumChannel.l_tensor_equiv
        (ℋ₁ := Space B) (ℋ₂ := Space E)).symm (X ⊗ₜ[ℂ] Y) := by
  apply LinearMap.ext
  intro z
  change (jointSpaceEquiv B E).symm
      (operatorTensorEquiv B E (X ⊗ₜ[ℂ] Y) (jointSpaceEquiv B E z)) = _
  rw [operatorTensorEquiv_eq_tensorOperator]
  rw [← jointSpaceEquiv_map X Y z]
  rw [LinearIsometryEquiv.symm_apply_apply]
  rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul]

namespace KrausFamily

variable {A B : Sys}

end KrausFamily

end QuantumModel
