/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.Conditions

/-! Scoped instance caches for compression proofs.
Importing this module alone does not activate them. -/

namespace HansenPedersen.ConvexityCharacterization

open scoped ComplexOrder

universe u

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/- Instance caches: the real-scalar action on `L K` and its order/topology
compatibility classes (`Module`/`SMul`/`Algebra`/`PosSMulMono`/... below) each
trigger a deep, non-cached `synthInstance` derivation through the C⋆-algebra
structure on `L K`, re-run at many use sites of the regularization argument in
`conditionV_implies_conditionIV`. Caching them as scoped
reducible instances turns each search into a head-match; `@[reducible]`
keeps the aliases transparent so statements stay syntactically compatible with
Mathlib lemmas (same pattern as
`HiaiPetz/MatrixFunctionalCalculus/MatrixPower/Composition.lean`). -/

/-- Scoped reducible cache for the real module structure on `L K`,
used by the projection regularization proof. -/
@[reducible] noncomputable def instModuleRealLKScoped :
    Module ℝ (L K) := inferInstance

/-- Scoped reducible cache for positivity-preserving real scalar
multiplication on `L K`. -/
@[reducible] noncomputable def instPosSMulMonoRealLKScoped :
    PosSMulMono ℝ (L K) := inferInstance

/-- Scoped reducible cache for order-preserving positive scalar
multiplication on `L K`. -/
@[reducible] noncomputable def instSMulPosMonoRealLKScoped :
    SMulPosMono ℝ (L K) := inferInstance

/-- Scoped reducible cache for continuity of real scalar multiplication
on `L K`. -/
@[reducible] noncomputable def instContinuousSMulRealLKScoped :
    ContinuousSMul ℝ (L K) := inferInstance

/-- Scoped reducible cache for the real star-module structure on
operators. -/
@[reducible] noncomputable def instStarModuleRealLKScoped :
    StarModule ℝ (L K) := inferInstance

/-- Scoped reducible cache for the real algebra structure on `L K`. -/
@[reducible] noncomputable def instAlgebraRealLKScoped :
    Algebra ℝ (L K) := inferInstance

/-- Scoped reducible cache for the real scalar action on `L K`. -/
@[reducible] noncomputable def instSMulRealLKScoped :
    SMul ℝ (L K) := inferInstance

/-- Scoped reducible cache for the real multiplicative action on
`L K`. -/
@[reducible] noncomputable def instMulActionRealLKScoped :
    MulAction ℝ (L K) := inferInstance

/-- Scoped reducible cache for scalar multiplication preserving zero on
`L K`. -/
@[reducible] noncomputable def instSMulZeroClassRealLKScoped :
    SMulZeroClass ℝ (L K) := inferInstance

/-- Scoped reducible cache for right-addition monotonicity in the order
on `L K`. -/
@[reducible] noncomputable def instAddRightMonoLKScoped :
    AddRightMono (L K) := inferInstance

/-- Scoped reducible cache for left-addition monotonicity in the order
on `L K`. -/
@[reducible] noncomputable def instAddLeftMonoLKScoped :
    AddLeftMono (L K) := inferInstance

/-- Scoped reducible cache for reflecting inequalities across right
addition in `L K`. -/
@[reducible] noncomputable def instAddRightReflectLELKScoped :
    AddRightReflectLE (L K) := inferInstance

namespace ProjectionInstances

attribute [scoped instance]
  instModuleRealLKScoped
  instPosSMulMonoRealLKScoped
  instSMulPosMonoRealLKScoped
  instContinuousSMulRealLKScoped
  instStarModuleRealLKScoped
  instAlgebraRealLKScoped
  instSMulRealLKScoped
  instMulActionRealLKScoped
  instSMulZeroClassRealLKScoped
  instAddRightMonoLKScoped
  instAddLeftMonoLKScoped
  instAddRightReflectLELKScoped

end ProjectionInstances

end HansenPedersen.ConvexityCharacterization
