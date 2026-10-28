/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.Main

/-!
# Basic condition for the monotone-convex equivalence

This file introduces the additional endpoint condition used in the
Hiai–Yanagi characterization at `α = ⊤`: after negating `f`, the function is
operator monotone on `[0, ∞)`.  It also records local instance caches used by
the fixed-Hilbert-space proof of the direction from operator convexity to this
monotonicity condition.

## Main results

* `ConvexityCharacterization.ConditionVI`: the condition that `-f` is
  operator monotone on the nonnegative half-line.
* `ConvexityCharacterization.inst...ScopedI6`: reducible local caches for the
  order, scalar-action, and star instances on `L K` used in the
  `ConditionI → ConditionVI` proof.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.8.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

namespace ConvexityCharacterization

/-- Condition (vi) in Theorem 5.1.8: `-f` is operator monotone on `[0,\infty)`. -/
def ConditionVI (f : ℝ → ℝ) : Prop :=
  AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) (fun t : ℝ ↦ -f t)

section ConditionItoVI

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

/- Instance caches: same pattern as
`CompressionInequality/RatioMonotoneToProjection.lean` — the real-scalar action
on `L K` and its order/topology compatibility classes each trigger a deep,
non-cached `synthInstance` derivation re-run at many use sites of the limit
arguments below. Section-level reducible local instances turn each search into
a head-match. -/

/-- Local reducible cache for the real module structure on `L K` used in the
`ConditionI → ConditionVI` limit argument. -/
@[reducible, local instance] noncomputable def instModuleRealLKScopedI6 :
    Module ℝ (L K) := inferInstance

/-- Local reducible cache for positive scalar multiplication monotonicity on
`L K` used in the `ConditionI → ConditionVI` limit argument. -/
@[reducible, local instance] noncomputable def instPosSMulMonoRealLKScopedI6 :
    PosSMulMono ℝ (L K) := inferInstance

/-- Local reducible cache for positivity preservation of real scalar
multiplication on `L K` in the `ConditionI → ConditionVI` proof. -/
@[reducible, local instance] noncomputable def instSMulPosMonoRealLKScopedI6 :
    SMulPosMono ℝ (L K) := inferInstance

/-- Local reducible cache for continuity of real scalar multiplication on
`L K` used in the limiting part of the `ConditionI → ConditionVI` proof. -/
@[reducible, local instance] noncomputable def instContinuousSMulRealLKScopedI6 :
    ContinuousSMul ℝ (L K) := inferInstance

/-- Local reducible cache for the real star-module structure on `L K` used by
the CFC and order calculations in the `ConditionI → ConditionVI` proof. -/
@[reducible, local instance] noncomputable def instStarModuleRealLKScopedI6 :
    StarModule ℝ (L K) := inferInstance

/-- Local reducible cache for the real algebra structure on `L K` used in the
fixed-Hilbert-space proof of `ConditionI → ConditionVI`. -/
@[reducible, local instance] noncomputable def instAlgebraRealLKScopedI6 :
    Algebra ℝ (L K) := inferInstance

/-- Local reducible cache for real scalar multiplication on `L K` used in the
regularization and convex-combination estimates. -/
@[reducible, local instance] noncomputable def instSMulRealLKScopedI6 :
    SMul ℝ (L K) := inferInstance

/-- Local reducible cache for the real multiplicative action on `L K` used to
avoid repeated instance synthesis in scalar-action expressions. -/
@[reducible, local instance] noncomputable def instMulActionRealLKScopedI6 :
    MulAction ℝ (L K) := inferInstance

/-- Local reducible cache for the zero-compatible real scalar action on `L K`
used in the `ConditionI → ConditionVI` limit proof. -/
@[reducible, local instance] noncomputable def instSMulZeroClassRealLKScopedI6 :
    SMulZeroClass ℝ (L K) := inferInstance

/-- Local reducible cache for right-additive monotonicity of the order on
`L K` used in order estimates in the endpoint proof. -/
@[reducible, local instance] noncomputable def instAddRightMonoLKScopedI6 :
    AddRightMono (L K) := inferInstance

/-- Local reducible cache for left-additive monotonicity of the order on
`L K` used in order estimates in the endpoint proof. -/
@[reducible, local instance] noncomputable def instAddLeftMonoLKScopedI6 :
    AddLeftMono (L K) := inferInstance

/-- Local reducible cache for reflecting inequalities under right addition on
`L K`, used by the order algebra in the endpoint proof. -/
@[reducible, local instance] noncomputable def instAddRightReflectLELKScopedI6 :
    AddRightReflectLE (L K) := inferInstance

end ConditionItoVI

end ConvexityCharacterization

end HansenPedersen
