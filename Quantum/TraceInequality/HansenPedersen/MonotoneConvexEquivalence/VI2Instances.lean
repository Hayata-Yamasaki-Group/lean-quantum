/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Basic

/-!
# Instance caches for the `(vi) → (ii)` endpoint proof

This file contains only reducible local instance caches used by the
Julia-block and regularization proof that the endpoint monotonicity condition
for `-f` implies the contraction inequality.  The caches make the later proof
declarations elaborate by head-matching common scalar, order, star, and CFC
instances instead of re-running deep type-class search.

## Main results

* `ConvexityCharacterization.inst...ScopedVI2`: local caches for operators on
  `L K` and on the two-by-two Hilbert product `L (WithLp 2 (K × K))`.

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

section ConditionVItoII

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
`ConditionVI → ConditionII` regularization proof. -/
@[reducible, local instance] noncomputable def instModuleRealLKScopedVI2 :
    Module ℝ (L K) := inferInstance

/-- Local reducible cache for positive scalar multiplication monotonicity on
`L K` in the endpoint contraction proof. -/
@[reducible, local instance] noncomputable def instPosSMulMonoRealLKScopedVI2 :
    PosSMulMono ℝ (L K) := inferInstance

/-- Local reducible cache for positivity preservation of real scalar
multiplication on `L K` in the endpoint contraction proof. -/
@[reducible, local instance] noncomputable def instSMulPosMonoRealLKScopedVI2 :
    SMulPosMono ℝ (L K) := inferInstance

/-- Local reducible cache for continuity of real scalar multiplication on
`L K` used by the regularized limiting argument. -/
@[reducible, local instance] noncomputable def instContinuousSMulRealLKScopedVI2 :
    ContinuousSMul ℝ (L K) := inferInstance

/-- Local reducible cache for the real star-module structure on `L K` used by
the Julia-block order and CFC calculations. -/
@[reducible, local instance] noncomputable def instStarModuleRealLKScopedVI2 :
    StarModule ℝ (L K) := inferInstance

/-- Local reducible cache for the real algebra structure on `L K` used in the
endpoint contraction proof. -/
@[reducible, local instance] noncomputable def instAlgebraRealLKScopedVI2 :
    Algebra ℝ (L K) := inferInstance

/-- Local reducible cache for real scalar multiplication on `L K` used in the
regularization estimates. -/
@[reducible, local instance] noncomputable def instSMulRealLKScopedVI2 :
    SMul ℝ (L K) := inferInstance

/-- Local reducible cache for the real multiplicative action on `L K` used to
avoid repeated scalar-action instance search. -/
@[reducible, local instance] noncomputable def instMulActionRealLKScopedVI2 :
    MulAction ℝ (L K) := inferInstance

/-- Local reducible cache for the zero-compatible real scalar action on `L K`
used in regularized block estimates. -/
@[reducible, local instance] noncomputable def instSMulZeroClassRealLKScopedVI2 :
    SMulZeroClass ℝ (L K) := inferInstance

/-- Local reducible cache for right-additive monotonicity of the order on
`L K` used in endpoint order estimates. -/
@[reducible, local instance] noncomputable def instAddRightMonoLKScopedVI2 :
    AddRightMono (L K) := inferInstance

/-- Local reducible cache for left-additive monotonicity of the order on
`L K` used in endpoint order estimates. -/
@[reducible, local instance] noncomputable def instAddLeftMonoLKScopedVI2 :
    AddLeftMono (L K) := inferInstance

/-- Local reducible cache for reflecting inequalities under right addition on
`L K`, used in the endpoint order algebra. -/
@[reducible, local instance] noncomputable def instAddRightReflectLELKScopedVI2 :
    AddRightReflectLE (L K) := inferInstance

/-- Local reducible cache for star multiplication on `L K` used by Julia-block
conjugation formulas. -/
@[reducible, local instance] noncomputable def instStarMulLKScopedVI2 :
    StarMul (L K) := inferInstance

/-- Local reducible cache for the monoid structure on `L K` used by block
operator products in the endpoint proof. -/
@[reducible, local instance] noncomputable def instMonoidLKScopedVI2 :
    Monoid (L K) := inferInstance

/-- Local reducible cache for star multiplication on the two-by-two Hilbert
product operator algebra used in Julia-block calculations. -/
@[reducible, local instance] noncomputable def instStarMulLPairScopedVI2 :
    StarMul (L (WithLp 2 (K × K))) := inferInstance

/-- Local reducible cache for the monoid structure on the two-by-two Hilbert
product operator algebra used in Julia-block calculations. -/
@[reducible, local instance] noncomputable def instMonoidLPairScopedVI2 :
    Monoid (L (WithLp 2 (K × K))) := inferInstance

/-- Local reducible cache for the real module structure on the two-by-two
Hilbert product operator algebra used in regularized block estimates. -/
@[reducible, local instance] noncomputable def instModuleRealLPairScopedVI2 :
    Module ℝ (L (WithLp 2 (K × K))) := inferInstance

/-- Local reducible cache for real CFC on the two-by-two Hilbert product
operator algebra used by the block monotonicity comparison. -/
@[reducible, local instance] noncomputable def instCFCRealLPairScopedVI2 :
    ContinuousFunctionalCalculus ℝ (L (WithLp 2 (K × K))) IsSelfAdjoint := inferInstance

end ConditionVItoII

end ConvexityCharacterization

end HansenPedersen
