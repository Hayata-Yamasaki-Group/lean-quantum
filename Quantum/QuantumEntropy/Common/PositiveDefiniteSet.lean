/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.YoungInequalityLinear
import Quantum.TraceInequality.LiebAndo.PositiveDefiniteGeometry
import Quantum.QuantumEntropy.TensorCFCCore
import Quantum.QuantumMechanics.OperatorBridge

/-! Positive-definite linear maps (LM) and continuous linear maps (CLM),
with the continuous trace functional. -/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Definition

open LiebAndoTrace GeneralizedPerspectiveFunction

universe uDef

variable {ℋ : Type uDef} [Qudit ℋ]

/-- The finite-dimensional trace as a continuous linear functional on bounded operators. -/
noncomputable def traceCLM : (ℋ →L[ℂ] ℋ) →L[ℂ] ℂ :=
  { toFun := fun A => LinearMap.trace ℂ ℋ (A : L ℋ)
    map_add' := fun A B => by simp
    map_smul' := fun (c : ℂ) A => by
      change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
        c • LinearMap.trace ℂ ℋ (A : L ℋ)
      exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ)
    cont := LinearMap.continuous_of_finiteDimensional
      { toFun := fun A : ℋ →L[ℂ] ℋ => LinearMap.trace ℂ ℋ (A : L ℋ)
        map_add' := fun A B => by simp
        map_smul' := fun (c : ℂ) A => by
          change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
            c • LinearMap.trace ℂ ℋ (A : L ℋ)
          exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ) } }

variable [Nontrivial ℋ]

/-- The pullback of `pdSet` along `LinearMap.toContinuousLinearMap`. -/
def pdSetLM : Set (L ℋ) :=
  {A | A.toContinuousLinearMap ∈ pdSet}

end Definition

end SandwichedRenyiRelativeEntropy
