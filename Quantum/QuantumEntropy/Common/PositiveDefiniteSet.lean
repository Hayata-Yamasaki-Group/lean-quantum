/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.YoungInequality
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorBridge
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! Positive-definite linear operators and their continuous trace functional. -/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Definition

open LiebAndoTrace GeneralizedPerspectiveFunction

universe uDef

variable {ℋ : Type uDef} [Qudit ℋ]

/-- The finite-dimensional trace as a continuous linear functional on the CLM carrier. -/
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

/-- The pullback of the positive-definite set along Mathlib's canonical LM-to-CLM lift. -/
def pdSetLM : Set (L ℋ) :=
  {A | A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)}

end Definition

end SandwichedRenyiRelativeEntropy
