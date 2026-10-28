/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

open QuantumState QuantumChannel
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem rightOrbit_nonneg :
∀ {K E : Type u} [Qudit K] [Qudit E]
  [Nontrivial K] [Nontrivial E] {X : L (K ⊗[ℂ] E)},
  0 ≤ X → ∀ U : unitary (L E), 0 ≤ rightOrbit X U := by
  intro K E _ _ _ _ X hX U
  have hstar : star (TensorProduct.map (1 : L K) (U : L E)) =
      TensorProduct.map (1 : L K) (star (U : L E)) := by
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map,
      ← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, star_one]
  have h := star_left_conjugate_nonneg hX
    (star (TensorProduct.map (1 : L K) (U : L E)))
  simp only [star_star] at h
  simpa only [rightOrbit, hstar] using h

theorem rightOrbit_integrable :
∀ {K E : Type u} [Qudit K] [Qudit E]
  [Nontrivial K] [Nontrivial E] (X : L (K ⊗[ℂ] E)),
  MeasureTheory.Integrable (rightOrbit X) (HaarUnitary.haarUnitary E) := by
  intro K E _ _ _ _ X
  exact HaarUnitary.integrable_unitaryConj_tensor_right X

end RenyiDPI
