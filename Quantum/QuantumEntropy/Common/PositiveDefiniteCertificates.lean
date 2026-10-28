/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

lemma strictlyPositive_toContinuousLinearMap_iff (A : L ℋ) :
    IsStrictlyPositive A.toContinuousLinearMap ↔ IsStrictlyPositive A := by
  rw [IsStrictlyPositive.iff_of_unital, IsStrictlyPositive.iff_of_unital]
  exact and_congr
    (by
      change (0 : B ℋ) ≤ A.toContinuousLinearMap ↔ (0 : L ℋ) ≤ A
      simpa using
        (ContinuousLinearMap.coe_le_coe_iff
          (0 : B ℋ) A.toContinuousLinearMap).symm)
    (by
      simpa using
        (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap
          (𝕜 := ℂ) (E := ℋ) (f := A.toContinuousLinearMap)))

/-- Identifies `pdSetLM` membership with LM strict positivity. -/
theorem pdSetLM_strictPositivity_certificate (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔ IsStrictlyPositive A := by
  change A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ) ↔ IsStrictlyPositive A
  exact (pdSet_membership_certificate A.toContinuousLinearMap).trans
    (strictlyPositive_toContinuousLinearMap_iff A)

end SandwichedRenyiRelativeEntropy
