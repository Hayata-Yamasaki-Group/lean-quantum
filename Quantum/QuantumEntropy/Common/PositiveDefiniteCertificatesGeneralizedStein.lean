/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- Identifies `pdSetLM` membership with LM
positive-definiteness. -/
theorem pdSetLM_isPositiveDefinite_certificate (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔ QuantumState.IsPositiveDefinite A := by
  have hstrict :
      A ∈ pdSetLM (ℋ := ℋ) ↔ IsStrictlyPositive A := by
    change A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ) ↔ IsStrictlyPositive A
    exact (pdSet_membership_certificate A.toContinuousLinearMap).trans
      (strictlyPositive_toContinuousLinearMap_iff A)
  rw [hstrict, QuantumState.IsPositiveDefinite, IsStrictlyPositive.iff_of_unital,
    LinearMap.nonneg_iff_isPositive]
  constructor
  · rintro ⟨hpos, hunit⟩
    exact ⟨hpos, isUnit_iff_ne_zero.1 ((LinearMap.isUnit_iff_isUnit_det A).1 hunit)⟩
  · rintro ⟨hpos, hdet⟩
    exact ⟨hpos, (LinearMap.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet)⟩

section PositiveDefiniteFromNonnegUnit

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

/-- From non-negativity and invertibility, conclude positive-definiteness in `pdSetLM`
    (the spectrum is `≥ 0` by positivity and avoids `0` by invertibility). -/
lemma pdSetLM_of_nonneg_isUnit {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (h_nn : (0 : L ℋ) ≤ A) (h_unit : IsUnit A) : A ∈ pdSetLM (ℋ := ℋ) := by
  apply (pdSetLM_strictPositivity_certificate _).2
  exact h_unit.isStrictlyPositive h_nn

end PositiveDefiniteFromNonnegUnit

end SandwichedRenyiRelativeEntropy
