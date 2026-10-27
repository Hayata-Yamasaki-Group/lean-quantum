/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.QuantumMechanics.QuantumState

/-!
Membership in `pdSet` is equivalent to strict positivity.
-/

namespace GeneralizedPerspectiveFunction

open LownerHeinzTheorem

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- Membership in `pdSet` is equivalent to strict positivity. -/
theorem pdSet_membership_certificate (T : (ℋ →L[ℂ] ℋ)) :
    T ∈ pdSet (ℋ := ℋ) ↔ IsStrictlyPositive T := by
  change (IsSelfAdjoint T ∧ spectrum ℝ T ⊆ Set.Ioi 0) ↔ IsStrictlyPositive T
  simpa [Set.subset_def] using
    (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
      (a := T)).symm

end GeneralizedPerspectiveFunction

namespace GeneralizedPerspectiveFunction

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ]

/-- A `pdSet` operator is strictly positive (nonnegative and a unit). -/
lemma isStrictlyPositive_of_pdSet {σ : B ℋ} (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    IsStrictlyPositive σ := (pdSet_membership_certificate σ).1 hσ

end

end GeneralizedPerspectiveFunction
