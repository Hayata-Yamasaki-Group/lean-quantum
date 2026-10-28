/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- Membership in `pdSetLM` is equivalent to self-adjointness together with a
strictly positive real spectrum. -/
theorem pdSetLM_spectrum_iff [Nontrivial ℋ] (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔
      IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ioi 0 := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  exact (pdSetLM_strictPositivity_certificate A).trans (by
    simpa [Set.subset_def] using
      (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
        (a := A)))

/-- Membership in `pdSetLM` is equivalent to a uniform positive lower bound
by a positive real multiple of the identity. -/
theorem pdSetLM_uniformLowerBound_iff [Nontrivial ℋ] (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔
      ∃ ε : ℝ, 0 < ε ∧ ((ε : ℂ) • (1 : L ℋ)) ≤ A := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  have hscalar (ε : ℝ) :
      algebraMap ℝ (L ℋ) ε = (ε : ℂ) • (1 : L ℋ) := by
    ext x
    rfl
  rw [pdSetLM_spectrum_iff]
  constructor
  · rintro ⟨hA_sa, hA_spec⟩
    obtain ⟨ε, hε, hεA⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hA_sa).2 hA_spec
    refine ⟨ε, hε, ?_⟩
    rwa [hscalar ε] at hεA
  · rintro ⟨ε, hε, hεA⟩
    have hεA' : algebraMap ℝ (L ℋ) ε ≤ A := by
      rwa [hscalar ε]
    have hA_sa : IsSelfAdjoint A := by
      have hε_nn : (0 : L ℋ) ≤ algebraMap ℝ (L ℋ) ε := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact smul_nonneg hε.le zero_le_one
      exact IsSelfAdjoint.of_nonneg (hε_nn.trans hεA')
    refine ⟨hA_sa, ?_⟩
    intro x hx
    exact lt_of_lt_of_le hε
      ((algebraMap_le_iff_le_spectrum (R := ℝ)).1 hεA' x hx)

end SandwichedRenyiRelativeEntropy
