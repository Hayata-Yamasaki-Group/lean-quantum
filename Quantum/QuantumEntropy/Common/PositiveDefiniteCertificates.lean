/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

private lemma strictlyPositive_toContinuousLinearMap_iff (A : L ℋ) :
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

/-- Membership in `pdSetLM` is equivalent to
`QuantumState.IsPositiveDefinite`. -/
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

/-- Membership in `pdSetLM` is equivalent to strict positivity. -/
theorem pdSetLM_strictPositivity_certificate (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔ IsStrictlyPositive A := by
  change A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ) ↔ IsStrictlyPositive A
  exact (pdSet_membership_certificate A.toContinuousLinearMap).trans
    (strictlyPositive_toContinuousLinearMap_iff A)

/-- Membership in `pdSetLM` is equivalent to self-adjointness together with a
strictly positive real spectrum. -/
theorem pdSetLM_spectrum_iff [Nontrivial ℋ] (A : L ℋ) :
    A ∈ pdSetLM ↔
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
