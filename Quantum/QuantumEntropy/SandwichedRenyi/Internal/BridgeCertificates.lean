/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesStrongSubadditivity
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.Defs
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

/-!
φ-free characterizations of `pdSetLM`.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- In finite dimension, membership in `pdSetLM` is equivalent to
self-adjointness and strict positivity of its quadratic form on nonzero vectors. -/
theorem pdSetLM_quadraticForm_iff [Nontrivial ℋ] (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔
      IsSelfAdjoint A ∧
        ∀ x : ℋ, x ≠ 0 → 0 < RCLike.re (inner ℂ (A x) x) := by
  constructor
  · intro hA
    refine ⟨((pdSetLM_strictPositivity_certificate A).1 hA).isSelfAdjoint, ?_⟩
    intro x hx
    obtain ⟨ε, hε, hεA⟩ := (pdSetLM_uniformLowerBound_iff A).1 hA
    have hdiff_pos : (A - (ε : ℂ) • (1 : L ℋ)).IsPositive :=
      (LinearMap.nonneg_iff_isPositive _).1 (sub_nonneg.mpr hεA)
    have hdiff := hdiff_pos.re_inner_nonneg_left x
    have hxnorm : 0 < ε * ‖x‖ ^ 2 :=
      mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hx))
    have hle : ε * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (A x) x) := by
      have hle' :
          RCLike.re (inner ℂ (((ε : ℂ) • (1 : L ℋ)) x) x) ≤
            RCLike.re (inner ℂ (A x) x) := by
        rw [LinearMap.sub_apply, inner_sub_left, map_sub] at hdiff
        exact sub_nonneg.mp hdiff
      change RCLike.re (inner ℂ ((ε : ℂ) • x) x) ≤
        RCLike.re (inner ℂ (A x) x) at hle'
      have hscalar_re :
          RCLike.re (inner ℂ ((ε : ℂ) • x) x) = ε * ‖x‖ ^ 2 := by
        have hnorm_re : Complex.re ((‖x‖ : ℂ) ^ 2) = ‖x‖ ^ 2 := by
          norm_cast
        rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
        change Complex.re (star (ε : ℂ) * (‖x‖ : ℂ) ^ 2) = ε * ‖x‖ ^ 2
        rw [Complex.mul_re, hnorm_re]
        norm_num
      rw [hscalar_re] at hle'
      exact hle'
    exact hxnorm.trans_le hle
  · rintro ⟨hA_sa, hquad⟩
    have hpos : A.IsPositive := by
      refine ⟨(LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA_sa, ?_⟩
      intro x
      change 0 ≤ RCLike.re (inner ℂ (A x) x)
      by_cases hx : x = 0
      · subst x
        simp
      · exact (hquad x hx).le
    have hinjective : Function.Injective A := by
      intro x y hxy
      by_contra hne
      have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hne
      have hsub_zero : A (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      have hpositive := hquad (x - y) hsub_ne
      simp [hsub_zero] at hpositive
    have hunit : IsUnit A :=
      (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap
        (f := A.toContinuousLinearMap)).1 <|
          ContinuousLinearMap.isUnit_iff_bijective.2
            ⟨hinjective, LinearMap.injective_iff_surjective.mp hinjective⟩
    have hnonneg : (0 : L ℋ) ≤ A :=
      (LinearMap.nonneg_iff_isPositive _).2 hpos
    apply (pdSetLM_strictPositivity_certificate A).2
    exact (IsStrictlyPositive.iff_of_unital).2 ⟨hnonneg, hunit⟩

end SandwichedRenyiRelativeEntropy
