/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumChannelCore

/-!
# Isometric Stinespring dilation of finite-dimensional channels
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace QuantumChannel.Stinespring

section Monotonicity

open QuantumChannel TensorProduct

universe u₅

variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

/-! ### Pure-environment Stinespring dilation tools -/
omit [Nontrivial ℋ] in
/-- Pure-state Stinespring isometry from a Kraus family `A : κ → (ℋ →ₗ[ℂ] 𝒦)`
    (possibly different input/output spaces) satisfying `Σ_a A_a* A_a = I_ℋ`.
    The map `V ψ := Σ_a (A_a ψ) ⊗ e_a` is a linear isometry `ℋ → 𝒦 ⊗ ℂ^κ`
    realizing the channel `γ ↦ Σ_a A_a γ A_a*` as `traceOutRight(V γ V*)`. -/
private lemma kraus_to_pure_stinespring_isometry
    {𝒦 : Type u₅} [Qudit 𝒦]
    {κ : Type u₅} [Fintype κ] [DecidableEq κ]
    (A : κ → (ℋ →ₗ[ℂ] 𝒦))
    (hSumAA : (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) = (1 : L ℋ)) :
    ∃ V : ℋ →ₗ[ℂ] 𝒦 ⊗[ℂ] EuclideanSpace ℂ κ,
      (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
      ∀ γ : L ℋ,
        (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) =
          traceOutRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  -- The Stinespring isometry from QuantumChannel.lean.
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A, ?_, ?_⟩
  · -- `V* V = Σ_a A_a* A_a = 1` by `hSumAA`.
    set V := krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A with hV_def
    apply LinearMap.ext
    intro ψ
    -- Reduce to computing `(V* V) ψ` directly.
    have hVψ : V ψ = ∑ a : κ, (A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
      krausToStinespringOperator_apply (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A ψ
    have hcomp : (V.adjoint.comp V) ψ = V.adjoint (V ψ) := rfl
    rw [hcomp, hVψ, map_sum]
    have hpiece : ∀ a : κ,
        V.adjoint ((A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)) =
          (LinearMap.adjoint (A a)) (A a ψ) := by
      intro a
      simpa [hV_def] using
        adjoint_krausToStinespringOperator_tmul_basisFun
          (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A (A a ψ) a
    -- Replace each summand and recognize `Σ_a A_a* A_a = 1`.
    simp_rw [hpiece]
    have hSumApp :
        (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ = (1 : L ℋ) ψ := by
      rw [hSumAA]
    -- LHS sum equals `(∑ a, A_a* ∘ A_a) ψ`.
    have hsum_eq :
        (∑ a : κ, (LinearMap.adjoint (A a)) (A a ψ)) =
          (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ := by
      simp [LinearMap.sum_apply]
    rw [hsum_eq, hSumApp]
  · -- Partial-trace identity: this is exactly `traceOutRight_kraus`.
    intro γ
    have h := traceOutRight_kraus (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A γ
    exact h.symm

/-! The two helpers below pass from the canonical lifted CP witness to amplification
positivity and then to Kraus data. -/
omit [Nontrivial ℋ] in
private lemma st_isKPositive_of_lifted_cp
    {𝒦 : Type u₅} [Qudit 𝒦] (k : ℕ) (Φ : (L ℋ) →ₗ[ℂ] (L 𝒦))
    (hΦ : QuantumChannel.IsCompletelyPositive Φ) :
    IsKPositive k Φ := by
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ k

omit [Nontrivial ℋ] in
private lemma st_hasKraus_of_lifted_cp
    {𝒦 : Type u₅} [Qudit 𝒦]
    (Φ : T ℋ 𝒦)
    (hΦ : QuantumChannel.IsCompletelyPositive Φ) :
    HasKraus Φ := by
  exact hasKraus_of_amplificationPositive Φ
    (amplificationPositive_of_cp Φ hΦ)

/-- A CPTP map admits an isometric Stinespring dilation with a
    finite-dimensional nontrivial environment and exact partial-trace realization.

Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Corollary 2.27 / Theorem 2.22 / Proposition 2.20 / Theorem 2.26. A one-directional corollary
of Corollary 2.27, from CPTP
to an isometric dilation. Rank minimality and the other direction of the equivalence are not
included. -/
theorem _root_.QuantumChannel.CPTP.exists_isometric_stinespring_dilation
    {𝒦 : Type u₅} [Qudit 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦) :
    ∃ (ℋ_env : Type u₅) (_ : Qudit ℋ_env) (_ : Nontrivial ℋ_env)
      (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env)),
        (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
        ∀ γ : L ℋ,
          Φ.toFun γ =
            traceOutRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  let ΦL : T ℋ 𝒦 := Φ.toLinearMap
  have hKraus : HasKraus ΦL :=
    st_hasKraus_of_lifted_cp ΦL ⟨Φ.toCompletelyPositiveMap, rfl⟩
  obtain ⟨κ, hκ_dec, hκ_fin, A, hA_eq⟩ := hKraus
  letI : DecidableEq κ := hκ_dec
  letI : Fintype κ := hκ_fin
  set S : L ℋ := ∑ a : κ, (LinearMap.adjoint (A a)).comp (A a) with hS_def
  have hSρ_tr : ∀ ρ : L ℋ, Tr (S * ρ) = Tr ρ := by
    intro ρ
    have htr : Tr ρ = Tr (ΦL ρ) := Φ.trace_map ρ
    have hKr : ΦL ρ =
        ∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a))) := hA_eq ρ
    have hcycle : ∀ a : κ,
        Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) =
          Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
      intro a
      rw [← LinearMap.trace_comp_comm' (A a) (ρ.comp (LinearMap.adjoint (A a))),
        LinearMap.comp_assoc, Module.End.mul_eq_comp]
      exact (LinearMap.trace_comp_comm' ρ ((LinearMap.adjoint (A a)).comp (A a))).symm
    calc
      Tr (S * ρ) = Tr ((∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
        rw [hS_def]
      _ = ∑ a : κ, Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
        rw [Finset.sum_mul]
        exact map_sum Tr _ _
      _ = ∑ a : κ, Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [(hcycle a).symm]
      _ = Tr (∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
        rw [map_sum Tr]
      _ = Tr (ΦL ρ) := by rw [← hKr]
      _ = Tr ρ := htr.symm
  have hSumAA : S = (1 : L ℋ) := by
    apply LinearMap.ext
    intro v
    refine ext_inner_left ℂ ?_
    intro w
    have h_compOuter : ∀ M : L ℋ, M.comp (outer_product w v) = outer_product w (M v) := by
      intro M
      ext x
      simp [outer_product_eq_rankOne]
    have htrace_eq := hSρ_tr (outer_product w v)
    have hLHS : Tr (S * outer_product w v) = inner ℂ w (S v) := by
      change Tr (S.comp (outer_product w v)) = inner ℂ w (S v)
      rw [h_compOuter S, trace_outer_product]
    rw [show (1 : L ℋ) v = v by rfl, ← hLHS, htrace_eq, trace_outer_product]
  have hκ_nonempty : Nonempty κ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hS_zero : S = 0 := by simp [hS_def, Finset.sum_empty]
    exact one_ne_zero (hSumAA ▸ hS_zero)
  haveI : Nonempty κ := hκ_nonempty
  haveI : Nontrivial (EuclideanSpace ℂ κ) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_euclideanSpace]
      exact Fintype.card_pos)
  obtain ⟨V, hV_iso, hV_eq⟩ :=
    kraus_to_pure_stinespring_isometry (ℋ := ℋ) A hSumAA
  refine ⟨EuclideanSpace ℂ κ, inferInstance, inferInstance, V, hV_iso, ?_⟩
  intro γ
  change ΦL γ = traceOutRight ((V.comp γ).comp (LinearMap.adjoint V))
  rw [hA_eq γ, hV_eq γ]

end Monotonicity

end QuantumChannel.Stinespring

namespace QuantumChannel.CPTP

@[deprecated (since := "2026-09-05")]
alias exists_stinespring_dilation := exists_isometric_stinespring_dilation

end QuantumChannel.CPTP
