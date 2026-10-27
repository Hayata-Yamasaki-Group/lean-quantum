/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.Continuity
import Quantum.QuantumEntropy.UmegakiDPI.Provider

/-!
# Provider-neutral non-negative Umegaki data processing

This module owns the faithful-approximation lift from the positive-definite
provider contract to non-negative inputs.  The Sandwiched Rényi path below is
an analytic implementation dependency, not the public theorem owner.
-/
namespace UmegakiDPI

open SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder Topology

universe u

/-- Route-neutral name for the faithful channel approximation used by the lift. -/
noncomputable abbrev faithfulApproximation
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    QuantumChannel.CPTP ℋ 𝒦 :=
  SandwichedRenyiRelativeEntropy.faithfulApprox Φ lam hlam0 hlam1

/-- Route-neutral alias for positive definiteness of the approximated identity. -/
alias faithfulApproximation_one_pdSetLM :=
  SandwichedRenyiRelativeEntropy.faithfulApprox_one_pdSetLM

/-- Route-neutral alias for positive definiteness of an approximated nonzero input. -/
alias faithfulApproximation_pdSetLM :=
  SandwichedRenyiRelativeEntropy.faithfulApprox_pdSetLM

/-- Route-neutral alias for convergence of the faithful approximation. -/
alias faithfulApproximation_tendsto :=
  SandwichedRenyiRelativeEntropy.tendsto_faithfulApprox

/-- Route-neutral alias for the pointwise faithful-approximation formula. -/
alias faithfulApproximation_toFun_eq :=
  UmegakiDPI.faithfulApprox_toFun_eq

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **step1**: for each faithful parameter `λ ∈ (0,1]`,
    `umegakiNorm (F_λ ρ) (F_λ σ) ≤ umegakiNorm ρ σ`. Proven by perturbing inputs to
    `ρ+ε, σ+ε` (pd), applying the provider-neutral pd DPI
    `UmegakiDPI.monotoneOnPosDef`, and taking `ε → 0⁺` (RHS via
    `tendsto_umegakiNorm_perturb`, LHS via `tendsto_umegakiNorm_within` since `F_λ`
    outputs are pd). -/
lemma faithfulApproxNorm_le {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    umegakiNorm
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun σ) ≤
      umegakiNorm ρ σ := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, h⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
    exact hρ0 (le_antisymm (by simpa using h) hρ)
  set F := faithfulApprox Φ lam hlam0.le hlam1 with hF
  have hFρ : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM Φ hlam0 hlam1 hρ hρ0
  have hFσ : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM Φ hlam0 hlam1 hσ hσ0
  have hpd (τ : L ℋ) (hτ : 0 ≤ τ) (ε : ℝ) (hε : 0 < ε) :
      τ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSetLM hτ hε
  have hFcont (τ : L ℋ) : Continuous (fun ε : ℝ =>
      F.toFun (τ + (ε : ℂ) • 1)) :=
    (LinearMap.continuous_of_finiteDimensional
      F.toLinearMap).comp (by fun_prop)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      umegakiNorm
          (F.toFun (ρ + (ε : ℂ) • 1))
          (F.toFun (σ + (ε : ℂ) • 1))
        ≤ umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1) := by
    intro ε hε
    have hρε := hpd ρ hρ ε hε
    have hσε := hpd σ hσ ε hε
    exact UmegakiDPI.monotoneOnPosDef F hρε hσε
      (faithfulApprox_pdSetLM Φ hlam0 hlam1
        (nonneg_of_pdSetLM hρε) (isUnit_of_pdSetLM hρε).ne_zero)
      (faithfulApprox_pdSetLM Φ hlam0 hlam1
        (nonneg_of_pdSetLM hσε) (isUnit_of_pdSetLM hσε).ne_zero)
  have h_RHS := tendsto_umegakiNorm_perturb hρ hσ hρ0 hsupp
  have hpd2sa : ∀ {τ : L 𝒦},
      τ ∈ pdSetLM (ℋ := 𝒦) → IsSelfAdjoint τ ∧ IsUnit τ :=
    fun hτ => ⟨((pdSetLM_strictPositivity_certificate _).1 hτ).1.isSelfAdjoint,
      isUnit_of_pdSetLM hτ⟩
  have hFmem (τ : L ℋ) (hτ : 0 ≤ τ) : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      IsSelfAdjoint (F.toFun (τ + (ε : ℂ) • 1)) ∧
        IsUnit (F.toFun (τ + (ε : ℂ) • 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hτε := hpd τ hτ ε hε
    exact hpd2sa (faithfulApprox_pdSetLM Φ hlam0 hlam1
      (nonneg_of_pdSetLM hτε) (isUnit_of_pdSetLM hτε).ne_zero)
  have h_LHS : Filter.Tendsto
      (fun ε : ℝ => umegakiNorm
        (F.toFun (ρ + (ε : ℂ) • 1))
        (F.toFun (σ + (ε : ℂ) • 1)))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm
        (F.toFun ρ)
        (F.toFun σ))) := by
    refine tendsto_umegakiNorm_within
      (a := fun ε => F.toFun (ρ + (ε : ℂ) • 1))
      (b := fun ε => F.toFun (σ + (ε : ℂ) • 1))
      (a₀ := F.toFun ρ) (b₀ := F.toFun σ)
      (by simpa using ((hFcont ρ).tendsto 0).mono_left nhdsWithin_le_nhds)
      (by simpa using ((hFcont σ).tendsto 0).mono_left nhdsWithin_le_nhds)
      (hFmem ρ hρ) (hFmem σ hσ) (hpd2sa hFρ) (hpd2sa hFσ)
      (ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero
        (nonneg_of_pdSetLM hFρ) (isUnit_of_pdSetLM hFρ).ne_zero))
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Core non-negative DPI for `umegakiNorm`** (`supp ρ ⊆ supp σ`): assembled from
    `umegakiNorm_faithfulApprox_le` (each faithful `F_λ` decreases `umegakiNorm`) and the
    faithful limit `tendsto_umegakiNorm_faithful`. -/
theorem monotoneNormOnNonNeg
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    umegakiNorm (Φ.toFun ρ)
      (Φ.toFun σ) ≤ umegakiNorm ρ σ := by
  by_cases hρ0 : ρ = 0
  · subst hρ0
    rw [show Φ.toFun 0 = 0 from by
      change Φ.toLinearMap 0 = 0
      exact map_zero Φ.toLinearMap]
    simp only [umegakiNorm_eq_toContinuousLinearMap, map_zero, Complex.zero_re, div_zero,
      le_refl]
  · have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        umegakiNorm
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ) ≤
            umegakiNorm ρ σ :=
      fun l => faithfulApproxNorm_le Φ hρ hσ hρ0 hsupp l.2.1 l.2.2
    haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
        (𝓝[>] (0:ℝ))).NeBot := by
      refine Filter.comap_neBot fun t ht => ?_
      obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
      obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
      have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
      refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
      apply hU_sub
      refine ⟨hball ?_, hx_pos⟩
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact le_of_tendsto (tendsto_umegakiNorm_faithful Φ hρ hσ hρ0 hsupp)
      (Filter.Eventually.of_forall step1)

/-- **Data-processing for the Umegaki relative entropy on non-negative operators.**
    Off-support the right-hand side is `⊤` (trivial); on-support it reduces to the
    real-valued core DPI `umegakiNorm_monotone_nn`. -/
theorem monotoneOnNonNeg
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    umegakiRelEntropyNN (Φ.toFun ρ)
      (Φ.toFun σ) ≤ umegakiRelEntropyNN ρ σ := by
  by_cases hsupp : SupportLE ρ σ
  · -- support holds: both sides are real, reduce to the core DPI
    have hΦsupp := supportLE_map_of_cptp Φ hρ hσ hsupp
    rw [umegakiRelEntropyNN_of_supportLE hΦsupp,
      umegakiRelEntropyNN_of_supportLE hsupp,
      EReal.coe_le_coe_iff]
    exact monotoneNormOnNonNeg Φ hρ hσ hsupp
  · -- support fails: the right-hand side is `⊤`
    rw [umegakiRelEntropyNN_of_not_supportLE hsupp]
    exact le_top


end Umegaki

end UmegakiDPI

namespace SandwichedRenyiRelativeEntropy

@[deprecated UmegakiDPI.faithfulApproxNorm_le (since := "2026-09-03")]
alias umegakiNorm_faithfulApprox_le := UmegakiDPI.faithfulApproxNorm_le

@[deprecated UmegakiDPI.monotoneNormOnNonNeg (since := "2026-09-03")]
alias umegakiNorm_monotone_nn := UmegakiDPI.monotoneNormOnNonNeg

-- Compatibility aliases for generated simplification lemmas.
-- Prefer `UmegakiDPI.monotoneNormOnNonNeg` in new proofs.
alias umegakiNorm_monotone_nn._simp_1_1 :=
  UmegakiDPI.monotoneNormOnNonNeg._simp_1_1

alias umegakiNorm_monotone_nn._simp_1_2 :=
  UmegakiDPI.monotoneNormOnNonNeg._simp_1_2

@[deprecated UmegakiDPI.monotoneOnNonNeg (since := "2026-09-03")]
alias umegakiRelEntropyNN_monotone := UmegakiDPI.monotoneOnNonNeg

end SandwichedRenyiRelativeEntropy
