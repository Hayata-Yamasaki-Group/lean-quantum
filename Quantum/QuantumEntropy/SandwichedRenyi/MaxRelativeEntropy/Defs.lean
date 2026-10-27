/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Defs
import Quantum.QuantumMechanics.OperatorBridge

/-!
# Max-relative entropy: definitions

Order-theoretic and Frank--Lieb definitions for the max-relative endpoint.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-! ### α = ∞ : max-relative entropy -/

section MaxRelEntropy

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The set of scalars `λ ≥ 0` with `ρ ≤ λ • σ`. -/
def maxRelSet (ρ σ : L ℋ) : Set ℝ :=
  {lam : ℝ | 0 ≤ lam ∧ ρ ≤ (lam : ℂ) • σ}

omit [Nontrivial ℋ] in
/-- `0` is a lower bound of `maxRelSet ρ σ`. -/
lemma bddBelow_maxRelSet (ρ σ : L ℋ) : BddBelow (maxRelSet ρ σ) :=
  ⟨0, fun _ hx => hx.1⟩

@[deprecated (since := "2026-09-05")]
alias re_inner_le_of_le_smul := QuantumChannel.re_inner_le_of_le_smul

@[deprecated (since := "2026-09-05")]
alias exists_re_inner_pos_of_ne_zero := QuantumChannel.exists_re_inner_pos_of_ne_zero

/-- For nonneg `ρ ≠ 0` with `SupportLE ρ σ`, `maxRelSet ρ σ` has a strictly positive
  lower bound. -/
lemma maxRelSet_pos_lowerBound {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ) :
    ∃ c > (0 : ℝ), ∀ lam ∈ maxRelSet ρ σ, c ≤ lam := by
  obtain ⟨x, hx⟩ := QuantumChannel.exists_re_inner_pos_of_ne_zero hρ hρ0
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  -- re ⟨σ x, x⟩ > 0, else σ x = 0 ⇒ x ∈ ker σ ⊆ ker ρ ⇒ ρ x = 0 ⇒
  -- re⟨ρx,x⟩ = 0.
  have hσx_pos : 0 < RCLike.re (inner ℂ (σ x) x) := by
    rcases eq_or_lt_of_le (hσ_pos.2 x) with h_eq | h_lt
    · exfalso
      have hσx : σ x = 0 := QuantumChannel.nonneg_apply_eq_zero_of_inner_self_eq_zero hσ h_eq.symm
      have hxker : x ∈ LinearMap.ker σ := hσx
      have hρx : ρ x = 0 := hsupp hxker
      rw [hρx] at hx; simp at hx
    · exact h_lt
  refine ⟨RCLike.re (inner ℂ (ρ x) x) / RCLike.re (inner ℂ (σ x) x), div_pos hx
    hσx_pos, ?_⟩
  intro lam hlam
  have hle := QuantumChannel.re_inner_le_of_le_smul hlam.2 x
  rw [div_le_iff₀ hσx_pos]
  linarith

/-- For nonneg `ρ ≠ 0` with `SupportLE ρ σ`, `0 < sInf (maxRelSet ρ σ)`. -/
lemma sInf_maxRelSet_pos {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ) :
    0 < sInf (maxRelSet ρ σ) := by
  obtain ⟨c, hc_pos, hc_lb⟩ := maxRelSet_pos_lowerBound hρ hσ hρ0 hsupp
  obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
  have hne : (maxRelSet ρ σ).Nonempty := ⟨lam, hlam_pos.le, hlam_le⟩
  exact lt_of_lt_of_le hc_pos (le_csInf hne hc_lb)

/-- **Max-relative entropy** for non-negative `ρ, σ` (the `α → ∞` limit of the
    sandwiched Rényi divergence), in the **explicit Frank–Lieb form**
    [arXiv:1306.5358]: `D_∞(ρ‖σ) = log ‖σ^{-1/2} ρ σ^{-1/2}‖` (with `σ^{-1/2}` the
    Moore–Penrose power), and value `⊤ : EReal` on the support-mismatch region
    `¬ SupportLE ρ σ`. The equivalent order-theoretic form `log inf{λ ≥ 0 : ρ ≤ λ σ}` is
    `maxRelEntropyNN_eq_log_sInf`. -/
noncomputable def maxRelEntropyNN (ρ σ : L ℋ) : EReal :=
  letI : Decidable (SupportLE ρ σ) := Classical.propDecidable _
  if SupportLE ρ σ then
    ((Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ : ℝ) : EReal)
  else (⊤ : EReal)

omit [Nontrivial ℋ] in
/-- `maxRelSet` is monotone under a positive map: every `λ` working for `ρ ≤ λσ`
    also works for `Φ ρ ≤ λ Φ σ`. -/
lemma maxRelSet_subset_of_cptp
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} :
    maxRelSet ρ σ ⊆ maxRelSet
      (Φ.toFun ρ)
      (Φ.toFun σ) := by
  intro lam hlam
  refine ⟨hlam.1, ?_⟩
  have h1 := map_nonneg Φ.toCompletelyPositiveMap (sub_nonneg.mpr hlam.2)
  rw [map_sub, map_smul] at h1
  exact sub_nonneg.mp h1

/-- For nonneg `τ`, `maxRelSet 0 τ = [0, ∞)`. -/
lemma maxRelSet_zero_left {ℋ' : Type u} [Qudit ℋ'] [Nontrivial ℋ']
    {τ : L ℋ'} (hτ : 0 ≤ τ) :
    maxRelSet (0 : L ℋ') τ = Set.Ici (0 : ℝ) := by
  ext lam
  simp only [maxRelSet, Set.mem_setOf_eq, Set.mem_Ici]
  refine ⟨fun h => h.1, fun hlam => ⟨hlam, ?_⟩⟩
  exact smul_nonneg (Complex.zero_le_real.mpr hlam) hτ


end MaxRelEntropy

end SandwichedRenyiRelativeEntropy
