/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Petz.TracePower
import Quantum.QuantumEntropy.Common.FaithfulApproximation

/-! # Provider-neutral lift of positive-definite Petz data processing

First regularize the inputs for a fixed faithful channel, then let the channel
approach the original CPTP map. Both passages use CFC continuity on the closed
nonnegative cone. Only after obtaining Q monotonicity do we take logarithms.
-/

namespace RenyiDPI

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy ComplexOrder Topology

universe u

/-- The positive-definite trace-power core accepted by the nonnegative lift. -/
def PetzTracePowerMonotoneOnPosDef : Prop :=
  ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {ρ σ : L H},
    ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
    E.toFun ρ ∈ pdSetLM (ℋ := K) → E.toFun σ ∈ pdSetLM (ℋ := K) →
    ∀ {α : ℝ}, α ∈ Set.Ioo (0 : ℝ) 1 →
    petzTracePower α ρ σ ≤ petzTracePower α (E.toFun ρ) (E.toFun σ)

variable {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]

/-- Fixed faithful channel: pass to the nonnegative boundary as ε tends to zero. -/
theorem petzTracePower_le_faithfulApprox
    (core : PetzTracePowerMonotoneOnPosDef.{u}) (E : CPTP H K)
    {α : ℝ} {ρ σ : L H} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    petzTracePower α ρ σ ≤
      petzTracePower α ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) := by
  let F := faithfulApprox E lam hlam0.le hlam1
  have hpd (τ : L H) (hτ : 0 ≤ τ) (ε : ℝ) (hε : 0 < ε) :=
    nonneg_add_pos_smul_one_pdSetLM hτ hε
  have ht (τ : L H) : Filter.Tendsto (fun ε : ℝ => τ + (ε : ℂ) • 1)
      (𝓝[>] (0 : ℝ)) (𝓝 τ) := by
    have hc : Continuous (fun ε : ℝ => τ + (ε : ℂ) • 1) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hn (τ : L H) (hτ : 0 ≤ τ) :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ τ + (ε : ℂ) • 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact nonneg_of_pdSetLM (hpd τ hτ ε hε)
  have hFcont : Continuous F.toLinearMap := LinearMap.continuous_of_finiteDimensional _
  have hFnn (τ : L H) (hτ : 0 ≤ τ) : 0 ≤ F.toFun τ :=
    map_nonneg F.toCompletelyPositiveMap hτ
  have hleft := tendsto_petzTracePower_nonneg hα hρ hσ (ht ρ) (ht σ) (hn ρ hρ) (hn σ hσ)
  have hright := tendsto_petzTracePower_nonneg hα (hFnn ρ hρ) (hFnn σ hσ)
    ((hFcont.tendsto ρ).comp (ht ρ)) ((hFcont.tendsto σ).comp (ht σ))
    ((hn ρ hρ).mono fun ε hε => hFnn _ hε)
    ((hn σ hσ).mono fun ε hε => hFnn _ hε)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hρε := hpd ρ hρ ε hε
  have hσε := hpd σ hσ ε hε
  exact core F hρε hσε
    (faithfulApprox_pdSetLM E hlam0 hlam1
      (nonneg_of_pdSetLM hρε) (isUnit_of_pdSetLM hρε).ne_zero)
    (faithfulApprox_pdSetLM E hlam0 hlam1
      (nonneg_of_pdSetLM hσε) (isUnit_of_pdSetLM hσε).ne_zero) hα

/-- Let λ tend to zero: Q increases under any CPTP map on all nonnegative inputs. -/
theorem petzTracePower_le_of_nonneg
    (core : PetzTracePowerMonotoneOnPosDef.{u}) (E : CPTP H K)
    {α : ℝ} {ρ σ : L H} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    petzTracePower α ρ σ ≤ petzTracePower α (E.toFun ρ) (E.toFun σ) := by
  let f := Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (𝓝[>] (0 : ℝ))
  haveI : f.NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, hU_sub ⟨hball ?_, hx_pos⟩⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht := tendsto_petzTracePower_nonneg hα
    (map_nonneg E.toCompletelyPositiveMap hρ) (map_nonneg E.toCompletelyPositiveMap hσ)
    (faithfulApprox_tendsto E ρ) (faithfulApprox_tendsto E σ)
    (Filter.Eventually.of_forall fun l =>
      map_nonneg (faithfulApprox E l.val l.property.1.le l.property.2).toCompletelyPositiveMap hρ)
    (Filter.Eventually.of_forall fun l =>
      map_nonneg (faithfulApprox E l.val l.property.1.le l.property.2).toCompletelyPositiveMap hσ)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun l =>
    petzTracePower_le_faithfulApprox core E hα hρ hσ l.property.1 l.property.2)

/-- The extended DPI: zero input, zero input Q, and positive input Q are separate branches. -/
theorem petzMonotoneOnNonNeg_of_posDef
    (core : PetzTracePowerMonotoneOnPosDef.{u}) : PetzMonotoneOnNonNeg.{u} := by
  intro H _ _ K _ _ E α ρ σ hα hρ hσ
  by_cases hρ0 : ρ = 0
  · subst ρ
    have hE0 : E.toFun 0 = 0 := map_zero E.toLinearMap
    simp [hE0]
  by_cases hQ0 : petzTracePower α ρ σ = 0
  · rw [show petzDivNN α ρ σ = ⊤ by simp [petzDivNN, hρ0, hQ0]]
    exact le_top
  have hQ : 0 < petzTracePower α ρ σ :=
    lt_of_le_of_ne (petzTracePower_nonneg hα hρ hσ) (Ne.symm hQ0)
  have hmono := petzTracePower_le_of_nonneg core E hα hρ hσ
  have hEQ : 0 < petzTracePower α (E.toFun ρ) (E.toFun σ) := hQ.trans_le hmono
  have htr : 0 < (Tr ρ).re := QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  have hlog := Real.log_le_log (div_pos hQ htr) (div_le_div_of_nonneg_right hmono htr.le)
  have hαneg : α - 1 < 0 := sub_neg.mpr hα.2
  simp only [petzDivNN, hQ0, ne_of_gt hEQ, and_false, ↓reduceIte, EReal.coe_le_coe_iff]
  unfold petzDiv
  rw [← E.trace_map ρ]
  exact div_le_div_of_nonpos_of_le hαneg.le hlog

end RenyiDPI
