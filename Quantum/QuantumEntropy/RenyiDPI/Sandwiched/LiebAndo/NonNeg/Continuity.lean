import Quantum.QuantumEntropy.Common.TraceNonnegative
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Defs
import Quantum.QuantumMechanics.OperatorBridge
import Quantum.QuantumMechanics.Channel.BasicGeneralizedStein
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.TensorCFC
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.Defs
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

/-!
# Non-negative sandwiched Rényi divergence: continuity

Continuity of rpow and sandwiched quasi-entropy on non-negative cones,
boundary continuity, and CFC eigenvector formulas.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-- Continuity of `(ρ, σ) ↦ σ^β ρ σ^β` on the non-negative cone, for `β ≥ 0`. -/
private lemma rpow_conj_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {β : ℝ} (hβ : 0 ≤ β) :
    ContinuousOn (fun p : B ℋ × B ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) := by
  have h_rpow_snd : ContinuousOn (fun p : B ℋ × B ℋ => CFC.rpow p.2 β)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) :=
    (rpow_continuousOn_nonneg hβ).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : B ℋ × B ℋ => p.1)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- Linear-map endpoint form of continuity on the non-negative cone. -/
private lemma sandwichedQuasi_re_continuousOn_nonneg_lm
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) =>
      (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  let e : L 𝒦 → B 𝒦 := fun A => A.toContinuousLinearMap
  have he : Continuous e := by fun_prop
  have h := sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα1
  have hc := h.comp (he.prodMap he).continuousOn
    (fun (p : L 𝒦 × L 𝒦) (hp : p ∈
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A})) => by
      constructor
      · exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hp.1)
      · exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hp.2))
  simpa [e, Function.comp_def, Function.uncurry] using hc

/-- For `0 < α ≤ 1`, `Q_α` is continuous along the non-negative perturbation path
    `ε ↦ (ρ + ε•P, σ + ε•P)` (with `P ≥ 0`) as `ε → 0⁺`. -/
private lemma sandwichedQuasi_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg_lm (𝒦 := ℋ) hα0 hα1
  set S : Set (L ℋ × L ℋ) := {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A} with hS
  set g : ℝ → L ℋ × L ℋ := fun ε => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P)
    with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      exact Set.mk_mem_prod
        (add_nonneg hρ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
        (add_nonneg hσ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) =>
        (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- **Boundary-continuity of `sandwichedRenyiDiv` for `α < 1`** along a non-negative
    perturbation direction `P`, at a point where `Q_α ≠ 0` and `Tr ρ ≠ 0`. No support
    condition is needed: the exponents are non-negative, so `Q_α` is jointly continuous
    on the whole non-negative cone. -/
lemma sandwichedRenyiDiv_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0)
    (hTr : (Tr ρ).re ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := sandwichedQuasi_tendsto_nonneg_lt hα0 hα1.le hρ hσ hP
  have hpath : Filter.Tendsto (fun ε : ℝ => ρ + (ε : ℂ) • P)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ρ) := by
    have hcont : Continuous (fun ε : ℝ => ρ + (ε : ℂ) • P) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hTc : Filter.Tendsto (fun ε : ℝ =>
      (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ).re) := by
    have htrace : Continuous (fun A : L ℋ => (Tr A).re) := by fun_prop
    exact (htrace.tendsto ρ).comp hpath
  have hRatio : Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P)).re /
        (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
    Filter.Tendsto.div hQc hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ σ).re / (Tr ρ).re ≠ 0 :=
    div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Joint continuity (within the non-negative cone) of `sandwichedRenyiDiv` for `α < 1`**
    at a point `(ρ₀, σ₀)` with `Q_α ≠ 0` and `Tr ρ₀ ≠ 0`. Used to pass both the
    `λ → 0⁺` (channel) and `ε → 0⁺` (perturbation) limits.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
lemma sandwichedRenyiDiv_continuousWithinAt_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ₀ σ₀ : L ℋ}
    (hρ₀ : 0 ≤ ρ₀) (hσ₀ : 0 ≤ σ₀)
    (hQ : (sandwichedQuasi α ρ₀ σ₀).re ≠ 0)
    (hTr : (Tr ρ₀).re ≠ 0) :
    ContinuousWithinAt (fun p : L ℋ × L ℋ =>
      sandwichedRenyiDiv α p.1 p.2)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg_lm (𝒦 := ℋ) hα0 hα1.le
  have hQc : ContinuousWithinAt (fun p : L ℋ × L ℋ =>
      (sandwichedQuasi α p.1 p.2).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    hcont (ρ₀, σ₀) ⟨hρ₀, hσ₀⟩
  have h_trace_cont : Continuous (fun A : L ℋ => (Tr A).re) := by fun_prop
  have hTc : ContinuousWithinAt (fun p : L ℋ × L ℋ => (Tr p.1).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    (h_trace_cont.comp continuous_fst).continuousWithinAt
  have hRatio := hQc.div hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ₀ σ₀).re / (Tr ρ₀).re ≠ 0 :=
    div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul (1 / (α - 1))

end SandwichedRenyiRelativeEntropy
