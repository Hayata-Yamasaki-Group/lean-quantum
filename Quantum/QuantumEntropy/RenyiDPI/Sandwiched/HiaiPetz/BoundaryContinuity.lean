/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity
import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.Convex.Integral
import Mathlib.Topology.Algebra.Star.Unitary

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma c13_rpow_continuousOn_pd
    {H : Type u} [Qudit H] [Nontrivial H] (p : ℝ) :
    ContinuousOn (fun A : B H => CFC.rpow A p) (pdSet (ℋ := H)) := by
  have h_subset : (⋃ A ∈ pdSet (ℋ := H), spectrum NNReal A) ⊆ Set.Ioi 0 := by
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨A, hA, hrA⟩ := hr
    have h0 : (0 : NNReal) ∉ spectrum NNReal A :=
      (spectrum.zero_notMem_iff (R := NNReal)).mpr
        ((pdSet_membership_certificate A).1 hA).isUnit
    rcases lt_or_eq_of_le (zero_le r) with hr_pos | hr_zero
    · exact hr_pos
    · exact absurd (hr_zero ▸ hrA) h0
  have h_nhds : (Set.Ioi 0 : Set NNReal) ∈
      𝓝ˢ (⋃ A ∈ pdSet (ℋ := H), spectrum NNReal A) :=
    isOpen_Ioi.mem_nhdsSet.mpr h_subset
  exact (continuousOn_id (s := pdSet (ℋ := H))).cfc_nnreal_of_mem_nhdsSet
    (s := Set.Ioi 0) (f := (· ^ p)) h_nhds
    (ha' := fun A hA => ((pdSet_membership_certificate A).1 hA).nonneg)
    (hf := NNReal.continuousOn_rpow_const
      (.inl (by simp : (0 : NNReal) ∉ Set.Ioi 0)))

private lemma c13_quasi_re_continuousOn_pd
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} (hα : 0 < α) :
    ContinuousOn (Function.uncurry (fun (ρ σ : B H) =>
      (sandwichedQuasi α (ρ : L H) (σ : L H)).re))
      (pdSet (ℋ := H) ×ˢ pdSet (ℋ := H)) := by
  let β : ℝ := (1 - α) / (2 * α)
  have hs : ContinuousOn (fun p : B H × B H => CFC.rpow p.2 β)
      (pdSet (ℋ := H) ×ˢ pdSet (ℋ := H)) :=
    (c13_rpow_continuousOn_pd β).comp continuousOn_snd (fun _ hp => hp.2)
  have hi : ContinuousOn
      (fun p : B H × B H => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      (pdSet (ℋ := H) ×ˢ pdSet (ℋ := H)) :=
    (hs.mul continuousOn_fst).mul hs
  have hp : ContinuousOn
      (fun p : B H × B H => CFC.rpow
        (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
      (pdSet (ℋ := H) ×ˢ pdSet (ℋ := H)) :=
    (rpow_continuousOn_nonneg hα.le).comp hi (by
      rintro ⟨ρ, σ⟩ ⟨hρ, _⟩
      exact conjugate_nonneg_of_nonneg
        ((pdSet_membership_certificate ρ).1 hρ).nonneg CFC.rpow_nonneg)
  have ht : Continuous (fun A : B H => (traceCLM A).re) :=
    Complex.continuous_re.comp traceCLM.continuous
  refine (ht.comp_continuousOn hp).congr ?_
  rintro ⟨ρ, σ⟩ _
  simpa [β, traceCLM] using
    congrArg Complex.re (sandwichedQuasi_eq_clm_direct α ρ σ)

private lemma c13_quasi_re_continuousOn_pd_lm
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} (hα : 0 < α) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L H) =>
      (sandwichedQuasi α ρ σ).re))
      (pdSetLM (ℋ := H) ×ˢ pdSetLM (ℋ := H)) := by
  let e : L H → B H := fun A => A.toContinuousLinearMap
  have he : Continuous e := by fun_prop
  have h := (c13_quasi_re_continuousOn_pd (H := H) hα).comp
    (he.prodMap he).continuousOn
    (fun (p : L H × L H) (hp : p ∈
      (pdSetLM (ℋ := H) ×ˢ pdSetLM (ℋ := H))) => hp)
  simpa [e, Function.comp_def, Function.uncurry] using h

private lemma c13_perturb_pair_tendsto_pd
    {H : Type u} [Qudit H] [Nontrivial H] {ρ σ P : L H}
    (hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H))
    (hP : P ∈ pdSetLM (ℋ := H)) :
    Filter.Tendsto (fun ε : ℝ => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P))
      (𝓝[>] (0 : ℝ))
      (𝓝[pdSetLM (ℋ := H) ×ˢ pdSetLM (ℋ := H)] (ρ, σ)) := by
  let g : ℝ → L H × L H := fun ε =>
    (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P)
  have hg : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [g]
  change Filter.Tendsto g _ _
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [← hg0]
    exact (hg.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεP : (ε : ℂ) • P ∈ pdSetLM (ℋ := H) := by
      apply (pdSetLM_strictPositivity_certificate _).2
      exact IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε)
        ((pdSetLM_strictPositivity_certificate P).1 hP)
    exact Set.mk_mem_prod
      (pdSetLM_add_nonneg (nonneg_of_pdSetLM hρ) hεP)
      (pdSetLM_add_nonneg (nonneg_of_pdSetLM hσ) hεP)

private lemma c13_quasi_re_tendsto_pd
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} (hα : 0 < α)
    {ρ σ P : L H} (hρ : ρ ∈ pdSetLM (ℋ := H))
    (hσ : σ ∈ pdSetLM (ℋ := H)) (hP : P ∈ pdSetLM (ℋ := H)) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α
        (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (sandwichedQuasi α ρ σ).re) := by
  have hc := (c13_quasi_re_continuousOn_pd_lm (H := H) hα) (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := hc.tendsto.comp (c13_perturb_pair_tendsto_pd hρ hσ hP)
  simpa only [Function.comp_def, Function.uncurry] using hcomp

theorem sandwichedRenyiDiv_tendsto_pd_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ P : L H},
  1 < α → ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
  P ∈ pdSetLM (ℋ := H) →
  Filter.Tendsto
    (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P))
    (𝓝[>] (0 : ℝ)) (𝓝 (sandwichedRenyiDiv α ρ σ)) := by
  intro H _ _ α ρ σ P hα hρ hσ hP
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hQ := c13_quasi_re_tendsto_pd hα0 hρ hσ hP
  have hTr0 : (Tr ρ).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero (nonneg_of_pdSetLM hρ)
      (isUnit_of_pdSetLM hρ).ne_zero)
  have hQ0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  have hpath : Filter.Tendsto (fun ε : ℝ => ρ + (ε : ℂ) • P)
      (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
    have hc : Continuous (fun ε : ℝ => ρ + (ε : ℂ) • P) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht : Continuous (fun A : L H => (Tr A).re) := by fun_prop
  have hT := (ht.tendsto ρ).comp hpath
  have hLog := (Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp
    (Filter.Tendsto.div hQ hT hTr0)
  exact hLog.const_mul _

theorem sandwichedRenyiDiv_tendsto_support_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ : L H},
  1 < α → 0 ≤ ρ → 0 ≤ σ → SupportLE ρ σ → ρ ≠ 0 →
  Filter.Tendsto
    (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1))
    (𝓝[>] (0 : ℝ)) (𝓝 (sandwichedRenyiDiv α ρ σ)) := by
  intro H _ _ α ρ σ hα hρ hσ hsupp hρ0
  exact sandwichedRenyiDiv_tendsto_of_suppLE hα hρ hσ hsupp hρ0

end RenyiDPI
