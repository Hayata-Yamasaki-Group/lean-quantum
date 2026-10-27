import Quantum.QuantumEntropy.Common.TraceNonnegativeLinear
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Approximation
import Quantum.QuantumMechanics.OperatorBridge
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumEntropy.TensorCFCCore

import Quantum.QuantumEntropy.CFCTransport

section EigenvectorTransport
open QuantumState

private lemma rpow_apply_eigenvector_clm_support {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT : 0 ≤ T) (p : ℝ) (v : ℋ) (μ : ℝ)
    (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    CFC.rpow T p v = (algebraMap ℝ ℂ (μ ^ p)) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) := RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  letI : IsScalarTower ℝ ℂ (L ℋ) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  have hμL : μ ∈ spectrum ℝ (T : L ℋ) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)] at hμ ⊢
    simpa only [ContinuousLinearMap.spectrum_eq] using hμ
  have hp := congrArg (fun A : B ℋ => A v)
    (CFCTransport.cfc_rpow_toCLM (T : L ℋ) p)
  change CFC.rpow (T : L ℋ) p v = CFC.rpow T p v at hp
  rw [← hp]
  exact TensorCFC.rpow_apply_eigenvector_linear (T : L ℋ)
    ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hT) p v μ hv hμL

end EigenvectorTransport

/-!
# Non-negative sandwiched Rényi divergence: continuity

Continuity of rpow and sandwiched quasi-entropy on non-negative cones,
boundary continuity, and CFC eigenvector formulas.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

private lemma continuity_toCLM_toLinearMap
    {ℋ : Type u} [Qudit ℋ] (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

private lemma continuity_rpow_toContinuousLinearMap
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  letI : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower ℝ≥0 ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eNN : L ℋ ≃ₐ[ℝ≥0] B ℋ := e.toAlgEquiv.restrictScalars ℝ≥0
  change e (cfc (fun x : ℝ≥0 => x ^ p) A) = cfc (fun x : ℝ≥0 => x ^ p) (e A)
  by_cases hA : 0 ≤ A
  · have heA : (0 : B ℋ) ≤ e A := by
      exact (ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mp hA
    by_cases hf : ContinuousOn (fun x : ℝ≥0 => x ^ p) (spectrum ℝ≥0 A)
    · exact StarAlgHomClass.map_cfc (R := ℝ≥0) (S := ℂ) e _ A hf
        (StarAlgEquiv.isometry e).continuous hA heA
    · have hf' : ¬ ContinuousOn (fun x : ℝ≥0 => x ^ p)
          (spectrum ℝ≥0 (e A)) := by
        rw [show e A = eNN A from rfl, AlgEquiv.spectrum_eq eNN A]
        exact hf
      rw [cfc_apply_of_not_continuousOn A hf,
        cfc_apply_of_not_continuousOn (e A) hf', map_zero]
  · have heA : ¬ (0 : B ℋ) ≤ e A := by
      intro heA
      exact hA ((ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mpr heA)
    rw [cfc_apply_of_not_predicate A hA,
      cfc_apply_of_not_predicate (e A) heA, map_zero]

private lemma continuity_rpow_toLinearMap
    {ℋ : Type u} [Qudit ℋ] (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := continuity_rpow_toContinuousLinearMap (A : L ℋ) p
  rw [continuity_toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

private lemma continuity_sandwichedQuasi_eq_clm_direct
    {ℋ : Type u} [Qudit ℋ] (a : ℝ) (rho sigma : B ℋ) :
    sandwichedQuasi a (rho : L ℋ) (sigma : L ℋ) =
      Tr ((CFC.rpow
        (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
          CFC.rpow sigma ((1 - a) / (2 * a))) a : B ℋ) : L ℋ) := by
  rw [sandwichedQuasi_eq_direct]
  change Tr (CFC.rpow
      (CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a)) * (rho : L ℋ) *
        CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a))) a) =
    Tr ((CFC.rpow
      (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
        CFC.rpow sigma ((1 - a) / (2 * a))) a : B ℋ) : L ℋ)
  rw [continuity_rpow_toLinearMap]
  change _ = Tr (CFC.rpow
    (((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ) * (rho : L ℋ) *
      ((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ)) a)
  rw [continuity_rpow_toLinearMap]

/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/

/-- For non-negative `ρ, σ`, the conjugate `σ^β ρ σ^β` is non-negative. -/
private lemma rpow_conj_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (β : ℝ) {ρ σ : B ℋ}
    (hρ : 0 ≤ ρ) (_hσ : 0 ≤ σ) :
    (0 : B ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β :=
  conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg

/-- Continuity of `(ρ, σ) ↦ σ^β ρ σ^β` on the non-negative cone, for `β ≥ 0`. -/
private lemma rpow_conj_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {β : ℝ} (hβ : 0 ≤ β) :
    ContinuousOn (fun p : B ℋ × B ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) := by
  have h_rpow_snd : ContinuousOn (fun p : B ℋ × B ℋ => CFC.rpow p.2 β)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) :=
    (continuousOn_rpow_nonneg hβ).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : B ℋ × B ℋ => p.1)
      ({A : B ℋ | 0 ≤ A} ×ˢ {A : B ℋ | 0 ≤ A}) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

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
  have hcont := continuousOn_sandwichedQuasi_re_nonneg_lm (𝒦 := ℋ) hα0 hα1
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
lemma tendsto_sandwichedRenyiDiv_nonneg_of_lt_one
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
lemma continuousWithinAt_sandwichedRenyiDiv_of_lt_one
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ₀ σ₀ : L ℋ}
    (hρ₀ : 0 ≤ ρ₀) (hσ₀ : 0 ≤ σ₀)
    (hQ : (sandwichedQuasi α ρ₀ σ₀).re ≠ 0)
    (hTr : (Tr ρ₀).re ≠ 0) :
    ContinuousWithinAt (fun p : L ℋ × L ℋ =>
      sandwichedRenyiDiv α p.1 p.2)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) := by
  have hcont := continuousOn_sandwichedQuasi_re_nonneg_lm (𝒦 := ℋ) hα0 hα1.le
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

/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/
@[deprecated (since := "2026-09-05")]
alias cfc_real_apply_eigenvector := TensorCFC.cfc_real_apply_eigenvector

@[deprecated (since := "2026-09-05")]
alias mem_spectrum_real_of_eigenvector := TensorCFC.mem_spectrum_real_of_eigenvector

/-- Convergence on every vector of an orthonormal basis implies convergence of
continuous endomorphisms in finite dimension. -/
lemma tendsto_continuousLinearMap_of_apply_orthonormalBasis
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ ℋ)
    {X : Type*} {l : Filter X}
    (T : X → B ℋ)
    (T₀ : B ℋ)
    (hT : ∀ i,
      Filter.Tendsto
        (fun x => T x (b i))
        l
        (nhds (T₀ (b i)))) :
    Filter.Tendsto T l (nhds T₀) := by
  rw [QuantumChannel.continuousLinearMap_eq_sum_outer_product b T₀]
  have hfun : T = fun x => ∑ i : ι,
      (outer_product (b i) (T x (b i))).toContinuousLinearMap :=
    funext fun x => QuantumChannel.continuousLinearMap_eq_sum_outer_product b (T x)
  rw [hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((QuantumChannel.continuous_outerL (b i)).tendsto _).comp (hT i)

/-- Along a convergent eigenvalue path, the product of two real rpow coefficients
converges at every pair of nonzero limiting eigenvalues. -/
lemma tendsto_rpow_pair_coeff
    {X ι : Type*} {l : Filter X}
    {μ : ι → ℝ} {ν : X → ι → ℝ} {β : ℝ}
    (hν : ∀ k,
      Filter.Tendsto (fun x => ν x k) l (nhds (μ k)))
    (w : X → ℂ)
    (hw : Filter.Tendsto w l (nhds 1))
    {i j : ι}
    (hi : μ i ≠ 0) (hj : μ j ≠ 0)
    (z : ℂ) :
    Filter.Tendsto
      (fun x =>
        w x *
          ((((ν x i) ^ β * (ν x j) ^ β : ℝ) : ℂ)) *
          z)
      l
      (nhds
        (((((μ i) ^ β * (μ j) ^ β : ℝ) : ℂ)) * z)) := by
  have hi_rpow : Filter.Tendsto (fun x => (ν x i) ^ β) l (nhds ((μ i) ^ β)) :=
    ((Real.continuousAt_rpow_const (μ i) β (Or.inl hi)).tendsto).comp (hν i)
  have hj_rpow : Filter.Tendsto (fun x => (ν x j) ^ β) l (nhds ((μ j) ^ β)) :=
    ((Real.continuousAt_rpow_const (μ j) β (Or.inl hj)).tendsto).comp (hν j)
  have hpair := (Complex.continuous_ofReal.tendsto _).comp (hi_rpow.mul hj_rpow)
  simpa using (hw.mul hpair).mul_const z

/-- If a positive eigenvalue path is bounded below by `t * cσ`, then its
singular rpow-square contribution is squeezed to zero. -/
lemma tendsto_singular_rpow_sq
    {β γ cσ cρ : ℝ}
    (h2β : 2 * β ≤ 0)
    (hγ : 1 + 2 * β = γ)
    (hγpos : 0 < γ)
    (hcσ : 0 < cσ)
    (hcρ : 0 ≤ cρ)
    (ν : ℝ → ℝ)
    (hν :
      ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        t * cσ ≤ ν t) :
    Filter.Tendsto
      (fun t : ℝ =>
        (((t * cρ * ((ν t) ^ β) ^ 2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hg : Filter.Tendsto (fun t : ℝ => cρ * cσ ^ (2 * β) * t ^ γ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hgc : Filter.Tendsto (fun t : ℝ => t ^ γ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h0 := (Real.continuousAt_rpow_const 0 γ (Or.inr hγpos.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hγpos)] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    simpa using hgc.const_mul (cρ * cσ ^ (2 * β))
  have hreal : Filter.Tendsto (fun t : ℝ => t * cρ * ((ν t) ^ β) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply squeeze_zero' (f := fun t => t * cρ * ((ν t) ^ β) ^ 2)
      (g := fun t => cρ * cσ ^ (2 * β) * t ^ γ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_nonneg (mul_nonneg ht.le hcρ) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, hν] with t ht hνt
      have htcσ : 0 < t * cσ := mul_pos ht hcσ
      have hνpos : 0 < ν t := lt_of_lt_of_le htcσ hνt
      have hsq : ((ν t) ^ β) ^ 2 = (ν t) ^ (2 * β) := by
        rw [← Real.rpow_natCast ((ν t) ^ β) 2, ← Real.rpow_mul hνpos.le]
        ring_nf
      rw [hsq]
      have hle : (ν t) ^ (2 * β) ≤ (t * cσ) ^ (2 * β) :=
        Real.rpow_le_rpow_of_nonpos htcσ hνt h2β
      have htpow : t * t ^ (2 * β) = t ^ γ := by
        rw [← hγ, Real.rpow_add ht, Real.rpow_one]
      calc
        t * cρ * (ν t) ^ (2 * β) ≤ t * cρ * (t * cσ) ^ (2 * β) :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg ht.le hcρ)
        _ = cρ * cσ ^ (2 * β) * t ^ γ := by
          rw [Real.mul_rpow ht.le hcσ.le, ← htpow]
          ring
    · exact hg
  have hcomp := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp

/-- Action of a diagonal-rpow/affine/diagonal-rpow sandwich on a vector of the
fixed eigenbasis. -/
lemma rpow_conj_affine_apply_eigenbasis
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ ℋ)
    {P B : ℋ →L[ℂ] ℋ}
    (hP : 0 ≤ P)
    (μ : ι → ℝ)
    (hPb : ∀ k, P (b k) = (μ k : ℂ) • b k)
    (β w d : ℝ) (i : ι) :
    (CFC.rpow P β *
        (((w : ℂ) • B) + ((d : ℂ) • (1 : ℋ →L[ℂ] ℋ))) *
        CFC.rpow P β) (b i) =
      (∑ j : ι,
        (((w : ℂ) *
            ((((μ i) ^ β * (μ j) ^ β : ℝ) : ℂ)) *
            inner ℂ (b j) (B (b i))) • b j)) +
        (((d * ((μ i) ^ β) ^ 2 : ℝ) : ℂ) • b i) := by
  have hb_ne : ∀ k, b k ≠ 0 := fun k => b.orthonormal.ne_zero k
  have hspec : ∀ k, μ k ∈ spectrum ℝ P :=
    fun k => TensorCFC.mem_spectrum_real_of_eigenvector (hb_ne k) (hPb k)
  have hSb : ∀ k, CFC.rpow P β (b k) = (((μ k) ^ β : ℝ) : ℂ) • b k :=
    fun k => rpow_apply_eigenvector_clm_support P hP β (b k) (μ k)
      (hPb k) (hspec k)
  have hSB : CFC.rpow P β (B (b i)) =
      ∑ j, ((((μ j) ^ β : ℝ) : ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    conv_lhs =>
      rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from
        (b.sum_repr' (B (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hSb j, smul_smul]
    congr 1
    ring
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hSb i,
      map_smul, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_add, map_smul, map_smul, hSB, hSb i,
      smul_add]
  congr 1
  · rw [smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast
    ring
  · rw [smul_smul, smul_smul]
    congr 1
    push_cast
    ring

/-- **Operator convergence under `SupportLE` (α > 1).**
    `(σ+εI)^β (ρ+εI) (σ+εI)^β → σ^β ρ σ^β` as `ε → 0⁺`, where `β =
      (1-α)/(2α) < 0`.
    The pseudo-inverse blow-up of `(σ+εI)^β` on `ker σ` is killed because `ρ` vanishes
    there (`SupportLE`); the residual `εI`-contribution on `ker σ` scales as `ε^{1/α} → 0`. -/
private lemma rpow_conj_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : B ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE
      (ρ : L ℋ)
      (σ : L ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ + (ε:ℂ)•(1:B ℋ)) ((1-α)/(2*α)) * (ρ +
        (ε:ℂ)•(1:B ℋ))
        * CFC.rpow (σ + (ε:ℂ)•(1:B ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow σ ((1-α)/(2*α)) * ρ * CFC.rpow σ ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  have hρ_sym : ρ.IsSymmetric :=
    ((ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ):ℂ) • b i :=
    hσ_sym.apply_eigenvectorBasis hn
  change LinearMap.ker (σ : L ℋ) ≤ LinearMap.ker (ρ : L ℋ) at hsupp
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (ρ (b i)) =
    (0:ℂ) := by
    exact fun i j hij =>
      QuantumChannel.inner_apply_eq_zero_of_ker_le hρ_sym b eig h_eig_apply hsupp hij
  have hM0 : ∀ i, (CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
    intro i; simpa using rpow_conj_affine_apply_eigenbasis b hσ eig h_eig_apply β 1 0 i
  have hMε : ∀ (ε : ℝ), 0 < ε → ∀ i,
      (CFC.rpow (σ + (ε:ℂ)•(1:B ℋ)) β * (ρ + (ε:ℂ)•(1:B ℋ)) * CFC.rpow (σ +
        (ε:ℂ)•(1:B ℋ)) β) (b i)
      = (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i := by
    intro ε hε i
    have hσε_nn : (0:B ℋ) ≤ σ + (ε:ℂ)•(1:B ℋ) :=
      add_nonneg hσ (smul_nonneg (Complex.zero_le_real.mpr hε.le) zero_le_one)
    have hσε_app : ∀ k, (σ + (ε:ℂ)•(1:B ℋ)) (b k) = ((eig k + ε : ℝ):ℂ) • b
      k := by
      intro k
      rw [ContinuousLinearMap.add_apply, h_eig_apply k, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, ← add_smul]
      push_cast; ring_nf
    simpa using rpow_conj_affine_apply_eigenbasis b hσε_nn
      (fun k => eig k + ε) hσε_app β 1 ε i
  have h_eig_tendsto : ∀ k,
      Filter.Tendsto (fun ε : ℝ => eig k + ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun ε : ℝ => eig k + ε) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hextra : ∀ i, Filter.Tendsto (fun ε : ℝ => (((ε * ((eig i+ε)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    simpa using tendsto_singular_rpow_sq
      (β := β) (γ := 1 / α) (cσ := 1) (cρ := 1)
      (by linarith [hβneg]) h2β (one_div_pos.mpr hαpos) one_pos zero_le_one
      (fun ε => eig i + ε)
      (by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        linarith [h_eig_nn i])
  have key : ∀ i, Filter.Tendsto
      (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:B ℋ)) β * (ρ + (ε:ℂ)•(1:B ℋ)) *
        CFC.rpow (σ +
        (ε:ℂ)•(1:B ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i))) := by
    intro i
    rw [hM0 i]
    have hEq : (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:B ℋ)) β * (ρ +
      (ε:ℂ)•(1:B ℋ)) * CFC.rpow (σ
      + (ε:ℂ)•(1:B ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε => (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ
          (b i))) • b j)
          + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMε ε hε i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
          + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · obtain ⟨hi, hj⟩ := not_or.mp hzero
        have hsc : Filter.Tendsto (fun ε : ℝ => ((((eig i+ε)^β * (eig j+ε)^β :
          ℝ)):ℂ) * inner ℂ
          (b j) (ρ (b i)))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (((((eig i)^β * (eig j)^β : ℝ)):ℂ) * inner
              ℂ (b j)
              (ρ (b i)))) := by
          simpa using tendsto_rpow_pair_coeff
            (μ := eig) (ν := fun ε k => eig k + ε) h_eig_tendsto
            (fun _ : ℝ => (1 : ℂ)) tendsto_const_nhds hi hj
            (inner ℂ (b j) (ρ (b i)))
        exact hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  exact tendsto_continuousLinearMap_of_apply_orthonormalBasis b _ _ key

/-- **Boundary-continuity of `sandwichedQuasi` (α > 1) under `SupportLE`.** Under the support
    condition, `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as `ε → 0⁺`. The
      pseudo-inverse blow-up of
    `(σ+εI)^β` (β < 0) on `ker σ` is killed by `SupportLE` (`rpow_conj_tendsto_of_suppLE`); the
    outer `Tr(·^α)` is continuous on the non-negative cone (`α > 0`). -/
private lemma sandwichedQuasi_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : (ℋ →L[ℂ] ℋ)} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE
      (ρ : L ℋ)
      (σ : L ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedQuasi α
        ((ρ + (ε : ℂ) • (1 : (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) : L ℋ)
        ((σ + (ε : ℂ) • (1 : (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) : L ℋ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α
        (ρ : L ℋ)
        (σ : L ℋ))) := by
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  have hM := rpow_conj_tendsto_of_suppLE hα_gt hρ hσ hsupp
  have hMnn : ∀ A B : (ℋ →L[ℂ] ℋ), 0 ≤ B → (0:(ℋ →L[ℂ] ℋ)) ≤ CFC.rpow A
    β * B * CFC.rpow A β :=
    fun A B hB => conjugate_nonneg_of_nonneg hB CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : (ℋ →L[ℂ] ℋ) =>
      traceCLM (CFC.rpow X α))
      {X : (ℋ →L[ℂ] ℋ) | 0 ≤ X}
      (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
    have h1 : ContinuousOn (fun X : (ℋ →L[ℂ] ℋ) => CFC.rpow X α) {X : (ℋ →L[ℂ]
      ℋ) | 0 ≤ X} :=
      continuousOn_rpow_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : (ℋ →L[ℂ] ℋ) => traceCLM A) :=
      traceCLM.continuous
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn σ ρ hρ)
  have hMwithin : Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ+(ε:ℂ)•(1:(ℋ →L[ℂ] ℋ))) β *
        (ρ+(ε:ℂ)•(1:(ℋ →L[ℂ] ℋ))) * CFC.rpow
        (σ+(ε:ℂ)•(1:(ℋ →L[ℂ] ℋ))) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow σ β * ρ * CFC.rpow σ β) {X : (ℋ →L[ℂ] ℋ) | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε1 : (0:(ℋ →L[ℂ] ℋ)) ≤ (ε:ℂ)•(1:(ℋ →L[ℂ] ℋ)) :=
      smul_nonneg (Complex.zero_le_real.mpr (le_of_lt hε)) zero_le_one
    exact hMnn _ _ (add_nonneg hρ hε1)
  have hcomp := Filter.Tendsto.comp hcont hMwithin
  rw [hβ] at hcomp
  have hfun :
      (fun ε : ℝ => sandwichedQuasi α
        (ContinuousLinearMap.toLinearMap
          (ρ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)))
        (ContinuousLinearMap.toLinearMap
          (σ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)))) =
      (fun ε : ℝ => traceCLM (CFC.rpow
        (CFC.rpow (σ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)) ((1 - α) / (2 * α)) *
          (ρ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)) *
          CFC.rpow (σ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)) ((1 - α) / (2 * α))) α)) := by
    funext ε
    simpa [traceCLM] using
      (continuity_sandwichedQuasi_eq_clm_direct α
        (ρ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ))
        (σ + (ε : ℂ) • (1 : ℋ →L[ℂ] ℋ)))
  have hlim : sandwichedQuasi α
      (ContinuousLinearMap.toLinearMap ρ)
      (ContinuousLinearMap.toLinearMap σ) =
      traceCLM (CFC.rpow
        (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
          CFC.rpow σ ((1 - α) / (2 * α))) α) :=
    by simpa [traceCLM] using
      (continuity_sandwichedQuasi_eq_clm_direct α ρ σ)
  rw [hfun, hlim]
  exact hcomp

/-- **Zero criterion for the sandwiched quasi-entropy.** For `0 < α` and `ρ ≥ 0`,
    the real part of the quasi-entropy vanishes iff the conjugated operator does:
    `Q_α(ρ‖σ).re = 0 ↔ σ^β ρ σ^β = 0`, where `β = (1−α)/(2α)`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
lemma sandwichedQuasi_re_eq_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) :
    (sandwichedQuasi α ρ σ).re = 0 ↔
      CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) = 0 := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  set M : L ℋ := CFC.rpow σ β * ρ * CFC.rpow σ β with hM
  have hM_nn : (0 : L ℋ) ≤ M :=
    conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hMα_nn : (0 : L ℋ) ≤ CFC.rpow M α := CFC.rpow_nonneg
  have hQ_eq : sandwichedQuasi α ρ σ = Tr (CFC.rpow M α) := by
    rw [sandwichedQuasi_eq_direct]
  rw [hQ_eq]
  constructor
  · intro htr
    have hMα0 : CFC.rpow M α = 0 := by
      by_contra hne
      exact absurd htr (ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hMα_nn hne))
    have hαinv : α * (1 / α) = 1 := by rw [mul_one_div, div_self (ne_of_gt hα0)]
    have hcomp : CFC.rpow (CFC.rpow M α) (1 / α) = M := by
      have key := CFC.rpow_rpow_of_exponent_nonneg M α (1 / α) hα0.le (by positivity) hM_nn
      rw [hαinv, CFC.rpow_one M hM_nn] at key
      exact key
    rw [hMα0, CFC.zero_rpow (one_div_ne_zero (ne_of_gt hα0))] at hcomp
    exact hcomp.symm
  · intro hM0
    rw [hM0, CFC.zero_rpow (ne_of_gt hα0)]
    simp

/-- Continuous-linear endpoint helper used by the spectral support argument below. -/
private lemma sandwichedQuasi_re_eq_zero_iff_clm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : B ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re = 0 ↔
      CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) = 0 := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  set M : B ℋ := CFC.rpow σ β * ρ * CFC.rpow σ β with hM
  have hM_nn : (0 : B ℋ) ≤ M := rpow_conj_nonneg β hρ hσ
  have hMα_nn : (0 : B ℋ) ≤ CFC.rpow M α := CFC.rpow_nonneg
  have hQ_eq : sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ) =
      Tr ((CFC.rpow M α : B ℋ) : L ℋ) := by
    rw [continuity_sandwichedQuasi_eq_clm_direct]
  rw [hQ_eq]
  constructor
  · intro htr
    have hMα0 : CFC.rpow M α = 0 := by
      by_contra hne
      exact absurd htr (ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero
        ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hMα_nn)
        (fun h => hne (by ext x; exact congrArg (fun A : L _ => A x) h))))
    have hαinv : α * (1 / α) = 1 := by rw [mul_one_div, div_self (ne_of_gt hα0)]
    have hcomp : CFC.rpow (CFC.rpow M α) (1 / α) = M := by
      have key := CFC.rpow_rpow_of_exponent_nonneg M α (1 / α) hα0.le (by positivity) hM_nn
      rw [hαinv, CFC.rpow_one M hM_nn] at key
      exact key
    rw [hMα0, CFC.zero_rpow (one_div_ne_zero (ne_of_gt hα0))] at hcomp
    exact hcomp.symm
  · intro hM0
    rw [hM0, CFC.zero_rpow (ne_of_gt hα0)]
    simp

/-- Matrix coefficient of a conjugated operator on two eigenvectors. -/
private lemma inner_rpow_conj_of_eigenvectors
    {ℋ : Type u} [Qudit ℋ] {β : ℝ} {ρ σ : B ℋ}
    {u v : ℋ} {a b : ℝ}
    (hu : CFC.rpow σ β u = ((a : ℝ) : ℂ) • u)
    (hv : CFC.rpow σ β v = ((b : ℝ) : ℂ) • v)
    (hsym : (CFC.rpow σ β).IsSymmetric) :
    inner ℂ v ((CFC.rpow σ β * ρ * CFC.rpow σ β) u) =
      ((a : ℝ) : ℂ) * ((b : ℝ) : ℂ) * inner ℂ v (ρ u) := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hu,
      map_smul, map_smul, inner_smul_right,
      show inner ℂ v (CFC.rpow σ β (ρ u)) =
        inner ℂ (CFC.rpow σ β v) (ρ u) from (hsym v (ρ u)).symm,
      hv, inner_smul_left, Complex.conj_ofReal]
  ring

/-- `CFC.rpow` acts diagonally on a supplied orthonormal eigenbasis. -/
private lemma rpow_apply_eigenbasis
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {n : ℕ}
    {β : ℝ} {σ : B ℋ} (hσ : 0 ≤ σ)
    (b : OrthonormalBasis (Fin n) ℂ ℋ) (eig : Fin n → ℝ)
    (h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i) :
    ∀ i, CFC.rpow σ β (b i) = (((eig i) ^ β : ℝ) : ℂ) • b i := by
  intro i
  exact rpow_apply_eigenvector_clm_support σ hσ β (b i) (eig i) (h_eig_apply i)
    (TensorCFC.mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (h_eig_apply i))

/-- Non-kernel matrix coefficients vanish when the conjugated power vanishes. -/
private lemma inner_eq_zero_of_rpow_conj_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {n : ℕ}
    {β : ℝ} {ρ σ : B ℋ} (hσ : 0 ≤ σ)
    (b : OrthonormalBasis (Fin n) ℂ ℋ) (eig : Fin n → ℝ)
    (h_eig_nn : ∀ i, 0 ≤ eig i)
    (h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i)
    (h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) →
      inner ℂ (b j) (ρ (b i)) = (0 : ℂ))
    (hzre : CFC.rpow σ β * ρ * CFC.rpow σ β = 0) :
    ∀ i k, inner ℂ (b k) (ρ (b i)) = (0 : ℂ) := by
  have hS0b : ∀ i, CFC.rpow σ β (b i) = (((eig i) ^ β : ℝ) : ℂ) • b i :=
    rpow_apply_eigenbasis hσ b eig h_eig_apply
  have hS_nn : (0 : B ℋ) ≤ CFC.rpow σ β := CFC.rpow_nonneg
  have hSsym : (CFC.rpow σ β).IsSymmetric :=
    (IsSelfAdjoint.of_nonneg hS_nn).isSymmetric
  have hcoeff : ∀ i k, inner ℂ (b k) ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)) =
      (((eig i) ^ β : ℝ) : ℂ) * (((eig k) ^ β : ℝ) : ℂ) *
        inner ℂ (b k) (ρ (b i)) :=
    fun i k => inner_rpow_conj_of_eigenvectors (hS0b i) (hS0b k) hSsym
  intro i k
  by_cases h : eig i = 0 ∨ eig k = 0
  · exact h_supp_zero i k h
  · push_neg at h
    have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm h.1)
    have hk' : 0 < eig k := lt_of_le_of_ne (h_eig_nn k) (Ne.symm h.2)
    have hc := hcoeff i k
    rw [hzre, ContinuousLinearMap.zero_apply, inner_zero_right] at hc
    have hne : (((eig i) ^ β : ℝ) : ℂ) * (((eig k) ^ β : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_mul]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos
        (Real.rpow_pos_of_pos hi' β) (Real.rpow_pos_of_pos hk' β)))
    exact (mul_eq_zero.mp hc.symm).resolve_left hne

/-- An operator whose matrix coefficients vanish in an orthonormal basis is zero. -/
private lemma continuousLinearMap_eq_zero_of_inner_basis
    {ℋ : Type u} [Qudit ℋ] {n : ℕ} (ρ : B ℋ)
    (b : OrthonormalBasis (Fin n) ℂ ℋ)
    (hzero : ∀ i k, inner ℂ (b k) (ρ (b i)) = (0 : ℂ)) : ρ = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.zero_apply]
  conv_lhs => rw [← b.sum_repr' x]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul,
      show ρ (b i) = ∑ k, inner ℂ (b k) (ρ (b i)) • b k from
        (b.sum_repr' (ρ (b i))).symm]
  rw [show (∑ k, inner ℂ (b k) (ρ (b i)) • b k) = 0 from
      Finset.sum_eq_zero fun k _ => by rw [hzero i k, zero_smul]]
  rw [smul_zero]

/-- **Support-overlap ⟹ `Q_α ≠ 0` (α > 1).** Under `SupportLE ρ σ` with `ρ ≠ 0`, the
    quasi-entropy is non-zero. Indeed `Q_α.re = 0 ⟺ σ^β ρ σ^β = 0`; expanding in the
    eigenbasis of `σ`, this forces `⟨b_k, ρ b_i⟩ = 0` for all `i, k` (using `SupportLE` to
    kill the `ker σ` directions and positivity of `eigᵢ^β` elsewhere), hence `ρ = 0`,
    contradicting `ρ ≠ 0`. -/
private lemma sandwichedQuasi_re_ne_zero_of_suppLE_clm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : B ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE
      (ρ : L ℋ)
      (σ : L ℋ))
    (hρ0 : ρ ≠ 0) :
    (sandwichedQuasi α
      (ρ : L ℋ)
      (σ : L ℋ)).re ≠ 0 := by
  intro hzre
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  rw [sandwichedQuasi_re_eq_zero_iff_clm hαpos hρ hσ] at hzre
  apply hρ0
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  have hρ_sym : ρ.IsSymmetric :=
    ((ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ):ℂ) • b i :=
    hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → ρ (b k) = 0 :=
    fun k hk => hsupp (LinearMap.mem_ker.mpr (by
      change σ (b k) = 0
      rw [h_eig_apply k, hk]
      simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (ρ (b i)) =
    (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (ρ (b i)) = inner ℂ (ρ (b j)) (b i) from (hρ_sym (b j) (b
      i)).symm,
          h_ker j hj]; simp
  have hzero_all := inner_eq_zero_of_rpow_conj_eq_zero hσ b eig h_eig_nn
    h_eig_apply h_supp_zero hzre
  exact continuousLinearMap_eq_zero_of_inner_basis ρ b hzero_all

/-- **Support-overlap ⟹ `Q_α ≠ 0` (α > 1)** at the linear-map endpoint. -/
lemma sandwichedQuasi_re_ne_zero_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) (hρ0 : ρ ≠ 0) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  have hρc : (0 : B ℋ) ≤ ρ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hρ)
  have hσc : (0 : B ℋ) ≤ σ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hσ)
  have hρ0c : ρ.toContinuousLinearMap ≠ 0 := by
    intro h
    apply hρ0
    exact LinearMap.toContinuousLinearMap.injective h
  simpa using sandwichedQuasi_re_ne_zero_of_suppLE_clm hα_gt hρc hσc hsupp hρ0c

/-- Continuity of `Tr` on perturbed states: `Tr(ρ + εI) → Tr ρ` as `ε → 0+`. -/
private lemma trace_tendsto_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) :
    Filter.Tendsto
      (fun ε : ℝ => Tr (ρ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ)) := by
  have hpath : Filter.Tendsto
      (fun ε : ℝ => ρ + (ε : ℂ) • (1 : L ℋ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ρ) := by
    have hcont : Continuous
        (fun ε : ℝ => ρ + (ε : ℂ) • (1 : L ℋ)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have htrace : Continuous (fun A : L ℋ => Tr A) := by fun_prop
  exact (htrace.tendsto ρ).comp hpath

/-- **Boundary-continuity** of `sandwichedRenyiDiv` for non-negative `ρ, σ` with `SupportLE
  ρ σ`,
    `α > 1`, and `ρ ≠ 0`.

    Derived from `sandwichedQuasi_tendsto_of_suppLE` (continuity of the quasi-relative
    entropy under `SupportLE`), continuity of `Tr`, and continuity of `log`. Under `ρ ≠ 0` the
    denominator `(Tr ρ).re > 0` (`trace_re_pos_of_ne_zero`) and, under `SupportLE`, the numerator
    `Q_α(ρ‖σ).re ≠ 0` (`sandwichedQuasi_re_ne_zero_of_suppLE`), so the limiting quotient is a
    continuity point of `log`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
lemma tendsto_sandwichedRenyiDiv_of_supportLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ)
    (hρ0 : ρ ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α
        (ρ + (ε : ℂ) • (1 : L ℋ))
        (σ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have h_tr : (Tr ρ).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0)
  have h_Q : (sandwichedQuasi α ρ σ).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hρ hσ hsupp hρ0
  -- (1) `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as ε → 0+ (deep step under `SupportLE`).
  have hQ : Filter.Tendsto
      (fun ε : ℝ =>
        (sandwichedQuasi α
          (ρ + (ε : ℂ) • (1 : L ℋ))
          (σ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
    have hρc : (0 : B ℋ) ≤ ρ.toContinuousLinearMap :=
      (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hρ)
    have hσc : (0 : B ℋ) ≤ σ.toContinuousLinearMap :=
      (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hσ)
    have hQ_C := sandwichedQuasi_tendsto_of_suppLE hα_gt hρc hσc hsupp
    simpa using (Complex.continuous_re.tendsto _).comp hQ_C
  -- (2) `Tr(ρ+εI) → Tr ρ` (immediate, linear).
  have hT : Filter.Tendsto
      (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ).re) :=
    (Complex.continuous_re.tendsto _).comp (trace_tendsto_perturbed (ℋ := ℋ) ρ)
  -- (3)+(4) Quotient and `log`: continuous since both limits are nonzero.
  exact ((Real.continuousAt_log (div_ne_zero h_Q h_tr)).tendsto.comp
    (Filter.Tendsto.div hQ hT h_tr)).const_mul _

end SandwichedRenyiRelativeEntropy
