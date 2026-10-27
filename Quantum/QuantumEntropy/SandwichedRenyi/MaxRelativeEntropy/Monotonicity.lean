/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.MaxRelativeEntropy.Defs
import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Monotonicity
import Quantum.QuantumEntropy.CFCTransport

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
# Max-relative entropy: characterization and data processing

The order-theoretic characterization and the two existing max-relative
monotonicity theorems.  Their public names and statements are unchanged.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

section MaxRelEntropy

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-! ### α = ∞ : the order-theoretic characterization and the data-processing inequality

`maxRelEntropyNN` is *defined* via the explicit Frank–Lieb formula
`D_∞(ρ‖σ) = log ‖σ^{-1/2} ρ σ^{-1/2}‖` [arXiv:1306.5358]. Here we prove it equals the
order-theoretic form `log inf{λ ≥ 0 : ρ ≤ λ σ}` (`maxRelEntropyNN_eq_log_sInf`), and use
that characterization to prove the data-processing inequality (Theorem 1, `α = ∞`). -/

omit [Nontrivial ℋ] in
/-- `CFC.rpow σ y` as a real continuous-functional-calculus expression. -/
private lemma rpow_eq_cfc_aux {σ : L ℋ} (hσ : 0 ≤ σ) (y : ℝ) :
    CFC.rpow σ y = cfc (fun x : ℝ => x ^ y) σ := by
  rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real hσ

omit [Nontrivial ℋ] in
section

private lemma spectrum_real_finite_lm (σ : L ℋ) : Set.Finite (spectrum ℝ σ) := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)]
  exact (Module.End.finite_spectrum σ).preimage
    (fun _ _ _ _ h => RCLike.ofReal_injective h)

/-- Product of two real powers of `σ`, merged into a single `cfc`
    (valid even at singular `σ`, since the real spectrum is finite hence discrete). -/
private lemma rpow_mul_rpow_cfc {σ : L ℋ} (hσ : 0 ≤ σ) (a b : ℝ) :
    CFC.rpow σ a * CFC.rpow σ b = cfc (fun x : ℝ => x ^ a * x ^ b) σ := by
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ σ) :=
    fun g => (spectrum_real_finite_lm σ).continuousOn g
  rw [rpow_eq_cfc_aux hσ a, rpow_eq_cfc_aux hσ b]
  exact (cfc_mul _ _ σ (hcont _) (hcont _)).symm

/-- Product of three real powers of `σ`, merged into a single `cfc`. -/
private lemma rpow_mul_rpow_mul_rpow_cfc {σ : L ℋ} (hσ : 0 ≤ σ) (a b c : ℝ) :
    CFC.rpow σ a * CFC.rpow σ b * CFC.rpow σ c
      = cfc (fun x : ℝ => x ^ a * x ^ b * x ^ c) σ := by
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ σ) :=
    fun g => (spectrum_real_finite_lm σ).continuousOn g
  rw [rpow_mul_rpow_cfc hσ a b, rpow_eq_cfc_aux hσ c]
  exact (cfc_mul _ _ σ (hcont _) (hcont _)).symm

/-- `σ^{1/2} · σ^{1/2} = σ`. -/
private lemma rpow_half_sq {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (1/2) * CFC.rpow σ (1/2) = σ := by
  rw [rpow_mul_rpow_cfc hσ]
  have hfun : (spectrum ℝ σ).EqOn (fun x : ℝ => x ^ (1/2:ℝ) * x ^ (1/2:ℝ)) (fun x :
    ℝ => x) := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
    change x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (1/2:ℝ) ≠ 0 by norm_num), mul_zero]
    · rw [← Real.rpow_add hpos, show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one]
  rw [cfc_congr hfun, cfc_id' ℝ σ]

/-- `σ^{1/2}` and `σ^{-1/2}` commute. -/
private lemma rpow_half_mul_rpow_neg_comm {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)) = CFC.rpow σ (-(1/2)) * CFC.rpow σ (1/2) := by
  rw [rpow_mul_rpow_cfc hσ, rpow_mul_rpow_cfc hσ]
  exact cfc_congr (fun x _ => mul_comm _ _)

/-- `σ · (σ^{1/2} · σ^{-1/2}) = σ`: the support projection fixes `σ`. -/
private lemma self_mul_rpow_half_mul_rpow_neg {σ : L ℋ} (hσ : 0 ≤ σ) :
    σ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) = σ := by
  rw [← mul_assoc]
  nth_rewrite 1 [show σ = CFC.rpow σ (1:ℝ) from
    (CFC.rpow_one σ hσ).symm]
  rw [rpow_mul_rpow_mul_rpow_cfc hσ]
  have hfun : (spectrum ℝ σ).EqOn
      (fun x : ℝ => x ^ (1:ℝ) * x ^ (1/2:ℝ) * x ^ (-(1/2):ℝ)) (fun x : ℝ => x) := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
    change x ^ (1:ℝ) * x ^ (1/2:ℝ) * x ^ (-(1/2):ℝ) = x
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (1:ℝ) ≠ 0 by norm_num),
        Real.zero_rpow (show (1/2:ℝ) ≠ 0 by norm_num),
        Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num)]
      ring
    · rw [← Real.rpow_add hpos, ← Real.rpow_add hpos,
        show (1:ℝ) + 1/2 + (-(1/2)) = 1 by norm_num, Real.rpow_one]
  rw [cfc_congr hfun, cfc_id' ℝ σ]

/-- `σ^{-1/2} · σ · σ^{-1/2} ≤ 1`: the conjugate of `σ` by `σ^{-1/2}` is a projection. -/
private lemma rpow_neg_conj_self_le_one {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2)) ≤ 1 := by
  nth_rewrite 2 [show σ = CFC.rpow σ (1:ℝ) from
    (CFC.rpow_one σ hσ).symm]
  rw [rpow_mul_rpow_mul_rpow_cfc hσ]
  apply cfc_le_one
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
  change x ^ (-(1/2):ℝ) * x ^ (1:ℝ) * x ^ (-(1/2):ℝ) ≤ 1
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · rw [← h0, Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num),
      Real.zero_rpow (show (1:ℝ) ≠ 0 by norm_num)]
    norm_num
  · refine le_of_eq ?_
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos,
      show (-(1/2):ℝ) + 1 + (-(1/2)) = 0 by norm_num, Real.rpow_zero]

end

/-- **Support-projection identity** under `SupportLE`:
    `σ^{1/2} · (σ^{-1/2} ρ σ^{-1/2}) · σ^{1/2} = ρ`. -/
private lemma conjugate_rpow_self_eq {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    CFC.rpow σ (1/2) * (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))) * CFC.rpow σ (1/2)
      = ρ := by
  have hsa_s : IsSelfAdjoint (CFC.rpow σ (1/2)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hsa_t : IsSelfAdjoint (CFC.rpow σ (-(1/2))) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hcomm := rpow_half_mul_rpow_neg_comm hσ
  have hσP := self_mul_rpow_half_mul_rpow_neg hσ
  -- `P := σ^{1/2} σ^{-1/2}` is self-adjoint.
  have hP_sa : star (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)))
      = CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)) := by
    rw [star_mul, hsa_t.star_eq, hsa_s.star_eq, ← hcomm]
  -- `ρ · P = ρ` (kernel of `σ` is killed by `ρ`).
  have hρP : ρ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) = ρ := by
    refine LinearMap.ext fun v => ?_
    have hker : v - (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) v ∈
        LinearMap.ker σ := by
      rw [LinearMap.mem_ker, map_sub]
      change σ v - (σ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)))) v = 0
      rw [hσP, sub_self]
    have hv0 : ρ (v - (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) v) = 0 :=
      LinearMap.mem_ker.mp (hsupp hker)
    rw [map_sub] at hv0
    change (ρ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)))) v = ρ v
    exact (sub_eq_zero.mp hv0).symm
  -- `P · ρ = ρ` (adjoint of the previous).
  have hPρ : (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) * ρ = ρ := by
    have h := congrArg star hρP
    rwa [star_mul, hP_sa, (IsSelfAdjoint.of_nonneg hρ).star_eq] at h
  have key : CFC.rpow σ (1/2) * (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))) * CFC.rpow
    σ (1/2)
      = (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) * ρ * (CFC.rpow σ (-(1/2)) * CFC.rpow σ (1/2))
        := by
    simp only [mul_assoc]
  rw [key, ← hcomm, hPρ, hρP]

/-- **Frank–Lieb operator-norm form.** For non-negative `ρ, σ` with `SupportLE ρ σ`,
    `inf{λ ≥ 0 : ρ ≤ λ σ} = ‖σ^{-1/2} ρ σ^{-1/2}‖`. -/
lemma sInf_maxRelSet_eq_norm {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    sInf (maxRelSet ρ σ) = ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ := by
  set M := CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2)) with hM
  have hMnn : (0 : L ℋ) ≤ M := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hsa_s : IsSelfAdjoint (CFC.rpow σ (1/2)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hsa_t : IsSelfAdjoint (CFC.rpow σ (-(1/2))) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  -- `‖M‖ ∈ maxRelSet ρ σ`, i.e. `ρ ≤ ‖M‖ • σ`.
  have hmem : ‖M‖ ∈ maxRelSet ρ σ := by
    refine ⟨norm_nonneg _, ?_⟩
    have hMle : M ≤ algebraMap ℝ (L ℋ) ‖M‖ :=
      IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hMnn)
    have hconj := hsa_s.conjugate_le_conjugate hMle
    rw [hM, conjugate_rpow_self_eq hρ hσ hsupp] at hconj
    have hRHS : CFC.rpow σ (1/2) * algebraMap ℝ (L ℋ) ‖M‖ * CFC.rpow σ (1/2)
        = (‖M‖ : ℝ) • σ := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, rpow_half_sq hσ]
    rw [hRHS] at hconj
    rw [Complex.coe_smul]; exact hconj
  -- `‖M‖` is a lower bound of `maxRelSet ρ σ`.
  have hlb : ∀ lam ∈ maxRelSet ρ σ, ‖M‖ ≤ lam := by
    intro lam hlam
    have hlam0 : 0 ≤ lam := hlam.1
    have hle : ρ ≤ (lam : ℝ) • σ := by
      have h := hlam.2; rwa [Complex.coe_smul] at h
    have hconj := hsa_t.conjugate_le_conjugate hle
    rw [← hM] at hconj
    have hrhs : CFC.rpow σ (-(1/2)) * ((lam : ℝ) • σ) * CFC.rpow σ (-(1/2))
        = (lam : ℝ) • (CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2))) := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hrhs] at hconj
    have hstep : (lam : ℝ) • (CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2)))
        ≤ (lam : ℝ) • (1 : L ℋ) := by
      rw [← sub_nonneg, ← smul_sub]
      exact smul_nonneg hlam0 (sub_nonneg.mpr (rpow_neg_conj_self_le_one hσ))
    have hMle1 : M ≤ algebraMap ℝ (L ℋ) lam := by
      rw [Algebra.algebraMap_eq_smul_one]; exact le_trans hconj hstep
    exact (CStarAlgebra.norm_le_iff_le_algebraMap M hlam0 hMnn).mpr hMle1
  exact le_antisymm (csInf_le (bddBelow_maxRelSet ρ σ) hmem) (le_csInf ⟨‖M‖, hmem⟩ hlb)

/-- **Exponent-continuity of `CFC.rpow` at a possibly-singular operator**, along the
    sandwiched-Rényi exponent path `α ↦ (1-α)/(2α) → -1/2` as `α → ∞`. Valid even for
    singular `σ` (Moore–Penrose power): on the finite spectrum, the eigenvalue `0` stays
    pinned to `0` (the exponent is eventually negative), and positive eigenvalues move
    continuously. Proved by eigenbasis reconstruction. -/
private lemma tendsto_rpow_exponent_atTop_clm {σ : B ℋ} (hσ : 0 ≤ σ) :
    Filter.Tendsto (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) Filter.atTop
      (nhds (CFC.rpow σ (-(1/2)))) := by
  classical
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i :=
    hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hspec : ∀ i, eig i ∈ spectrum ℝ σ :=
    fun i => TensorCFC.mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hβ : Filter.Tendsto (fun α : ℝ => (1 - α) / (2 * α)) Filter.atTop (𝓝 (-(1/2))) := by
    have heq : (fun α : ℝ => (1 - α) / (2 * α)) =ᶠ[Filter.atTop] (fun α => 1 / (2 * α)
      - 1/2) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with α hα
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp
    rw [Filter.tendsto_congr' heq]
    have h2α : Filter.Tendsto (fun α : ℝ => 2 * α) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
    have h0 : Filter.Tendsto (fun α : ℝ => 1 / (2 * α)) Filter.atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h2α
    simpa using h0.sub_const (1/2)
  have key : ∀ i, Filter.Tendsto (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)) (b i))
    Filter.atTop
      (𝓝 (CFC.rpow σ (-(1/2)) (b i))) := by
    intro i
    have hrw : ∀ s : ℝ, CFC.rpow σ s (b i) = (((eig i) ^ s : ℝ) : ℂ) • b i :=
      fun s => rpow_apply_eigenvector_clm_support σ hσ s (b i) (eig i)
        (h_eig_apply i) (hspec i)
    simp only [hrw]
    apply Filter.Tendsto.smul_const
    apply (Complex.continuous_ofReal.tendsto _).comp
    rcases eq_or_lt_of_le (h_eig_nn i) with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      have hne : (1 - α) / (2 * α) ≠ 0 :=
        ne_of_lt (div_neg_of_neg_of_pos (by linarith) (by positivity))
      rw [Real.zero_rpow hne]
    · exact ((Real.continuous_const_rpow (ne_of_gt hpos)).tendsto _).comp hβ
  have hrecon : CFC.rpow σ (-(1/2)) =
      ∑ i, (outer_product (b i) (CFC.rpow σ (-(1/2)) (b i))).toContinuousLinearMap :=
    QuantumChannel.continuousLinearMap_eq_sum_outer_product b _
  have hfun : (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)))
      = (fun α => ∑ i, (outer_product (b i)
        (CFC.rpow σ ((1 - α) / (2 * α)) (b i))).toContinuousLinearMap) :=
    funext fun α => QuantumChannel.continuousLinearMap_eq_sum_outer_product b _
  rw [hrecon, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((QuantumChannel.continuous_outerL (b i)).tendsto _).comp (key i)

-- Real powers commute with the canonical lift to bounded operators.
omit [Nontrivial ℋ] in
private lemma main_rpow_toContinuousLinearMap (A : L ℋ) (p : ℝ) :
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

/-- Exponent continuity at the linear-map endpoint. -/
lemma tendsto_rpow_exponent_atTop {σ : L ℋ} (hσ : 0 ≤ σ) :
    Filter.Tendsto (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) Filter.atTop
      (nhds (CFC.rpow σ (-(1/2)))) := by
  have hσc : (0 : B ℋ) ≤ σ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hσ)
  have h := tendsto_rpow_exponent_atTop_clm hσc
  have hi : Continuous (fun A : B ℋ => (A : L ℋ)) := by
    simpa using LinearMap.continuous_of_finiteDimensional
      ((LinearMap.toContinuousLinearMap : L ℋ ≃ₗ[ℂ] B ℋ).symm.toLinearMap)
  have hc := (hi.tendsto (CFC.rpow σ.toContinuousLinearMap (-(1/2)))).comp h
  have hrpow (p : ℝ) : ((CFC.rpow σ.toContinuousLinearMap p : B ℋ) : L ℋ) =
      CFC.rpow σ p := by
    calc
      ((CFC.rpow σ.toContinuousLinearMap p : B ℋ) : L ℋ) =
          ((CFC.rpow σ p).toContinuousLinearMap : L ℋ) :=
        congrArg (fun A : B ℋ => (A : L ℋ))
          (main_rpow_toContinuousLinearMap σ p).symm
      _ = CFC.rpow σ p := rfl
  have hfun : (fun α : ℝ =>
      ((CFC.rpow σ.toContinuousLinearMap ((1 - α) / (2 * α)) : B ℋ) : L ℋ)) =
      (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) :=
    funext fun α => hrpow ((1 - α) / (2 * α))
  rw [Function.comp_def, hfun, hrpow (-(1/2))] at hc
  exact hc

/-- `maxRelEntropyNN` unfolds to the Frank–Lieb operator-norm form on the `SupportLE`
    region (definitional). -/
lemma maxRelEntropyNN_eq_log_norm {ρ σ : L ℋ}
    (hsupp : SupportLE ρ σ) :
    maxRelEntropyNN ρ σ =
      ((Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ : ℝ) : EReal) := by
  unfold maxRelEntropyNN; rw [if_pos hsupp]

/-- **Order-theoretic characterization** of the max-relative entropy on the `SupportLE`
    region: `D_∞(ρ‖σ) = log inf{λ ≥ 0 : ρ ≤ λ σ}`. -/
lemma maxRelEntropyNN_eq_log_sInf {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    maxRelEntropyNN ρ σ = ((Real.log (sInf (maxRelSet ρ σ)) : ℝ) : EReal) := by
  rw [maxRelEntropyNN_eq_log_norm hsupp, sInf_maxRelSet_eq_norm hρ hσ hsupp]

/-- **Data-processing inequality for the max-relative entropy** (`α = ∞`).
    For any CPTP map `Φ` and non-negative `ρ, σ`, `D_∞(Φ ρ ‖ Φ σ) ≤ D_∞(ρ ‖ σ)`.
    Proved through the order-theoretic characterization: `maxRelSet ρ σ ⊆ maxRelSet (Eρ)(Eσ)`
    (positivity of `Φ`), so the infimum decreases and `log` is monotone. -/
theorem maxRelEntropyNN_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    maxRelEntropyNN (Φ.toFun ρ)
      (Φ.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  by_cases hsupp : SupportLE ρ σ
  · -- support condition holds on both sides
    have hΦsupp := supportLE_map_of_cptp Φ hρ hσ hsupp
    have hΦρ : 0 ≤ Φ.toFun ρ := map_nonneg Φ.toCompletelyPositiveMap hρ
    have hΦσ : 0 ≤ Φ.toFun σ := map_nonneg Φ.toCompletelyPositiveMap hσ
    rw [maxRelEntropyNN_eq_log_sInf hΦρ hΦσ hΦsupp, maxRelEntropyNN_eq_log_sInf hρ hσ hsupp,
      EReal.coe_le_coe_iff]
    by_cases hρ0 : ρ = 0
    · -- both infima are `0`, both logs are `0`
      have hΦρ0 : Φ.toFun ρ = 0 := by
        change Φ.toLinearMap ρ = 0
        rw [hρ0, map_zero]
      rw [hΦρ0, hρ0, maxRelSet_zero_left hΦσ, maxRelSet_zero_left hσ]
    · -- ρ ≠ 0: both infima positive, use subset + log monotonicity
      have hΦρ0 : Φ.toFun ρ ≠ 0 :=
        cptp_toFun_ne_zero Φ hρ hρ0
      have h_sub : maxRelSet ρ σ ⊆ maxRelSet
          (Φ.toFun ρ)
          (Φ.toFun σ) :=
        maxRelSet_subset_of_cptp Φ
      have h_ne : (maxRelSet ρ σ).Nonempty := by
        obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
        exact ⟨lam, hlam_pos.le, hlam_le⟩
      have h_inf_le : sInf (maxRelSet (Φ.toFun ρ)
          (Φ.toFun σ)) ≤ sInf (maxRelSet ρ σ) :=
        csInf_le_csInf (bddBelow_maxRelSet _ _) h_ne h_sub
      have h_pos_Φ : 0 < sInf (maxRelSet
          (Φ.toFun ρ)
          (Φ.toFun σ)) :=
        sInf_maxRelSet_pos hΦρ hΦσ hΦρ0 hΦsupp
      exact Real.log_le_log h_pos_Φ h_inf_le
  · -- support fails: RHS is ⊤
    have h_RHS : maxRelEntropyNN ρ σ = (⊤ : EReal) := by
      unfold maxRelEntropyNN; rw [if_neg hsupp]
    rw [h_RHS]; exact le_top

/-- **Theorem 1 (Frank–Lieb), `α = ∞`, paper form.** For a CPTP map `Φ` and
    non-negative `ρ, σ` with `SupportLE ρ σ`,
    `log ‖(Eσ)^{-1/2} (Eρ) (Eσ)^{-1/2}‖ ≤ log ‖σ^{-1/2} ρ σ^{-1/2}‖`. -/
theorem maxRelEntropy_norm_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    Real.log ‖CFC.rpow (Φ.toFun σ) (-(1/2)) *
      Φ.toFun ρ *
      CFC.rpow (Φ.toFun σ) (-(1/2))‖
      ≤ Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ := by
  have hΦρ : 0 ≤ Φ.toFun ρ := map_nonneg Φ.toCompletelyPositiveMap hρ
  have hΦσ : 0 ≤ Φ.toFun σ := map_nonneg Φ.toCompletelyPositiveMap hσ
  have hΦsupp := supportLE_map_of_cptp Φ hρ hσ hsupp
  have hmono := maxRelEntropyNN_monotone Φ hρ hσ
  rw [maxRelEntropyNN_eq_log_norm hΦsupp, maxRelEntropyNN_eq_log_norm hsupp,
    EReal.coe_le_coe_iff] at hmono
  exact hmono

end MaxRelEntropy

end SandwichedRenyiRelativeEntropy
