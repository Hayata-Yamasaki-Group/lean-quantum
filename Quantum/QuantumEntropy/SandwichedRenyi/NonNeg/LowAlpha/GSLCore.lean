/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.CPTPNonzero.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.QuasiJensen.Concavity
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.AlphaOne
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.NonNeg.Continuity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.PositiveDefinite
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Sandwiched Rényi data processing for orders in [1/2, 1)

The nonnegative sandwiched Rényi divergence is monotone under CPTP maps for orders in `[1/2, 1)`
(`RenyiDPI.sandwichedRenyiDivNN_monotone_low`).  The proof combines positive-definite
monotonicity, faithful approximation and the Haar--Jensen inequality for the sandwiched
quasi-entropy.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

private lemma sandwichedQuasi_re_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (α : ℝ) (ρ σ : L ℋ) :
    0 ≤ (sandwichedQuasi α ρ σ).re := by
  have hpos : (0 : L ℋ) ≤ CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α := CFC.rpow_nonneg
  have h := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  rw [Complex.le_def] at h
  rw [sandwichedQuasi_eq_direct]
  exact h.1

private theorem sandwichedQuasi_jensen_haar_local
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (hEρ : traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)))
        (traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)))).re -
      (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  set Eρ : L 𝒦 := traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) with hEρ_def
  set Eσ : L 𝒦 := traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) with hEσ_def
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with
    hτ_max_def
  have hτ_max_pd : τ_max ∈ pdSetLM (ℋ := ℋ_env) := maxmixed_pdSetLM ℋ_env
  have hτ_max_trace : Tr τ_max = 1 := by
    rw [hτ_max_def, map_smul, smul_eq_mul, LinearMap.trace_one]
    have hd : (Module.finrank ℂ ℋ_env : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ_env)).ne'
    field_simp
  have hLHS_factor : sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max) = sandwichedQuasi α Eρ Eσ := by
    rw [sandwichedQuasi_tensor α Eρ Eσ τ_max τ_max
        (nonneg_of_pdSetLM hEρ) (nonneg_of_pdSetLM hEσ)
        (nonneg_of_pdSetLM hτ_max_pd) (nonneg_of_pdSetLM hτ_max_pd),
      sandwichedQuasi_self_pdSetLM hα_ne0 hτ_max_pd, hτ_max_trace, mul_one]
  have hRHS_factor : sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V)) = sandwichedQuasi α ρ σ :=
    sandwichedQuasi_isometric_conj V hV hα0 hα_ne1
      (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
  have h_core := jensen_haar_core hα_ge hα_ne1 hρ hσ V hV hEρ hEσ
  change ((sandwichedQuasi α Eρ Eσ).re - (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0
  have hLHS_re : (sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max)).re = (sandwichedQuasi α Eρ Eσ).re := by
    rw [hLHS_factor]
  have hRHS_re : (sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V))).re = (sandwichedQuasi α ρ σ).re := by
    rw [hRHS_factor]
  rw [← hLHS_re, ← hRHS_re]
  exact h_core

private theorem sandwichedRenyiDiv_monotone_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  obtain ⟨ℋ_env, h_qudit, h_nontriv, V, hV_iso, hV_eq⟩ :=
    E.exists_isometric_stinespring_dilation
  letI := h_qudit
  letI := h_nontriv
  have hEρ_eq : E.toFun ρ =
      traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) := hV_eq ρ
  have hEσ_eq : E.toFun σ =
      traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) := hV_eq σ
  have hQ_ineq :
      ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re -
        (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar_local hα_ge hα_ne1 hρ hσ V hV_iso
      (hEρ_eq ▸ hEρ) (hEσ_eq ▸ hEσ)
    rw [hEρ_eq, hEσ_eq]
    exact h
  have hTr_Eρ : (Tr (E.toFun ρ)).re = (Tr ρ).re := by
    exact congrArg Complex.re (E.trace_map ρ).symm
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := by
    have hn := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
    exact lt_of_le_of_ne (sandwichedQuasi_re_nonneg α ρ σ) (Ne.symm hn)
  have hQEρEσ_pos :
      (0 : ℝ) < (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    lt_of_le_of_ne (sandwichedQuasi_re_nonneg α (E.toFun ρ) (E.toFun σ))
      (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hEρ hEσ))
  have hlegacy : sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
    unfold sandwichedRenyiDiv
    rw [hTr_Eρ]
    rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
    · have hQ_ge : (sandwichedQuasi α ρ σ).re ≤
          (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re := by
        nlinarith
      have hlog := Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge hTr_ρ_pos.le)
      have hinv : (1 / (α - 1) : ℝ) < 0 := one_div_neg.mpr (by linarith)
      nlinarith
    · have hQ_le : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≤
          (sandwichedQuasi α ρ σ).re := by
        nlinarith
      have hlog := Real.log_le_log (div_pos hQEρEσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le hTr_ρ_pos.le)
      exact mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (by linarith))
  exact hlegacy

private theorem sandwichedRenyiDiv_monotone_nonneg_perturbed_aux
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hEI : E.toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α
        (E.toFun (ρ + (ε : ℂ) • 1) : L 𝒦)
        (E.toFun (σ + (ε : ℂ) • 1) : L 𝒦) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • 1)
        (σ + (ε : ℂ) • 1) := by
  have hpd : ∀ {X : L ℋ}, 0 ≤ X → X + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := by
    intro X hX
    exact nonneg_add_pos_smul_one_pdSetLM hX hε
  have hEpd : ∀ {X : L ℋ}, 0 ≤ X →
      E.toFun (X + (ε : ℂ) • 1) ∈ pdSetLM (ℋ := 𝒦) := by
    intro X hX
    change E.toLinearMap (X + (ε : ℂ) • 1) ∈ pdSetLM (ℋ := 𝒦)
    rw [map_add, map_smul]
    apply pdSetLM_add_nonneg (map_nonneg E.toCompletelyPositiveMap hX)
    apply (pdSetLM_strictPositivity_certificate _).2
    exact IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε)
      ((pdSetLM_strictPositivity_certificate _).1 hEI)
  exact sandwichedRenyiDiv_monotone_pd E hα_ge hα_ne1
    (hpd hρ) (hpd hσ) (hEpd hρ) (hEpd hσ)

private lemma sandwichedRenyiDiv_faithfulApprox_le
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0) (hσ0 : σ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α
        ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0)
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_one_pdSetLM E hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have hFρ_nn := nonneg_of_pdSetLM hFρ_pd
  have hFσ_nn := nonneg_of_pdSetLM hFσ_pd
  have hF1_nn := nonneg_of_pdSetLM hF1
  have hQF :=
    sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd
  have hTrFρ : (Tr (F.toFun ρ)).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hFρ_nn (isUnit_of_pdSetLM hFρ_pd).ne_zero)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      sandwichedRenyiDiv α (F.toFun ρ + (ε : ℂ) • F.toFun 1)
        (F.toFun σ + (ε : ℂ) • F.toFun 1) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ))
        (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε hε
    have hF (τ : L ℋ) : F.toFun (τ + (ε : ℂ) • 1) =
        F.toFun τ + (ε : ℂ) • F.toFun 1 := by
      change F.toLinearMap (τ + (ε : ℂ) • 1) =
        F.toLinearMap τ + (ε : ℂ) • F.toLinearMap 1
      rw [map_add, map_smul]
    rw [← hF ρ, ← hF σ]
    exact sandwichedRenyiDiv_monotone_nonneg_perturbed_aux F hα_ge
      (ne_of_lt hα_lt) hρ hσ hF1 hε
  have h_RHS := sandwichedRenyiDiv_tendsto_nonneg_lt hα0 hα_lt hρ hσ zero_le_one hQρσ hTrρ
  have h_LHS := sandwichedRenyiDiv_tendsto_nonneg_lt (P := F.toFun (1 : L ℋ))
    hα0 hα_lt hFρ_nn hFσ_nn hF1_nn hQF hTrFρ
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

private lemma sandwichedQuasi_re_ne_zero_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) :
    (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 := by
  have hα0 : 0 < α := by linarith
  have hTrρ_pos : 0 < (Tr ρ).re := QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  have hb_pos : 0 < (sandwichedQuasi α ρ σ).re :=
    lt_of_le_of_ne (sandwichedQuasi_re_nonneg α ρ σ) (Ne.symm hQ)
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQ
    rw [sandwichedQuasi_re_eq_zero_iff hα0 hρ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)` for each `λ`.
  have hQ_ge : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (sandwichedQuasi α ρ σ).re ≤
        (sandwichedQuasi α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)).re := by
    rintro ⟨lam, hlam0, hlam1⟩
    simp only
    set F := faithfulApprox E lam hlam0.le hlam1 with hF
    have hFρ_pd := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
    have hFσ_pd := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
    have ha_pos : 0 < (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re :=
      lt_of_le_of_ne (sandwichedQuasi_re_nonneg _ _ _)
        (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd))
    have hTrF : (Tr (F.toFun ρ)).re = (Tr ρ).re :=
      congrArg Complex.re (F.trace_map ρ).symm
    have hD := sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ
      hρ0 hσ0 hQ hlam0 hlam1
    -- Convert `D_F ≤ D_ρ` to `Q_ρ ≤ Q_F`.
    change sandwichedRenyiDiv α
        ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤
      sandwichedRenyiDiv α ρ σ at hD
    unfold sandwichedRenyiDiv at hD
    rw [hTrF] at hD
    -- `(1/(α-1)) log (Q_F/t) ≤ (1/(α-1)) log (Q_ρ/t)` with `1/(α-1) < 0` ⟹ flip.
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re /
          (Tr ρ).re) := by
      nlinarith [one_div_neg.mpr (show α - 1 < 0 by linarith)]
    rw [Real.log_le_log_iff (by positivity) (by positivity),
        div_le_div_iff_of_pos_right hTrρ_pos] at hlog
    exact hlog
  -- `λ → 0⁺`: `Q_α(F_λρ‖F_λσ).re → Q_α(Eρ‖Eσ).re`.
  have hcont_lm : ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) =>
      (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
    let e : L 𝒦 → B 𝒦 := fun A => A.toContinuousLinearMap
    have he : Continuous e := by fun_prop
    have h := sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα_lt.le
    have hc := h.comp (he.prodMap he).continuousOn
      (fun (p : L 𝒦 × L 𝒦) (hp : p ∈
        ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A})) => by
        constructor
        · exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hp.1)
        · exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hp.2))
    simpa [e, Function.comp_def, Function.uncurry] using hc
  have hcwa := hcont_lm (E.toFun ρ, E.toFun σ)
    ⟨map_nonneg E.toCompletelyPositiveMap hρ, map_nonneg E.toCompletelyPositiveMap hσ⟩
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ,
          (faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (E.toFun ρ,
        E.toFun σ)
        ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(faithfulApprox_tendsto E ρ).prodMk_nhds (faithfulApprox_tendsto E σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E
        l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E
        l.property.1 l.property.2 hσ hσ0))
  have hlim := hcwa.tendsto.comp hpair
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, hU_sub ⟨hball ?_, hx_pos⟩⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ne_of_gt (hb_pos.trans_le
    (ge_of_tendsto hlim (Filter.Eventually.of_forall hQ_ge)))

private lemma sandwichedRenyiDivNN_monotone_real_aux_lt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    (hQEρσ : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hEρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ := map_nonneg E.toCompletelyPositiveMap hσ
  have hEρ0 := cptp_toFun_ne_zero E hρ hρ0
  have hTrEρ := ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hEρ hEρ0)
  -- `Q_α(ρ‖σ) ≠ 0` forces `σ ≠ 0` (otherwise `σ^β = 0` and `Q = 0`).
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQρσ
    rw [sandwichedQuasi_re_eq_zero_iff hα0 hρ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- **Step 1**: for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ) ≤
        sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ
      hρ0 hσ0 hQρσ hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`. `(F_λρ, F_λσ) → (Eρ, Eσ)` within the non-negative cone.
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ,
          (faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (E.toFun ρ,
        E.toFun σ)
        ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(faithfulApprox_tendsto E ρ).prodMk_nhds (faithfulApprox_tendsto E σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E
        l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E
        l.property.1 l.property.2 hσ hσ0))
  have hcwa : ContinuousWithinAt (fun p : L 𝒦 × L 𝒦 =>
      sandwichedRenyiDiv α p.1 p.2)
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})
      (E.toFun ρ, E.toFun σ) :=
    sandwichedRenyiDiv_continuousWithinAt_lt hα0 hα_lt hEρ hEσ hQEρσ hTrEρ
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    apply Filter.comap_coe_neBot_of_le_principal
    rw [Filter.le_principal_iff]
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with l hl0 hl1
    exact ⟨hl0, hl1⟩
  exact le_of_tendsto (hcwa.tendsto.comp hpair) (Filter.Eventually.of_forall step1)

/-- Low-order DPI is fixed, independently of the α > 1 provider selection. -/
theorem _root_.RenyiDPI.sandwichedRenyiDivNN_monotone_low
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    sandwichedRenyiDivNN α (E.toFun ρ)
      (E.toFun σ) ≤ sandwichedRenyiDivNN α ρ σ := by
  have hEρ : 0 ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : 0 ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  by_cases hρ0 : ρ = 0
  · subst ρ
    rw [show E.toFun (0 : L ℋ) = 0 by exact E.toLinearMap.map_zero]
    simp [sandwichedRenyiDivNN, sandwichedRenyiDiv, SupportLE]
  have hα0 : 0 < α := by linarith
  by_cases hRtop : (ρ : L ℋ) ≠ 0 ∧
    (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re = 0
  · -- Orthogonal supports (`Q_α = 0`, `ρ ≠ 0`): RHS is `⊤`.
    have h_RHS_top : sandwichedRenyiDivNN α (ρ : L ℋ) (σ : L ℋ) = (⊤ : EReal) := by
      unfold sandwichedRenyiDivNN
      exact if_pos (Or.inr ⟨hα_lt, hRtop.1, hRtop.2⟩)
    rw [h_RHS_top]
    exact le_top
  · -- `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0`: real-valued DPI applies
    -- (LHS also finite by reflection).
    have hρLM0 : (ρ : L ℋ) ≠ 0 := by
      intro h
      apply hρ0
      ext x
      exact LinearMap.congr_fun h x
    have hQρσ : (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re ≠ 0 :=
      fun h => hRtop ⟨hρLM0, h⟩
    have hQEρσ := sandwichedQuasi_re_ne_zero_of_CPTP E hα_ge hα_lt
      hρ hσ hρ0 hQρσ
    have h_LHS : sandwichedRenyiDivNN α (E.toFun ρ : L 𝒦) (E.toFun σ : L 𝒦) =
        ((sandwichedRenyiDiv α (E.toFun ρ : L 𝒦)
          (E.toFun σ : L 𝒦) : ℝ) : EReal) := by
      unfold sandwichedRenyiDivNN
      rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · linarith
      · exact hQEρσ h
    have h_RHS : sandwichedRenyiDivNN α (ρ : L ℋ) (σ : L ℋ) =
        ((sandwichedRenyiDiv α (ρ : L ℋ) (σ : L ℋ) : ℝ) : EReal) := by
      unfold sandwichedRenyiDivNN
      rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · linarith
      · exact hQρσ h
    rw [h_LHS, h_RHS]
    exact_mod_cast sandwichedRenyiDivNN_monotone_real_aux_lt E hα_ge hα_lt
      hρ hσ hρ0 hQρσ hQEρσ

end SandwichedRenyiRelativeEntropy
