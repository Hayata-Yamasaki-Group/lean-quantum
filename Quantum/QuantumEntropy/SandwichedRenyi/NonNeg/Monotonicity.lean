/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.ContinuityCore

/-!
# Non-negative sandwiched Rényi divergence: main theorems

Real-valued monotonicity helpers, the Frank-Lieb data-processing theorem,
and the max-relative entropy endpoint.
-/

namespace SandwichedRenyiRelativeEntropy

section RepresentationSupport
open QuantumState
open scoped ComplexOrder NNReal Topology
universe uRep
variable {ℋ : Type uRep} [Qudit ℋ]

private lemma continuity_toCLM_toLinearMap
    {ℋ : Type uRep} [Qudit ℋ] (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

private lemma continuity_rpow_toContinuousLinearMap
    {ℋ : Type uRep} [Qudit ℋ] (A : L ℋ) (p : ℝ) :
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
    {ℋ : Type uRep} [Qudit ℋ] (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := continuity_rpow_toContinuousLinearMap (A : L ℋ) p
  rw [continuity_toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

private lemma continuity_sandwichedQuasi_eq_clm_direct
    {ℋ : Type uRep} [Qudit ℋ] (a : ℝ) (rho sigma : B ℋ) :
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

end RepresentationSupport

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-! ### CLM boundary helpers -/
private lemma nonneg_of_pdSet
    {ℋ : Type u} [Qudit ℋ] {A : B ℋ}
    (hA : A ∈ pdSet (ℋ := ℋ)) : 0 ≤ A :=
  ((pdSet_membership_certificate A).1 hA).nonneg

private lemma isUnit_of_pdSet
    {ℋ : Type u} [Qudit ℋ] {A : B ℋ}
    (hA : A ∈ pdSet (ℋ := ℋ)) : IsUnit A :=
  ((pdSet_membership_certificate A).1 hA).isUnit

/-- A CPTP map cannot send a non-zero non-negative state to zero. -/
lemma cptp_toFun_ne_zero
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    Φ.toFun ρ ≠ 0 := by
  intro hzero
  have htrace := Φ.trace_map ρ
  have htr : (Tr ρ).re = 0 := by
    rw [htrace, hzero]
    simp
  exact absurd htr (ne_of_gt (by
    simpa using QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0))

/-! ### Helpers for the `α < 1` main-theorem case -/

/-- `sandwichedRenyiDiv α 0 τ = 0`: with `ρ = 0`, `Tr ρ = 0` and `Real.log (· / 0) = 0`. -/
private lemma sandwichedRenyiDiv_zero_left
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ) (τ : L ℋ) :
    sandwichedRenyiDiv α (0 : L ℋ) τ = 0 := by
  unfold sandwichedRenyiDiv
  simp

/-- For positive-definite `ρ, σ` (in `pdSetLM`), the quasi-entropy is non-zero: `σ^β ρ σ^β`
    is a product of units (hence a unit, hence `≠ 0`), so by `sandwichedQuasi_re_eq_zero_iff`
    its `Q_α.re ≠ 0`. -/
lemma sandwichedQuasi_re_ne_zero_of_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  have hrpow_unit : IsUnit (CFC.rpow σ ((1 - α) / (2 * α))) :=
    (isUnit_of_pdSetLM hσ).cfcRpow _ (nonneg_of_pdSetLM hσ)
  have hρ_unit : IsUnit ρ := isUnit_of_pdSetLM hρ
  intro hzero
  rw [sandwichedQuasi_re_eq_zero_iff (ρ := ρ) (σ := σ) hα0
    (nonneg_of_pdSetLM hρ)] at hzero
  exact (((hrpow_unit.mul hρ_unit).mul hrpow_unit).ne_zero) hzero

/-- The real part of the quasi-entropy is non-negative (it is `Tr` of a non-negative operator). -/
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

/-! A local Jensen--Haar inequality keeps this module independently checkable
without importing the positive-definite data-processing theorem. -/
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
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hΦρ : Φ.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hΦσ : Φ.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  obtain ⟨ℋ_env, h_qudit, h_nontriv, V, hV_iso, hV_eq⟩ :=
    Φ.exists_isometric_stinespring_dilation
  letI := h_qudit
  letI := h_nontriv
  have hΦρ_eq : Φ.toFun ρ =
      traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) := hV_eq ρ
  have hΦσ_eq : Φ.toFun σ =
      traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) := hV_eq σ
  have hQ_ineq :
      ((sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re -
        (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar_local hα_ge hα_ne1 hρ hσ V hV_iso
      (hΦρ_eq ▸ hΦρ) (hΦσ_eq ▸ hΦσ)
    rw [hΦρ_eq, hΦσ_eq]
    exact h
  have hTr_Φρ : (Tr (Φ.toFun ρ)).re = (Tr ρ).re := by
    exact congrArg Complex.re (Φ.trace_map ρ).symm
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := by
    have hn := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
    exact lt_of_le_of_ne (sandwichedQuasi_re_nonneg α ρ σ) (Ne.symm hn)
  have hQΦρΦσ_pos :
      (0 : ℝ) < (sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re :=
    lt_of_le_of_ne (sandwichedQuasi_re_nonneg α (Φ.toFun ρ) (Φ.toFun σ))
      (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hΦρ hΦσ))
  have hlegacy : sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
    unfold sandwichedRenyiDiv
    rw [hTr_Φρ]
    rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
    · have hQ_ge : (sandwichedQuasi α ρ σ).re ≤
          (sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re := by
        nlinarith
      have hlog := Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge hTr_ρ_pos.le)
      have hinv : (1 / (α - 1) : ℝ) < 0 := one_div_neg.mpr (by linarith)
      nlinarith
    · have hQ_le : (sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re ≤
          (sandwichedQuasi α ρ σ).re := by
        nlinarith
      have hlog := Real.log_le_log (div_pos hQΦρΦσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le hTr_ρ_pos.le)
      exact mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (by linarith))
  exact hlegacy

private theorem sandwichedRenyiDiv_monotone_nonneg_perturbed_aux
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hΦI : Φ.toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α
        (Φ.toFun (ρ + (ε : ℂ) • 1) : L 𝒦)
        (Φ.toFun (σ + (ε : ℂ) • 1) : L 𝒦) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • 1)
        (σ + (ε : ℂ) • 1) := by
  have hpd : ∀ {X : L ℋ}, 0 ≤ X → X + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := by
    intro X hX
    exact nonneg_add_pos_smul_one_pdSetLM hX hε
  have hΦpd : ∀ {X : L ℋ}, 0 ≤ X →
      Φ.toFun (X + (ε : ℂ) • 1) ∈ pdSetLM (ℋ := 𝒦) := by
    intro X hX
    change Φ.toLinearMap (X + (ε : ℂ) • 1) ∈ pdSetLM (ℋ := 𝒦)
    rw [map_add, map_smul]
    apply pdSetLM_add_nonneg (map_nonneg Φ.toCompletelyPositiveMap hX)
    apply (pdSetLM_strictPositivity_certificate _).2
    exact IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε)
      ((pdSetLM_strictPositivity_certificate _).1 hΦI)
  exact sandwichedRenyiDiv_monotone_pd Φ hα_ge hα_ne1
    (hpd hρ) (hpd hσ) (hΦpd hρ) (hΦpd hσ)

/-- Monotonicity of the sandwiched Rényi divergence under a CPTP map.

Source: this paper, arXiv:2607.05492v1, formalization of the main results in §4 (no individual paper
theorem number is assigned). -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM) (hσ : σ ∈ pdSetLM)
    (hΦρ : Φ.toFun ρ ∈ pdSetLM)
    (hΦσ : Φ.toFun σ ∈ pdSetLM) :
    sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ :=
  sandwichedRenyiDiv_monotone_pd Φ hα_ge hα_ne1 hρ hσ hΦρ hΦσ

/-- Perturbed monotonicity for non-negative states under a CPTP map. -/
theorem sandwichedRenyiDiv_monotone_nonneg_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hΦI : Φ.toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α (Φ.toFun (ρ + (ε : ℂ) • 1) : L 𝒦)
        (Φ.toFun (σ + (ε : ℂ) • 1) : L 𝒦) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • 1)
        (σ + (ε : ℂ) • 1) :=
  sandwichedRenyiDiv_monotone_nonneg_perturbed_aux Φ hα_ge hα_ne1 hρ hσ hΦI hε

/-- **Faithful-approximation DPI** (`α < 1`): for each `λ ∈ (0,1]`, the faithful channel
    `F_λ` satisfies `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`. Obtained by taking `ε →
      0⁺` in the
    perturbed PD inequality (`F_λρ, F_λσ` are positive-definite). -/
private lemma sandwichedRenyiDiv_faithfulApprox_le
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0) (hσ0 : σ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0)
  set F := faithfulApprox Φ lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_one_pdSetLM Φ hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM Φ hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) :=
    faithfulApprox_pdSetLM Φ hlam0 hlam1 hσ hσ0
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
  have h_RHS := tendsto_sandwichedRenyiDiv_nonneg_of_lt_one hα0 hα_lt hρ hσ zero_le_one hQρσ hTrρ
  have h_LHS := tendsto_sandwichedRenyiDiv_nonneg_of_lt_one (P := F.toFun (1 : L ℋ))
    hα0 hα_lt hFρ_nn hFσ_nn hF1_nn hQF hTrFρ
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Orthogonality reflection** (`α < 1`): a CPTP map cannot create orthogonality.
    If `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0` (i.e. `ρ`, `σ` are not orthogonal), then
    `Q_α(Eρ‖Eσ) ≠ 0`.

    **Proof** (no Stinespring needed): the faithful DPI gives, for each `λ ∈ (0,1]`,
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`; since `α < 1` (so `1/(α−1) < 0`) and
      `Tr(F_λρ) = Tr ρ`,
    this is equivalent to `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)`. As `λ → 0⁺`,
      `Q_α(F_λρ‖F_λσ) →
    Q_α(Eρ‖Eσ)` by nonneg-cone continuity, so `0 < Q_α(ρ‖σ) ≤ Q_α(Eρ‖Eσ)`. -/
private lemma sandwichedQuasi_re_ne_zero_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) :
    (sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re ≠ 0 := by
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
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ)).re := by
    rintro ⟨lam, hlam0, hlam1⟩
    simp only
    set F := faithfulApprox Φ lam hlam0.le hlam1 with hF
    have hFρ_pd := faithfulApprox_pdSetLM Φ hlam0 hlam1 hρ hρ0
    have hFσ_pd := faithfulApprox_pdSetLM Φ hlam0 hlam1 hσ hσ0
    have ha_pos : 0 < (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re :=
      lt_of_le_of_ne (sandwichedQuasi_re_nonneg _ _ _)
        (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd))
    have hTrF : (Tr (F.toFun ρ)).re = (Tr ρ).re :=
      congrArg Complex.re (F.trace_map ρ).symm
    have hD := sandwichedRenyiDiv_faithfulApprox_le Φ hα_ge hα_lt hρ hσ
      hρ0 hσ0 hQ hlam0 hlam1
    -- Convert `D_F ≤ D_ρ` to `Q_ρ ≤ Q_F`.
    change sandwichedRenyiDiv α
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun σ) ≤
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
    exact continuousOn_sandwichedQuasi_re_nonneg_lm hα0 hα_lt.le
  have hcwa := hcont_lm (Φ.toFun ρ, Φ.toFun σ)
    ⟨map_nonneg Φ.toCompletelyPositiveMap hρ, map_nonneg Φ.toCompletelyPositiveMap hσ⟩
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ,
          (faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (Φ.toFun ρ,
        Φ.toFun σ)
        ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(tendsto_faithfulApprox Φ ρ).prodMk_nhds (tendsto_faithfulApprox Φ σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM Φ
        l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM Φ
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

/-! ### Real-valued monotonicity (used in the main theorem) -/

/-- `Q_α` continuity along a pd perturbation path `ε ↦ (ρ+εP, σ+εP)` (all pd). -/
private lemma sandwichedQuasi_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (_hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont_clm := continuousOn_sandwichedQuasi_re_pdSetLM (ℋ_aux := ℋ) α
  let e : L ℋ → B ℋ := fun A => A.toContinuousLinearMap
  have he : Continuous e := by fun_prop
  have hcont : ContinuousOn (Function.uncurry (fun (ρ σ : L ℋ) =>
      (sandwichedQuasi α ρ σ).re))
      (pdSetLM (ℋ := ℋ) ×ˢ pdSetLM (ℋ := ℋ)) := by
    have hc := hcont_clm.comp (he.prodMap he).continuousOn
      (fun (p : L ℋ × L ℋ) (hp : p ∈
        (pdSetLM (ℋ := ℋ) ×ˢ pdSetLM (ℋ := ℋ))) => by
        exact hp)
    simpa [e, Function.comp_def, Function.uncurry] using hc
  set S : Set (L ℋ × L ℋ) :=
    pdSetLM (ℋ := ℋ) ×ˢ pdSetLM (ℋ := ℋ) with hS
  set g : ℝ → L ℋ × L ℋ := fun ε =>
    (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P) with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεP : (ε : ℂ) • P ∈ pdSetLM (ℋ := ℋ) := by
        apply (pdSetLM_strictPositivity_certificate _).2
        exact IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε)
          ((pdSetLM_strictPositivity_certificate P).1 hP)
      have hρadd : ρ + (ε : ℂ) • P ∈ pdSetLM (ℋ := ℋ) :=
        pdSetLM_add_nonneg (nonneg_of_pdSetLM hρ) hεP
      have hσadd : σ + (ε : ℂ) • P ∈ pdSetLM (ℋ := ℋ) :=
        pdSetLM_add_nonneg (nonneg_of_pdSetLM hσ) hεP
      exact Set.mk_mem_prod hρadd hσadd
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) =>
        (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont _ ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- `D_α` continuity along a pd perturbation path. -/
private lemma sandwichedRenyiDiv_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := sandwichedQuasi_tendsto_pd hα0 hρ hσ hP
  have hTr0 : (Tr ρ).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero (nonneg_of_pdSetLM hρ)
      (isUnit_of_pdSetLM hρ).ne_zero)
  have hQ0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  have hpath : Filter.Tendsto (fun ε : ℝ => ρ + (ε : ℂ) • P)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ρ) := by
    have hc : Continuous (fun ε : ℝ => ρ + (ε : ℂ) • P) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have htrace : Continuous (fun A : L ℋ => (Tr A).re) := by fun_prop
  have hTc := (htrace.tendsto ρ).comp hpath
  have hRatio : Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α
        (ρ + (ε : ℂ) • P)
        (σ + (ε : ℂ) • P)).re /
        (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
    Filter.Tendsto.div hQc hTc hTr0
  have hLog := (Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Faithful-approximation DPI** (`α > 1`): for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤
    D_α(ρ‖σ)`. Take `ε → 0⁺` in the perturbed PD inequality: the LHS limit at the PD pair
    `(F_λρ, F_λσ)` uses PD-continuity, the RHS limit uses `SupportLE`-boundary continuity. -/
private lemma sandwichedRenyiDiv_faithfulApprox_le_gt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox Φ lam hlam0.le hlam1).toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have hα0 : 0 < α := by linarith
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  set F := faithfulApprox Φ lam hlam0.le hlam1 with hF
  have hF1 := faithfulApprox_one_pdSetLM Φ hlam0 hlam1
  have hFρ_pd := faithfulApprox_pdSetLM Φ hlam0 hlam1 hρ hρ0
  have hFσ_pd := faithfulApprox_pdSetLM Φ hlam0 hlam1 hσ hσ0
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
      (ne_of_gt hα_gt) hρ hσ hF1 hε
  have h_RHS := tendsto_sandwichedRenyiDiv_of_supportLE hα_gt hρ hσ hsupp hρ0
  have h_LHS := sandwichedRenyiDiv_tendsto_pd hα0 hFρ_pd hFσ_pd hF1
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Operator convergence along the faithful path** (`α > 1`). With
    `Pσ λ := (1−λ)•A + (λ·cσ)•1` and `Pρ λ := (1−λ)•B + (λ·cρ)•1` (`A =
      Eσ`, `B = Eρ`,
    `cσ > 0`, `cρ ≥ 0`), `Pσ^β Pρ Pσ^β → A^β B A^β` as `λ → 0⁺`. The
      depolarizing shift
    `(λ·cσ)•1` commutes with `A`, so the pseudo-inverse blow-up on `ker A` is killed by
    `SupportLE B A`; the residual `ker A`-contribution scales as `λ^{1/α} → 0`. -/
private lemma rpow_conj_tendsto_faithful
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {A B : ℋ →L[ℂ] ℋ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupp : SupportLE (B : L ℋ) (A : L ℋ))
    {cσ cρ : ℝ} (hcσ : 0 < cσ) (hcρ : 0 ≤ cρ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          ((1-α)/(2*α))
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
            ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow A ((1-α)/(2*α)) * B * CFC.rpow A ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym : A.IsSymmetric := hA_pos.isSymmetric
  have hB_sym : B.IsSymmetric := ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  change LinearMap.ker (A : L ℋ) ≤ LinearMap.ker (B : L ℋ) at hsupp
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hA_pos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ):ℂ) • b i :=
    hA_sym.apply_eigenvectorBasis hn
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (B (b i)) = (0:ℂ)
    := by
    exact fun i j hij =>
      QuantumChannel.inner_apply_eq_zero_of_ker_le hB_sym b eig h_eig_apply hsupp hij
  -- eigenvalue of the perturbed operator `Pσ λ`.
  set ν : ℝ → Fin n → ℝ := fun lam i => (1-lam)*eig i + lam*cσ with hν
  have hPσ_app : ∀ (lam : ℝ) k,
      (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) (b k) = ((ν lam k
        : ℝ):ℂ) • b k := by
    intro lam k
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, h_eig_apply k,
      ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_smul, ← add_smul, hν]
    push_cast; ring_nf
  have hν_le : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, lam*cσ ≤ ν lam k := by
    intro lam hlam0 hlam1 k
    rw [hν]
    linarith [mul_nonneg (show 0 ≤ 1 - lam by linarith) (h_eig_nn k)]
  have hM0 : ∀ i, (CFC.rpow A β * B * CFC.rpow A β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i; simpa using rpow_conj_affine_apply_eigenbasis b hA eig h_eig_apply β 1 0 i
  -- per-λ formula for `Pσ^β Pρ Pσ^β (b i)`.
  have hMlam : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ i,
      (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
        * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
        * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β) (b i)
      = (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
        + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i := by
    intro lam hlam0 hlam1 i
    have hPσ_nn : (0 : ℋ →L[ℂ] ℋ) ≤
        ((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hA)
        (smul_nonneg (Complex.zero_le_real.mpr (by positivity)) zero_le_one)
    exact rpow_conj_affine_apply_eigenbasis b hPσ_nn (ν lam) (hPσ_app lam)
      β (1 - lam) (lam * cρ) i
  -- `ν lam k → eig k` as `λ → 0⁺`.
  have hν_tendsto : ∀ k, Filter.Tendsto (fun lam : ℝ => ν lam k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun lam : ℝ => ν lam k) := by rw [hν]; fun_prop
    simpa [hν] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  -- extra-term scalar `λ·cρ·(ν λ i)^{2β} → 0`.
  have hextra : ∀ i, Filter.Tendsto (fun lam : ℝ => (((lam*cρ * ((ν lam i)^β)^2 : ℝ))
    : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    apply tendsto_singular_rpow_sq (by linarith [hβneg]) h2β hα_inv_pos hcσ hcρ
      (fun lam => ν lam i)
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    exact hν_le lam hlam (le_of_lt hlam1) i
  -- per-i vector convergence.
  have key : ∀ i, Filter.Tendsto
      (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β)
            (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow A β * B * CFC.rpow A β) (b i))) := by
    intro i
    rw [hM0 i]
    have hEq : (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β)
            (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun lam => (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
          + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
      exact hMlam lam hlam (le_of_lt hlam1) i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
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
        have hsc : Filter.Tendsto
            (fun lam : ℝ => ((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
              * inner ℂ (b j) (B (b i)))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i)))) := by
          have hone : Filter.Tendsto (fun lam : ℝ => ((1-lam : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
            have hc : Continuous (fun lam : ℝ => ((1-lam : ℝ):ℂ)) := by fun_prop
            simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
          exact tendsto_rpow_pair_coeff hν_tendsto _ hone hi hj
            (inner ℂ (b j) (B (b i)))
        simpa using hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  exact tendsto_continuousLinearMap_of_apply_orthonormalBasis b _ _ key

/-- **`λ → 0⁺` boundary continuity along the faithful (depolarizing) path** (`α > 1`):
    `D_α(F_λρ ‖ F_λσ) → D_α(Eρ ‖ Eσ)`. The pseudo-inverse blow-up of
      `(F_λσ)^β` is killed by
    `SupportLE (Eρ) (Eσ)` (the depolarizing perturbation commutes with `Eσ`). -/
private lemma sandwichedRenyiDiv_tendsto_faithful
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0)
    (hΦsupp : SupportLE (Φ.toFun ρ) (Φ.toFun σ)) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ))) := by
  classical
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  set Eρ : B 𝒦 := (Φ.toFun ρ).toContinuousLinearMap with hΦρdef
  set Eσ : B 𝒦 := (Φ.toFun σ).toContinuousLinearMap with hΦσdef
  have hΦρ_nn_lm : (0 : L 𝒦) ≤ Φ.toFun ρ := map_nonneg Φ.toCompletelyPositiveMap hρ
  have hΦσ_nn_lm : (0 : L 𝒦) ≤ Φ.toFun σ := map_nonneg Φ.toCompletelyPositiveMap hσ
  have hΦρ_nn : (0 : B 𝒦) ≤ Eρ := by
    rw [hΦρdef]
    exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hΦρ_nn_lm)
  have hΦσ_nn : (0 : B 𝒦) ≤ Eσ := by
    rw [hΦσdef]
    exact (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hΦσ_nn_lm)
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  set cσ : ℝ := (Tr σ).re /
    (Module.finrank ℂ 𝒦 : ℝ) with hcσ
  set cρ : ℝ := (Tr ρ).re /
    (Module.finrank ℂ 𝒦 : ℝ) with hcρ
  have hcσ_pos : 0 < cσ := div_pos (QuantumEntropy.trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  have hcρ_nn : 0 ≤ cρ :=
    div_nonneg (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0).le hd_pos.le
  have hΦρ0 : Eρ ≠ 0 := by
    rw [hΦρdef]
    exact LinearMap.toContinuousLinearMap.injective.ne (cptp_toFun_ne_zero Φ hρ hρ0)
  have hΦsupp_clm : SupportLE (Eρ : L 𝒦) (Eσ : L 𝒦) := by
    simpa [hΦρdef, hΦσdef] using hΦsupp
  -- Operator convergence along the faithful path (in the target space `𝒦`).
  have hM := rpow_conj_tendsto_faithful (ℋ := 𝒦) hα_gt hΦσ_nn hΦρ_nn
    hΦsupp_clm hcσ_pos hcρ_nn
  -- Wrap to `sandwichedQuasi` via continuity of `X ↦ Tr (X^α)` on the non-negative cone.
  have hMnn : ∀ X Y : B 𝒦, 0 ≤ Y →
      (0 : B 𝒦) ≤ CFC.rpow X β * Y * CFC.rpow X β :=
    fun X Y hY => conjugate_nonneg_of_nonneg hY CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : B 𝒦 =>
      traceCLM (CFC.rpow X α))
      {X : B 𝒦 | 0 ≤ X}
      (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) := by
    have h1 : ContinuousOn (fun X : B 𝒦 => CFC.rpow X α)
        {X : B 𝒦 | 0 ≤ X} :=
      continuousOn_rpow_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : B 𝒦 => traceCLM A) :=
      traceCLM.continuous
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn Eσ Eρ hΦρ_nn)
  have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have hMwithin : Filter.Tendsto
      (fun lam : ℝ => CFC.rpow (((1-lam:ℝ):ℂ)•Eσ +
          ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦)) β
        * (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦))
        * CFC.rpow (((1-lam:ℝ):ℂ)•Eσ +
          ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β)
        {X : B 𝒦 | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    have hlam0 : (0:ℝ) < lam := hlam
    have hlam1' : lam < 1 := hlam1
    have hPρ_nn : (0 : B 𝒦) ≤ ((1-lam:ℝ):ℂ)•Eρ +
        ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hΦρ_nn)
        (smul_nonneg (Complex.zero_le_real.mpr (mul_nonneg hlam0.le hcρ_nn)) zero_le_one)
    exact hMnn _ _ hPρ_nn
  have hQcx := Filter.Tendsto.comp hcont hMwithin
  -- `sandwichedRenyiDiv` tendsto over the real parameter `λ`.
  have hTr0 : (Tr (ContinuousLinearMap.toLinearMap Eρ)).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero
      ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hΦρ_nn)
      (fun h => hΦρ0 (by ext x; exact congrArg (fun A : L _ => A x) h)))
  have hΦρ0_lm : (Eρ : L 𝒦) ≠ 0 := by
    intro h
    apply hΦρ0
    ext x
    simpa using congrArg (fun A : L 𝒦 => A x) h
  have hΦρ_nn' : (0 : L 𝒦) ≤ (Eρ : L 𝒦) := by
    exact (ContinuousLinearMap.coe_le_coe_iff _ _).mpr hΦρ_nn
  have hΦσ_nn' : (0 : L 𝒦) ≤ (Eσ : L 𝒦) := by
    exact (ContinuousLinearMap.coe_le_coe_iff _ _).mpr hΦσ_nn
  have hQ0 : (sandwichedQuasi α (Eρ : L 𝒦) (Eσ : L 𝒦)).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hΦρ_nn' hΦσ_nn'
      hΦsupp_clm hΦρ0_lm
  have hQre : Filter.Tendsto
      (fun lam : ℝ => (sandwichedQuasi α
        (ContinuousLinearMap.toLinearMap
          (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)))
        (ContinuousLinearMap.toLinearMap
          (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦)))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α
        (ContinuousLinearMap.toLinearMap Eρ)
        (ContinuousLinearMap.toLinearMap Eσ)).re) := by
    have hQcx_re := (Complex.continuous_re.tendsto _).comp hQcx
    rw [hβ] at hQcx_re
    have hfun :
        (fun lam : ℝ => (sandwichedQuasi α
          (ContinuousLinearMap.toLinearMap
            (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)))
          (ContinuousLinearMap.toLinearMap
            (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦)))).re) =
        (fun lam : ℝ => (traceCLM (CFC.rpow
          (CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦))
              ((1 - α) / (2 * α)) *
            (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)) *
            CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦))
              ((1 - α) / (2 * α))) α)).re) := by
      funext lam
      exact congrArg Complex.re (by
        simpa [traceCLM] using
          (continuity_sandwichedQuasi_eq_clm_direct α
            (((1-lam:ℝ):ℂ) • Eρ + ((lam*cρ:ℝ):ℂ) • (1 : B 𝒦))
            (((1-lam:ℝ):ℂ) • Eσ + ((lam*cσ:ℝ):ℂ) • (1 : B 𝒦))))
    have hlim : (sandwichedQuasi α
        (ContinuousLinearMap.toLinearMap Eρ)
        (ContinuousLinearMap.toLinearMap Eσ)).re =
        (traceCLM (CFC.rpow
          (CFC.rpow Eσ ((1 - α) / (2 * α)) * Eρ *
            CFC.rpow Eσ ((1 - α) / (2 * α))) α)).re :=
      congrArg Complex.re (by
        simpa [traceCLM] using
          (continuity_sandwichedQuasi_eq_clm_direct α Eρ Eσ))
    rw [hfun, hlim]
    exact hQcx_re
  have hTre : Filter.Tendsto
      (fun lam : ℝ => (Tr (ContinuousLinearMap.toLinearMap
        (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr (ContinuousLinearMap.toLinearMap Eρ)).re) := by
    have hp : Filter.Tendsto (fun lam : ℝ => ((1-lam:ℝ):ℂ)•Eρ +
        ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds Eρ) := by
      have hc : Continuous (fun lam : ℝ => ((1-lam:ℝ):ℂ)•Eρ +
          ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (QuantumState.continuous_re_trace.tendsto Eρ).comp hp
  have hD : Filter.Tendsto
      (fun lam : ℝ => sandwichedRenyiDiv α
        (ContinuousLinearMap.toLinearMap
          (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1 : B 𝒦)))
        (ContinuousLinearMap.toLinearMap
          (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1 : B 𝒦))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedRenyiDiv α
        (ContinuousLinearMap.toLinearMap Eρ)
        (ContinuousLinearMap.toLinearMap Eσ))) := by
    unfold sandwichedRenyiDiv
    have hRatio := Filter.Tendsto.div hQre hTre hTr0
    exact ((Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio).const_mul _
  -- Transfer to the subtype filter; identify the CLM action of `F_λ` with the explicit
  -- perturbation.
  have hFeq : ∀ (X : L ℋ) (cX : ℝ),
      cX = (Tr X).re /
        (Module.finrank ℂ 𝒦 : ℝ) → 0 ≤ X →
      ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun X).toContinuousLinearMap =
          ((1-l.val:ℝ):ℂ)•(Φ.toFun X).toContinuousLinearMap +
            ((l.val*cX:ℝ):ℂ)•(1 : B 𝒦) := by
    intro X cX hcX hX l
    have hTrX_re : Tr X = ((Tr X).re : ℂ) := by
      have h := ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
      change (0 : ℂ) ≤ Tr X at h
      rw [Complex.le_def] at h
      exact (Complex.ext rfl h.2.symm)
    change ((1-l.val:ℝ):ℂ) • (Φ.toFun X).toContinuousLinearMap +
        ((l.val:ℝ):ℂ) •
          ((Tr X / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : B 𝒦)) =
      ((1-l.val:ℝ):ℂ) • (Φ.toFun X).toContinuousLinearMap +
        ((l.val*cX:ℝ):ℂ) • (1 : B 𝒦)
    rw [smul_smul]
    congr 2
    have hcX' : cX = (Tr X).re / (Module.finrank ℂ 𝒦 : ℝ) := by
      simpa using hcX
    rw [hTrX_re, hcX']
    push_cast
    rfl
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htc : Filter.Tendsto (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin 0 (Set.Ioi 0)) := Filter.tendsto_comap
  have hcomp := hD.comp htc
  refine hcomp.congr' ?_
  filter_upwards with l
  rw [Function.comp_apply]
  congr 1
  · apply LinearMap.toContinuousLinearMap.injective
    simpa [hΦρdef] using (hFeq ρ cρ hcρ hρ l).symm
  · apply LinearMap.toContinuousLinearMap.injective
    simpa [hΦσdef] using (hFeq σ cσ hcσ hσ l).symm

/-- **Real-valued monotonicity for `α > 1`** with the support condition and `ρ ≠ 0`.

    Mirrors the `α < 1` proof (`sandwichedRenyiDivNN_monotone_real_aux_lt`):

    1. **Faithful DPI per `λ`** (`step1`): for each `λ ∈ (0, 1]`, `F_λ` is faithful
       (`F_λ 1 ∈ pdSetLM`), and `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by
         taking
       `ε → 0⁺` in the perturbed PD inequality, with the LHS limit using PD-continuity
       (the path `F_λ(ρ+εI) = F_λρ + ε F_λ1` stays in `pdSetLM`) and the RHS limit using
       boundary continuity under `SupportLE` (`tendsto_sandwichedRenyiDiv_of_supportLE`).
    2. **`λ → 0⁺`** (`step2`): `(F_λρ, F_λσ) → (Eρ, Eσ)` and `D_α(F_λρ ‖
      F_λσ) →
       D_α(Eρ ‖ Eσ)` by boundary continuity along the faithful (depolarizing) path. -/
private lemma sandwichedRenyiDivNN_monotone_real_aux
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ)
    (hΦsupp : SupportLE (Φ.toFun ρ) (Φ.toFun σ))
    (hρ0 : ρ ≠ 0) :
    sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, h⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
    exact hρ0 (le_antisymm (by simpa using h) hρ)
  -- **Step 1**: faithful DPI for each `λ ∈ (0,1]`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ) ≤
        sandwichedRenyiDiv α ρ σ := fun l =>
    sandwichedRenyiDiv_faithfulApprox_le_gt Φ hα_gt hρ hσ hρ0 hsupp
      l.property.1 l.property.2
  -- **Step 2**: `λ → 0⁺`, boundary continuity along the faithful path.
  haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have step2 : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ))) :=
    sandwichedRenyiDiv_tendsto_faithful Φ hα_gt hρ hσ hσ0 hρ0 hΦsupp
  exact le_of_tendsto step2 (Filter.Eventually.of_forall step1)

/-- Real-valued monotonicity for `α < 1`, in the non-orthogonal regime
    (`Q_α(ρ‖σ) ≠ 0` and `Q_α(Eρ‖Eσ) ≠ 0`).

    **Proof**: For each `λ ∈ (0,1]`, the faithful approximation `F_λ` satisfies
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by taking `ε → 0⁺` in the
      perturbed PD
    inequality `sandwichedRenyiDiv_monotone_nonneg_perturbed_aux` (`F_λρ, F_λσ` are pd, so
    no support condition is needed and `Q_α > 0` automatically). Taking `λ → 0⁺`, the
    LHS converges to `D_α(Eρ ‖ Eσ)` by nonneg-cone continuity (`Q_α(Eρ‖Eσ) ≠ 0`). -/
private lemma sandwichedRenyiDivNN_monotone_real_aux_lt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    (hQΦρσ : (sandwichedQuasi α (Φ.toFun ρ) (Φ.toFun σ)).re ≠ 0) :
    sandwichedRenyiDiv α (Φ.toFun ρ) (Φ.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hΦρ := map_nonneg Φ.toCompletelyPositiveMap hρ
  have hΦσ := map_nonneg Φ.toCompletelyPositiveMap hσ
  have hΦρ0 := cptp_toFun_ne_zero Φ hρ hρ0
  have hTrΦρ := ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hΦρ hΦρ0)
  -- `Q_α(ρ‖σ) ≠ 0` forces `σ ≠ 0` (otherwise `σ^β = 0` and `Q = 0`).
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQρσ
    rw [sandwichedQuasi_re_eq_zero_iff hα0 hρ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- **Step 1**: for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ) ≤
        sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact sandwichedRenyiDiv_faithfulApprox_le Φ hα_ge hα_lt hρ hσ
      hρ0 hσ0 hQρσ hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`. `(F_λρ, F_λσ) → (Eρ, Eσ)` within the non-negative cone.
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ,
          (faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (Φ.toFun ρ,
        Φ.toFun σ)
        ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(tendsto_faithfulApprox Φ ρ).prodMk_nhds (tendsto_faithfulApprox Φ σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM Φ
        l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM Φ
        l.property.1 l.property.2 hσ hσ0))
  have hcwa : ContinuousWithinAt (fun p : L 𝒦 × L 𝒦 =>
      sandwichedRenyiDiv α p.1 p.2)
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})
      (Φ.toFun ρ, Φ.toFun σ) :=
    continuousWithinAt_sandwichedRenyiDiv_of_lt_one hα0 hα_lt hΦρ hΦσ hQΦρσ hTrΦρ
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    apply Filter.comap_coe_neBot_of_le_principal
    rw [Filter.le_principal_iff]
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with l hl0 hl1
    exact ⟨hl0, hl1⟩
  exact le_of_tendsto (hcwa.tendsto.comp hpair) (Filter.Eventually.of_forall step1)

/-! ### Main theorem: Theorem 1 for non-negative operators, general CPTP maps -/

/-- **Theorem 1 (Frank–Lieb, arXiv:1306.5358v3): Data-processing for the
    sandwiched Rényi relative entropy on non-negative operators.**

    For any bundled CPTP map `Φ`, any
    `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    non-negative `ρ, σ : L ℋ`,

      `D_α^{NN}(Φ ρ ‖ Φ σ) ≤ D_α^{NN}(ρ ‖ σ)`,

    where `D_α^{NN}` is the Frank–Lieb extension (`sandwichedRenyiDivNN`) with
    value `+∞ : EReal` on the support-mismatch region for `α > 1`.

    This declaration covers the real range `α ∈ [1/2, 1) ∪ (1, ∞)` of the
    paper's `1/2 ≤ α ≤ ∞`: the endpoint `α = ∞` is handled by the separate
    declaration `maxRelEntropyNN_monotone`, and the endpoint `α = 1` (the
    relative-entropy limit) is not formalized in this declaration. The
    `ρ = 0` case (both sides equal to the convention value `0`) is a
    Lean-side extension beyond the scope of Theorem 1 of the paper.

Source: this paper, arXiv:2607.05492v1, formalization of the main results in §4 (no individual paper
theorem number is assigned).
Source: arXiv:1306.5358v3, Theorem 1. -/
theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    sandwichedRenyiDivNN α (Φ.toFun ρ)
      (Φ.toFun σ) ≤ sandwichedRenyiDivNN α ρ σ := by
  have hΦρ : 0 ≤ Φ.toFun ρ := map_nonneg Φ.toCompletelyPositiveMap hρ
  have hΦσ : 0 ≤ Φ.toFun σ := map_nonneg Φ.toCompletelyPositiveMap hσ
  by_cases hρ0 : ρ = 0
  · subst ρ
    rw [show Φ.toFun (0 : L ℋ) = 0 by exact Φ.toLinearMap.map_zero]
    simp [sandwichedRenyiDivNN, sandwichedRenyiDiv, SupportLE]
  by_cases hα_gt : 1 < α
  · -- `α > 1`.
    by_cases hsupp : SupportLE (ρ : L ℋ) (σ : L ℋ)
    · have hΦsupp := supportLE_map_of_cptp Φ hρ hσ hsupp
      have h_LHS : sandwichedRenyiDivNN α (Φ.toFun ρ : L 𝒦) (Φ.toFun σ : L 𝒦) =
          ((sandwichedRenyiDiv α (Φ.toFun ρ : L 𝒦)
            (Φ.toFun σ : L 𝒦) : ℝ) : EReal) := by
        unfold sandwichedRenyiDivNN
        rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h hΦsupp
        · linarith
      have h_RHS : sandwichedRenyiDivNN α (ρ : L ℋ) (σ : L ℋ) =
          ((sandwichedRenyiDiv α (ρ : L ℋ) (σ : L ℋ) : ℝ) : EReal) := by
        unfold sandwichedRenyiDivNN
        rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h hsupp
        · linarith
      rw [h_LHS, h_RHS]
      exact_mod_cast sandwichedRenyiDivNN_monotone_real_aux Φ hα_gt hρ hσ
        hsupp hΦsupp hρ0
    · have h_RHS_top : sandwichedRenyiDivNN α (ρ : L ℋ) (σ : L ℋ) = (⊤ : EReal) := by
        unfold sandwichedRenyiDivNN
        exact if_pos (Or.inl ⟨hα_gt, hsupp⟩)
      rw [h_RHS_top]
      exact le_top
  · -- `α < 1`.
    push_neg at hα_gt
    have hα_lt : α < 1 := lt_of_le_of_ne hα_gt hα_ne1
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
      have hQΦρσ := sandwichedQuasi_re_ne_zero_of_CPTP Φ hα_ge hα_lt
        hρ hσ hρ0 hQρσ
      have h_LHS : sandwichedRenyiDivNN α (Φ.toFun ρ : L 𝒦) (Φ.toFun σ : L 𝒦) =
          ((sandwichedRenyiDiv α (Φ.toFun ρ : L 𝒦)
            (Φ.toFun σ : L 𝒦) : ℝ) : EReal) := by
        unfold sandwichedRenyiDivNN
        rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
        · linarith
        · exact hQΦρσ h
      have h_RHS : sandwichedRenyiDivNN α (ρ : L ℋ) (σ : L ℋ) =
          ((sandwichedRenyiDiv α (ρ : L ℋ) (σ : L ℋ) : ℝ) : EReal) := by
        unfold sandwichedRenyiDivNN
        rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
        · linarith
        · exact hQρσ h
      rw [h_LHS, h_RHS]
      exact_mod_cast sandwichedRenyiDivNN_monotone_real_aux_lt Φ hα_ge hα_lt
        hρ hσ hρ0 hQρσ hQΦρσ

end SandwichedRenyiRelativeEntropy
