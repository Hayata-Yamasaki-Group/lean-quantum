/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.QuasiJensen.ConcavitySupportCore

/-!
# Quasi-Jensen concavity on linear endomorphisms

The Jensen–Haar theorem uses the shared cone and integral support layer.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction QuasiJensenSupport
open scoped ComplexOrder NNReal Topology

universe u

section JensenHaarCore

-- The convex branch combines bounded-operator Jensen with `quasiVarOpt` on linear maps;
-- its bridge coercion checks terminate but exceed the default declaration budget.
/-- **Inner Jensen–Haar inequality (isometric Stinespring).**

    For an isometry `V : ℋ →ₗ[ℂ] (𝒦 ⊗ ℋ_env)` with `V*V = I`, let
    `E γ := traceOutRight (V γ V*)` and `τ_max := (dim ℋ_env)⁻¹ • 1`.
    The inequality is

    `Re sandwichedQuasi α ((E ρ) ⊗ τ_max) ((E σ) ⊗ τ_max)`
    `⋚ Re sandwichedQuasi α (V ρ V*) (V σ V*)`,

    with direction `≤` for `α > 1` and `≥` for `α ∈ [1/2, 1)`.

    **Proof (Frank–Lieb arXiv:1306.5358, isometric variant).**
    The non-negative Haar conjugates
    `g_ρ u := (1_𝒦 ⊗ u) · (V ρ V*) · (1_𝒦 ⊗ u*)` may be rank-deficient.
    The right-twirl identity identifies their averages with `(E ρ) ⊗ τ_max`;
    unitary invariance makes `Re Q_α(g_ρ u, g_σ u)` constant.

    For `α ∈ [1/2, 1)`, apply Bochner–Jensen directly to `Re Q_α`, using
    `sandwichedQuasi_re_jointlyConcave_nonneg` and
    `sandwichedQuasi_re_continuousOn_nonneg` on the non-negative cone.

    For `α > 1`, fix `Hopt := quasiVarOpt α Pρ Pσ` at the positive-definite
    average pair `Pρ, Pσ`, where `Re Q_α = Re quasiVar(·,·,Hopt)` is attained.
    Use `quasiVar_re_continuousOn_nonneg` and `quasiVar_re_jointlyConvex_nonneg`
    for this fixed optimizer, then apply
    `GeneralizedPerspectiveFunction.JointlyConvexOn.map_integral_le`.
    The pointwise bound `Re quasiVar(g_ρ u, g_σ u, Hopt) ≤ Re Q_α(g_ρ u, g_σ u)`
    and unitary invariance finish the proof. This branch does not require
    continuity of `Re Q_α` at singular `σ`, where its negative powers obstruct it.

Source: arXiv:1306.5358. -/
theorem jensen_haar_core
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (_hα_ge : (1 : ℝ) / 2 ≤ α) (_hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (_hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (_hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (_hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (_hEρ : traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (_hEσ : traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TensorProduct.map
          (traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map
          (traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α
        ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V))).re) * (α - 1) ≤ 0 := by
  -- `ℋ ⊗ ℋ_env` is again a (nontrivial) qudit.
  haveI : Nontrivial (𝒦 ⊗[ℂ] ℋ_env) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos (Module.finrank_pos) (Module.finrank_pos))
  set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (LinearMap.adjoint V) with hXρ_def
  set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (LinearMap.adjoint V) with hXσ_def
  have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSetLM _hρ
  have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM _hσ
  have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
    rw [hXρ_def]
    exact (LinearMap.nonneg_iff_isPositive _).2
      (((LinearMap.nonneg_iff_isPositive ρ).1 hρ_nn).conj_adjoint V)
  have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
    rw [hXσ_def]
    exact (LinearMap.nonneg_iff_isPositive _).2
      (((LinearMap.nonneg_iff_isPositive σ).1 hσ_nn).conj_adjoint V)
  rcases lt_or_gt_of_ne _hα_ne1 with hα_lt | hα_gt
  · -- **α ∈ [1/2, 1): concave Jensen–Haar.**
    -- Strategy: the Haar integrand `gρ u = (1⊗u)(VρV*)(1⊗u*)` is non-negative and
    -- `Re Q_α` is jointly concave + continuous on the whole non-negative cone, so
    -- Bochner–Jensen gives `∫ Re Q_α(gρ, gσ) ≤ Re Q_α(∫gρ, ∫gσ)`. The integrand is
    -- constant (`= Re Q_α(VρV*, VσV*)` by unitary invariance) and `∫gρ = Eρ ⊗ τmax`
    -- (right twirl), yielding `Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`.
    exact jensen_haar_concave_clm _hα_ge hα_lt Xρ Xσ hXρ_nn hXσ_nn
  · -- **α > 1: convex case, via the Frank–Lieb variational functional `quasiVar`.**
    -- `Re Q_α` is discontinuous at singular `σ`, so we cannot apply Jensen to it directly.
    -- Instead we use that at the (pd) integral point `Pρ = ∫gρ`, `Pσ = ∫gσ`,
    -- `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)` for the optimizer `H*`, that
    -- `quasiVar(·,·,H*)` IS jointly convex + continuous on the psd cone (positive
    -- exponents), and that pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` (reduced via
    -- the single isometry `(1⊗u)∘V` to `quasiVar_le_quasi` on the pd pair `ρ,σ`).
    have hα0 : (0 : ℝ) < α := by linarith
    have hα_ne1 : α ≠ 1 := ne_of_gt hα_gt
    let eT := Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)
    set gρ : unitary (B ℋ_env) →
        B (𝒦 ⊗[ℂ] ℋ_env) :=
      concavityRightTwirlCLM (eT Xρ) with hgρ_def
    set gσ : unitary (B ℋ_env) →
        B (𝒦 ⊗[ℂ] ℋ_env) :=
      concavityRightTwirlCLM (eT Xσ) with hgσ_def
    -- Unitary invariance: the `Re Q_α` integrand is constant.
    have h_inv : ∀ u : unitary (B ℋ_env),
        (sandwichedQuasi α (eT.symm (gρ u)) (eT.symm (gσ u))).re =
          (sandwichedQuasi α Xρ Xσ).re := by
      exact concavity_rightTwirl_quasi_invariant α Xρ Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (eT.symm (gρ u))
          (eT.symm (gσ u))).re) (HaarUnitaryCLM.haarUnitary ℋ_env) := by
      simp_rw [h_inv]; exact integrable_const _
    have h_lhs_int : (∫ u, (sandwichedQuasi α (eT.symm (gρ u))
        (eT.symm (gσ u))).re ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
        (sandwichedQuasi α Xρ Xσ).re := by simp_rw [h_inv]; simp
    -- The pd integral points `Pρ = ∫gρ`, `Pσ = ∫gσ`, and the optimizer `H*`.
    set Pρ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (traceOutRight Xρ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPρ_def
    set Pσ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (traceOutRight Xσ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPσ_def
    have hτmax_pd : ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM
      (ℋ := ℋ_env) :=
      maxmixed_pdSetLM ℋ_env
    have hPρ_pd : Pρ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPρ_def]; exact tensorMap_pdSetLM (by rw [hXρ_def]; exact _hEρ) hτmax_pd
    have hPσ_pd : Pσ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPσ_def]; exact tensorMap_pdSetLM (by rw [hXσ_def]; exact _hEσ) hτmax_pd
    set Hopt := quasiVarOpt α Pρ Pσ with hHopt_def
    have hHopt_pd : Hopt ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) :=
      quasiVarOpt_pdSetLM hα0 hα_ne1 hPρ_pd hPσ_pd
    have hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt := nonneg_of_pdSetLM hHopt_pd
    -- Attainment at the pd point: `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)`.
    have hatt : (sandwichedQuasi α Pρ Pσ).re = (quasiVar α Pρ Pσ Hopt).re := by
      rw [hHopt_def, quasiVarOpt_eq_quasi_gt hα_gt
        ((LinearMap.nonneg_iff_isPositive Pρ).1 (nonneg_of_pdSetLM hPρ_pd))
        ((LinearMap.nonneg_iff_isPositive Pσ).1 (nonneg_of_pdSetLM hPσ_pd))
        (isUnit_of_pdSetLM hPσ_pd)]
    obtain ⟨hquasi_int, hJ⟩ := concavity_rightTwirl_variational_jensen
      hα_gt Xρ Xσ Hopt hXρ_nn hXσ_nn hHopt_pd
    -- Pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` via the isometry `Vu = (1⊗u)∘V`,
    -- outsourced to `quasiVar_haar_integrand_le`.
    have hpoint : ∀ u : unitary (B ℋ_env),
        (quasiVar α (eT.symm (gρ u)) (eT.symm (gσ u)) Hopt).re ≤
          (sandwichedQuasi α (eT.symm (gρ u)) (eT.symm (gσ u))).re := by
      intro u
      simp only [hgρ_def, hgσ_def, hXρ_def, hXσ_def]
      change (quasiVar α
        ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u : B _) : L _)
        ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u : B _) : L _) Hopt).re ≤ _
      rw [concavity_rightTwirlCLM_symm, concavity_rightTwirlCLM_symm]
      exact quasiVar_haar_integrand_le hα_gt hρ_nn hσ_nn _hσ V _hV hHopt_nn
        ((concavityUnitaryEquiv (ℋ := ℋ_env)).symm u)
    -- Combine: `Re Q_α(Pρ,Pσ) ≤ ∫ Re quasiVar ≤ ∫ Re Q_α = Re Q_α(Xρ,Xσ)`.
    have hfinal : (sandwichedQuasi α Pρ Pσ).re ≤ (sandwichedQuasi α Xρ Xσ).re := by
      rw [hatt]
      exact le_trans hJ (integral_mono_eq hquasi_int hfg_int hpoint h_lhs_int)
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfinal) hα1_pos.le

end JensenHaarCore

end SandwichedRenyiRelativeEntropy
