import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.OperatorScalarTower
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.HaarUnitaryMeasureCore
import Quantum.QuantumEntropy.TensorCFCCore

/-!
# Quasi-Jensen cone and positive perturbation helpers

Spectral bounds for `pdSetLM`, closed convex sub-cones, isometric conjugation
helpers, and positive-definite perturbation lemmas used by the Jensen-Haar proof.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

/-! Topological and order-theoretic helpers below live on the canonical CLM carrier. -/

/-- For unitary `u : L ℋ₁`, `TensorProduct.map u 1` is unitary on `L (ℋ₁ ⊗[ℂ]
  ℋ₂)`. -/
private lemma tensorMap_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₁)) :
    TensorProduct.map (u : L ℋ₁) (LinearMap.id (M := ℋ₂)) ∈
      unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  -- `star (TensorProduct.map u id) = TensorProduct.map (star u) id`.
  have h_id_sa : star (LinearMap.id : L ℋ₂) = LinearMap.id := by
    have h_id_one : (LinearMap.id : L ℋ₂) = 1 := rfl
    rw [h_id_one, IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ₂))]
  have h_star_eq :
      star (TensorProduct.map (u : L ℋ₁) (LinearMap.id (M := ℋ₂)) : L (ℋ₁ ⊗[ℂ]
        ℋ₂)) =
      TensorProduct.map (star (u : L ℋ₁)) (LinearMap.id (M := ℋ₂)) := by
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, h_id_sa]
  have h_id_mul_id : (LinearMap.id : L ℋ₂) * LinearMap.id = 1 := mul_one _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · -- star (T(u,1)) * T(u,1) = T(star u * u, 1 * 1) = T(1, 1) = 1
    rw [h_star_eq, ← TensorProduct.map_mul, (Unitary.mem_iff.mp u.property).1, h_id_mul_id]
    exact TensorProduct.map_one
  · rw [h_star_eq, ← TensorProduct.map_mul, (Unitary.mem_iff.mp u.property).2, h_id_mul_id]
    exact TensorProduct.map_one

@[deprecated (since := "2026-09-05")]
alias tensorMap_right_star := TensorCFC.tensorMap_right_star

/-- For unitary `u : L ℋ₂`, `TensorProduct.map 1 u` is unitary on `L (ℋ₁ ⊗[ℂ]
  ℋ₂)`. -/
lemma tensorMap_right_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₂)) :
    TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) ∈
      unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  have h_id_mul_id : (LinearMap.id : L ℋ₁) * LinearMap.id = 1 := mul_one _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [TensorCFC.tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).1]
    exact TensorProduct.map_one
  · rw [TensorCFC.tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).2]
    exact TensorProduct.map_one

/-- The non-negative cone `{A | 0 ≤ A}` of continuous endomorphisms is convex. -/
@[deprecated convex_Ici (since := "2026-09-05")]
lemma convex_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    Convex ℝ {A : B 𝒦 | (0 : B 𝒦) ≤ A} :=
  convex_Ici (𝕜 := ℝ) (0 : B 𝒦)

/-- The non-negative cone `{A | 0 ≤ A}` of continuous endomorphisms is closed. -/
@[deprecated isClosed_Ici (since := "2026-09-05")]
lemma isClosed_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    IsClosed {A : B 𝒦 | (0 : B 𝒦) ≤ A} :=
  isClosed_Ici

private noncomputable def isometricConjLM
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') : L ℋ →ₗ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    ext x
    simp
  map_smul' c σ := by
    ext x
    simp

private noncomputable def isometricConjHomLM
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    L ℋ →⋆ₙₐ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    ext x
    simp
  map_smul' c σ := by
    ext x
    simp
  map_zero' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    change V (σ (τ ((LinearMap.adjoint V) x))) =
      V (σ ((LinearMap.adjoint V) (V (τ ((LinearMap.adjoint V) x)))))
    have h_id (y : ℋ) : (LinearMap.adjoint V) (V y) = y := by
      have hy := LinearMap.congr_fun hV y
      simpa [LinearMap.comp_apply] using hy
    rw [h_id]
  map_star' σ := by
    change (V.comp (star σ)).comp (LinearMap.adjoint V) =
      star ((V.comp σ).comp (LinearMap.adjoint V))
    rw [show (star σ : L ℋ) = LinearMap.adjoint σ from
        LinearMap.star_eq_adjoint σ,
      show (star ((V.comp σ).comp (LinearMap.adjoint V)) : L ℋ') =
        LinearMap.adjoint ((V.comp σ).comp (LinearMap.adjoint V)) from
          LinearMap.star_eq_adjoint _,
      LinearMap.adjoint_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, ← LinearMap.comp_assoc]

/-- Continuity of the isometric-conjugation map (needed to apply `map_cfcₙ`).
    Follows from `continuous_of_finiteDimensional` on the underlying linear map. -/
private lemma isometricConjHom_continuous
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    Continuous (isometricConjHomLM V hV) := by
  change Continuous (isometricConjLM V)
  exact (isometricConjLM V).continuous_of_finiteDimensional

/-- The `ℝ`-quasispectrum of any operator on a finite-dimensional qudit is finite:
    `spectrum ℂ a` is finite (`Module.End.finite_spectrum`), `spectrum ℝ a` is its
    preimage under the injective `algebraMap ℝ ℂ`, and the quasispectrum adds only `0`. -/
private lemma quasispectrum_finite {ℋ : Type u} [Qudit ℋ] (a : L ℋ) :
    (quasispectrum ℝ a).Finite := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [quasispectrum_eq_spectrum_union_zero, ← spectrum.preimage_algebraMap ℂ]
  exact ((Module.End.finite_spectrum a).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn).union (Set.finite_singleton 0)

private lemma nonUnital_rpow_map
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (ψ : L ℋ →⋆ₙₐ[ℂ] L ℋ') (hψ : Continuous ψ)
    {A : L ℋ} (hA : 0 ≤ A) (hψA : 0 ≤ ψ A) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow (ψ A) p = ψ (CFC.rpow A p) := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  letI : IsScalarTower ℝ ℂ (L ℋ') :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ')
  let f : ℝ → ℝ := fun x => x ^ p
  have hf0 : f 0 = 0 := by simp [f, Real.zero_rpow hp]
  have hcontA : ContinuousOn f (quasispectrum ℝ A) :=
    (quasispectrum_finite A).continuousOn _
  have hcontψA : ContinuousOn f (quasispectrum ℝ (ψ A)) :=
    (quasispectrum_finite (ψ A)).continuousOn _
  have hAeq : CFC.rpow A p = cfc f A := CFC.rpow_eq_cfc_real (ha := hA)
  have hψAeq : CFC.rpow (ψ A) p = cfc f (ψ A) := CFC.rpow_eq_cfc_real (ha := hψA)
  have hcfcA : cfcₙ f A = cfc f A := cfcₙ_eq_cfc hcontA hf0
  have hcfcψA : cfcₙ f (ψ A) = cfc f (ψ A) := cfcₙ_eq_cfc hcontψA hf0
  rw [hAeq, hψAeq, ← hcfcA, ← hcfcψA]
  exact (NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) ψ f A hcontA hf0 hψ
    (IsSelfAdjoint.of_nonneg hA) (IsSelfAdjoint.of_nonneg hψA)).symm

/-- **Isometric `rpow` covariance.** For an isometry `V` with `V*V = 1`, a non-negative
    `ω`, and any *nonzero* real `p`: `(V ω V*)^p = V (ω^p) V*`. This is valid even for
    `p < 0`: the function `x ↦ x ^ p` is globally discontinuous at `0`, but the
    quasispectrum of any operator here is finite (so `0` is isolated), hence the function
    is `ContinuousOn` it and the non-unital ⋆-hom naturality `map_cfcₙ` applies. -/
private lemma isometricConj_rpow {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {ω : L ℋ} (hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow (isometricConjHomLM V hV ω) p =
      isometricConjHomLM V hV (CFC.rpow ω p) := by
  let ψ := isometricConjHomLM V hV
  have hψ_cont : Continuous ψ := isometricConjHom_continuous V hV
  have hψω_nn : (0 : L ℋ') ≤ ψ ω := map_nonneg ψ hω
  exact nonUnital_rpow_map ψ hψ_cont hω hψω_nn hp

/-- **Isometric invariance of sandwichedQuasi** (valid for all `α > 0`, `α ≠ 1`).

    For an isometry `V : ℋ →ₗ[ℂ] ℋ'` with `V*V = I` and `ρ, σ ≥ 0`,
    `sandwichedQuasi α (V ρ V*) (V σ V*) = sandwichedQuasi α ρ σ`.

    **No convention obstruction in finite dimensions.** Even for `α > 1`, where
    `β = (1 − α) / (2 α) < 0`, the identity still holds: `CFC.rpow (V σ V*) β`
    does *not* collapse to `0`. The function `x ↦ x ^ β` is discontinuous at `0`
    on `ℝ`, but the *quasispectrum* of `V σ V*` is finite (so `0` is an isolated
    point), hence `x ↦ x ^ β` is `ContinuousOn` it and the non-unital ⋆-hom
    naturality `NonUnitalStarAlgHomClass.map_cfcₙ` — which requires only
    `ContinuousOn` over the quasispectrum, not global continuity — applies. The
    result is the support-restricted `V σ^β V*`, exactly as in the `α < 1` case.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
lemma sandwichedQuasi_isometric_conj
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : (0 : L ℋ) ≤ ρ) (hσ : (0 : L ℋ) ≤ σ) :
    sandwichedQuasi α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ := by
  let ψ := isometricConjHomLM V hV
  have h_tr_conj (X : L ℋ) : Tr (ψ X) = Tr X := by
    change Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]
    rfl
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct]
  change Tr (CFC.rpow
      (CFC.rpow (ψ σ) ((1 - α) / (2 * α)) * ψ ρ *
        CFC.rpow (ψ σ) ((1 - α) / (2 * α))) α) =
    Tr (CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α)
  set β := (1 - α) / (2 * α) with hβ_def
  have hβ_ne : β ≠ 0 := by
    rw [hβ_def]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  have hinner_nn : (0 : L ℋ) ≤
      CFC.rpow σ β * ρ * CFC.rpow σ β := by
    have hP_nn : (0 : L ℋ) ≤ CFC.rpow σ β := CFC.rpow_nonneg
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg hP_nn
    have hconj := star_left_conjugate_nonneg hρ (CFC.rpow σ β)
    rwa [hP_sa.star_eq] at hconj
  rw [isometricConj_rpow V hV hσ hβ_ne,
    ← map_mul ψ, ← map_mul ψ,
    isometricConj_rpow V hV hinner_nn (ne_of_gt hα0), h_tr_conj]

/-- **Isometric covariance of the variational functional `quasiVar`** (all `α > 0`,
    `α ≠ 1`). For an isometry `V` (`V*V = 1`), nonneg `σ`, nonneg `G`,
    `quasiVar α (V ρ V*) (V σ V*) G = quasiVar α ρ σ (V* G V)`.

    All `CFC.rpow` exponents appearing (`(α−1)/(2α)` and `α/(α−1)`) are nonzero, so
    `isometricConj_rpow` applies; the inner sandwich identity
    `(V σ^c V*) G (V σ^c V*) = V (σ^c (V* G V) σ^c) V*` is pure associativity. -/
lemma quasiVar_isometric_conj {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hσ : (0 : L ℋ) ≤ σ) {G : L ℋ'} (hG : (0 : L ℋ') ≤ G) :
    quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) G =
      quasiVar α ρ σ ((LinearMap.adjoint V).comp (G.comp V)) := by
  let ψ := isometricConjHomLM V hV
  set GV : L ℋ := (LinearMap.adjoint V).comp (G.comp V) with hGV_def
  set c : ℝ := (α - 1) / (2 * α) with hc_def
  set q : ℝ := α / (α - 1) with hq_def
  have hc_ne : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα_ne1) (by positivity)
  have hq_ne : q ≠ 0 := div_ne_zero (ne_of_gt hα0) (sub_ne_zero.mpr hα_ne1)
  have hGV_nn : (0 : L ℋ) ≤ GV :=
    (LinearMap.nonneg_iff_isPositive _).2 <| by
      rw [hGV_def]
      exact ((LinearMap.nonneg_iff_isPositive G).1 hG).adjoint_conj V
  have h_tr_conj (X : L ℋ) : Tr (ψ X) = Tr X := by
    change Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]; rfl
  have hterm1 : Tr (G * ψ ρ) = Tr (GV * ρ) := by
    rw [show ψ ρ = (V.comp ρ).comp (LinearMap.adjoint V) from rfl, hGV_def]
    change Tr (((G.comp V).comp ρ).comp (LinearMap.adjoint V)) =
      Tr (((LinearMap.adjoint V).comp (G.comp V)).comp ρ)
    rw [LinearMap.trace_comp_comm']
    rfl
  have hinner : ψ (CFC.rpow σ c) * G * ψ (CFC.rpow σ c) =
      ψ (CFC.rpow σ c * GV * CFC.rpow σ c) := by
    rw [hGV_def]
    ext x
    rfl
  have hY_nn : (0 : L ℋ) ≤
      CFC.rpow σ c * GV * CFC.rpow σ c := by
    have hP_nn : (0 : L ℋ) ≤ CFC.rpow σ c := CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hGV_nn (CFC.rpow σ c)
    rwa [(IsSelfAdjoint.of_nonneg hP_nn).star_eq] at h
  change quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V)) G = quasiVar α ρ σ GV
  rw [quasiVar_eq_direct, quasiVar_eq_direct]
  change (α : ℂ) * Tr (G * ψ ρ) -
      ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow (ψ σ) ((α - 1) / (2 * α)) * G *
          CFC.rpow (ψ σ) ((α - 1) / (2 * α))) (α / (α - 1))) =
    (α : ℂ) * Tr (GV * ρ) -
      ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * GV *
          CFC.rpow σ ((α - 1) / (2 * α))) (α / (α - 1)))
  rw [← hc_def, ← hq_def, isometricConj_rpow V hV hσ hc_ne, hinner,
      isometricConj_rpow V hV hY_nn hq_ne, h_tr_conj, hterm1]

/-! ### Positive-definite perturbations `A + ε • 1` (used for the cone arguments) -/

/-- From non-negativity and invertibility, conclude positive-definiteness in `pdSetLM`
    (the spectrum is `≥ 0` by positivity and avoids `0` by invertibility). -/
lemma pdSetLM_of_nonneg_isUnit {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (h_nn : (0 : L ℋ) ≤ A) (h_unit : IsUnit A) : A ∈ pdSetLM (ℋ := ℋ) := by
  apply (pdSetLM_strictPositivity_certificate _).2
  exact h_unit.isStrictlyPositive h_nn

/-- The tensor product `A ⊗ B` of two positive-definite operators is positive-definite.
    Non-negativity comes from `A ⊗ B = T * T` with `T = √A ⊗ √B` self-adjoint
    (`T * T = T * T*` is positive); invertibility from the inverse `A⁻¹ ⊗ B⁻¹`. -/
lemma tensorMap_pdSetLM {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial
  ℋ₁] [Nontrivial ℋ₂]
    {A : L ℋ₁} {B : L ℋ₂} (hA : A ∈ pdSetLM (ℋ := ℋ₁)) (hB : B ∈ pdSetLM (ℋ
      := ℋ₂)) :
    TensorProduct.map A B ∈ pdSetLM (ℋ := ℋ₁ ⊗[ℂ] ℋ₂) := by
  exact pdSetLM_tensorMap hA hB

end SandwichedRenyiRelativeEntropy
