/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.QuasiJensen.Cone
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.Defs
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.JointConvexity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.PositiveDefiniteCertificates

/-!
# Quasi-Jensen continuity and concavity

Continuity of the real sandwiched quasi-entropy on the non-negative cone,
convexity/concavity extensions from `pdSetLM`, and the inner Jensen-Haar core.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

/-! Continuity, functional-calculus, and Haar arguments are carried out on the canonical
CLM carrier and transported back only at public LM boundaries. -/

/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/

/-- For `α > 1` and a fixed non-negative `H`, the real part of the variational functional
    `quasiVar α ρ σ H` is jointly continuous on the non-negative cone. The `σ`-exponents
    `(α-1)/(2α)` and `α/(α-1)` are both positive (continuous up to the cone boundary), and
    the `ρ`-term `α (Tr (H ρ))` is linear hence continuous everywhere. -/
private lemma quasiVar_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : B 𝒦}
    (hH : (0 : B 𝒦) ≤ H) :
    ContinuousOn (Function.uncurry (fun (ρ σ : B 𝒦) =>
      (quasiVar α
        (ρ : L 𝒦) (σ : L 𝒦) (H : L 𝒦)).re))
      ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
        {A : B 𝒦 | (0 : B 𝒦) ≤ A}) := by
  set c : ℝ := (α - 1) / (2 * α) with hc
  have hc_nn : 0 ≤ c := le_of_lt (div_pos (by linarith) (by linarith))
  set q : ℝ := α / (α - 1) with hq
  have hq_nn : 0 ≤ q := le_of_lt (div_pos (by linarith) (by linarith))
  set S : Set (B 𝒦) :=
    {A : B 𝒦 | (0 : B 𝒦) ≤ A} with hS
  -- `ρ`-term `(Tr (H * ρ)).re`, continuous everywhere.
  have hTr : Continuous (fun A : B 𝒦 => (traceCLM A).re) :=
    Complex.continuous_re.comp traceCLM.continuous
  have h_rho : Continuous
      (fun p : B 𝒦 × B 𝒦 => (traceCLM (H * p.1)).re) :=
    hTr.comp (continuous_const.mul continuous_fst)
  -- `σ`-term `(Tr ((σ^c H σ^c)^q)).re`, continuous on the cone.
  have h_rpow_snd : ContinuousOn
      (fun p : B 𝒦 × B 𝒦 => CFC.rpow p.2 c)
      (S ×ˢ S) :=
    (rpow_continuousOn_nonneg hc_nn).comp continuous_snd.continuousOn
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_inner_cont :
      ContinuousOn (fun p : B 𝒦 × B 𝒦 =>
        CFC.rpow p.2 c * H * CFC.rpow p.2 c) (S ×ˢ S) :=
    (h_rpow_snd.mul continuousOn_const).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S,
      (0 : B 𝒦) ≤ CFC.rpow p.2 c * H * CFC.rpow p.2 c := by
    rintro ⟨ρ, σ⟩ _
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hH (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : B 𝒦 × B 𝒦 =>
        CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q) (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ q))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hq_nn).continuousOn)
  have h_sigma :
      ContinuousOn (fun p : B 𝒦 × B 𝒦 =>
        (traceCLM (CFC.rpow
          (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re) (S ×ˢ S) :=
    hTr.comp_continuousOn h_pow_cont
  have hfinal : ContinuousOn
      (fun p : B 𝒦 × B 𝒦 =>
      α * (traceCLM (H * p.1)).re -
        (α - 1) * (traceCLM (CFC.rpow
          (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re) (S ×ˢ S) :=
    (continuous_const.mul h_rho).continuousOn.sub (continuousOn_const.mul h_sigma)
  refine hfinal.congr ?_
  rintro ⟨ρ, σ⟩ ⟨_hρ, _hσ⟩
  simpa [hc, hq, traceCLM, Complex.sub_re, Complex.re_ofReal_mul] using
    congrArg Complex.re (quasiVar_eq_clm_direct α ρ σ H)

/-- The perturbation `ε • 1` commutes with convex combinations. -/
private lemma convexCombo_add_smul_one {𝒦 : Type u} [Qudit 𝒦] (θ : ℝ) (a₁ a₂ : B 𝒦)
    (ε : ℝ) :
    ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
      (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
  have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : B 𝒦)) +
      (θ : ℝ) • ((ε : ℂ) • (1 : B 𝒦)) =
      (ε : ℂ) • (1 : B 𝒦) := by
    rw [← add_smul]; norm_num
  simp only [smul_add]
  rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
      ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
    h1]

/-- A non-negative operator perturbed by `ε • 1` (`ε > 0`) is positive definite. -/
private lemma add_smul_one_mem_pdSet {𝒦 : Type u} [Qudit 𝒦] {A : B 𝒦} (hA : (0 : B 𝒦) ≤ A)
    {ε : ℝ} (hε : 0 < ε) : A + (ε : ℂ) • 1 ∈ pdSet (ℋ := 𝒦) := by
  apply (pdSet_membership_certificate _).2
  exact IsStrictlyPositive.nonneg_add hA
    (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε) isStrictlyPositive_one)

/-- A function jointly continuous on the non-negative cone is the limit of its values at the
perturbations `(a + ε • 1, b + ε • 1)` as `ε → 0⁺`. -/
private lemma tendsto_add_smul_one_of_continuousOn {𝒦 : Type u} [Qudit 𝒦]
    {F : B 𝒦 → B 𝒦 → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
    {a b : B 𝒦} (ha : (0 : B 𝒦) ≤ a) (hb : (0 : B 𝒦) ≤ b) :
    Filter.Tendsto (fun ε : ℝ => F (a + (ε : ℂ) • 1) (b + (ε : ℂ) • 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (F a b)) := by
  have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) :=
    by fun_prop
  have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
        ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ {A : B 𝒦 | (0 : B 𝒦) ≤ A}) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hsmul : (0 : B 𝒦) ≤ (ε : ℂ) • (1 : B 𝒦) :=
      (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε') isStrictlyPositive_one).nonneg
    exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
  have h_tendsto_curve :
      Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (a, b)
          ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ {A : B 𝒦 | (0 : B 𝒦) ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, h_into⟩
    have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
        (nhds (0 : ℝ)) (nhds (a, b)) := by
      have h := hcurve.tendsto 0; simpa using h
    exact h0.mono_left nhdsWithin_le_nhds
  exact Filter.Tendsto.comp (hcont (a, b) ⟨ha, hb⟩) h_tendsto_curve

/-- Joint convexity extends from `pdSet` to the non-negative cone for a jointly continuous
function, by the `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε • 1, σ + ε • 1)`. -/
private lemma jointlyConvexOn_nonneg_of_pdSet {𝒦 : Type u} [Qudit 𝒦]
    {F : B 𝒦 → B 𝒦 → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
    (hpd : JointlyConvexOn (pdSet (ℋ := 𝒦)) (pdSet (ℋ := 𝒦)) F) :
    JointlyConvexOn {A : B 𝒦 | (0 : B 𝒦) ≤ A} {A : B 𝒦 | (0 : B 𝒦) ≤ A} F := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  have hρc : (0 : B 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : B 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  refine le_of_tendsto_of_tendsto (tendsto_add_smul_one_of_continuousOn hcont hρc hσc)
    (((tendsto_add_smul_one_of_continuousOn hcont hρ₁ hσ₁).const_smul (1 - θ)).add
      ((tendsto_add_smul_one_of_continuousOn hcont hρ₂ hσ₂).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [convexCombo_add_smul_one θ ρ₁ ρ₂ ε, convexCombo_add_smul_one θ σ₁ σ₂ ε]
  exact hpd (add_smul_one_mem_pdSet hρ₁ hε) (add_smul_one_mem_pdSet hρ₂ hε)
    (add_smul_one_mem_pdSet hσ₁ hε) (add_smul_one_mem_pdSet hσ₂ hε) hθ0 hθ1

/-- Joint concavity extends from `pdSet` to the non-negative cone for a jointly continuous
function, by the `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε • 1, σ + ε • 1)`. -/
private lemma jointlyConcaveOn_nonneg_of_pdSet {𝒦 : Type u} [Qudit 𝒦]
    {F : B 𝒦 → B 𝒦 → ℝ}
    (hcont : ContinuousOn (Function.uncurry F)
      ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
    (hpd : JointlyConcaveOn (pdSet (ℋ := 𝒦)) (pdSet (ℋ := 𝒦)) F) :
    JointlyConcaveOn {A : B 𝒦 | (0 : B 𝒦) ≤ A} {A : B 𝒦 | (0 : B 𝒦) ≤ A} F := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  have hρc : (0 : B 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : B 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  refine le_of_tendsto_of_tendsto
    (((tendsto_add_smul_one_of_continuousOn hcont hρ₁ hσ₁).const_smul (1 - θ)).add
      ((tendsto_add_smul_one_of_continuousOn hcont hρ₂ hσ₂).const_smul θ))
    (tendsto_add_smul_one_of_continuousOn hcont hρc hσc) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [convexCombo_add_smul_one θ ρ₁ ρ₂ ε, convexCombo_add_smul_one θ σ₁ σ₂ ε]
  exact hpd (add_smul_one_mem_pdSet hρ₁ hε) (add_smul_one_mem_pdSet hρ₂ hε)
    (add_smul_one_mem_pdSet hσ₁ hε) (add_smul_one_mem_pdSet hσ₂ hε) hθ0 hθ1

section JointlyConvexNonneg
attribute [local irreducible] quasiVar

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` extends from `pdSet` to the whole
    non-negative cone (fixed pd `H`, `α > 1`), by the same `ε → 0⁺` perturbation + joint
    continuity (`quasiVar_re_continuousOn_nonneg`) argument as the concave case. -/
private lemma quasiVar_re_jointlyConvex_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : B 𝒦} (hH : H ∈ pdSet (ℋ := 𝒦)) :
    JointlyConvexOn
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      (fun ρ σ => (quasiVar (ℋ := 𝒦) α
        (ρ : L 𝒦) (σ : L 𝒦) (H : L 𝒦)).re) :=
  jointlyConvexOn_nonneg_of_pdSet
    (quasiVar_re_continuousOn_nonneg (𝒦 := 𝒦) hα ((pdSet_membership_certificate H).1 hH).nonneg)
    (quasiVar_re_jointlyConvex_pdSetLM (ℋ := 𝒦) hα hH)

end JointlyConvexNonneg

section JointlyConcaveNonneg
-- `sandwichedQuasi` is treated as a black box here (only continuity, the pd Jensen
-- inequality, and limits are used), so making it irreducible avoids the unifier
-- unfolding the large CFC expression during def-eq checks.
attribute [local irreducible] sandwichedQuasi

/-- **Proposition 3 on the non-negative cone (concave case, `1/2 ≤ α < 1`).**
    Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` extends from `pdSet` to the whole
    non-negative cone by an `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε•1, σ +
      ε•1)`, using
    joint continuity on the cone (`sandwichedQuasi_re_continuousOn_nonneg`). -/
private lemma sandwichedQuasi_re_jointlyConcave_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial
  𝒦]
    {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      (fun ρ σ => (sandwichedQuasi (ℋ := 𝒦) α
        (ρ : L 𝒦) (σ : L 𝒦)).re) :=
  jointlyConcaveOn_nonneg_of_pdSet
    (sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) (by linarith) hα_lt.le)
    (sandwichedQuasi_re_jointlyConcave (ℋ := 𝒦) hα_ge hα_lt)

end JointlyConcaveNonneg

/-! ### CLM transport for the Jensen--Haar consumer -/

-- These definitions are used only through their continuity/convexity interfaces below.
-- Keeping them opaque prevents bridge composition from unfolding their large CFC bodies.
attribute [local irreducible] sandwichedQuasi quasiVar

private noncomputable def concavityUnitaryEquiv {ℋ : Type u} [Qudit ℋ] :
    unitary (L ℋ) ≃⋆* unitary (B ℋ) := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  let es : L ℋ ≃⋆* B ℋ := { e.toStarRingEquiv with }
  exact Unitary.mapEquiv es

private noncomputable def concavityRightTwirlCLM
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    (X : B (𝒦 ⊗[ℂ] ℋ_env))
    (u : unitary (B ℋ_env)) :
    B (𝒦 ⊗[ℂ] ℋ_env) :=
  HaarUnitaryCLM.tensorMap (1 : B 𝒦) (u : B ℋ_env) * X *
    HaarUnitaryCLM.tensorMap (1 : B 𝒦) (star (u : B ℋ_env))

private lemma concavity_tensorMap_eq_mul_clm
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    HaarUnitaryCLM.tensorMap A B =
      TensorCFC.rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A *
        TensorCFC.lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((TensorCFC.rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁) *
      (TensorCFC.lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_rTensor_mul_lTensor (A : L ℋ₁) (B : L ℋ₂))

private lemma concavity_tensorMap_eq_mul_comm_clm
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    HaarUnitaryCLM.tensorMap A B =
      TensorCFC.lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B *
        TensorCFC.rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((TensorCFC.lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂) *
      (TensorCFC.rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_lTensor_mul_rTensor (A : L ℋ₁) (B : L ℋ₂))

private lemma concavity_tensorMap_star_clm
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    star (HaarUnitaryCLM.tensorMap A B) =
      HaarUnitaryCLM.tensorMap (star A) (star B) := by
  rw [concavity_tensorMap_eq_mul_clm, star_mul]
  rw [← map_star (TensorCFC.lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) B,
    ← map_star (TensorCFC.rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) A]
  exact (concavity_tensorMap_eq_mul_comm_clm (star A) (star B)).symm

private lemma concavity_tensorMap_bridge
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] (A : L ℋ₁) (B : L ℋ₂) :
    (TensorProduct.map A B).toContinuousLinearMap =
      HaarUnitaryCLM.tensorMap
        A.toContinuousLinearMap B.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  simp only [HaarUnitaryCLM.tensorMap_toLinearMap, LinearMap.coe_toContinuousLinearMap]

private lemma concavity_traceOutRight_bridge
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    (QuantumChannel.traceOutRight X).toContinuousLinearMap =
      HaarUnitaryCLM.traceOutRight
        X.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  simp only [HaarUnitaryCLM.traceOutRight_toLinearMap, LinearMap.coe_toContinuousLinearMap]

private lemma concavity_rightTwirl_rhs_bridge
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env] (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
    HaarUnitaryCLM.tensorMap
        (HaarUnitaryCLM.traceOutRight
          X.toContinuousLinearMap)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : B ℋ_env)) =
      (TensorProduct.map (QuantumChannel.traceOutRight X)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))).toContinuousLinearMap := by
  symm
  calc
    (TensorProduct.map (QuantumChannel.traceOutRight X)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))).toContinuousLinearMap =
      HaarUnitaryCLM.tensorMap
        (QuantumChannel.traceOutRight X).toContinuousLinearMap
        (((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)).toContinuousLinearMap) :=
      concavity_tensorMap_bridge _ _
    _ = _ := by
      rw [concavity_traceOutRight_bridge]
      congr 1

private lemma concavity_rightTwirlCLM_symm
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    (X : L (𝒦 ⊗[ℂ] ℋ_env)) (u : unitary (B ℋ_env)) :
    ((concavityRightTwirlCLM X.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) =
      TensorProduct.map (LinearMap.id (M := 𝒦))
          (((concavityUnitaryEquiv (ℋ := ℋ_env)).symm u : unitary (L ℋ_env)) : L ℋ_env)
            * X *
        TensorProduct.map (LinearMap.id (M := 𝒦))
          (star (((concavityUnitaryEquiv (ℋ := ℋ_env)).symm u :
            unitary (L ℋ_env)) : L ℋ_env)) := by
  let e := Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)
  let uLM := (concavityUnitaryEquiv (ℋ := ℋ_env)).symm u
  have hu : (uLM : L ℋ_env).toContinuousLinearMap =
      (u : B ℋ_env) := by
    exact congrArg Subtype.val ((concavityUnitaryEquiv (ℋ := ℋ_env)).apply_symm_apply u)
  have hstar (A : L ℋ_env) :
      (star A).toContinuousLinearMap = star A.toContinuousLinearMap := by
    change (LinearMap.adjoint A).toContinuousLinearMap = star A.toContinuousLinearMap
    simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A))
  rw [ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  change concavityRightTwirlCLM X.toContinuousLinearMap u = e (_ * X * _)
  rw [map_mul, map_mul]
  rw [concavityRightTwirlCLM]
  change _ =
    (TensorProduct.map (LinearMap.id (M := 𝒦)) (uLM : L ℋ_env)).toContinuousLinearMap *
      X.toContinuousLinearMap *
      (TensorProduct.map (LinearMap.id (M := 𝒦))
        (star (uLM : L ℋ_env))).toContinuousLinearMap
  rw [
    concavity_tensorMap_bridge, concavity_tensorMap_bridge, hu, hstar, hu]
  rfl

private lemma clm_convex_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    Convex ℝ {A : B 𝒦 | (0 : B 𝒦) ≤ A} := by
  intro a ha b hb θ θ' hθ hθ' _hsum
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  exact add_nonneg (smul_nonneg hθ ha) (smul_nonneg hθ' hb)

private lemma clm_isClosed_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    IsClosed {A : B 𝒦 | (0 : B 𝒦) ≤ A} :=
  isClosed_Ici

/-- The right twirl integrand of a non-negative operator is non-negative. -/
private lemma concavityRightTwirlCLM_nonneg {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    {X : B (𝒦 ⊗[ℂ] ℋ_env)} (hX : (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ X) (u : unitary (B ℋ_env)) :
    (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ concavityRightTwirlCLM X u := by
  rw [concavityRightTwirlCLM]
  have h := star_left_conjugate_nonneg hX
    (star (HaarUnitaryCLM.tensorMap (1 : B 𝒦) (u : B ℋ_env)))
  have hstar := concavity_tensorMap_star_clm (1 : B 𝒦) (u : B ℋ_env)
  rw [star_one] at hstar
  rw [star_star] at h
  rwa [← hstar]

/-- The right twirl integrand is Haar-integrable. -/
private lemma integrable_concavityRightTwirlCLM {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    [Nontrivial ℋ_env] (X : B (𝒦 ⊗[ℂ] ℋ_env)) :
    Integrable (concavityRightTwirlCLM X) (HaarUnitaryCLM.haarUnitary ℋ_env) := by
  simpa only [concavityRightTwirlCLM] using
    HaarUnitaryCLM.integrable_unitaryConj_tensor_right X

/-- The right twirl integrand is continuous. -/
private lemma continuous_concavityRightTwirlCLM {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    (X : B (𝒦 ⊗[ℂ] ℋ_env)) : Continuous (concavityRightTwirlCLM X) := by
  simpa only [concavityRightTwirlCLM] using
    HaarUnitaryCLM.continuous_unitaryConj_tensor_right X

/-- Right-twirl collapse of the integral, on the linear-map carrier. -/
private lemma integral_concavityRightTwirlCLM {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    [Nontrivial ℋ_env] (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
    (∫ u, concavityRightTwirlCLM (Module.End.toContinuousLinearMap (𝕜 := ℂ)
        (𝒦 ⊗[ℂ] ℋ_env) X) u ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
      Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)
        (TensorProduct.map (traceOutRight X)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))) := by
  calc
    (∫ u, concavityRightTwirlCLM (Module.End.toContinuousLinearMap (𝕜 := ℂ)
        (𝒦 ⊗[ℂ] ℋ_env) X) u ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
        HaarUnitaryCLM.tensorMap (HaarUnitaryCLM.traceOutRight
          (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) X))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : B ℋ_env)) := by
      simpa only [concavityRightTwirlCLM] using
        HaarUnitaryCLM.twirl_eq_partialTrace_right_smul_id
          (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) X)
    _ = _ := concavity_rightTwirl_rhs_bridge X

/-- Unitary invariance: the real sandwiched quasi-entropy of the right-twirl integrands is
constant in `u`. -/
private lemma sandwichedQuasi_re_concavityRightTwirlCLM {𝒦 ℋ_env : Type u} [Qudit 𝒦]
    [Nontrivial 𝒦] [Qudit ℋ_env] [Nontrivial ℋ_env] (α : ℝ) (X Y : L (𝒦 ⊗[ℂ] ℋ_env))
    (u : unitary (B ℋ_env)) :
    (sandwichedQuasi α
      ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
        (concavityRightTwirlCLM
          (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) X) u))
      ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
        (concavityRightTwirlCLM
          (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Y) u))).re =
      (sandwichedQuasi α X Y).re := by
  let uLM := (concavityUnitaryEquiv (ℋ := ℋ_env)).symm u
  let U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
    ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env),
      tensorMap_right_unitary_of_unitary uLM⟩
  have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
      TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env) :=
    rfl
  have hg (Z : L (𝒦 ⊗[ℂ] ℋ_env)) :
      (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
        (concavityRightTwirlCLM
          (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Z) u) =
        (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Z * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
    change ((concavityRightTwirlCLM Z.toContinuousLinearMap u :
      B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) = _
    rw [concavity_rightTwirlCLM_symm]
    simp only [uLM, hUcoe, TensorCFC.tensorMap_right_star]
  rw [hg X, hg Y, sandwichedQuasi_unitary_conj α X Y U]

section JensenHaarCore
-- `sandwichedQuasi`/`quasiVar` are treated as black boxes (only via lemmas), so making
-- them irreducible avoids the unifier unfolding their large CFC expressions during the
-- many `rw`/`isDefEq` checks in the proof.  The local attribute above remains in scope.

/-- Pointwise variational bound for the Haar integrand of `jensen_haar_core` (`α > 1`):
    conjugating the pair `ρ, σ` by the isometry `Vu = (1 ⊗ u) ∘ V` reduces
    `Re quasiVar(gρ u, gσ u, H) ≤ Re Q_α(gρ u, gσ u)` to `quasiVar_le_quasi` on `ρ, σ`.
    Extracted from `jensen_haar_core` so that the heavy isometric-conjugation rewrites
    (`quasiVar_isometric_conj` / `sandwichedQuasi_isometric_conj` on the large tensor
    terms) get their own heartbeat budget instead of exhausting the main proof's one. -/
private lemma quasiVar_haar_integrand_le
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ_nn : (0 : L ℋ) ≤ ρ) (hσ_nn : (0 : L ℋ) ≤ σ)
    (hσ_pd : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {Hopt : L (𝒦 ⊗[ℂ] ℋ_env)} (hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt)
    (u : unitary (L ℋ_env)) :
    (quasiVar α
        (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) *
            ((V.comp ρ).comp (LinearMap.adjoint V)) *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)))
        (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) *
            ((V.comp σ).comp (LinearMap.adjoint V)) *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)))
        Hopt).re ≤
      (sandwichedQuasi α
        (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) *
            ((V.comp ρ).comp (LinearMap.adjoint V)) *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)))
        (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) *
            ((V.comp σ).comp (LinearMap.adjoint V)) *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)))).re := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα_gt
  have hHopt_pos : Hopt.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hHopt_nn
  set W : L (𝒦 ⊗[ℂ] ℋ_env) := TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L
    ℋ_env))
    with hW_def
  have hW_unit : W ∈ unitary (L (𝒦 ⊗[ℂ] ℋ_env)) := tensorMap_right_unitary_of_unitary u
  have hadjW : LinearMap.adjoint W =
      TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) := by
    rw [hW_def, ← LinearMap.star_eq_adjoint, TensorCFC.tensorMap_right_star]
  set Vu : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env) := W.comp V with hVu_def
  have hVu_iso : (LinearMap.adjoint Vu).comp Vu = 1 := by
    have hWadjW : LinearMap.adjoint W * W = 1 := by
      have h := (Unitary.mem_iff.mp hW_unit).1
      rwa [LinearMap.star_eq_adjoint] at h
    rw [hVu_def, LinearMap.adjoint_comp]
    calc ((LinearMap.adjoint V).comp (LinearMap.adjoint W)).comp (W.comp V)
        = (LinearMap.adjoint V).comp ((LinearMap.adjoint W * W).comp V) := by
          simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      _ = (LinearMap.adjoint V).comp V := by
          rw [hWadjW, Module.End.one_eq_id, LinearMap.id_comp]
      _ = 1 := hV
  have hgρu_eq : W * ((V.comp ρ).comp (LinearMap.adjoint V)) *
      TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) =
      (Vu.comp ρ).comp (LinearMap.adjoint Vu) := by
    rw [hVu_def, LinearMap.adjoint_comp, ← hadjW]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  have hgσu_eq : W * ((V.comp σ).comp (LinearMap.adjoint V)) *
      TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) =
      (Vu.comp σ).comp (LinearMap.adjoint Vu) := by
    rw [hVu_def, LinearMap.adjoint_comp, ← hadjW]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  rw [hgρu_eq, hgσu_eq, quasiVar_isometric_conj Vu hVu_iso hα0 hα_ne1 hσ_nn hHopt_nn,
    sandwichedQuasi_isometric_conj Vu hVu_iso hα0 hα_ne1 hρ_nn hσ_nn]
  exact (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα_gt
    ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn)
    ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn)
    (hHopt_pos.adjoint_conj Vu) (isUnit_of_pdSetLM hσ_pd))).1

/-! Carrier-only wrapper for the producer-native Haar integrand.  Keeping this rewrite out
of `jensen_haar_core` prevents its two large branches from sharing the same elaboration budget. -/
private lemma quasiVar_haar_clm_integrand_le
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ_nn : (0 : L ℋ) ≤ ρ) (hσ_nn : (0 : L ℋ) ≤ σ)
    (hσ_pd : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {Hopt : L (𝒦 ⊗[ℂ] ℋ_env)} (hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt)
    (u : unitary (B ℋ_env)) :
    let Xρ := (V.comp ρ).comp (LinearMap.adjoint V)
    let Xσ := (V.comp σ).comp (LinearMap.adjoint V)
    (quasiVar α
        ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
          B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
        ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
          B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) Hopt).re ≤
      (sandwichedQuasi α
        ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
          B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
        ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
          B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re := by
  dsimp only
  rw [concavity_rightTwirlCLM_symm, concavity_rightTwirlCLM_symm]
  exact quasiVar_haar_integrand_le hα_gt hρ_nn hσ_nn hσ_pd V hV hHopt_nn
    ((concavityUnitaryEquiv (ℋ := ℋ_env)).symm u)

private lemma integral_mono_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {c : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : ∀ x, f x ≤ g x)
    (hg_eq : (∫ x, g x ∂μ) = c) : (∫ x, f x ∂μ) ≤ c :=
  (integral_mono hf hg hfg).trans_eq hg_eq

private lemma jensen_haar_concave_clm
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    (Xρ Xσ : L (𝒦 ⊗[ℂ] ℋ_env))
    (hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ)
    (hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ) :
    ((sandwichedQuasi α
        (TensorProduct.map (traceOutRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (traceOutRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α Xρ Xσ).re) * (α - 1) ≤ 0 := by
  have hα0 : (0 : ℝ) < α := by linarith
  have toCLM_nonneg (X : L (𝒦 ⊗[ℂ] ℋ_env))
      (hX : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ X) :
      (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤
        X.toContinuousLinearMap := by
    apply (ContinuousLinearMap.coe_le_coe_iff
      (0 : B (𝒦 ⊗[ℂ] ℋ_env))
      X.toContinuousLinearMap).mp
    simpa only [LinearMap.coe_toContinuousLinearMap] using hX
  let g : L (𝒦 ⊗[ℂ] ℋ_env) →
      unitary (B ℋ_env) →
        B (𝒦 ⊗[ℂ] ℋ_env) :=
    fun X => concavityRightTwirlCLM X.toContinuousLinearMap
  have h_inv : ∀ u : unitary (B ℋ_env),
      (sandwichedQuasi α
        ((g Xρ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
        ((g Xσ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re =
        (sandwichedQuasi α Xρ Xσ).re := by
    intro u
    let uLM := (concavityUnitaryEquiv (ℋ := ℋ_env)).symm u
    set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
      ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env),
        tensorMap_right_unitary_of_unitary uLM⟩ with hU_def
    have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env) :=
      rfl
    have hgρ_eq : ((g Xρ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) =
        (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
      change ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) = _
      rw [concavity_rightTwirlCLM_symm]
      simp only [uLM, hUcoe, TensorCFC.tensorMap_right_star]
    have hgσ_eq : ((g Xσ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) =
        (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
      change ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) = _
      rw [concavity_rightTwirlCLM_symm]
      simp only [uLM, hUcoe, TensorCFC.tensorMap_right_star]
    rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]
  have g_nonneg (X : L (𝒦 ⊗[ℂ] ℋ_env))
      (hX : (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤
        X.toContinuousLinearMap) :
      ∀ u, (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ g X u := by
    intro u
    change (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤
      concavityRightTwirlCLM X.toContinuousLinearMap u
    rw [concavityRightTwirlCLM]
    have h := star_left_conjugate_nonneg hX
      (star (HaarUnitaryCLM.tensorMap (1 : B 𝒦) (u : B ℋ_env)))
    have hstar := concavity_tensorMap_star_clm
      (1 : B 𝒦) (u : B ℋ_env)
    rw [star_one] at hstar
    rw [star_star] at h
    rwa [← hstar]
  have g_integrable (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
      Integrable (g X) (HaarUnitaryCLM.haarUnitary ℋ_env) := by
    simpa only [g, concavityRightTwirlCLM] using
      HaarUnitaryCLM.integrable_unitaryConj_tensor_right X.toContinuousLinearMap
  have integral_g (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
      (∫ u, g X u ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
        (TensorProduct.map (traceOutRight X)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))).toContinuousLinearMap := by
    calc
      (∫ u, g X u ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
          HaarUnitaryCLM.tensorMap
            (HaarUnitaryCLM.traceOutRight X.toContinuousLinearMap)
            ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : B ℋ_env)) := by
        simpa only [g, concavityRightTwirlCLM] using
          HaarUnitaryCLM.twirl_eq_partialTrace_right_smul_id X.toContinuousLinearMap
      _ = _ := concavity_rightTwirl_rhs_bridge X
  have hgρ_nn_all := g_nonneg Xρ (toCLM_nonneg Xρ hXρ_nn)
  have hgσ_nn_all := g_nonneg Xσ (toCLM_nonneg Xσ hXσ_nn)
  have hgρ_mem : ∀ᵐ u ∂(HaarUnitaryCLM.haarUnitary ℋ_env),
      g Xρ u ∈ {A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
    Filter.Eventually.of_forall hgρ_nn_all
  have hgσ_mem : ∀ᵐ u ∂(HaarUnitaryCLM.haarUnitary ℋ_env),
      g Xσ u ∈ {A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
    Filter.Eventually.of_forall hgσ_nn_all
  have hgρ_int := g_integrable Xρ
  have hgσ_int := g_integrable Xσ
  have hfg_int : Integrable (fun u =>
      (sandwichedQuasi α
        ((g Xρ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
        ((g Xσ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env) := by
    simp_rw [h_inv]
    exact integrable_const _
  have hint_ρ := integral_g Xρ
  have hint_σ := integral_g Xσ
  have h_lhs_int : (∫ u, (sandwichedQuasi α
      ((g Xρ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((g Xσ u : B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re
      ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
      (sandwichedQuasi α Xρ Xσ).re := by
    simp_rw [h_inv]
    simp
  have hJ := HaarUnitaryCLM.jointly_concave_le_integral
    (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    clm_convex_nonneg_cone clm_convex_nonneg_cone
    clm_isClosed_nonneg_cone clm_isClosed_nonneg_cone
    (sandwichedQuasi_re_jointlyConcave_nonneg hα_ge hα_lt)
    (sandwichedQuasi_re_continuousOn_nonneg hα0 hα_lt.le)
    hgρ_mem hgσ_mem hgρ_int hgσ_int hfg_int
  rw [h_lhs_int, hint_ρ, hint_σ] at hJ
  have hD : (0 : ℝ) ≤ (sandwichedQuasi α
      (TensorProduct.map (traceOutRight Xρ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
      (TensorProduct.map (traceOutRight Xσ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α Xρ Xσ).re := sub_nonneg.mpr hJ
  exact mul_nonpos_of_nonneg_of_nonpos hD (by linarith)

/-- Jensen's inequality for `Re quasiVar(·,·,H)` (fixed positive-definite `H`, `α > 1`) along the
right twirl of non-negative `Xρ, Xσ`, together with the integrability of the integrand. -/
private lemma quasiVar_re_le_integral_rightTwirl {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    [Qudit ℋ_env] [Nontrivial ℋ_env] [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)]
    {α : ℝ} (hα_gt : 1 < α) {Xρ Xσ H : L (𝒦 ⊗[ℂ] ℋ_env)}
    (hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ) (hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ)
    (hH : H ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env)) :
    (quasiVar α
        (TensorProduct.map (traceOutRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (traceOutRight Xσ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        H).re ≤
      ∫ u, (quasiVar α
        ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
          (concavityRightTwirlCLM
            (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Xρ) u))
        ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
          (concavityRightTwirlCLM
            (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Xσ) u)) H).re
        ∂(HaarUnitaryCLM.haarUnitary ℋ_env) ∧
    Integrable (fun u => (quasiVar α
        ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
          (concavityRightTwirlCLM
            (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Xρ) u))
        ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)).symm
          (concavityRightTwirlCLM
            (Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env) Xσ) u)) H).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env) := by
  let eT := Module.End.toContinuousLinearMap (𝕜 := ℂ) (𝒦 ⊗[ℂ] ℋ_env)
  have hXρc_nn : (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ eT Xρ :=
    (ContinuousLinearMap.coe_le_coe_iff (0 : B (𝒦 ⊗[ℂ] ℋ_env)) (eT Xρ)).mp
      (by simpa only [eT, LinearMap.coe_toContinuousLinearMap] using hXρ_nn)
  have hXσc_nn : (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ eT Xσ :=
    (ContinuousLinearMap.coe_le_coe_iff (0 : B (𝒦 ⊗[ℂ] ℋ_env)) (eT Xσ)).mp
      (by simpa only [eT, LinearMap.coe_toContinuousLinearMap] using hXσ_nn)
  have hHc_pd : eT H ∈ pdSet (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by simpa only [eT, pdSetLM] using hH
  have hHc_nn : (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ eT H :=
    ((pdSet_membership_certificate (eT H)).1 hHc_pd).nonneg
  have hcont_on : ContinuousOn (Function.uncurry
      (fun ρ σ => (quasiVar α (eT.symm ρ) (eT.symm σ) H).re))
      ({A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} ×ˢ {A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A}) := by
    simpa only [eT.symm_apply_apply] using
      (quasiVar_re_continuousOn_nonneg (H := eT H) hα_gt hHc_nn)
  have hconvex : JointlyConvexOn
      {A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} {A | (0 : B (𝒦 ⊗[ℂ] ℋ_env)) ≤ A}
      (fun ρ σ => (quasiVar α (eT.symm ρ) (eT.symm σ) H).re) := by
    simpa only [eT.symm_apply_apply] using
      (quasiVar_re_jointlyConvex_nonneg (H := eT H) hα_gt hHc_pd)
  have hcont : Continuous (fun u => (quasiVar α
      (eT.symm (concavityRightTwirlCLM (eT Xρ) u))
      (eT.symm (concavityRightTwirlCLM (eT Xσ) u)) H).re) := by
    have h : Continuous (fun u => Function.uncurry
        (fun ρ σ => (quasiVar α (eT.symm ρ) (eT.symm σ) H).re)
        (concavityRightTwirlCLM (eT Xρ) u, concavityRightTwirlCLM (eT Xσ) u)) :=
      hcont_on.comp_continuous ((continuous_concavityRightTwirlCLM (eT Xρ)).prodMk
        (continuous_concavityRightTwirlCLM (eT Xσ)))
        (fun u => Set.mk_mem_prod (concavityRightTwirlCLM_nonneg hXρc_nn u)
          (concavityRightTwirlCLM_nonneg hXσc_nn u))
    simpa only [Function.uncurry_apply_pair] using h
  have hint : Integrable (fun u => (quasiVar α
      (eT.symm (concavityRightTwirlCLM (eT Xρ) u))
      (eT.symm (concavityRightTwirlCLM (eT Xσ) u)) H).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env) :=
    hcont.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hJ := HaarUnitaryCLM.jointly_convex_integral_le
    (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    clm_convex_nonneg_cone clm_convex_nonneg_cone
    clm_isClosed_nonneg_cone clm_isClosed_nonneg_cone
    hconvex hcont_on
    (Filter.Eventually.of_forall (concavityRightTwirlCLM_nonneg hXρc_nn))
    (Filter.Eventually.of_forall (concavityRightTwirlCLM_nonneg hXσc_nn))
    (integrable_concavityRightTwirlCLM (eT Xρ)) (integrable_concavityRightTwirlCLM (eT Xσ)) hint
  rw [integral_concavityRightTwirlCLM Xρ, integral_concavityRightTwirlCLM Xσ] at hJ
  exact ⟨hJ, hint⟩

/-- The convex branch (`α > 1`) of `jensen_haar_core`, via the Frank–Lieb variational
functional at the optimizer of the positive-definite average pair. -/
private lemma jensen_haar_core_gt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env] [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ} (hρ_nn : (0 : L ℋ) ≤ ρ) (hσ_nn : (0 : L ℋ) ≤ σ)
    (hσ_pd : σ ∈ pdSetLM (ℋ := ℋ)) (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {Xρ Xσ : L (𝒦 ⊗[ℂ] ℋ_env)}
    (hXρ : (V.comp ρ).comp (LinearMap.adjoint V) = Xρ)
    (hXσ : (V.comp σ).comp (LinearMap.adjoint V) = Xσ)
    (hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ) (hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ)
    (hEρ : traceOutRight Xρ ∈ pdSetLM (ℋ := 𝒦)) (hEσ : traceOutRight Xσ ∈ pdSetLM (ℋ := 𝒦)) :
    (sandwichedQuasi α
        (TensorProduct.map (traceOutRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (traceOutRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re ≤
      (sandwichedQuasi α Xρ Xσ).re := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα_gt
  have hτmax_pd := maxmixed_pdSetLM ℋ_env
  have hPρ_pd := tensorMap_pdSetLM hEρ hτmax_pd
  have hPσ_pd := tensorMap_pdSetLM hEσ hτmax_pd
  have hHopt_pd := quasiVarOpt_pdSetLM hα0 hα_ne1 hPρ_pd hPσ_pd
  obtain ⟨hJ, hquasi_int⟩ := quasiVar_re_le_integral_rightTwirl hα_gt hXρ_nn hXσ_nn hHopt_pd
  have hpoint := fun u => by
    have h := quasiVar_haar_clm_integrand_le hα_gt hρ_nn hσ_nn hσ_pd V hV
      (nonneg_of_pdSetLM hHopt_pd) u
    dsimp only at h
    rw [hXρ, hXσ] at h
    exact h
  have hfg_int := (integrable_const (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    (sandwichedQuasi α Xρ Xσ).re).congr
      (Filter.Eventually.of_forall fun u =>
        (sandwichedQuasi_re_concavityRightTwirlCLM α Xρ Xσ u).symm)
  rw [quasiVarOpt_eq_quasi_gt hα_gt
    ((LinearMap.nonneg_iff_isPositive _).1 (nonneg_of_pdSetLM hPρ_pd))
    ((LinearMap.nonneg_iff_isPositive _).1 (nonneg_of_pdSetLM hPσ_pd))
    (isUnit_of_pdSetLM hPσ_pd)] at hJ
  exact le_trans hJ (integral_mono_eq hquasi_int hfg_int hpoint
    (by simp_rw [sandwichedQuasi_re_concavityRightTwirlCLM]; simp))

/-- **Inner Jensen–Haar inequality (Form A, isometric Stinespring).**

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
    for this fixed optimizer, then apply `HaarUnitaryCLM.jointly_convex_integral_le`.
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
    -- At the pd average pair `Pρ, Pσ`, `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)` for the
    -- optimizer `H*`; Jensen for the jointly convex `quasiVar(·,·,H*)` and the pointwise bound
    -- `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` finish (see `jensen_haar_core_gt`).
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (jensen_haar_core_gt hα_gt hρ_nn hσ_nn _hσ V _hV hXρ_def.symm
        hXσ_def.symm hXρ_nn hXσ_nn _hEρ _hEσ)) (by linarith)

end JensenHaarCore

end SandwichedRenyiRelativeEntropy
