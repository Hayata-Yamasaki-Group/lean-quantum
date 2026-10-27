/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.HaarTwirl
import Quantum.QuantumEntropy.Common.RpowContinuity
import Quantum.QuantumEntropy.SandwichedRenyi.QuasiJensen.Cone

/-!
# Shared support for Quasi-Jensen concavity

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

section RepresentationSupport
variable {ℋ : Type u} [Qudit ℋ]

private lemma rpow_toContinuousLinearMap (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  let e := QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ
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

private lemma rpow_toLinearMap (A : L ℋ) (p : ℝ) :
    ((CFC.rpow A.toContinuousLinearMap p : B ℋ) : L ℋ) =
      CFC.rpow A p := by
  simpa using (congrArg ContinuousLinearMap.toLinearMap
    (rpow_toContinuousLinearMap A p)).symm

private lemma rpow_clm_toLinearMap
    (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have hA : (A : L ℋ).toContinuousLinearMap = A := by
    ext x
    rfl
  simpa only [hA] using rpow_toLinearMap (A : L ℋ) p

/-- Proof-support equation for evaluating `sandwichedQuasi`
at CLM arguments through the canonical coercion. -/
private lemma sandwichedQuasi_eq_clm_direct
    (a : ℝ) (rho sigma : B ℋ) :
    sandwichedQuasi a (rho : L ℋ) (sigma : L ℋ) =
      Tr ((CFC.rpow
        (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
          CFC.rpow sigma ((1 - a) / (2 * a))) a :
            B ℋ) : L ℋ) := by
  rw [sandwichedQuasi_eq_direct]
  change Tr (CFC.rpow
      (CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a)) * (rho : L ℋ) *
        CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a))) a) =
    Tr ((CFC.rpow
      (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
        CFC.rpow sigma ((1 - a) / (2 * a))) a : B ℋ) : L ℋ)
  rw [rpow_clm_toLinearMap]
  change _ = Tr (CFC.rpow
    (((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ) *
      (rho : L ℋ) *
      ((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ)) a)
  rw [rpow_clm_toLinearMap]

/-- Proof-support equation for evaluating `quasiVar`
at CLM arguments through the canonical coercion. -/
private lemma quasiVar_eq_clm_direct
    (a : ℝ) (rho sigma H : B ℋ) :
    quasiVar a (rho : L ℋ) (sigma : L ℋ) (H : L ℋ) =
      (a : ℂ) * Tr ((H * rho : B ℋ) : L ℋ) -
        ((a - 1 : ℝ) : ℂ) *
          Tr ((CFC.rpow
            (CFC.rpow sigma ((a - 1) / (2 * a)) * H *
              CFC.rpow sigma ((a - 1) / (2 * a)))
            (a / (a - 1)) : B ℋ) : L ℋ) := by
  rw [quasiVar_eq_direct]
  change
    (a : ℂ) * Tr ((H : L ℋ) * (rho : L ℋ)) -
        ((a - 1 : ℝ) : ℂ) * Tr (CFC.rpow
          (CFC.rpow (sigma : L ℋ) ((a - 1) / (2 * a)) * (H : L ℋ) *
            CFC.rpow (sigma : L ℋ) ((a - 1) / (2 * a)))
          (a / (a - 1))) =
      (a : ℂ) * Tr (((H * rho : B ℋ) : L ℋ)) -
        ((a - 1 : ℝ) : ℂ) * Tr (((CFC.rpow
          (CFC.rpow sigma ((a - 1) / (2 * a)) * H *
            CFC.rpow sigma ((a - 1) / (2 * a)))
          (a / (a - 1)) : B ℋ) : L ℋ))
  rw [rpow_clm_toLinearMap]
  change _ =
    (a : ℂ) * Tr ((H : L ℋ) * (rho : L ℋ)) -
      ((a - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (((CFC.rpow sigma ((a - 1) / (2 * a)) : B ℋ) : L ℋ) *
          (H : L ℋ) *
          ((CFC.rpow sigma ((a - 1) / (2 * a)) : B ℋ) : L ℋ))
        (a / (a - 1)))
  rw [rpow_clm_toLinearMap]

end RepresentationSupport

/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/

/-- For `0 < α ≤ 1`, the real part of `sandwichedQuasi` is jointly continuous on the
    non-negative cone. Both exponents `β = (1-α)/(2α)` and `α` are non-negative, so every
    `CFC.rpow` in the definition is continuous up to the boundary of the cone.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
private lemma sandwichedQuasi_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : B 𝒦) =>
      (sandwichedQuasi α (ρ : L 𝒦) (σ : L 𝒦)).re))
      ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
        {A : B 𝒦 | (0 : B 𝒦) ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  have hβ_nn : 0 ≤ β := div_nonneg (by linarith) (by positivity)
  set S : Set (B 𝒦) :=
    {A : B 𝒦 | (0 : B 𝒦) ≤ A} with hS
  have h_rpow_snd : ContinuousOn
      (fun p : B 𝒦 × B 𝒦 => CFC.rpow p.2 β)
      (S ×ˢ S) :=
    (continuousOn_rpow_nonneg hβ_nn).comp continuous_snd.continuousOn
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn
      (fun p : B 𝒦 × B 𝒦 => p.1) (S ×ˢ S) :=
    continuous_fst.continuousOn
  have h_inner_cont :
      ContinuousOn (fun p : B 𝒦 × B 𝒦 =>
        CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) (S ×ˢ S) :=
    (h_rpow_snd.mul h_fst).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S,
      (0 : B 𝒦) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β := by
    rintro ⟨ρ, σ⟩ ⟨hρ, _hσ⟩
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hρ (CFC.rpow σ β)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : B 𝒦 × B 𝒦 =>
        CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α) (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ α))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hα0.le).continuousOn)
  have h_trace_cont : Continuous
      (fun A : B 𝒦 => (traceCLM A).re) :=
    Complex.continuous_re.comp traceCLM.continuous
  have hfinal :=
    h_trace_cont.comp_continuousOn h_pow_cont
  refine hfinal.congr ?_
  rintro ⟨ρ, σ⟩ ⟨_hρ, _hσ⟩
  simpa [hβ, traceCLM] using
    congrArg Complex.re (sandwichedQuasi_eq_clm_direct α ρ σ)

/-- Linear-map endpoint form of continuity on the non-negative cone. -/
lemma continuousOn_sandwichedQuasi_re_nonneg_lm
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

namespace QuasiJensenSupport

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
    (continuousOn_rpow_nonneg hc_nn).comp continuous_snd.continuousOn
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

section JointlyConvexNonneg
attribute [local irreducible] quasiVar

-- The native CLM perturbation proof terminates but its four simultaneous limit transports
-- exceed the default declaration budget during `whnf`.
/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` extends from `pdSet` to the whole
    non-negative cone (fixed pd `H`, `α > 1`), by the same `ε → 0⁺` perturbation + joint
    continuity (`quasiVar_re_continuousOn_nonneg`) argument as the concave case. -/
private lemma quasiVar_re_jointlyConvex_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : B 𝒦} (hH : H ∈ pdSet (ℋ := 𝒦)) :
    JointlyConvexOn
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      {A : B 𝒦 | (0 : B 𝒦) ≤ A}
      (fun ρ σ => (quasiVar (ℋ := 𝒦) α
        (ρ : L 𝒦) (σ : L 𝒦) (H : L 𝒦)).re) := by
  have hcont := quasiVar_re_continuousOn_nonneg (𝒦 := 𝒦) hα
    ((pdSet_membership_certificate H).1 hH).nonneg
  have hpd : JointlyConvexOn (pdSet (ℋ := 𝒦)) (pdSet (ℋ := 𝒦))
      (fun ρ σ => (quasiVar α (ρ : L 𝒦) (σ : L 𝒦) (H : L 𝒦)).re) := by
    intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
    exact jointlyConvexOn_quasiVar_re_pdSetLM hα hH
      hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  have key : ∀ a b : B 𝒦, (0 : B 𝒦) ≤ a →
      (0 : B 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (quasiVar α
          ((a + (ε : ℂ) • 1 : B 𝒦) : L 𝒦)
          ((b + (ε : ℂ) • 1 : B 𝒦) : L 𝒦) (H : L 𝒦)).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (quasiVar α (a : L 𝒦) (b : L 𝒦) (H : L 𝒦)).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) :=
      by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
            {A : B 𝒦 | (0 : B 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : B 𝒦) ≤ (ε : ℂ) • (1 : B 𝒦) :=
        (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε') isStrictlyPositive_one).nonneg
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b)
            ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
              {A : B 𝒦 | (0 : B 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : B 𝒦 =>
          (quasiVar α (ρ : L 𝒦) (σ : L 𝒦) (H : L 𝒦)).re))
        (nhdsWithin (a, b)
          ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
            {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
        (nhds (quasiVar α (a : L 𝒦) (b : L 𝒦) (H : L 𝒦)).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  have hρc : (0 : B 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : B 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  have hcombo : ∀ a₁ a₂ : B 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : B 𝒦)) +
        (θ : ℝ) • ((ε : ℂ) • (1 : B 𝒦)) =
        (ε : ℂ) • (1 : B 𝒦) := by
      rw [← add_smul]; norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε :
      ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ)
          • 1) from by abel,
        h1]
  refine le_of_tendsto_of_tendsto (key _ _ hρc hσc)
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂
      hσ₂).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have perturbed_pd {A : B 𝒦} (hA : (0 : B 𝒦) ≤ A) :
      A + (ε : ℂ) • 1 ∈ pdSet (ℋ := 𝒦) := by
    apply (pdSet_membership_certificate _).2
    exact IsStrictlyPositive.nonneg_add hA
      (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε') isStrictlyPositive_one)
  have hj := hpd (perturbed_pd hρ₁) (perturbed_pd hρ₂)
    (perturbed_pd hσ₁) (perturbed_pd hσ₂) hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConvexNonneg

section JointlyConcaveNonneg
-- `sandwichedQuasi` is treated as a black box here (only continuity, the pd Jensen
-- inequality, and limits are used), so making it irreducible avoids the unifier
-- unfolding the large CFC expression during def-eq checks.
attribute [local irreducible] sandwichedQuasi

-- The native CLM perturbation proof terminates but its four simultaneous limit transports
-- exceed the default declaration budget during `whnf`.
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
        (ρ : L 𝒦) (σ : L 𝒦)).re) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα_lt.le
  have hpd : JointlyConcaveOn (pdSet (ℋ := 𝒦)) (pdSet (ℋ := 𝒦))
      (fun ρ σ => (sandwichedQuasi α (ρ : L 𝒦) (σ : L 𝒦)).re) := by
    intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
    exact jointlyConcaveOn_sandwichedQuasi_re_pdSetLM hα_ge hα_lt
      hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  -- Limit of `Re Q_α` at a non-negative pair, approached through pd perturbations `+ ε•1`.
  have key : ∀ a b : B 𝒦, (0 : B 𝒦) ≤ a →
      (0 : B 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (sandwichedQuasi α
          ((a + (ε : ℂ) • 1 : B 𝒦) : L 𝒦)
          ((b + (ε : ℂ) • 1 : B 𝒦) : L 𝒦)).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (sandwichedQuasi α (a : L 𝒦) (b : L 𝒦)).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) :=
      by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
            {A : B 𝒦 | (0 : B 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : B 𝒦) ≤ (ε : ℂ) • (1 : B 𝒦) :=
        (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε') isStrictlyPositive_one).nonneg
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b)
            ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
              {A : B 𝒦 | (0 : B 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : B 𝒦 =>
          (sandwichedQuasi α (ρ : L 𝒦) (σ : L 𝒦)).re))
        (nhdsWithin (a, b)
          ({A : B 𝒦 | (0 : B 𝒦) ≤ A} ×ˢ
            {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
        (nhds (sandwichedQuasi α (a : L 𝒦) (b : L 𝒦)).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  -- Non-negativity of the convex combinations.
  have hρc : (0 : B 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : B 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  -- The perturbed convex combination equals the convex combination of perturbations.
  have hcombo : ∀ a₁ a₂ : B 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : B 𝒦)) +
        (θ : ℝ) • ((ε : ℂ) • (1 : B 𝒦)) =
        (ε : ℂ) • (1 : B 𝒦) := by
      rw [← add_smul]; norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε :
      ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ)
          • 1) from by abel,
        h1]
  -- Pass the pd Jensen inequality to the limit `ε → 0⁺`.
  refine le_of_tendsto_of_tendsto
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂
      hσ₂).const_smul θ))
    (key _ _ hρc hσc) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have perturbed_pd {A : B 𝒦} (hA : (0 : B 𝒦) ≤ A) :
      A + (ε : ℂ) • 1 ∈ pdSet (ℋ := 𝒦) := by
    apply (pdSet_membership_certificate _).2
    exact IsStrictlyPositive.nonneg_add hA
      (IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε') isStrictlyPositive_one)
  have hj := hpd (perturbed_pd hρ₁) (perturbed_pd hρ₂)
    (perturbed_pd hσ₁) (perturbed_pd hσ₂) hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConcaveNonneg

/-! ### Bounded-operator transport for the Jensen--Haar theorem -/

-- These definitions are used only through their continuity/convexity interfaces below.
-- Keeping them opaque prevents bridge composition from unfolding their large CFC bodies.
attribute [local irreducible] sandwichedQuasi quasiVar

noncomputable def concavityUnitaryEquiv {ℋ : Type u} [Qudit ℋ] :
    unitary (L ℋ) ≃⋆* unitary (B ℋ) := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  let es : L ℋ ≃⋆* B ℋ := { e.toStarRingEquiv with }
  exact Unitary.mapEquiv es

noncomputable def concavityRightTwirlCLM
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    (X : B (𝒦 ⊗[ℂ] ℋ_env))
    (u : unitary (B ℋ_env)) :
    B (𝒦 ⊗[ℂ] ℋ_env) :=
  HaarUnitaryCLM.tensorMap (1 : B 𝒦) (u : B ℋ_env) * X *
    HaarUnitaryCLM.tensorMap (1 : B 𝒦) (star (u : B ℋ_env))

private theorem concavity_integral_rightTwirl
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env] [Nontrivial ℋ_env]
    (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
    (∫ u, concavityRightTwirlCLM X.toContinuousLinearMap u
      ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) =
      (TensorProduct.map (traceOutRight X)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))).toContinuousLinearMap := by
  exact congrArg (fun A : L (𝒦 ⊗[ℂ] ℋ_env) => A.toContinuousLinearMap)
    (HaarUnitaryL.twirlRight_eq X)

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
  rfl

private lemma concavity_traceOutRight_bridge
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    (QuantumChannel.traceOutRight X).toContinuousLinearMap =
      HaarUnitaryCLM.traceOutRight
        X.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  simp only [HaarUnitaryCLM.traceOutRight_toLinearMap, LinearMap.coe_toContinuousLinearMap]

lemma concavity_rightTwirlCLM_symm
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
lemma quasiVar_haar_integrand_le
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

lemma integral_mono_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {c : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : ∀ x, f x ≤ g x)
    (hg_eq : (∫ x, g x ∂μ) = c) : (∫ x, f x ∂μ) ≤ c :=
  (integral_mono hf hg hfg).trans_eq hg_eq

lemma concavity_rightTwirl_quasi_invariant
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env] [Nontrivial 𝒦] [Nontrivial ℋ_env]
    [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)] (α : ℝ)
    (Xρ Xσ : L (𝒦 ⊗[ℂ] ℋ_env)) (u : unitary (B ℋ_env)) :
    (sandwichedQuasi α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re =
      (sandwichedQuasi α Xρ Xσ).re := by
  let uLM := (concavityUnitaryEquiv (ℋ := ℋ_env)).symm u
  set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
    ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env),
      tensorMap_right_unitary_of_unitary uLM⟩ with hU_def
  have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
      TensorProduct.map (LinearMap.id (M := 𝒦)) ((uLM : unitary (L ℋ_env)) : L ℋ_env) :=
    rfl
  have hgρ_eq : ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) =
      (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
    change ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
      B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) = _
    rw [concavity_rightTwirlCLM_symm]
    simp only [uLM, hUcoe, TensorCFC.tensorMap_right_star]
  have hgσ_eq : ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) =
      (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
    change ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
      B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) = _
    rw [concavity_rightTwirlCLM_symm]
    simp only [uLM, hUcoe, TensorCFC.tensorMap_right_star]
  rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]

private lemma concavity_rightTwirl_nonneg
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    {X : B (𝒦 ⊗[ℂ] ℋ_env)} (hX : 0 ≤ X) (u : unitary (B ℋ_env)) :
    0 ≤ concavityRightTwirlCLM X u := by
  rw [concavityRightTwirlCLM]
  have h := star_left_conjugate_nonneg hX
    (star (HaarUnitaryCLM.tensorMap (1 : B 𝒦) (u : B ℋ_env)))
  have hstar := concavity_tensorMap_star_clm (1 : B 𝒦) (u : B ℋ_env)
  rw [star_one] at hstar
  rw [star_star] at h
  rwa [← hstar]

private lemma concavity_rightTwirl_jensen
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    [Nontrivial 𝒦] [Nontrivial ℋ_env] [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    (Xρ Xσ : L (𝒦 ⊗[ℂ] ℋ_env)) (hXρ : 0 ≤ Xρ) (hXσ : 0 ≤ Xσ)
    (hf : Integrable (fun u => (sandwichedQuasi α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env)) :
    (∫ u, (sandwichedQuasi α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re
      ∂(HaarUnitaryCLM.haarUnitary ℋ_env)) ≤
      (sandwichedQuasi α
        (TensorProduct.map (traceOutRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (traceOutRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re := by
  have hρc : 0 ≤ Xρ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff 0 Xρ.toContinuousLinearMap).mp hXρ
  have hσc : 0 ≤ Xσ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff 0 Xσ.toContinuousLinearMap).mp hXσ
  have hJ := GeneralizedPerspectiveFunction.JointlyConcaveOn.le_map_integral
    (E := B (𝒦 ⊗[ℂ] ℋ_env))
    (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    (g₁ := concavityRightTwirlCLM Xρ.toContinuousLinearMap)
    (g₂ := concavityRightTwirlCLM Xσ.toContinuousLinearMap)
    (convex_Ici (0 : B (𝒦 ⊗[ℂ] ℋ_env))) (convex_Ici (0 : B (𝒦 ⊗[ℂ] ℋ_env)))
    isClosed_Ici isClosed_Ici
    (sandwichedQuasi_re_jointlyConcave_nonneg hα_ge hα_lt)
    (sandwichedQuasi_re_continuousOn_nonneg (by linarith) hα_lt.le)
    (Filter.Eventually.of_forall (concavity_rightTwirl_nonneg hρc))
    (Filter.Eventually.of_forall (concavity_rightTwirl_nonneg hσc))
    (HaarUnitaryCLM.integrable_unitaryConj_tensor_right Xρ.toContinuousLinearMap)
    (HaarUnitaryCLM.integrable_unitaryConj_tensor_right Xσ.toContinuousLinearMap) hf
  rw [concavity_integral_rightTwirl Xρ, concavity_integral_rightTwirl Xσ] at hJ
  exact hJ

lemma concavity_rightTwirl_variational_jensen
    {𝒦 ℋ_env : Type u} [Qudit 𝒦] [Qudit ℋ_env]
    [Nontrivial 𝒦] [Nontrivial ℋ_env] [Nontrivial (𝒦 ⊗[ℂ] ℋ_env)]
    {α : ℝ} (hα : 1 < α) (Xρ Xσ H : L (𝒦 ⊗[ℂ] ℋ_env))
    (hXρ : 0 ≤ Xρ) (hXσ : 0 ≤ Xσ) (hH : H ∈ pdSetLM) :
    Integrable (fun u => (quasiVar α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) H).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env) ∧
    (quasiVar α
      (TensorProduct.map (traceOutRight Xρ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
      (TensorProduct.map (traceOutRight Xσ)
        ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))) H).re ≤
    ∫ u, (quasiVar α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env)) H).re
      ∂(HaarUnitaryCLM.haarUnitary ℋ_env) := by
  have hρc : 0 ≤ Xρ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff 0 Xρ.toContinuousLinearMap).mp hXρ
  have hσc : 0 ≤ Xσ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff 0 Xσ.toContinuousLinearMap).mp hXσ
  have hHc : H.toContinuousLinearMap ∈ pdSet := hH
  have hHn := ((pdSet_membership_certificate H.toContinuousLinearMap).1 hHc).nonneg
  have hcont := quasiVar_re_continuousOn_nonneg hα hHn
  have hconv := quasiVar_re_jointlyConvex_nonneg hα hHc
  have hρn := concavity_rightTwirl_nonneg hρc
  have hσn := concavity_rightTwirl_nonneg hσc
  have hcontinuous := hcont.comp_continuous
    ((HaarUnitaryCLM.continuous_unitaryConj_tensor_right Xρ.toContinuousLinearMap).prodMk
      (HaarUnitaryCLM.continuous_unitaryConj_tensor_right Xσ.toContinuousLinearMap))
    (fun u => Set.mk_mem_prod (hρn u) (hσn u))
  have hint := hcontinuous.integrable_of_hasCompactSupport
    (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hJ := GeneralizedPerspectiveFunction.JointlyConvexOn.map_integral_le
    (E := B (𝒦 ⊗[ℂ] ℋ_env))
    (μ := HaarUnitaryCLM.haarUnitary ℋ_env)
    (g₁ := concavityRightTwirlCLM Xρ.toContinuousLinearMap)
    (g₂ := concavityRightTwirlCLM Xσ.toContinuousLinearMap)
    (convex_Ici (0 : B (𝒦 ⊗[ℂ] ℋ_env))) (convex_Ici (0 : B (𝒦 ⊗[ℂ] ℋ_env)))
    isClosed_Ici isClosed_Ici hconv hcont
    (Filter.Eventually.of_forall hρn) (Filter.Eventually.of_forall hσn)
    (HaarUnitaryCLM.integrable_unitaryConj_tensor_right Xρ.toContinuousLinearMap)
    (HaarUnitaryCLM.integrable_unitaryConj_tensor_right Xσ.toContinuousLinearMap) hint
  rw [concavity_integral_rightTwirl Xρ, concavity_integral_rightTwirl Xσ] at hJ
  exact ⟨hint, hJ⟩

lemma jensen_haar_concave_clm
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
  have hinv := concavity_rightTwirl_quasi_invariant α Xρ Xσ
  have hf : Integrable (fun u => (sandwichedQuasi α
      ((concavityRightTwirlCLM Xρ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))
      ((concavityRightTwirlCLM Xσ.toContinuousLinearMap u :
        B (𝒦 ⊗[ℂ] ℋ_env)) : L (𝒦 ⊗[ℂ] ℋ_env))).re)
      (HaarUnitaryCLM.haarUnitary ℋ_env) := by
    simp_rw [hinv]
    exact integrable_const _
  have hJ := concavity_rightTwirl_jensen hα_ge hα_lt Xρ Xσ hXρ_nn hXσ_nn hf
  simp_rw [hinv] at hJ
  rw [integral_const, probReal_univ, one_smul] at hJ
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hJ) (by linarith)

end JensenHaarCore

end QuasiJensenSupport

end SandwichedRenyiRelativeEntropy
