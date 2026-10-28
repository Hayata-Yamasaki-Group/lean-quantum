import Quantum.QuantumEntropy.Common.PositiveDefiniteTensor
/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.TracePositiveDefinite
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.JointConvexity

/-!
# Sandwiched Rényi relative entropy: positive-definite normalization and continuity
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy


section Monotonicity

open MeasureTheory QuantumChannel TensorProduct GeneralizedPerspectiveFunction

universe u₅

variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

/-! ### Positive-definite normalization and tensor/trace closure lemmas -/
omit [Nontrivial ℋ] in
/-- For any positive-definite operator `τ` and any nonzero exponent `α`,
    `sandwichedQuasi α τ τ = Tr τ`. In particular, for a density operator
    (`Tr τ = 1`) this gives `Q_α(τ‖τ) = 1`. -/
lemma sandwichedQuasi_self_pdSetLM
    {α : ℝ} (hα_ne : α ≠ 0) {τ : L ℋ} (hτ : τ ∈ pdSetLM (ℋ := ℋ)) :
    sandwichedQuasi α τ τ = Tr τ := by
  have hτ_strict := (pdSetLM_strictPositivity_certificate τ).1 hτ
  have hτ_nn : (0 : L ℋ) ≤ τ := hτ_strict.nonneg
  have hτ_unit : IsUnit τ := hτ_strict.isUnit
  set β : ℝ := (1 - α) / (2 * α) with hβ_def
  have hexp1 : β + 1 + β = 1 / α := by rw [hβ_def]; field_simp; ring
  -- τ^β · τ · τ^β = τ^(1/α)
  have h_middle : CFC.rpow τ β * τ * CFC.rpow τ β = CFC.rpow τ (1 / α) := by
    have h_τ1 : τ = CFC.rpow τ 1 := (CFC.rpow_one τ hτ_nn).symm
    calc CFC.rpow τ β * τ * CFC.rpow τ β
        = CFC.rpow τ β * CFC.rpow τ 1 * CFC.rpow τ β := by rw [← h_τ1]
      _ = CFC.rpow τ (β + 1) * CFC.rpow τ β := by
          exact congrArg (fun P : L ℋ => P * CFC.rpow τ β)
            (CFC.rpow_add hτ_unit).symm
      _ = CFC.rpow τ (β + 1 + β) := by
          exact (CFC.rpow_add hτ_unit).symm
      _ = CFC.rpow τ (1 / α) := by rw [hexp1]
  -- (τ^(1/α))^α = τ
  have h_outer : CFC.rpow (CFC.rpow τ (1 / α)) α = τ := by
    have h1α_ne : (1 / α : ℝ) ≠ 0 := one_div_ne_zero hα_ne
    calc CFC.rpow (CFC.rpow τ (1 / α)) α
        = CFC.rpow τ ((1 / α) * α) :=
          CFC.rpow_rpow τ (1 / α) α hτ_unit h1α_ne hτ_nn
      _ = CFC.rpow τ 1 := by rw [show (1 / α) * α = 1 from by field_simp]
      _ = τ := CFC.rpow_one τ hτ_nn
  rw [sandwichedQuasi_eq_direct, h_middle, h_outer]

omit [Nontrivial ℋ] in
/-- Unitary conjugation preserves `pdSetLM`. -/
lemma pdSetLM_unitary_conj {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ))
    (V : unitary (L ℋ)) :
    (V : L ℋ) * A * star (V : L ℋ) ∈ pdSetLM (ℋ := ℋ) := by
  -- `pdSetLM_conj` gives `star B * A * B ∈ pdSetLM` when `B` is a unit. Apply with `B = star V`.
  have hV_unit : IsUnit (star (V : L ℋ)) := by
    refine ⟨⟨star (V : L ℋ), (V : L ℋ), ?_, ?_⟩, rfl⟩
    · exact (Unitary.mem_iff.mp V.property).1
    · exact (Unitary.mem_iff.mp V.property).2
  have h := pdSetLM_conj hA hV_unit
  rwa [star_star] at h

/-! ### Continuity of rpow and sandwiched quasi-entropy on the CLM pd cone -/
/-- The `ℝ≥0`-spectrum of any operator in `pdSet` lies in `Set.Ioi 0`. -/
private lemma pdSetLM_spectrum_nnreal_subset_Ioi
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux]
    {A : B ℋ_aux} (hA : A ∈ pdSet (ℋ := ℋ_aux)) :
    spectrum ℝ≥0 A ⊆ Set.Ioi 0 := by
  intro r hr
  have hA_unit : IsUnit A := ((pdSet_membership_certificate A).1 hA).isUnit
  have h0_notMem : (0 : ℝ≥0) ∉ spectrum ℝ≥0 A :=
    (spectrum.zero_notMem_iff (R := ℝ≥0)).mpr hA_unit
  rcases lt_or_eq_of_le (zero_le r) with hr_pos | hr_zero
  · exact hr_pos
  · exact absurd (hr_zero ▸ hr) h0_notMem

/-- For each fixed real exponent `p`, the map `A ↦ CFC.rpow A p` is continuous on `pdSet`. -/
private lemma rpow_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (p : ℝ) :
    ContinuousOn (fun A : B ℋ_aux => CFC.rpow A p)
      (pdSet (ℋ := ℋ_aux)) := by
  -- Strict positivity excludes zero from every spectrum, including for negative exponents.
  have h_subset :
      (⋃ A ∈ pdSet (ℋ := ℋ_aux), spectrum ℝ≥0 A) ⊆ Set.Ioi 0 := by
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨A, hA, hrA⟩ := hr
    exact pdSetLM_spectrum_nnreal_subset_Ioi hA hrA
  have h_nhds :
      (Set.Ioi 0 : Set ℝ≥0) ∈
        𝓝ˢ (⋃ A ∈ pdSet (ℋ := ℋ_aux), spectrum ℝ≥0 A) :=
    isOpen_Ioi.mem_nhdsSet.mpr h_subset
  have h_nn : ∀ A ∈ pdSet (ℋ := ℋ_aux), (0 : B ℋ_aux) ≤ A :=
    fun A hA => ((pdSet_membership_certificate A).1 hA).nonneg
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.Ioi 0) :=
    NNReal.continuousOn_rpow_const (.inl (by simp : (0 : ℝ≥0) ∉ Set.Ioi 0))
  exact (continuousOn_id (s := pdSet (ℋ := ℋ_aux))).cfc_nnreal_of_mem_nhdsSet
    (s := Set.Ioi 0) (f := (· ^ p)) h_nhds (ha' := h_nn) (hf := h_f_cont)

/-- Continuity of `(ρ, σ) ↦ σ^β * ρ * σ^β` on `pdSet × pdSet`. -/
private lemma rpow_conj_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ) :
    ContinuousOn
      (fun p : B ℋ_aux × B ℋ_aux =>
        CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) := by
  have h_rpow_snd : ContinuousOn
      (fun p : B ℋ_aux × B ℋ_aux => CFC.rpow p.2 β)
      (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) :=
    (rpow_continuousOn_pdSetLM (ℋ_aux := ℋ_aux) β).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn
      (fun p : B ℋ_aux × B ℋ_aux => p.1)
      (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- The conjugated operator `σ^β * ρ * σ^β` belongs to `pdSet` for `ρ, σ ∈ pdSet`. -/
private lemma rpow_conj_mem_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ)
    {ρ σ : B ℋ_aux}
    (hρ : ρ ∈ pdSet (ℋ := ℋ_aux)) (hσ : σ ∈ pdSet (ℋ := ℋ_aux)) :
    (CFC.rpow σ β * ρ * CFC.rpow σ β) ∈ pdSet (ℋ := ℋ_aux) := by
  have hP_pd : CFC.rpow σ β ∈ pdSet (ℋ := ℋ_aux) :=
    (pdSet_membership_certificate _).2
      (((pdSet_membership_certificate σ).1 hσ).rpow)
  have hP_sa : IsSelfAdjoint (CFC.rpow σ β) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hP_unit : IsUnit (CFC.rpow σ β) :=
    ((pdSet_membership_certificate _).1 hP_pd).isUnit
  have h_eq : CFC.rpow σ β * ρ * CFC.rpow σ β =
      star (CFC.rpow σ β) * ρ * CFC.rpow σ β := by rw [hP_sa.star_eq]
  rw [h_eq]
  apply (pdSet_membership_certificate _).2
  exact hP_unit.isStrictlyPositive_star_left_conjugate_iff.mpr
    ((pdSet_membership_certificate ρ).1 hρ)

/-- The real part of `sandwichedQuasi` is jointly continuous on `pdSet × pdSet`.
    Built from continuity of `CFC.rpow` (via `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`),
    continuity of multiplication, and continuity of `Tr`. -/
lemma sandwichedQuasi_re_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (α : ℝ) :
    ContinuousOn (Function.uncurry (fun (ρ σ : B ℋ_aux) =>
      (sandwichedQuasi α
        (ρ : L ℋ_aux)
        (σ : L ℋ_aux)).re))
      (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) := by
  set β : ℝ := (1 - α) / (2 * α)
  -- Step 1: `(ρ, σ) ↦ σ^β * ρ * σ^β` is continuous, and its image lies in `pdSet`.
  have h_inner_cont :
      ContinuousOn (fun p : B ℋ_aux × B ℋ_aux =>
        CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
        (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) :=
    rpow_conj_continuousOn_pdSetLM β
  have h_inner_mem : ∀ p ∈ pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux),
      CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β ∈ pdSet (ℋ := ℋ_aux) := by
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact rpow_conj_mem_pdSetLM β hρ hσ
  -- Step 2: compose the one-variable result with the inner map.
  have h_pow_cont :
      ContinuousOn
        (fun p : B ℋ_aux × B ℋ_aux =>
          CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) :=
    (rpow_continuousOn_pdSetLM (ℋ_aux := ℋ_aux) α).comp h_inner_cont h_inner_mem
  -- Step 3: `Tr` and `Re` are continuous.
  have h_trace_cont : Continuous (fun A : B ℋ_aux => (traceCLM A).re) :=
    Complex.continuous_re.comp traceCLM.continuous
  have h_final :
      ContinuousOn
        (fun p : B ℋ_aux × B ℋ_aux =>
          (traceCLM (CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)).re)
        (pdSet (ℋ := ℋ_aux) ×ˢ pdSet (ℋ := ℋ_aux)) :=
    h_trace_cont.comp_continuousOn h_pow_cont
  refine h_final.congr ?_
  rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
  simpa [β, traceCLM] using
    congrArg Complex.re (sandwichedQuasi_eq_clm_direct α ρ σ)

end Monotonicity

end SandwichedRenyiRelativeEntropy
