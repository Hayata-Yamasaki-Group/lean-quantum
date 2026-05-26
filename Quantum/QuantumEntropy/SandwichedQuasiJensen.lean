/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Jensen–Haar inequality and monotonicity of the sandwiched Rényi divergence

This file proves the central Jensen-style inequality
(`sandwichedQuasi_jensen_haar`) underlying monotonicity of the sandwiched Rényi
divergence under CPTP maps, and the main monotonicity theorem
(`sandwichedRenyiDiv_monotone`).

The proof is structured in three layers:

1. `jensen_haar_core` — Frank–Lieb's central inequality before tensor
   multiplicativity collapses the LHS / RHS to `Re Q_α(E ρ‖E σ)` and
   `Re Q_α(ρ‖σ)`. Proved by passing to a closed convex sub-cone of `pdSetLM`
   cut out by explicit spectral bounds and applying Mathlib's Bochner-integral
   Jensen (`HaarUnitary.jointly_convex_integral_le` /
   `HaarUnitary.jointly_concave_le_integral`).

2. `sandwichedQuasi_jensen_haar` — the abstract Jensen–Haar interface, obtained
   from `jensen_haar_core` by tensor multiplicativity and the self-quasi
   identity `sandwichedQuasi α τ τ = Tr τ`.

3. `sandwichedRenyiDiv_monotone` — the main theorem
   `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`, obtained from `sandwichedQuasi_jensen_haar`
   by applying the Stinespring dilation (`CPTP.exists_stinespring_dilation`)
   and the monotonic log transform.

The closed sub-cone construction in layer 1 uses
`CFC.exists_pos_algebraMap_le_iff` for the lower bound (positive spectrum gives
`∃ ε > 0, ε • 1 ≤ A`) and operator-norm bounds for the upper bound.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory HaarUnitary TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-! ### Spectral bounds for operators in `pdSetLM` -/

/-- For any `A ∈ pdSetLM`, there exists a positive real `ε` such that
    `ε • 1 ≤ A.toCLM` in the CLM order. -/
private lemma pdSetLM_exists_pos_lower_bound {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ ε : ℝ, 0 < ε ∧
      (ε • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) ≤
        A.toContinuousLinearMap := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨r, hr_pos, hr_le⟩ : ∃ r > 0, algebraMap ℝ (LownerHeinzTheorem.L ℋ) r ≤
      A.toContinuousLinearMap :=
    (CFC.exists_pos_algebraMap_le_iff hA_sa).mpr fun _x hx => hA_spec hx
  refine ⟨r, hr_pos, ?_⟩
  rwa [Algebra.algebraMap_eq_smul_one] at hr_le

/-- For any self-adjoint element `A` in a `CStarAlgebra` of operators on a
    finite-dim Hilbert space, there exists `M` such that `A ≤ M • 1`
    (we may take `M = ‖A‖`). -/
private lemma exists_upper_bound_self_adjoint {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : LownerHeinzTheorem.L ℋ} (hA : IsSelfAdjoint A) :
    ∃ M : ℝ, A ≤ (M • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) := by
  refine ⟨‖A‖, ?_⟩
  rw [show (‖A‖ • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) =
    algebraMap ℝ (LownerHeinzTheorem.L ℋ) ‖A‖ from
      (Algebra.algebraMap_eq_smul_one ‖A‖).symm]
  exact hA.le_algebraMap_norm_self

/-! ### The closed convex sub-cone -/

/-- The closed convex sub-cone of `L ℋ` cut out by `ε • 1 ≤ A ≤ M • 1` (in the
    CLM order, transferred along `toContinuousLinearMap`). -/
private def pdSubCone {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) : Set (L ℋ) :=
  {A | ε • (1 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap ∧
       A.toContinuousLinearMap ≤ M • (1 : LownerHeinzTheorem.L ℋ)}

/-- Monotonicity of the scalar-times-1 map in the CLM order: `r ≤ r'` implies
    `r • 1 ≤ r' • 1`. -/
private lemma smul_one_le_smul_one {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {r r' : ℝ} (hrr' : r ≤ r') :
    r • (1 : LownerHeinzTheorem.L ℋ) ≤ r' • (1 : LownerHeinzTheorem.L ℋ) := by
  have h_zero_le_one : (0 : LownerHeinzTheorem.L ℋ) ≤ 1 := zero_le_one
  have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ (r' - r) • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_nonneg (sub_nonneg.mpr hrr') h_zero_le_one
  rw [sub_smul] at h_nn
  exact sub_nonneg.mp h_nn

/-- The sub-cone is convex. -/
private lemma pdSubCone_convex {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) :
    Convex ℝ (pdSubCone (ℋ := ℋ) ε M) := by
  intro a ha b hb θ θ' hθ hθ' hsum
  refine ⟨?_, ?_⟩
  · have hA := ha.1
    have hB := hb.1
    have : ((θ : ℝ) • a + (θ' : ℝ) • b).toContinuousLinearMap =
        (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap := by
      ext x; rfl
    rw [this]
    calc ε • (1 : LownerHeinzTheorem.L ℋ)
        = (θ + θ') • (ε • (1 : LownerHeinzTheorem.L ℋ)) := by rw [hsum]; simp
      _ = θ • (ε • (1 : LownerHeinzTheorem.L ℋ)) + θ' • (ε • (1 : LownerHeinzTheorem.L ℋ)) := by
          rw [add_smul]
      _ ≤ θ • a.toContinuousLinearMap + θ' • b.toContinuousLinearMap := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left hA hθ
          · exact smul_le_smul_of_nonneg_left hB hθ'
  · have hA := ha.2
    have hB := hb.2
    have : ((θ : ℝ) • a + (θ' : ℝ) • b).toContinuousLinearMap =
        (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap := by
      ext x; rfl
    rw [this]
    calc (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap
        ≤ θ • (M • (1 : LownerHeinzTheorem.L ℋ)) + θ' • (M • (1 : LownerHeinzTheorem.L ℋ)) := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left hA hθ
          · exact smul_le_smul_of_nonneg_left hB hθ'
      _ = (θ + θ') • (M • (1 : LownerHeinzTheorem.L ℋ)) := by rw [add_smul]
      _ = M • (1 : LownerHeinzTheorem.L ℋ) := by rw [hsum]; simp

/-- The sub-cone is closed (preimage of the closed interval `Icc (ε•1) (M•1)`
    in the CLM order under the continuous `toContinuousLinearMap`). -/
private lemma pdSubCone_isClosed {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) :
    IsClosed (pdSubCone (ℋ := ℋ) ε M) := by
  have h_toCLM_cont : Continuous (fun A : L ℋ => A.toContinuousLinearMap) :=
    linear_isometry_equiv.continuous
  have h_eq : pdSubCone (ℋ := ℋ) ε M =
      (fun A : L ℋ => A.toContinuousLinearMap) ⁻¹'
        (Set.Icc (ε • (1 : LownerHeinzTheorem.L ℋ)) (M • (1 : LownerHeinzTheorem.L ℋ))) := by
    ext A
    simp only [pdSubCone, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
  rw [h_eq]
  exact isClosed_Icc.preimage h_toCLM_cont

/-- Auxiliary: for unitary `V` in CLM, `V * (r • 1) * V* = r • 1`. -/
private lemma smul_one_conj_unitary_eq {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (r : ℝ) {V : LownerHeinzTheorem.L ℋ} (hV : V * star V = 1) :
    V * (r • (1 : LownerHeinzTheorem.L ℋ)) * star V = r • (1 : LownerHeinzTheorem.L ℋ) :=
  calc V * (r • (1 : LownerHeinzTheorem.L ℋ)) * star V
      = r • (V * 1 * star V) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = r • (V * star V) := by rw [mul_one]
    _ = r • (1 : LownerHeinzTheorem.L ℋ) := by rw [hV]

/-- For unitary `u : L ℋ₁`, `TensorProduct.map u 1` is unitary on `L (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
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
      star (TensorProduct.map (u : L ℋ₁) (LinearMap.id (M := ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
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

/-- Unitary conjugation preserves the closed convex sub-cone `pdSubCone ε M`. -/
private lemma pdSubCone_unitary_conj {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} {A : L ℋ} (hA : A ∈ pdSubCone (ℋ := ℋ) ε M)
    (V : unitary (L ℋ)) :
    (V : L ℋ) * A * star (V : L ℋ) ∈ pdSubCone (ℋ := ℋ) ε M := by
  obtain ⟨hA_lower, hA_upper⟩ := hA
  -- Transfer to CLM: `(V * A * star V).toCLM = V.toCLM * A.toCLM * star V.toCLM`.
  have h_star_toCLM : (star (V : L ℋ)).toContinuousLinearMap =
      star ((V : L ℋ).toContinuousLinearMap) := by
    rw [LinearMap.star_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap,
        ContinuousLinearMap.star_eq_adjoint]
  have h_toCLM_eq : ((V : L ℋ) * A * star (V : L ℋ)).toContinuousLinearMap =
      (V : L ℋ).toContinuousLinearMap * A.toContinuousLinearMap *
        star ((V : L ℋ).toContinuousLinearMap) := by
    rw [show ((V : L ℋ) * A * star (V : L ℋ)).toContinuousLinearMap =
      (V : L ℋ).toContinuousLinearMap * A.toContinuousLinearMap *
      (star (V : L ℋ)).toContinuousLinearMap from by ext x; rfl, h_star_toCLM]
  -- V * star V = 1 in CLM.
  have hVV_LM : (V : L ℋ) * star (V : L ℋ) = 1 := (Unitary.mem_iff.mp V.property).2
  have hVV_CLM : (V : L ℋ).toContinuousLinearMap * star ((V : L ℋ).toContinuousLinearMap) = 1 := by
    rw [← h_star_toCLM]
    rw [show (V : L ℋ).toContinuousLinearMap * (star (V : L ℋ)).toContinuousLinearMap =
        ((V : L ℋ) * star (V : L ℋ)).toContinuousLinearMap from by ext x; rfl, hVV_LM]
    rfl
  -- For each scalar r, `V * (r • 1) * V* = r • 1`.
  have h_eps : (V : L ℋ).toContinuousLinearMap * (ε • (1 : LownerHeinzTheorem.L ℋ)) *
      star ((V : L ℋ).toContinuousLinearMap) = ε • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_one_conj_unitary_eq ε hVV_CLM
  have h_M : (V : L ℋ).toContinuousLinearMap * (M • (1 : LownerHeinzTheorem.L ℋ)) *
      star ((V : L ℋ).toContinuousLinearMap) = M • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_one_conj_unitary_eq M hVV_CLM
  refine ⟨?_, ?_⟩
  · -- ε • 1 ≤ (V * A * V*).toCLM
    rw [h_toCLM_eq, ← h_eps]
    -- Show: V * (ε • 1) * V* ≤ V * A.toCLM * V* via `star_left_conjugate` on the difference.
    have h_diff_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        A.toContinuousLinearMap - ε • (1 : LownerHeinzTheorem.L ℋ) := sub_nonneg.mpr hA_lower
    have h_conj_nn := star_left_conjugate_nonneg h_diff_nn (star ((V : L ℋ).toContinuousLinearMap))
    rw [star_star] at h_conj_nn
    rw [mul_sub, sub_mul] at h_conj_nn
    exact sub_nonneg.mp h_conj_nn
  · -- (V * A * V*).toCLM ≤ M • 1
    rw [h_toCLM_eq, ← h_M]
    have h_diff_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        M • (1 : LownerHeinzTheorem.L ℋ) - A.toContinuousLinearMap := sub_nonneg.mpr hA_upper
    have h_conj_nn := star_left_conjugate_nonneg h_diff_nn (star ((V : L ℋ).toContinuousLinearMap))
    rw [star_star] at h_conj_nn
    rw [mul_sub, sub_mul] at h_conj_nn
    exact sub_nonneg.mp h_conj_nn

/-- The sub-cone is contained in `pdSetLM` when `ε > 0`. -/
private lemma pdSubCone_subset_pdSetLM {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} (hε : 0 < ε) : pdSubCone (ℋ := ℋ) ε M ⊆ pdSetLM (ℋ := ℋ) := by
  intro A ⟨h_lower, _⟩
  -- Use that `ε • 1 = algebraMap ℝ _ ε` and that `algebraMap ε ≤ A.toCLM` gives both
  -- self-adjointness (positivity) and the spectrum bound.
  have h_eq : ε • (1 : LownerHeinzTheorem.L ℋ) = algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [h_eq] at h_lower
  -- `0 ≤ ε • 1` for ε ≥ 0, hence `0 ≤ A.toCLM`.
  have h_pos_1 : (0 : LownerHeinzTheorem.L ℋ) ≤ algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    have h_one_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ 1 := zero_le_one
    rw [← h_eq]
    exact smul_nonneg hε.le h_one_nn
  have h_A_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    le_trans h_pos_1 h_lower
  have h_A_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_A_nn
  refine ⟨h_A_sa, ?_⟩
  intro r hr
  have h_spec_ge : ∀ x ∈ spectrum ℝ A.toContinuousLinearMap, ε ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ)).mp h_lower
  exact lt_of_lt_of_le hε (h_spec_ge r hr)

/-! ### The central Jensen–Haar inequality (`jensen_haar_core`) -/

/-- The inner Jensen-style inequality, *before* applying tensor multiplicativity
    to collapse `τ_max ⊗ E ρ` to `E ρ` and `τ_env ⊗ ρ` to `ρ` (etc.).

    `Re sandwichedQuasi α (τ_max ⊗ Eρ) (τ_max ⊗ Eσ) ⋚ Re sandwichedQuasi α (τ_env ⊗ ρ) (τ_env ⊗ σ)`

    with the direction `≤` for `α > 1` and `≥` for `α ∈ [1/2, 1)`. The proof
    combines `stinespring_haar_eq`, `sandwichedQuasi_unitary_conj` (to compute
    the constant integrand), `sandwichedQuasi_re_jointlyConvex` / `sandwichedQuasi_re_jointlyConcave`,
    `sandwichedQuasi_re_continuousOn_pdSetLM`, and Mathlib's Bochner-integral
    Jensen `HaarUnitary.jointly_convex_integral_le` /
    `HaarUnitary.jointly_concave_le_integral` on the closed convex sub-cone
    `pdSubCone ε M ⊆ pdSetLM`. -/
private theorem jensen_haar_core
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    {τ_env : L ℋ_env} (hτ_env : τ_env ∈ pdSetLM (ℋ := ℋ_env))
    (U : unitary (L (ℋ_env ⊗[ℂ] ℋ)))
    (hEρ : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env ρ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ))
    (hEσ : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env σ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ)) :
    ((sandwichedQuasi α
        (TensorProduct.map
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))
          (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env ρ *
            star (U : L (ℋ_env ⊗[ℂ] ℋ)))))
        (TensorProduct.map
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env))
          (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env σ *
            star (U : L (ℋ_env ⊗[ℂ] ℋ)))))).re -
      (sandwichedQuasi α
        (TensorProduct.map τ_env ρ : L (ℋ_env ⊗[ℂ] ℋ))
        (TensorProduct.map τ_env σ)).re) * (α - 1) ≤ 0 := by
  -- Nontrivial instance on the tensor product (needed for `pdSetLM_exists_pos_lower_bound`).
  haveI : Nontrivial (ℋ_env ⊗[ℂ] ℋ) := by
    have h_env : 0 < Module.finrank ℂ ℋ_env := Module.finrank_pos
    have h_ℋ : 0 < Module.finrank ℂ ℋ := Module.finrank_pos
    have h_tensor : 0 < Module.finrank ℂ (ℋ_env ⊗[ℂ] ℋ) := by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos h_env h_ℋ
    exact Module.nontrivial_of_finrank_pos h_tensor
  -- Setup notation for the four key pd operators.
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with hτ_max_def
  set τρ : L (ℋ_env ⊗[ℂ] ℋ) := TensorProduct.map τ_env ρ with hτρ_def
  set τσ : L (ℋ_env ⊗[ℂ] ℋ) := TensorProduct.map τ_env σ with hτσ_def
  set Eρ' : L ℋ :=
    Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) with hEρ'_def
  set Eσ' : L ℋ :=
    Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) with hEσ'_def
  set τmEρ : L (ℋ_env ⊗[ℂ] ℋ) := TensorProduct.map τ_max Eρ' with hτmEρ_def
  set τmEσ : L (ℋ_env ⊗[ℂ] ℋ) := TensorProduct.map τ_max Eσ' with hτmEσ_def
  -- pd memberships.
  have hτ_max_pd : τ_max ∈ pdSetLM (ℋ := ℋ_env) := maxmixed_pdSetLM ℋ_env
  have hτρ_pd : τρ ∈ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) :=
    pdSetLM_tensorMap hτ_env hρ
  have hτσ_pd : τσ ∈ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) :=
    pdSetLM_tensorMap hτ_env hσ
  have hτmEρ_pd : τmEρ ∈ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) :=
    pdSetLM_tensorMap hτ_max_pd hEρ
  have hτmEσ_pd : τmEσ ∈ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) :=
    pdSetLM_tensorMap hτ_max_pd hEσ
  -- Get spectral lower bounds for each of the four pd operators.
  obtain ⟨ε1, hε1_pos, hε1_le⟩ := pdSetLM_exists_pos_lower_bound hτρ_pd
  obtain ⟨ε2, hε2_pos, hε2_le⟩ := pdSetLM_exists_pos_lower_bound hτσ_pd
  obtain ⟨ε3, hε3_pos, hε3_le⟩ := pdSetLM_exists_pos_lower_bound hτmEρ_pd
  obtain ⟨ε4, hε4_pos, hε4_le⟩ := pdSetLM_exists_pos_lower_bound hτmEσ_pd
  -- Get spectral upper bounds (each operator is self-adjoint).
  obtain ⟨M1, hM1_le⟩ := exists_upper_bound_self_adjoint hτρ_pd.1
  obtain ⟨M2, hM2_le⟩ := exists_upper_bound_self_adjoint hτσ_pd.1
  obtain ⟨M3, hM3_le⟩ := exists_upper_bound_self_adjoint hτmEρ_pd.1
  obtain ⟨M4, hM4_le⟩ := exists_upper_bound_self_adjoint hτmEσ_pd.1
  -- Take common bounds.
  set ε : ℝ := min ε1 (min ε2 (min ε3 ε4)) with hε_def
  set M : ℝ := max M1 (max M2 (max M3 M4)) with hM_def
  have hε_pos : 0 < ε :=
    lt_min hε1_pos (lt_min hε2_pos (lt_min hε3_pos hε4_pos))
  -- Membership of the four operators in `pdSubCone ε M`.
  have hτρ_in : τρ ∈ pdSubCone (ℋ := ℋ_env ⊗[ℂ] ℋ) ε M :=
    ⟨le_trans (smul_one_le_smul_one (min_le_left _ _)) hε1_le,
     le_trans hM1_le (smul_one_le_smul_one (le_max_left _ _))⟩
  have hτσ_in : τσ ∈ pdSubCone (ℋ := ℋ_env ⊗[ℂ] ℋ) ε M :=
    ⟨le_trans (smul_one_le_smul_one (le_trans (min_le_right _ _) (min_le_left _ _))) hε2_le,
     le_trans hM2_le (smul_one_le_smul_one (le_trans (le_max_left _ _) (le_max_right _ _)))⟩
  have hτmEρ_in : τmEρ ∈ pdSubCone (ℋ := ℋ_env ⊗[ℂ] ℋ) ε M :=
    ⟨le_trans (smul_one_le_smul_one
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) hε3_le,
     le_trans hM3_le (smul_one_le_smul_one
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))⟩
  have hτmEσ_in : τmEσ ∈ pdSubCone (ℋ := ℋ_env ⊗[ℂ] ℋ) ε M :=
    ⟨le_trans (smul_one_le_smul_one
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))) hε4_le,
     le_trans hM4_le (smul_one_le_smul_one
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))⟩
  -- The closed convex sub-cone `S` and its key properties.
  set S : Set (L (ℋ_env ⊗[ℂ] ℋ)) := pdSubCone (ℋ := ℋ_env ⊗[ℂ] ℋ) ε M with hS_def
  have hS_convex : Convex ℝ S := pdSubCone_convex ε M
  have hS_closed : IsClosed S := pdSubCone_isClosed ε M
  have hS_pdSetLM : S ⊆ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) := pdSubCone_subset_pdSetLM hε_pos
  -- Define the integrand functions `g_ρ`, `g_σ` (continuous in the Haar variable).
  set g_ρ : unitary (L ℋ_env) → L (ℋ_env ⊗[ℂ] ℋ) := fun u =>
    TensorProduct.map ((u : L ℋ_env)) (LinearMap.id (M := ℋ)) *
      ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
      TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) with hg_ρ_def
  set g_σ : unitary (L ℋ_env) → L (ℋ_env ⊗[ℂ] ℋ) := fun u =>
    TensorProduct.map ((u : L ℋ_env)) (LinearMap.id (M := ℋ)) *
      ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
      TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) with hg_σ_def
  -- Closed sub-cone properties (already established).
  -- `S = pdSubCone ε M` is closed (`pdSubCone_isClosed`), convex
  -- (`pdSubCone_convex`), and contained in `pdSetLM`
  -- (`pdSubCone_subset_pdSetLM` for `ε > 0`).
  --
  -- Orbit membership: by `pdSubCone_unitary_conj` applied to the joint
  -- unitary `V_u := (u⊗1) U`, the orbit `{V_u τρ V_u*, V_u τσ V_u*}` is
  -- contained in `S`. Specifically:
  --   * `(U) * τρ * star (U) ∈ S` by `pdSubCone_unitary_conj hτρ_in U`,
  --   * `g_ρ u = (T u 1) * (U τρ U*) * (T (star u) 1)` and `(T u 1)` is unitary
  --     by `tensorMap_unitary_of_unitary u`, so `g_ρ u ∈ S` by another
  --     application of `pdSubCone_unitary_conj`. Similarly for `g_σ`.
  have hUτρU_in : (U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ)) ∈ S :=
    pdSubCone_unitary_conj hτρ_in U
  have hUτσU_in : (U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ)) ∈ S :=
    pdSubCone_unitary_conj hτσ_in U
  -- `star (TensorProduct.map u 1) = TensorProduct.map (star u) 1`.
  have h_id_sa : star (LinearMap.id : L ℋ) = LinearMap.id := by
    have h_id_one : (LinearMap.id : L ℋ) = 1 := rfl
    rw [h_id_one, IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ))]
  have h_star_tensor : ∀ w : L ℋ_env,
      star (TensorProduct.map w (LinearMap.id (M := ℋ)) : L (ℋ_env ⊗[ℂ] ℋ)) =
        TensorProduct.map (star w) (LinearMap.id (M := ℋ)) := by
    intro w
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, h_id_sa]
  -- Orbit membership.
  have hg_ρ_in : ∀ u : unitary (L ℋ_env), g_ρ u ∈ S := by
    intro u
    let V_u : unitary (L (ℋ_env ⊗[ℂ] ℋ)) :=
      ⟨TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)),
       tensorMap_unitary_of_unitary u⟩
    have h_eq : g_ρ u = (V_u : L (ℋ_env ⊗[ℂ] ℋ)) *
        ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
        star (V_u : L (ℋ_env ⊗[ℂ] ℋ)) := by
      change TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
          ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
          TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) = _
      rw [h_star_tensor]
    rw [h_eq]; exact pdSubCone_unitary_conj hUτρU_in V_u
  have hg_σ_in : ∀ u : unitary (L ℋ_env), g_σ u ∈ S := by
    intro u
    let V_u : unitary (L (ℋ_env ⊗[ℂ] ℋ)) :=
      ⟨TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)),
       tensorMap_unitary_of_unitary u⟩
    have h_eq : g_σ u = (V_u : L (ℋ_env ⊗[ℂ] ℋ)) *
        ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
        star (V_u : L (ℋ_env ⊗[ℂ] ℋ)) := by
      change TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
          ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
          TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) = _
      rw [h_star_tensor]
    rw [h_eq]; exact pdSubCone_unitary_conj hUτσU_in V_u
  -- Unitary invariance: `Re sandwichedQuasi α (g_ρ u) (g_σ u)` is constant in `u`,
  -- equal to `Re sandwichedQuasi α τρ τσ`. Proof: `g_ρ u = V_u τρ star V_u` and
  -- similarly `g_σ u = V_u τσ star V_u` for `V_u := T(u,1) * U` unitary, so by
  -- `sandwichedQuasi_unitary_conj` applied with the joint unitary `V_u`.
  have h_integrand_const : ∀ u : unitary (L ℋ_env),
      (sandwichedQuasi α (g_ρ u) (g_σ u)).re =
        (sandwichedQuasi α τρ τσ).re := by
    intro u
    let V_u : unitary (L (ℋ_env ⊗[ℂ] ℋ)) :=
      ⟨TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
         (U : L (ℋ_env ⊗[ℂ] ℋ)),
       mul_mem (tensorMap_unitary_of_unitary u) U.property⟩
    have h_V_eq : (V_u : L (ℋ_env ⊗[ℂ] ℋ)) =
        TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
          (U : L (ℋ_env ⊗[ℂ] ℋ)) := rfl
    have h_star_V_eq : star (V_u : L (ℋ_env ⊗[ℂ] ℋ)) =
        star (U : L (ℋ_env ⊗[ℂ] ℋ)) *
          TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) := by
      rw [h_V_eq, star_mul, h_star_tensor]
    -- g_ρ u = V_u * τρ * star V_u
    have h_g_ρ_eq : g_ρ u =
        (V_u : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (V_u : L (ℋ_env ⊗[ℂ] ℋ)) := by
      change TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
          ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τρ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
          TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) = _
      rw [h_V_eq, h_star_V_eq]
      simp only [mul_assoc]
    have h_g_σ_eq : g_σ u =
        (V_u : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (V_u : L (ℋ_env ⊗[ℂ] ℋ)) := by
      change TensorProduct.map (u : L ℋ_env) (LinearMap.id (M := ℋ)) *
          ((U : L (ℋ_env ⊗[ℂ] ℋ)) * τσ * star (U : L (ℋ_env ⊗[ℂ] ℋ))) *
          TensorProduct.map (star (u : L ℋ_env)) (LinearMap.id (M := ℋ)) = _
      rw [h_V_eq, h_star_V_eq]
      simp only [mul_assoc]
    rw [h_g_ρ_eq, h_g_σ_eq, sandwichedQuasi_unitary_conj α τρ τσ V_u]
  -- Integral identification via `stinespring_haar_eq`:
  --   `τ_max ⊗ Eρ' = ∫ g_ρ u du` (and similarly for σ).
  have h_int_ρ : ∫ u, g_ρ u ∂(HaarUnitary.haarUnitary ℋ_env) = τmEρ :=
    (HaarUnitary.stinespring_haar_eq U τ_env ρ).symm
  have h_int_σ : ∫ u, g_σ u ∂(HaarUnitary.haarUnitary ℋ_env) = τmEσ :=
    (HaarUnitary.stinespring_haar_eq U τ_env σ).symm
  -- Integrability of the integrand functions over the (probability) Haar measure.
  have h_int_ρ_intble : Integrable g_ρ (HaarUnitary.haarUnitary ℋ_env) :=
    HaarUnitary.integrable_unitaryConj_tensor _
  have h_int_σ_intble : Integrable g_σ (HaarUnitary.haarUnitary ℋ_env) :=
    HaarUnitary.integrable_unitaryConj_tensor _
  -- The composite integrand is a constant; trivially integrable.
  have h_comp_intble :
      Integrable (fun u => (sandwichedQuasi α (g_ρ u) (g_σ u)).re)
        (HaarUnitary.haarUnitary ℋ_env) := by
    have h_eq : (fun u => (sandwichedQuasi α (g_ρ u) (g_σ u)).re) =
        (fun _ : unitary (L ℋ_env) => (sandwichedQuasi α τρ τσ).re) := by
      funext u; exact h_integrand_const u
    rw [h_eq]; exact integrable_const _
  -- Continuity and joint convexity / concavity of `f` on `S × S`.
  have hS_T_prod_subset :
      S ×ˢ S ⊆ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) ×ˢ pdSetLM (ℋ := ℋ_env ⊗[ℂ] ℋ) :=
    Set.prod_mono hS_pdSetLM hS_pdSetLM
  have hf_cont :
      ContinuousOn
        (Function.uncurry (fun ρ' σ' : L (ℋ_env ⊗[ℂ] ℋ) =>
          (sandwichedQuasi α ρ' σ').re))
        (S ×ˢ S) :=
    (sandwichedQuasi_re_continuousOn_pdSetLM α).mono hS_T_prod_subset
  -- Apply Jensen.
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · -- α ∈ [1/2, 1): use sandwichedQuasi_re_jointlyConcave and HaarUnitary.jointly_concave_le_integral.
    have h_concave_pd := sandwichedQuasi_re_jointlyConcave hα_ge hα_lt (ℋ := ℋ_env ⊗[ℂ] ℋ)
    have hf_concave : JointlyConcaveOn S S
        (fun ρ' σ' : L (ℋ_env ⊗[ℂ] ℋ) => (sandwichedQuasi α ρ' σ').re) :=
      fun a a' b b' θ ha ha' hb hb' h0 h1 =>
        h_concave_pd (hS_pdSetLM ha) (hS_pdSetLM ha') (hS_pdSetLM hb) (hS_pdSetLM hb') h0 h1
    have h_int_τmEρ : (∫ u, g_ρ u ∂(HaarUnitary.haarUnitary ℋ_env)) ∈ S := h_int_ρ ▸ hτmEρ_in
    have h_int_τmEσ : (∫ u, g_σ u ∂(HaarUnitary.haarUnitary ℋ_env)) ∈ S := h_int_σ ▸ hτmEσ_in
    have hJensen :=
      HaarUnitary.jointly_concave_le_integral hS_convex hS_convex hS_closed hS_closed
        hf_concave hf_cont
        (Filter.Eventually.of_forall hg_ρ_in) (Filter.Eventually.of_forall hg_σ_in)
        h_int_ρ_intble h_int_σ_intble h_comp_intble h_int_τmEρ h_int_τmEσ
    -- Rewrite LHS using h_integrand_const, RHS using h_int_ρ, h_int_σ.
    rw [show (∫ u, (sandwichedQuasi α (g_ρ u) (g_σ u)).re ∂(HaarUnitary.haarUnitary ℋ_env))
          = (sandwichedQuasi α τρ τσ).re from by
        rw [show (fun u => (sandwichedQuasi α (g_ρ u) (g_σ u)).re) =
            (fun _ : unitary (L ℋ_env) => (sandwichedQuasi α τρ τσ).re) from by
          funext u; exact h_integrand_const u]
        simp [MeasureTheory.integral_const, measureReal_def,
          (HaarUnitary.haarUnitary_isProbabilityMeasure (ℋ := ℋ_env)).measure_univ]] at hJensen
    rw [h_int_ρ, h_int_σ] at hJensen
    -- hJensen : Re Q_α(τρ, τσ) ≤ Re Q_α(τmEρ, τmEσ)
    -- Goal: (Re Q_α(τmEρ, τmEσ) - Re Q_α(τρ, τσ)) * (α - 1) ≤ 0
    -- Since α - 1 < 0 and Re Q_α(τmEρ, τmEσ) ≥ Re Q_α(τρ, τσ), the product is ≤ 0.
    have hα1 : α - 1 < 0 := by linarith
    nlinarith
  · -- α > 1: use sandwichedQuasi_re_jointlyConvex and HaarUnitary.jointly_convex_integral_le.
    have h_convex_pd := sandwichedQuasi_re_jointlyConvex hα_gt (ℋ := ℋ_env ⊗[ℂ] ℋ)
    have hf_convex : JointlyConvexOn S S
        (fun ρ' σ' : L (ℋ_env ⊗[ℂ] ℋ) => (sandwichedQuasi α ρ' σ').re) :=
      fun a a' b b' θ ha ha' hb hb' h0 h1 =>
        h_convex_pd (hS_pdSetLM ha) (hS_pdSetLM ha') (hS_pdSetLM hb) (hS_pdSetLM hb') h0 h1
    have h_int_τmEρ : (∫ u, g_ρ u ∂(HaarUnitary.haarUnitary ℋ_env)) ∈ S := h_int_ρ ▸ hτmEρ_in
    have h_int_τmEσ : (∫ u, g_σ u ∂(HaarUnitary.haarUnitary ℋ_env)) ∈ S := h_int_σ ▸ hτmEσ_in
    have hJensen :=
      HaarUnitary.jointly_convex_integral_le hS_convex hS_convex hS_closed hS_closed
        hf_convex hf_cont
        (Filter.Eventually.of_forall hg_ρ_in) (Filter.Eventually.of_forall hg_σ_in)
        h_int_ρ_intble h_int_σ_intble h_comp_intble h_int_τmEρ h_int_τmEσ
    rw [show (∫ u, (sandwichedQuasi α (g_ρ u) (g_σ u)).re ∂(HaarUnitary.haarUnitary ℋ_env))
          = (sandwichedQuasi α τρ τσ).re from by
        rw [show (fun u => (sandwichedQuasi α (g_ρ u) (g_σ u)).re) =
            (fun _ : unitary (L ℋ_env) => (sandwichedQuasi α τρ τσ).re) from by
          funext u; exact h_integrand_const u]
        simp [MeasureTheory.integral_const, measureReal_def,
          (HaarUnitary.haarUnitary_isProbabilityMeasure (ℋ := ℋ_env)).measure_univ]] at hJensen
    rw [h_int_ρ, h_int_σ] at hJensen
    -- hJensen : Re Q_α(τmEρ, τmEσ) ≤ Re Q_α(τρ, τσ)
    -- Goal: (Re Q_α(τmEρ, τmEσ) - Re Q_α(τρ, τσ)) * (α - 1) ≤ 0
    have hα1 : α - 1 > 0 := by linarith
    nlinarith

/-! ### The abstract Jensen–Haar interface -/

/-- **Jensen–Haar inequality** for `sandwichedQuasi`, in the form used by the
    monotonicity argument.

    Given the data of a Stinespring dilation (an environment Hilbert space
    `ℋ_env`, a positive-definite density matrix `τ_env` on `ℋ_env` with
    `Tr τ_env = 1`, and a unitary `U` on `ℋ_env ⊗ ℋ`), let
    `E(γ) := Tr₂[U (τ_env ⊗ γ) U*]`. Then for any `α ∈ [1/2, 1) ∪ (1, ∞)` and any
    positive-definite `ρ, σ` with positive-definite images `E ρ`, `E σ`,
    `(Re sandwichedQuasi α (E ρ) (E σ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`.

    The proof reduces to `jensen_haar_core` plus tensor multiplicativity (via
    `sandwichedQuasi_tensor` and `sandwichedQuasi_self_pdSetLM`). -/
theorem sandwichedQuasi_jensen_haar
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    {τ_env : L ℋ_env} (hτ_env : τ_env ∈ pdSetLM (ℋ := ℋ_env))
    (hτ_env_trace : Tr τ_env = 1)
    (U : unitary (L (ℋ_env ⊗[ℂ] ℋ)))
    (hEρ : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env ρ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ))
    (hEσ : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env σ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ)) :
    ((sandwichedQuasi α
        (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env ρ *
            star (U : L (ℋ_env ⊗[ℂ] ℋ))))
        (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env σ *
            star (U : L (ℋ_env ⊗[ℂ] ℋ))))).re -
      (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  -- Abbreviations
  set Eρ : L ℋ :=
    Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env ρ *
      star (U : L (ℋ_env ⊗[ℂ] ℋ))) with hEρ_def
  set Eσ : L ℋ :=
    Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ_env σ *
      star (U : L (ℋ_env ⊗[ℂ] ℋ))) with hEσ_def
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with hτ_max_def
  -- `τ_max ∈ pdSetLM` and `Tr τ_max = 1`.
  have hτ_max_pd : τ_max ∈ pdSetLM (ℋ := ℋ_env) := maxmixed_pdSetLM ℋ_env
  have hτ_max_trace : Tr τ_max = 1 := by
    rw [hτ_max_def, map_smul, smul_eq_mul, LinearMap.trace_one]
    have hd : (Module.finrank ℂ ℋ_env : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ_env)).ne'
    field_simp
  -- LHS factorisation: `Q_α(τ_max⊗Eρ, τ_max⊗Eσ) = Q_α(Eρ, Eσ)`.
  have hLHS_factor : sandwichedQuasi α
      (TensorProduct.map τ_max Eρ : L (ℋ_env ⊗[ℂ] ℋ))
      (TensorProduct.map τ_max Eσ) =
      sandwichedQuasi α Eρ Eσ := by
    rw [sandwichedQuasi_tensor α τ_max τ_max Eρ Eσ
        (nonneg_of_pdSetLM hτ_max_pd) (nonneg_of_pdSetLM hτ_max_pd)
        (nonneg_of_pdSetLM hEρ) (nonneg_of_pdSetLM hEσ),
        sandwichedQuasi_self_pdSetLM hα_ne0 hτ_max_pd, hτ_max_trace, one_mul]
  -- RHS factorisation: `Q_α(τ_env⊗ρ, τ_env⊗σ) = Q_α(ρ, σ)`.
  have hRHS_factor : sandwichedQuasi α
      (TensorProduct.map τ_env ρ : L (ℋ_env ⊗[ℂ] ℋ))
      (TensorProduct.map τ_env σ) =
      sandwichedQuasi α ρ σ := by
    rw [sandwichedQuasi_tensor α τ_env τ_env ρ σ
        (nonneg_of_pdSetLM hτ_env) (nonneg_of_pdSetLM hτ_env)
        (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ),
        sandwichedQuasi_self_pdSetLM hα_ne0 hτ_env, hτ_env_trace, one_mul]
  -- Apply the inner Jensen–Haar inequality and substitute the factorisations.
  have h_inner := jensen_haar_core hα_ge hα_ne1 hρ hσ hτ_env U hEρ hEσ
  change ((sandwichedQuasi α Eρ Eσ).re - (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0
  have hLHS_re : (sandwichedQuasi α (TensorProduct.map τ_max Eρ : L (ℋ_env ⊗[ℂ] ℋ))
      (TensorProduct.map τ_max Eσ)).re = (sandwichedQuasi α Eρ Eσ).re := by
    rw [hLHS_factor]
  have hRHS_re : (sandwichedQuasi α (TensorProduct.map τ_env ρ : L (ℋ_env ⊗[ℂ] ℋ))
      (TensorProduct.map τ_env σ)).re = (sandwichedQuasi α ρ σ).re := by
    rw [hRHS_factor]
  rw [← hLHS_re, ← hRHS_re]
  exact h_inner

/-! ### Main monotonicity theorem -/

/-- Monotonicity of the sandwiched Rényi divergence under CPTP maps (data-processing inequality).

    For any quantum channel `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    positive-definite operators `ρ, σ` with positive-definite images `E ρ`, `E σ`,
        `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`.

    **Proof.** Apply the Stinespring dilation `E(γ) = Tr_env[U(τ⊗γ)U*]`
    (`CPTP.exists_stinespring_dilation`). The central inequality
        `(Re sandwichedQuasi α (Eρ) (Eσ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`
    follows from `sandwichedQuasi_jensen_haar` (the abstract Jensen–Haar inequality
    above). Dividing by `Tr Eρ = Tr ρ > 0` (trace preservation by `E`) and applying
    `(α−1)⁻¹ log(·)` gives the result, with sign tracking unifying the `α > 1`
    and `α < 1` cases. -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (E : CPTP ℋ ℋ) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := ℋ))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := ℋ)) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  -- Step 1: Stinespring dilation.
  obtain ⟨ℋ_env, h_qudit, h_nontriv, τ, hτ_pos, hτ_unit, hτ_trace, U, hU_eq⟩ :=
    CPTP.exists_stinespring_dilation E
  letI := h_qudit
  letI := h_nontriv
  -- τ as a member of pdSetLM (positive-definite + invertible).
  have hτ_pdSetLM : τ ∈ pdSetLM (ℋ := ℋ_env) := by
    have hτ_nn : (0 : L ℋ_env) ≤ τ := (LinearMap.nonneg_iff_isPositive τ).mpr hτ_pos
    have hτ_clm_nn : (0 : LownerHeinzTheorem.L ℋ_env) ≤ τ.toContinuousLinearMap :=
      map_nonneg (toCLMStarAlgHom (ℋ := ℋ_env)) hτ_nn
    have hτ_clm_sa : IsSelfAdjoint τ.toContinuousLinearMap :=
      IsSelfAdjoint.of_nonneg hτ_clm_nn
    have hτ_clm_unit : IsUnit τ.toContinuousLinearMap :=
      (toCLMStarAlgHom (ℋ := ℋ_env)).toRingHom.isUnit_map hτ_unit
    refine ⟨hτ_clm_sa, ?_⟩
    intro r hr
    have h_spec_nn : spectrum ℝ τ.toContinuousLinearMap ⊆ Set.Ici 0 :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hτ_clm_sa)).1 hτ_clm_nn
    rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
    · exact h
    · exfalso; rw [← h] at hr
      exact (spectrum.zero_notMem_iff (R := ℝ)).mpr hτ_clm_unit hr
  -- Step 2: Eρ and Eσ as the Stinespring images.
  have hEρ_eq : E.toFun ρ =
      Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ ρ *
        star (U : L (ℋ_env ⊗[ℂ] ℋ))) := hU_eq ρ
  have hEσ_eq : E.toFun σ =
      Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ σ *
        star (U : L (ℋ_env ⊗[ℂ] ℋ))) := hU_eq σ
  -- pdSetLM membership of the Stinespring images (re-stated in the form needed
  -- by `sandwichedQuasi_jensen_haar`).
  have hEρ' : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ ρ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ) := hEρ_eq ▸ hEρ
  have hEσ' : (Tr₂ ((U : L (ℋ_env ⊗[ℂ] ℋ)) * TensorProduct.map τ σ *
              star (U : L (ℋ_env ⊗[ℂ] ℋ)))) ∈ pdSetLM (ℋ := ℋ) := hEσ_eq ▸ hEσ
  -- Step 3: the central Q_α-inequality, from `sandwichedQuasi_jensen_haar`.
  have hQ_ineq :
      ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re - (sandwichedQuasi α ρ σ).re) *
        (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar hα_ge hα_ne1 hρ hσ hτ_pdSetLM hτ_trace U hEρ' hEσ'
    -- Rewrite using `Eρ = Tr₂(...)` and `Eσ = Tr₂(...)`.
    rw [hEρ_eq, hEσ_eq]
    exact h
  -- Step 4: unfold D_α and apply log monotonicity.
  unfold sandwichedRenyiDiv
  -- `E` preserves traces: `Tr (E.toFun ρ) = Tr ρ`.
  have hTr_Eρ : (Tr (E.toFun ρ)).re = (Tr ρ).re := by
    rw [← E.trace_map ρ]
  -- Positivity of the relevant real parts.
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  -- Positivity of `Re sandwichedQuasi α ρ' σ'` for `ρ', σ' ∈ pdSetLM`: the inner
  -- operator `σ'^β ρ' σ'^β` is pd, hence `(·)^α` is pd, hence the trace is positive.
  have hQ_pos_aux : ∀ {ρ' σ' : L ℋ},
      ρ' ∈ pdSetLM (ℋ := ℋ) → σ' ∈ pdSetLM (ℋ := ℋ) →
      (0 : ℝ) < (sandwichedQuasi α ρ' σ').re := by
    intro ρ' σ' hρ' hσ'
    unfold sandwichedQuasi
    have hP_pd : CFC.rpow σ' ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ'
    have hP_sa : IsSelfAdjoint (CFC.rpow σ' ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hP_pd)
    have hP_unit : IsUnit (CFC.rpow σ' ((1 - α) / (2 * α))) := isUnit_of_pdSetLM hP_pd
    have h_inner_eq :
        CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) =
        star (CFC.rpow σ' ((1 - α) / (2 * α))) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) := by
      rw [hP_sa.star_eq]
    have h_inner_pd :
        (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) ∈
          pdSetLM (ℋ := ℋ) := by
      rw [h_inner_eq]; exact pdSetLM_conj hρ' hP_unit
    have h_pow_pd :
        CFC.rpow
            (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) α ∈
          pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne h_inner_pd
    exact trace_re_pos_of_pdSetLM h_pow_pd
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := hQ_pos_aux hρ hσ
  have hQEρEσ_pos : (0 : ℝ) < (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    hQ_pos_aux hEρ hEσ
  -- Final step: deduce the log inequality.
  -- From `hQ_ineq`: `(Q_α(Eρ,Eσ).re − Q_α(ρ,σ).re) · (α-1) ≤ 0`.
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · -- α < 1: α - 1 < 0
    have hα1_neg : (α - 1 : ℝ) < 0 := by linarith
    have hQ_ge :
        (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
          (Tr (E.toFun ρ)).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge (le_of_lt hTr_ρ_pos))
    have h1α : (1 / (α - 1) : ℝ) < 0 := by
      rw [one_div]; exact inv_neg''.mpr hα1_neg
    nlinarith
  · -- α > 1: α - 1 > 0
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    have hQ_le' :
        (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≤ (sandwichedQuasi α ρ σ).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
        (Tr (E.toFun ρ)).re) ≤
          Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQEρEσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le' (le_of_lt hTr_ρ_pos))
    have h1α_pos : (0 : ℝ) < 1 / (α - 1) := by
      rw [one_div]; exact inv_pos.mpr hα1_pos
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt h1α_pos)

end SandwichedRenyiRelativeEntropy
