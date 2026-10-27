/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.SupportOrder
import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumEntropy.Common.TraceReCore

/-!
# Non-negative sandwiched Rényi divergence: faithful approximation

Support preservation, depolarizing Kraus data, and faithful approximating channels
for the Frank-Lieb non-negative extension.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-! ### Support preservation under positive maps -/

/-- Positive maps preserve the support inclusion: if `supp ρ ⊂ supp σ` and `Φ` is
    completely positive, then `supp (Φ ρ) ⊂ supp (Φ σ)`. -/
lemma supportLE_map_of_cptp
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : SupportLE ρ σ) :
    SupportLE (Φ.toFun ρ) (Φ.toFun σ) := by
  intro x hx
  have hΦρ_nn : 0 ≤ Φ.toFun ρ :=
    map_nonneg Φ.toCompletelyPositiveMap hρ
  obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ h
  have hΦρ_le :
      Φ.toFun ρ ≤ (lam : ℂ) • Φ.toFun σ := by
    have h1 := map_nonneg Φ.toCompletelyPositiveMap (sub_nonneg.mpr hlam_le)
    rw [map_sub, map_smul] at h1
    exact sub_nonneg.mp h1
  exact QuantumChannel.nonneg_eq_zero_of_le_of_apply_eq_zero hΦρ_nn hΦρ_le (by
    rw [LinearMap.smul_apply, hx, smul_zero])

/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/
@[deprecated (since := "2026-09-05")]
alias outer_product_apply := QuantumChannel.outer_product_apply

/-- Adjoint of an outer product swaps its factors: `(|v⟩⟨u|)† = |u⟩⟨v|`. -/
private lemma adjoint_outer_product {ℋ : Type u} [Qudit ℋ] (u v : ℋ) :
    LinearMap.adjoint (outer_product u v) = outer_product v u := by
  apply LinearMap.ext; intro x
  apply ext_inner_right ℂ; intro y
  rw [LinearMap.adjoint_inner_left, QuantumChannel.outer_product_apply,
      QuantumChannel.outer_product_apply, inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

/-- **Kraus sum for the (cross-space) depolarizing channel.** With `bp` an orthonormal basis
    of the target `𝒦`, `bq` an orthonormal basis of the source `ℋ`, and a real scalar `c`,
    `∑_{i,j} (c • |bp i⟩⟨bq j|) γ (c • |bp i⟩⟨bq j|)† = (c² · Tr γ) •
      1_𝒦`. -/
private lemma depolarizing_kraus_sum
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Qudit 𝒦]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bp : OrthonormalBasis ι ℂ 𝒦) (bq : OrthonormalBasis κ ℂ ℋ)
    (γ : L ℋ) (c : ℝ) :
    (∑ p : ι × κ, (krausTerm ((c : ℂ) • outer_product (bq p.2) (bp p.1)) : T ℋ 𝒦) γ)
      = ((c : ℂ) ^ 2 * Tr γ) • (1 : L 𝒦) := by
  classical
  -- Per-term: `(c•|eᵢ⟩⟨fⱼ|) γ (c•|eᵢ⟩⟨fⱼ|)† = c² ⟪fⱼ, γ fⱼ⟫
  -- • |eᵢ⟩⟨eᵢ|`.
  have hterm : ∀ (i : ι) (j : κ),
      ((krausTerm ((c : ℂ) • outer_product (bq j) (bp i)) : T ℋ 𝒦) γ) =
        ((c : ℂ) ^ 2 * inner ℂ (bq j) (γ (bq j))) •
          outer_product (bp i) (bp i) := by
    intro i j
    have hadj : LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i))
        = (c : ℂ) • outer_product (bp i) (bq j) := by
      rw [map_smulₛₗ, Complex.conj_ofReal]
      congr 1
      rw [outer_product_eq_rankOne, outer_product_eq_rankOne]
      apply LinearMap.toContinuousLinearMap.injective
      rw [LinearMap.adjoint_toContinuousLinearMap]
      exact InnerProductSpace.adjoint_rankOne (𝕜 := ℂ) (bp i) (bq j)
    change ((c : ℂ) • outer_product (bq j) (bp i)) ∘ₗ γ ∘ₗ
      LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i)) = _
    rw [hadj]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      QuantumChannel.outer_product_apply, smul_smul]
    congr 1
    ring
  -- Reassemble the double sum into `(c² · Tr γ) • 1_𝒦`.
  have hTr : (∑ j, inner ℂ (bq j) (γ (bq j))) = Tr γ :=
    (LinearMap.trace_eq_sum_inner (T := γ) bq).symm
  have hId : (∑ i, outer_product (bp i) (bp i)) = (1 : L 𝒦) := by
    ext x
    simpa [LinearMap.sum_apply, QuantumChannel.outer_product_apply] using bp.sum_repr' x
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_smul, ← Finset.mul_sum, hTr]
  rw [← Finset.smul_sum, hId]

/-- The (cross-space) depolarizing channel's underlying linear map `γ ↦ (Tr γ / d_𝒦) •
  1_𝒦`. -/
noncomputable def depolLinMap (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    L ℋ →ₗ[ℂ] L 𝒦 where
  toFun γ := (Tr γ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  map_add' x y := by
    change (Tr (x + y) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) +
         (Tr y / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
    rw [map_add, add_div, add_smul]
  map_smul' c x := by
    change (Tr (c • x) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (RingHom.id ℂ) c • ((Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul]

/-- **Complete positivity of the (cross-space) depolarizing channel**, via the Kraus
    decomposition `depolLinMap = ∑_{i,j} krausTerm ((√d_𝒦)⁻¹ • |i⟩⟨j|)`. -/
lemma cp_depolLinMap (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    QuantumChannel.IsCompletelyPositive (depolLinMap ℋ 𝒦) := by
  classical
  set m := Module.finrank ℂ 𝒦 with hm
  set n := Module.finrank ℂ ℋ with hn
  set bp : OrthonormalBasis (Fin m) ℂ 𝒦 := stdOrthonormalBasis ℂ 𝒦 with hbp
  set bq : OrthonormalBasis (Fin n) ℂ ℋ := stdOrthonormalBasis ℂ ℋ with hbq
  set V : Fin m × Fin n → (ℋ →ₗ[ℂ] 𝒦) :=
    fun p => (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) • outer_product (bq p.2) (bp p.1) with hV
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc2 : ((((Real.sqrt (m : ℝ))⁻¹ : ℝ)) : ℂ) ^ 2 = ((m : ℂ))⁻¹ := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt hm_nn, Complex.ofReal_inv,
        Complex.ofReal_natCast]
  have hmap : depolLinMap ℋ 𝒦 = ∑ p : Fin m × Fin n, krausTerm (V p) := by
    apply LinearMap.ext; intro γ
    rw [LinearMap.sum_apply]
    change (Tr γ / (m : ℂ)) • (1 : L 𝒦) =
        ∑ p : Fin m × Fin n, (krausTerm (V p) : T ℋ 𝒦) γ
    rw [depolarizing_kraus_sum bp bq γ ((Real.sqrt (m : ℝ))⁻¹), hc2]
    congr 1
    ring
  rw [hmap]
  exact isCompletelyPositive_sum_krausTerm V

/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

/-- The (cross-space) depolarizing channel `ρ ↦ (Tr ρ / d_𝒦) • 1_𝒦`, bundled
    with complete positivity and trace preservation. -/
noncomputable def depolarizingChannel
    (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    QuantumChannel.CPTP ℋ 𝒦 := by
  let Ψ : CompletelyPositiveMap (L ℋ) (L 𝒦) :=
    { depolLinMap ℋ 𝒦 with
      map_cstarMatrix_nonneg' := by
        intro k M hM
        exact (QuantumChannel.isCompletelyPositive_iff_cstarMatrix_nonneg _).mp
          (cp_depolLinMap ℋ 𝒦) k M hM }
  exact
    { Ψ with
      trace_map := by
        intro ρ
        change Tr ρ = Tr ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
        rw [map_smul, smul_eq_mul, LinearMap.trace_one,
          div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')] }

/-- The faithful approximating channel `F_λ := (1 − λ) Φ + λ · depolarizing`,
    bundled as CPTP data for `0 ≤ λ ≤ 1`. -/
noncomputable def faithfulApprox
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    QuantumChannel.CPTP ℋ 𝒦 where
  toFun X := ((1 - lam : ℝ) : ℂ) • Φ.toFun X +
    ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun X
  map_add' X Y := by
    change ((1 - lam : ℝ) : ℂ) • Φ.toLinearMap (X + Y) +
        ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toLinearMap (X + Y) =
      (((1 - lam : ℝ) : ℂ) • Φ.toLinearMap X +
          ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toLinearMap X) +
        (((1 - lam : ℝ) : ℂ) • Φ.toLinearMap Y +
          ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toLinearMap Y)
    rw [Φ.toLinearMap.map_add, (depolarizingChannel ℋ 𝒦).toLinearMap.map_add]
    simp only [smul_add]
    abel
  map_smul' c X := by
    change ((1 - lam : ℝ) : ℂ) • Φ.toLinearMap (c • X) +
        ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toLinearMap (c • X) =
      c • (((1 - lam : ℝ) : ℂ) • Φ.toLinearMap X +
        ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toLinearMap X)
    rw [Φ.toLinearMap.map_smul, (depolarizingChannel ℋ 𝒦).toLinearMap.map_smul]
    simp only [smul_add, smul_smul]
    rw [mul_comm c (((1 - lam : ℝ) : ℂ)), mul_comm c (((lam : ℝ) : ℂ))]
  map_cstarMatrix_nonneg' k M hM := by
    have hΦM : 0 ≤ M.map Φ.toCompletelyPositiveMap :=
      Φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    have hDM : 0 ≤ M.map (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap :=
      (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.map_cstarMatrix_nonneg' k M hM
    have heq : M.map (fun X =>
        ((1 - lam : ℝ) : ℂ) • Φ.toFun X +
          ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun X) =
        ((1 - lam : ℝ) : ℂ) • M.map Φ.toCompletelyPositiveMap +
          ((lam : ℝ) : ℂ) • M.map (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap := by
      ext i j
      rfl
    change 0 ≤ M.map (fun X =>
      ((1 - lam : ℝ) : ℂ) • Φ.toFun X +
        ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun X)
    rw [heq]
    exact add_nonneg
      (smul_nonneg (Complex.zero_le_real.mpr (sub_nonneg.mpr hlam1)) hΦM)
      (smul_nonneg (Complex.zero_le_real.mpr hlam0) hDM)
  trace_map X := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← Φ.trace_map X, ← (depolarizingChannel ℋ 𝒦).trace_map X]
    push_cast
    ring

@[deprecated (since := "2026-09-05")]
alias trace_re_pos_of_ne_zero := QuantumEntropy.trace_re_pos_of_ne_zero

/-- For `0 < λ ≤ 1`, the approximating channel is faithful (`F_λ 1_ℋ` is positive definite
    in the target `𝒦`). -/
lemma faithfulApprox_one_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (faithfulApprox Φ lam hlam0.le hlam1).toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦) := by
  -- `F_λ 1_ℋ = (1-λ) Φ 1 + λ • (Tr 1_ℋ / d_𝒦) • 1_𝒦 = (1-λ) Φ 1 +
  -- (λ·d_ℋ/d_𝒦) • 1_𝒦`.
  have hdℋ_pos : 0 < (Module.finrank ℂ ℋ : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd𝒦_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have h_F1 :
      (faithfulApprox Φ lam hlam0.le hlam1).toFun (1 : L ℋ) =
        ((1 - lam : ℝ) : ℂ) •
          Φ.toFun (1 : L ℋ) +
        ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) •
          (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • Φ.toFun (1 : L ℋ) +
      ((lam : ℝ) : ℂ) •
        ((Tr (1 : L ℋ) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [LinearMap.trace_one]
    simp only [smul_smul]
    congr 2
    push_cast
    ring
  rw [h_F1]
  -- `(1-λ) Φ 1 ≥ 0` (since `1 ≥ 0`, `Φ` preserves `≥ 0`, `1-λ ≥ 0`).
  have h_Φ1_nn : (0 : L 𝒦) ≤ Φ.toFun (1 : L ℋ) :=
    map_nonneg Φ.toCompletelyPositiveMap zero_le_one
  have h_coef_nn : (0 : ℂ) ≤ ((1 - lam : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by linarith)
  have h_first_nn : (0 : L 𝒦) ≤
      ((1 - lam : ℝ) : ℂ) • Φ.toFun (1 : L ℋ) :=
    smul_nonneg h_coef_nn h_Φ1_nn
  -- Use `pos_smul_one_pdSetLM` for the positive scalar multiple of the identity.
  have h_second_pd :
      ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) •
          (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (div_pos (mul_pos hlam0 hdℋ_pos) hd𝒦_pos)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- For `0 < λ ≤ 1` and `ρ ≠ 0` non-negative, `F_λ ρ` is positive definite:
    `F_λ ρ = (1−λ)·Eρ + λ·(Tr ρ / d)·1`, where the second summand is `(positive
      real)·1 ∈ pdSetLM`
    (since `Tr ρ > 0`) and the first is non-negative. -/
lemma faithfulApprox_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    (faithfulApprox Φ lam hlam0.le hlam1).toFun ρ ∈ pdSetLM (ℋ := 𝒦) := by
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hTrρ_pos : 0 < (Tr ρ).re := QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  -- `Tr ρ` is real (`ρ` non-negative, hence self-adjoint).
  have hTr_im : (Tr ρ).im = 0 := by
    have h : (0 : ℂ) ≤ Tr ρ :=
      ((LinearMap.nonneg_iff_isPositive ρ).mp hρ).trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  have hTr_real : Tr ρ = ((Tr ρ).re : ℂ) := by
    apply Complex.ext <;> simp [hTr_im]
  have hscalar : ((lam : ℝ) : ℂ) * (Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) =
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) := by
    set t : ℝ := (Tr ρ).re with ht
    rw [hTr_real]; push_cast; ring
  have h_Fρ :
      (faithfulApprox Φ lam hlam0.le hlam1).toFun ρ =
        ((1 - lam : ℝ) : ℂ) •
          Φ.toFun ρ +
        ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) •
          (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • Φ.toFun ρ +
      ((lam : ℝ) : ℂ) •
        ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    simp only [smul_smul]
    change ((1 - lam : ℝ) : ℂ) •
        Φ.toFun ρ +
      (((lam : ℝ) : ℂ) * (Tr ρ / (Module.finrank ℂ 𝒦 : ℂ))) •
        (1 : L 𝒦) = _
    rw [hscalar]
  rw [h_Fρ]
  have hΦρ_nn : (0 : L 𝒦) ≤ Φ.toFun ρ :=
    map_nonneg Φ.toCompletelyPositiveMap hρ
  have h_first_nn : (0 : L 𝒦) ≤
      ((1 - lam : ℝ) : ℂ) • Φ.toFun ρ :=
    smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hΦρ_nn
  have h_second_pd :
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) •
          (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (div_pos (mul_pos hlam0 hTrρ_pos) hd_pos)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- `F_λ X → Φ X` as `λ → 0+`. -/
lemma tendsto_faithfulApprox
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : QuantumChannel.CPTP ℋ 𝒦) (X : L ℋ) :
    Filter.Tendsto
      (fun (lam : {l : ℝ // 0 < l ∧ l ≤ 1}) =>
        (faithfulApprox Φ lam.val lam.property.1.le lam.property.2).toFun X)
      (Filter.comap (fun lam : {l : ℝ // 0 < l ∧ l ≤ 1} => lam.val)
        (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (Φ.toFun X)) := by
  -- Extend to all `lam : ℝ`: `g lam = (1-lam) • Φ X + lam • c` where `c = (Tr X /
  -- d_𝒦) • 1_𝒦`.
  let c : L 𝒦 := (Tr X / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  let g : ℝ → L 𝒦 :=
    fun lam => ((1 - lam : ℝ) : ℂ) • Φ.toFun X + ((lam : ℝ) : ℂ) • c
  -- The defining formula of `F_λ X` matches `g lam.val` definitionally.
  have h_F_eq : ∀ (lam : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (faithfulApprox Φ lam.val lam.property.1.le lam.property.2).toFun X = g lam.val := by
    intro lam
    rfl
  simp_rw [h_F_eq]
  -- `g` is continuous on ℝ.
  have hg_cont : Continuous g := by
    change Continuous (fun lam : ℝ =>
      ((1 - lam : ℝ) : ℂ) • Φ.toFun X +
        ((lam : ℝ) : ℂ) • c)
    fun_prop
  -- `g 0 = Φ X` after CLM conjugation.
  have hg_zero : g 0 = Φ.toFun X := by
    change ((1 - (0 : ℝ) : ℝ) : ℂ) • Φ.toFun X +
      (((0 : ℝ)) : ℂ) • c = Φ.toFun X
    simp
  -- Tendsto in ℝ at 0 (from the right) follows from continuity at 0.
  have h_real : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Φ.toFun X)) := by
    rw [← hg_zero]
    exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Transfer along the subtype projection via `comap`.
  exact h_real.comp Filter.tendsto_comap

end SandwichedRenyiRelativeEntropy
