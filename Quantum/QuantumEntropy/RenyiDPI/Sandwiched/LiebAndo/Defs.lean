/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.YoungInequality
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.TensorCFC
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Quantum.QuantumEntropy.Common.OperatorScalarTower
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

/-!
# Sandwiched Rényi relative entropy: definitions and Frank-Lieb variational representation
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

private lemma trace_reverse_young_inequality_direct {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1) (M N : L ℋ)
    (hM : M.IsPositive) (hM_unit : IsUnit M) (hN : N.IsPositive) :
    Tr (CFC.rpow M r) / r + Tr (CFC.rpow N s) / s ≤ Tr (M * N) := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  have h := _root_.trace_reverse_young_inequality hr hs0 hs1 hrs
    M.toContinuousLinearMap N.toContinuousLinearMap
    ((LinearMap.isPositive_toContinuousLinearMap_iff M).2 hM)
    (IsUnit.map e hM_unit)
    ((LinearMap.isPositive_toContinuousLinearMap_iff N).2 hN)
  simpa only [rpow_toLinearMap] using h

private lemma quasiVarOpt_isPositive {α : ℝ} {ρ σ : L ℋ} :
    (quasiVarOpt α ρ σ).IsPositive := by
  rw [quasiVarOpt_eq_direct]
  let P := CFC.rpow σ ((1 - α) / (2 * α))
  let X := P * ρ * P
  change (P * CFC.rpow X (α - 1) * P).IsPositive
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hXpow_pos : (CFC.rpow X (α - 1)).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  exact QuantumChannel.isPositive_conj hP_sa hXpow_pos

/-- Attainment for `α > 1`, as the direct corollary of the explicit optimizer. -/
theorem exists_quasiVar_eq_quasi_gt {α : ℝ} (hα : 1 < α) {ρ σ : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) :
    ∃ H : L ℋ, H.IsPositive ∧ quasiVar α ρ σ H = sandwichedQuasi α ρ σ :=
  ⟨quasiVarOpt α ρ σ, quasiVarOpt_isPositive,
    quasiVarOpt_eq_quasi_gt hα hρ hσ hσ_unit⟩

/-- Algebraic rearrangement: from reverse Young's form to variational form.
    If b/r + c/s ≤ a with 0 < s < 1 and 1/r + 1/s = 1, then c ≤ s·a - (s-1)·b. -/
private lemma reverse_young_to_variational {a b c : ℂ} {r s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1)
    (h : b / ↑r + c / ↑s ≤ a) :
    c ≤ ↑s * a - ↑(s - 1) * b := by
  have hs_nn : (0 : ℂ) ≤ ↑s := by exact_mod_cast le_of_lt hs0
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs0
  have hr_ne : (r : ℂ) ≠ 0 := by
    suffices r ≠ 0 by exact_mod_cast this
    intro hr0; simp [hr0] at hrs; linarith [one_div_pos.mpr hs0]
  rw [le_sub_iff_add_le, add_comm]
  have key : ↑(s - 1) * b + c = ↑s * (b / ↑r + c / ↑s) := by
    have h_sr : (s - 1 : ℝ) = s / r := by
      have h1 : 1 / r = 1 - 1 / s := by linarith
      field_simp at h1 ⊢; linarith
    have h_cast : (↑(s - 1) : ℂ) = ↑s / ↑r := by
      rw [h_sr]; push_cast; ring
    rw [h_cast]; field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left h hs_nn

/-- Lower bound on the variational functional for `0 < α < 1`:
    for all invertible positive `H`, `sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H`.
    Proof by the reverse Young inequality.

Source: arXiv:1306.5358v3, Lemma 4 (part 1: the variational lower bound), p.4 (proof). -/
theorem quasi_le_quasiVar {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) (hH_unit : IsUnit H) :
    sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ :=
    (LinearMap.nonneg_iff_isPositive σ).2 hσ
  have hP_sa : IsSelfAdjoint P :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ_sa : IsSelfAdjoint Q :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hX_pos : X.IsPositive := by
    rw [hX_def]
    exact QuantumChannel.isPositive_conj hP_sa hρ
  have hY_pos : Y.IsPositive := by
    rw [hY_def]
    exact QuantumChannel.isPositive_conj hQ_sa hH
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit hσ_nn
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit hσ_nn
  have hQ_unit : IsUnit Q := hσ_unit.cfcRpow (-β') hσ_nn
  have hY_unit : IsUnit Y := (hQ_unit.mul hH_unit).mul hQ_unit
  set r := α / (α - 1) with hr_def
  have hr_neg : r < 0 := by
    rw [hr_def]
    exact div_neg_of_pos_of_neg hα0 (by linarith)
  have hrs : 1 / r + 1 / α = 1 := by
    rw [hr_def]
    field_simp
    ring
  have hRevYoung := trace_reverse_young_inequality_direct hr_neg hα0 hα1 hrs
    Y X hY_pos hY_unit hX_pos
  have h_xy : Tr (X * Y) = Tr (H * ρ) :=
    trace_conj_cancel hPQ hQP
  have h_yx : Tr (Y * X) = Tr (H * ρ) := by
    rw [LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) Y X]
    exact h_xy
  have h_Yr : Tr (CFC.rpow Y r) =
      Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ ((α - 1) / (2 * α))) r) := by
    have hexp : -β' = (α - 1) / (2 * α) := by
      rw [hβ'_def]
      ring
    rw [hY_def, hQ_def, hexp]
  rw [sandwichedQuasi_eq_direct, quasiVar_eq_direct]
  change Tr (CFC.rpow X α) ≤
    (α : ℂ) * Tr (H * ρ) -
      ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ ((α - 1) / (2 * α))) r)
  rw [← h_Yr, ← h_yx]
  exact reverse_young_to_variational hα0 hα1 hrs hRevYoung

/-- The explicit optimizer realizes the variational infimum for `0 < α < 1`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem quasiVarOpt_eq_quasi_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) (hρ_unit : IsUnit ρ) :
    quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  have hσ_nn : (0 : L ℋ) ≤ σ :=
    (LinearMap.nonneg_iff_isPositive σ).2 hσ
  have hP_sa : IsSelfAdjoint P :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hX_pos : X.IsPositive := by
    rw [hX_def]
    exact QuantumChannel.isPositive_conj hP_sa hρ
  have hX_nn : (0 : L ℋ) ≤ X :=
    (LinearMap.nonneg_iff_isPositive X).2 hX_pos
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  have hopt : quasiVarOpt α ρ σ = H_opt := by
    simpa [hH_opt_def, hX_def, hP_def, hβ'_def] using
      quasiVarOpt_eq_direct α ρ σ
  rw [hopt]
  have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
  have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit hσ_nn
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit hσ_nn
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    simp only [hH_opt_def, mul_assoc, hPQ, mul_one]
    rw [← mul_assoc, hQP, one_mul]
  have hα_sub_neg : (α - 1 : ℝ) < 0 := by linarith
  have hα_sub_ne : (α - 1 : ℝ) ≠ 0 := ne_of_lt hα_sub_neg
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) =
      CFC.rpow X α := by
    calc
      _ = CFC.rpow X ((α - 1) * (α / (α - 1))) :=
        CFC.rpow_rpow X (α - 1) (α / (α - 1)) hX_unit hα_sub_ne hX_nn
      _ = _ := by congr 1; field_simp
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    calc
      X * CFC.rpow X (α - 1) = CFC.rpow X 1 * CFC.rpow X (α - 1) := by
        exact congrArg (fun Y => Y * CFC.rpow X (α - 1))
          (CFC.rpow_one X hX_nn).symm
      _ = CFC.rpow X (1 + (α - 1)) :=
        (CFC.rpow_add hX_unit).symm
      _ = CFC.rpow X α := by
        congr 1
        ring
  have hTr_Hρ : Tr (H_opt * ρ) =
      Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    simpa only [hX_def, mul_assoc] using
      LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) (P * CFC.rpow X (α - 1)) (P * ρ)
  have hα_ne : α ≠ 0 := ne_of_gt hα0
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by
    rw [hβ'_def]
    field_simp [hα_ne]
    ring
  have h_penalty : CFC.rpow
      (CFC.rpow σ ((α - 1) / (2 * α)) * H_opt *
        CFC.rpow σ ((α - 1) / (2 * α))) (α / (α - 1)) =
      CFC.rpow X α := by
    rw [hexp, ← hQ_def, hY_opt, hYq_eq]
  have h_sand_power : CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α = CFC.rpow X α := by
    rw [hX_def, hP_def, hβ'_def]
  rw [quasiVar_eq_direct, sandwichedQuasi_eq_direct]
  rw [h_penalty, h_sand_power, hTr_Hρ, hXX_eq]
  set T := Tr (CFC.rpow X α)
  push_cast
  ring_nf

/-- Attainment for `0 < α < 1`, as the direct corollary of the explicit optimizer. -/
theorem exists_quasiVar_eq_quasi_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ σ : L ℋ} (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) (hρ_unit : IsUnit ρ) :
    ∃ H : L ℋ, H.IsPositive ∧ quasiVar α ρ σ H = sandwichedQuasi α ρ σ :=
  ⟨quasiVarOpt α ρ σ, quasiVarOpt_isPositive,
    quasiVarOpt_eq_quasi_lt hα0 hα1 hρ hσ hσ_unit hρ_unit⟩

end VariationalRepresentation

end SandwichedRenyiRelativeEntropy

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

/-- For `0 < α ≤ 1`, the real part of `sandwichedQuasi` is jointly continuous on the
    non-negative cone. Both exponents `β = (1-α)/(2α)` and `α` are non-negative, so every
    `CFC.rpow` in the definition is continuous up to the boundary of the cone.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
lemma sandwichedQuasi_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
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
    (rpow_continuousOn_nonneg hβ_nn).comp continuous_snd.continuousOn
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

end SandwichedRenyiRelativeEntropy
