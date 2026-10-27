/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.YoungInequalityLinear
import Quantum.TraceInequality.LiebAndo.PositiveDefiniteGeometry
import Quantum.QuantumEntropy.TensorCFCCore
import Quantum.QuantumMechanics.OperatorBridge

/-!
# Sandwiched Rényi relative entropy: definitions and Frank-Lieb variational representation
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Definition

open LiebAndoTrace GeneralizedPerspectiveFunction

universe uDef

variable {ℋ : Type uDef} [Qudit ℋ]

/-! ### Sandwiched quasi-entropy, divergence, and positive-definite operators -/
/-- Sandwiched quasi-relative entropy:
    `Q_α(ρ‖σ) = Tr((σ^{(1-α)/(2α)} ρ σ^{(1-α)/(2α)})^α)`. -/
noncomputable def sandwichedQuasi (α : ℝ) (ρ σ : L ℋ) : ℂ :=
  Tr (CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
    CFC.rpow σ ((1 - α) / (2 * α))) α)

lemma sandwichedQuasi_eq_direct (α : ℝ) (ρ σ : L ℋ) :
    sandwichedQuasi α ρ σ =
      Tr (CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α) := by
  rfl

/-- The variational functional:
    `F(H) = α Tr(Hρ) - (α-1) Tr((σ^{(α-1)/(2α)} H σ^{(α-1)/(2α)})^{α/(α-1)})`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def quasiVar (α : ℝ) (ρ σ H : L ℋ) : ℂ :=
  (α : ℂ) * Tr (H * ρ) - ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
    (CFC.rpow σ ((α - 1) / (2 * α)) * H *
      CFC.rpow σ ((α - 1) / (2 * α))) (α / (α - 1)))

lemma quasiVar_eq_direct (α : ℝ) (ρ σ H : L ℋ) :
    quasiVar α ρ σ H =
      (α : ℂ) * Tr (H * ρ) - ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1))) := by
  rfl

/-- The variational optimizer
`H_opt = P (P ρ P)^{α-1} P`, where `P = σ^{(1-α)/(2α)}`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def quasiVarOpt (α : ℝ) (ρ σ : L ℋ) : L ℋ :=
  CFC.rpow σ ((1 - α) / (2 * α)) *
    CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
      CFC.rpow σ ((1 - α) / (2 * α))) (α - 1) *
    CFC.rpow σ ((1 - α) / (2 * α))

lemma quasiVarOpt_eq_direct (α : ℝ) (ρ σ : L ℋ) :
    quasiVarOpt α ρ σ =
      CFC.rpow σ ((1 - α) / (2 * α)) *
        CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
          CFC.rpow σ ((1 - α) / (2 * α))) (α - 1) *
        CFC.rpow σ ((1 - α) / (2 * α)) := by
  rfl

/-- Sandwiched Rényi relative entropy for `α ∈ (0,1) ∪ (1,∞)`:
    `D_α(ρ‖σ) = (1/(α-1)) · log(Q_α(ρ‖σ) / Tr ρ)`. -/
noncomputable def sandwichedRenyiDiv (α : ℝ) (ρ σ : L ℋ) : ℝ :=
  (1 / (α - 1)) * Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)

variable [Nontrivial ℋ]

/-- Trace of the conjugated power `A ↦ Re Tr((B† · A^p · B)^{1/p})`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def traceConjPow (p : ℝ) (B A : L ℋ) : ℝ :=
  (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re

omit [Nontrivial ℋ] in
lemma traceConjPow_eq_direct (p : ℝ) (B A : L ℋ) :
    traceConjPow (ℋ := ℋ) p B A =
      (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re := by
  rfl

end Definition

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Frank-Lieb variational representation via Young inequalities -/
@[deprecated (since := "2026-09-05")]
alias isPositive_conj := QuantumChannel.isPositive_conj

/-- Cyclic trace with unit cancellation:
    Tr((P ρ P)(Q H Q)) = Tr(H ρ) when P Q = 1 and Q P = 1. -/
@[deprecated LinearMap.trace_mul_comm (since := "2026-09-05")]
lemma trace_mul_comm (f g : L ℋ) : Tr (f * g) = Tr (g * f) :=
  LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) f g

private lemma trace_conj_cancel {P Q ρ H : L ℋ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Tr ((P * ρ * P) * (Q * H * Q)) = Tr (H * ρ) := by
  have h1 : (P * ρ * P) * (Q * H * Q) = P * (ρ * H) * Q := by
    have : P * (ρ * (P * (Q * (H * Q)))) = P * (ρ * (H * Q)) := by
      congr 2; rw [show P * (Q * (H * Q)) = (P * Q) * (H * Q) from by
        simp only [mul_assoc]]; rw [hPQ, one_mul]
    simp only [mul_assoc] at this ⊢; exact this
  rw [h1]
  rw [show P * (ρ * H) * Q = P * (ρ * H) * Q from rfl]
  rw [LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) (P * (ρ * H)) Q, ← mul_assoc Q P, hQP, one_mul]
  exact (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) H ρ).symm

/-- rpow self-adjointness for positive operators. -/
@[deprecated IsSelfAdjoint.of_nonneg (since := "2026-09-05")]
lemma isSelfAdjoint_rpow {σ : B ℋ} (_hσ : σ.IsPositive) (s : ℝ) :
    IsSelfAdjoint (CFC.rpow σ s) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

/-- Algebraic rearrangement: from Young's form to variational form.
    If a ≤ b/p + c/q with p, q Hölder conjugates, then p·a - (p-1)·c ≤ b. -/
private lemma young_to_variational {a b c : ℂ} {p q : ℝ}
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (h : a ≤ b / ↑p + c / ↑q) :
    ↑p * a - ↑(p - 1) * c ≤ b := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_nn : (0 : ℂ) ≤ ↑p := by exact_mod_cast le_of_lt hp_pos
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp_pos
  have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpq.right_pos
  rw [sub_le_iff_le_add]
  calc ↑p * a
      ≤ ↑p * (b / ↑p + c / ↑q) := mul_le_mul_of_nonneg_left h hp_nn
    _ = b + ↑p * c / ↑q := by rw [mul_add, mul_div_assoc]; congr 1; field_simp
    _ = b + ↑(p - 1) * c := by
        congr 1; rw [show (p - 1 : ℝ) = p - 1 from rfl]
        rw [show q = p / (p - 1) from hpq.conjugate_eq]; push_cast; field_simp

/-- Upper bound on the variational functional for `α > 1`:
    for all positive `H`, `quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ`.
    Proof by the Young-inequality argument.

Source: arXiv:1306.5358v3, Lemma 4, variational upper bound, p.4 (proof). -/
theorem quasiVar_le_quasi {α : ℝ} (hα : 1 < α) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) :
    quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ :=
    (LinearMap.nonneg_iff_isPositive σ).2 hσ
  have hX_pos : X.IsPositive := by
    rw [hX_def]
    exact QuantumChannel.isPositive_conj (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg) hρ
  have hY_pos : Y.IsPositive := by
    rw [hY_def]
    exact QuantumChannel.isPositive_conj (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg) hH
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit hσ_nn
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit hσ_nn
  set q := α / (α - 1) with hq_def
  have hpq : α.HolderConjugate q :=
    Real.HolderConjugate.conjExponent hα
  have hYoung := trace_young_inequality hpq X Y hX_pos hY_pos
  have h_xy : Tr (X * Y) = Tr (H * ρ) :=
    trace_conj_cancel hPQ hQP
  have h_Xα : Tr (CFC.rpow X α) = sandwichedQuasi α ρ σ := by
    simpa [hX_def, hP_def, hβ'_def] using
      (sandwichedQuasi_eq_direct α ρ σ).symm
  have h_Yq : Tr (CFC.rpow Y q) =
      Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ ((α - 1) / (2 * α))) q) := by
    rw [hY_def, hQ_def, show -β' = (α - 1) / (2 * α) by rw [hβ'_def]; ring]
  rw [quasiVar_eq_direct, ← h_Xα, ← h_Yq, ← h_xy]
  exact young_to_variational hα hpq hYoung

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

/-- The explicit optimizer realizes the variational supremum for `α > 1`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem quasiVarOpt_eq_quasi_gt {α : ℝ} (hα : 1 < α) {ρ σ : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) :
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
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit hσ_nn
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit hσ_nn
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    simp only [hH_opt_def, mul_assoc, hPQ, mul_one]
    rw [← mul_assoc, hQP, one_mul]
  have hα_sub_pos : (0 : ℝ) < α - 1 := by linarith
  have hα_pos : (0 : ℝ) < α := by linarith
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) =
      CFC.rpow X α := by
    calc
      _ = CFC.rpow X ((α - 1) * (α / (α - 1))) :=
        CFC.rpow_rpow_of_exponent_nonneg X (α - 1) (α / (α - 1))
          hα_sub_pos.le (div_pos hα_pos hα_sub_pos).le hX_nn
      _ = _ := by congr 1; field_simp
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    set s : NNReal := ⟨α - 1, by linarith⟩
    set r : NNReal := ⟨α, by linarith⟩
    have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
    have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
    have h1s : (1 : NNReal) + s = r := by
      ext
      change (1 : ℝ) + (α - 1) = α
      ring
    calc
      X * CFC.rpow X (α - 1) = CFC.rpow X 1 * CFC.rpow X (α - 1) := by
        exact congrArg (fun Y => Y * CFC.rpow X (α - 1))
          (CFC.rpow_one X hX_nn).symm
      _ = (X ^ (1 : NNReal)) * (X ^ s) := by
        exact congrArg₂ (· * ·)
          (CFC.nnrpow_eq_rpow (a := X) (x := (1 : NNReal)) (by positivity)).symm
          (CFC.nnrpow_eq_rpow (a := X) hs0).symm
      _ = X ^ ((1 : NNReal) + s) := (CFC.nnrpow_add (by positivity) hs0).symm
      _ = X ^ r := by rw [h1s]
      _ = CFC.rpow X (r : ℝ) := CFC.nnrpow_eq_rpow hr0
      _ = CFC.rpow X α := by rfl
  have hTr_Hρ : Tr (H_opt * ρ) =
      Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    simpa only [hX_def, mul_assoc] using
      LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) (P * CFC.rpow X (α - 1)) (P * ρ)
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by
    rw [hβ'_def]
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

Source: arXiv:1306.5358v3, Lemma 4, variational lower bound, p.4 (proof). -/
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
  have hRevYoung := trace_reverse_young_inequality hr_neg hα0 hα1 hrs
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

