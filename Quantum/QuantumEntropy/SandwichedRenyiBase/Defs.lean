/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.YoungInequality
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Quantum.QuantumEntropy.Common.OperatorScalarTower

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

lemma rpow_toLinearMap (A : L ℋ) (p : ℝ) :
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

/-- Proof-support equation for evaluating `sandwichedQuasi`
at CLM arguments through the canonical coercion. -/
lemma sandwichedQuasi_eq_clm_direct
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

/-- The variational functional (equivalent QHQ form):
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

/-- Proof-support equation for evaluating `quasiVar`
at CLM arguments through the canonical coercion. -/
lemma quasiVar_eq_clm_direct
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

/-- Lieb trace functional on linear maps, via the continuous-linear model in `LiebAndoTrace`. -/
noncomputable def liebTraceMapLM (s : ℝ) (K A B : L ℋ) : ℝ :=
  liebTraceMap (ℋ := ℋ) s K.toContinuousLinearMap
    A.toContinuousLinearMap B.toContinuousLinearMap

omit [Nontrivial ℋ] in
lemma liebTraceMapLM_eq_direct (s : ℝ) (K A B : L ℋ) :
    liebTraceMapLM (ℋ := ℋ) s K A B =
      liebTraceMap (ℋ := ℋ) s K.toContinuousLinearMap
        A.toContinuousLinearMap B.toContinuousLinearMap := by
  rfl

/-- Trace of the conjugated power `A ↦ Re Tr((B† · A^p · B)^{1/p})`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def traceConjPow (p : ℝ) (B A : L ℋ) : ℝ :=
  (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re

omit [Nontrivial ℋ] in
lemma traceConjPow_eq_direct (p : ℝ) (B A : L ℋ) :
    traceConjPow (ℋ := ℋ) p B A =
      (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re := by
  rfl

/-- Variational (Legendre-type) functional associated to `traceConjPow`:
    `F(A, X) = liebTraceMapLM(p, B†, A, X) − (1−p) · Re Tr X`.
    For positive-definite `A` and invertible `B`, optimizing over positive-definite `X`:
    for `p < 0`, `p · traceConjPow = inf_X F`; for `0 < p ≤ 1`, `p · traceConjPow = sup_X F`. -/
noncomputable def traceConjPowVar (p : ℝ) (B A X : L ℋ) : ℝ :=
  liebTraceMapLM (ℋ := ℋ) p (star B) A X - (1 - p) * (Tr X).re

end Definition

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Frank-Lieb variational representation via Young inequalities -/

lemma trace_conj_cancel {P Q ρ H : L ℋ}
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

private lemma trace_young_inequality_direct {p q : ℝ}
    (hpq : p.HolderConjugate q) (X Y : L ℋ)
    (hX : X.IsPositive) (hY : Y.IsPositive) :
    Tr (X * Y) ≤ Tr (CFC.rpow X p) / p + Tr (CFC.rpow Y q) / q := by
  have h := trace_young_inequality hpq
    X.toContinuousLinearMap Y.toContinuousLinearMap
    ((LinearMap.isPositive_toContinuousLinearMap_iff X).2 hX)
    ((LinearMap.isPositive_toContinuousLinearMap_iff Y).2 hY)
  simpa only [rpow_toLinearMap] using h

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

Source: arXiv:1306.5358v3, Lemma 4 (part 1: the variational upper bound), p.4 (proof). -/
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
  have hYoung := trace_young_inequality_direct hpq X Y hX_pos hY_pos
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

end VariationalRepresentation

end SandwichedRenyiRelativeEntropy

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

/-- For `0 ≤ p`, the map `A ↦ CFC.rpow A p` is continuous on the cone of non-negative
    operators. (A positive power `x ↦ x^p` is continuous up to `0` in `ℝ≥0`, so unlike the
    positive-definite version no spectral gap away from `0` is required.) -/
lemma rpow_continuousOn_nonneg
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : B 𝒦 => CFC.rpow A p)
      {A : B 𝒦 | (0 : B 𝒦) ≤ A} :=
  (continuousOn_id (s := {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
    |>.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p)) Filter.univ_mem
      (ha' := fun _ hA => hA) (hf := (NNReal.continuous_rpow_const hp).continuousOn)

end SandwichedRenyiRelativeEntropy
