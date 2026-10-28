/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.TracePositiveDefinite
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.AndoConvexity.Concavity
import Quantum.TraceInequality.LiebAndo.Concavity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.YoungInequality
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

/-!
# Sandwiched Rényi relative entropy: conjugated powers
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy


section LiebAndoLinearMap

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u'

variable {ℋ : Type u'} [Qudit ℋ]
variable [Nontrivial ℋ]

end LiebAndoLinearMap

section TraceConjPowConcavity

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u''

variable {ℋ : Type u''} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
private lemma star_toCLM (f : L ℋ) :
    (star f).toContinuousLinearMap = star f.toContinuousLinearMap := by
  change f.adjoint.toContinuousLinearMap = star f.toContinuousLinearMap
  rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

omit [Nontrivial ℋ] in
private lemma toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

omit [Nontrivial ℋ] in
lemma pdSetLM_conj {A B : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hB : IsUnit B) :
    star B * A * B ∈ pdSetLM (ℋ := ℋ) := by
  apply (pdSetLM_strictPositivity_certificate _).2
  exact hB.isStrictlyPositive_star_left_conjugate_iff.mpr
    ((pdSetLM_strictPositivity_certificate A).1 hA)

omit [Nontrivial ℋ] in
private lemma traceRe_via_toCLM (T : L ℋ) :
    traceRe (ℋ := ℋ) T.toContinuousLinearMap = (Tr T).re := by
  rfl

omit [Nontrivial ℋ] in
private lemma rpow_toCLM_direct (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap =
      CFC.rpow A.toContinuousLinearMap p := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  letI : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower ℝ≥0 ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eNN : L ℋ ≃ₐ[ℝ≥0] B ℋ := e.toAlgEquiv.restrictScalars ℝ≥0
  change e (cfc (fun x : ℝ≥0 => x ^ p) A) =
    cfc (fun x : ℝ≥0 => x ^ p) (e A)
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

omit [Nontrivial ℋ] in
private lemma traceConjPow_eq_clm_direct (p : ℝ) (B A : L ℋ) :
    traceConjPow (ℋ := ℋ) p B A =
      traceRe (ℋ := ℋ) (CFC.rpow
        (star B.toContinuousLinearMap *
          CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap)
        (1 / p)) := by
  rw [traceConjPow_eq_direct, ← traceRe_via_toCLM]
  rw [rpow_toCLM_direct]
  change traceRe (ℋ := ℋ) (CFC.rpow
      ((star B).toContinuousLinearMap *
        (CFC.rpow A p).toContinuousLinearMap * B.toContinuousLinearMap)
      (1 / p)) = _
  rw [star_toCLM, rpow_toCLM_direct]

omit [Nontrivial ℋ] in
private lemma traceRe_mul_comm_direct
    (S T : QuantumState.B ℋ) :
    traceRe (ℋ := ℋ) (S * T) = traceRe (ℋ := ℋ) (T * S) := by
  exact congrArg Complex.re
    (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) S.toLinearMap T.toLinearMap)

omit [Nontrivial ℋ] in
private lemma trace_young_inequality_via_bridge {p q : ℝ} (hpq : p.HolderConjugate q)
    (S T : QuantumState.B ℋ) (hS : S.IsPositive) (hT : T.IsPositive) :
    traceRe (ℋ := ℋ) (S * T) ≤
      traceRe (ℋ := ℋ) (CFC.rpow S p) / p +
        traceRe (ℋ := ℋ) (CFC.rpow T q) / q := by
  have hYoung := _root_.trace_young_inequality hpq S T hS hT
  have hYoung_re := (RCLike.le_iff_re_im.mp hYoung).1
  change traceRe (ℋ := ℋ) (S * T) ≤
    (Tr (CFC.rpow S p).toLinearMap / ↑p +
      Tr (CFC.rpow T q).toLinearMap / ↑q).re at hYoung_re
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re,
    show (Tr (CFC.rpow S p).toLinearMap).re = traceRe (ℋ := ℋ) (CFC.rpow S p) from rfl,
    show (Tr (CFC.rpow T q).toLinearMap).re = traceRe (ℋ := ℋ) (CFC.rpow T q) from rfl]
    at hYoung_re
  exact hYoung_re

omit [Nontrivial ℋ] in
private lemma trace_reverse_young_inequality_via_bridge {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (M N : QuantumState.B ℋ) (hM : M.IsPositive)
    (hM_unit : IsUnit M) (hN : N.IsPositive) :
    traceRe (ℋ := ℋ) (CFC.rpow M r) / r +
        traceRe (ℋ := ℋ) (CFC.rpow N s) / s ≤ traceRe (ℋ := ℋ) (M * N) := by
  have hRev := _root_.trace_reverse_young_inequality hr hs0 hs1 hrs M N
    hM hM_unit hN
  have hRev_re := (RCLike.le_iff_re_im.mp hRev).1
  change (Tr (CFC.rpow M r).toLinearMap / ↑r +
    Tr (CFC.rpow N s).toLinearMap / ↑s).re ≤ traceRe (ℋ := ℋ) (M * N) at hRev_re
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re,
    show (Tr (CFC.rpow M r).toLinearMap).re = traceRe (ℋ := ℋ) (CFC.rpow M r) from rfl,
    show (Tr (CFC.rpow N s).toLinearMap).re = traceRe (ℋ := ℋ) (CFC.rpow N s) from rfl]
    at hRev_re
  exact hRev_re

omit [Nontrivial ℋ] in
private lemma liebTraceMapLM_as_bridge_trace (p : ℝ) (B A X : L ℋ) :
    liebTraceMapLM (ℋ := ℋ) p (star B) A X =
      traceRe (ℋ := ℋ) (star B.toContinuousLinearMap *
          CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap *
          CFC.rpow X.toContinuousLinearMap (1 - p)) := by
  rw [liebTraceMapLM_eq_direct]
  unfold liebTraceMap
  change traceRe (ℋ := ℋ) (A.toContinuousLinearMap ^ p *
      star (star B).toContinuousLinearMap * X.toContinuousLinearMap ^ (1 - p) *
      (star B).toContinuousLinearMap) = _
  rw [star_toCLM, star_star, ← CFC.rpow_eq_pow, ← CFC.rpow_eq_pow]
  simpa only [mul_assoc] using traceRe_mul_comm_direct (ℋ := ℋ)
    (CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap *
      CFC.rpow X.toContinuousLinearMap (1 - p)) (star B.toContinuousLinearMap)

/-! ### Variational formulas for conjugated powers -/
omit [Nontrivial ℋ] in
/-- `(Y ^ (1 - p)) ^ (1 / (1 - p)) = Y` for a nonnegative operator and `p < 1`. -/
private lemma rpow_rpow_one_sub_inv {p : ℝ} (Y : QuantumState.B ℋ) (hY : 0 ≤ Y)
    (h1p : 0 < 1 - p) : CFC.rpow (CFC.rpow Y (1 - p)) (1 / (1 - p)) = Y := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
    CFC.rpow_rpow_of_exponent_nonneg Y (1 - p) (1 / (1 - p)) h1p.le (by positivity),
    show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
  exact CFC.rpow_one (A := QuantumState.B ℋ) Y hY

omit [Nontrivial ℋ] in
/-- Reverse trace Young inequality in the form used by the variational formula (`p < 0`). -/
private lemma rev_young_conj_neg {p : ℝ} (hp0 : p < 0) (M Y : QuantumState.B ℋ)
    (hM : M.IsPositive) (hM_unit : IsUnit M) (hY : 0 ≤ Y) :
    p * traceRe (ℋ := ℋ) (CFC.rpow M (1 / p)) ≤
      traceRe (ℋ := ℋ) (M * CFC.rpow Y (1 - p)) - (1 - p) * traceRe (ℋ := ℋ) Y := by
  have h1p : 0 < 1 - p := by linarith
  have hRev := trace_reverse_young_inequality_via_bridge (r := 1 / p) (s := 1 / (1 - p))
    (div_neg_of_pos_of_neg one_pos hp0) (by positivity)
    (by rw [div_lt_one h1p]; linarith) (by rw [one_div_one_div, one_div_one_div]; ring) M
    (CFC.rpow Y (1 - p))
    hM hM_unit ((ContinuousLinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg)
  rw [rpow_rpow_one_sub_inv Y hY h1p, div_div_eq_mul_div, div_div_eq_mul_div, div_one,
    div_one] at hRev
  linarith

omit [Nontrivial ℋ] in
/-- Trace Young inequality in the form used by the variational formula (`0 < p < 1`). -/
private lemma young_conj_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (M Y : QuantumState.B ℋ)
    (hM : M.IsPositive) (hY : 0 ≤ Y) :
    traceRe (ℋ := ℋ) (M * CFC.rpow Y (1 - p)) - (1 - p) * traceRe (ℋ := ℋ) Y ≤
      p * traceRe (ℋ := ℋ) (CFC.rpow M (1 / p)) := by
  have h1p : 0 < 1 - p := by linarith
  have hYoung := trace_young_inequality_via_bridge
    (Real.holderConjugate_one_div hp0 h1p (by ring)) M (CFC.rpow Y (1 - p)) hM
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg)
  rw [rpow_rpow_one_sub_inv Y hY h1p, div_div_eq_mul_div, div_div_eq_mul_div, div_one,
    div_one] at hYoung
  linarith

omit [Nontrivial ℋ] in
/-- Variational inequality (p < 0):
    ∀ X ∈ pdSetLM, p · traceConjPow(p,B,A) ≤ F(A,X).
    Follows from the reverse trace Young inequality with M = B†A^pB. -/
private lemma traceConjPowVar_le_neg {p : ℝ} (hp0 : p < 0)
    {B A X : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ
      := ℋ)) :
    p * traceConjPow (ℋ := ℋ) p B A ≤ traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_pd := (pdSet_membership_certificate A.toContinuousLinearMap).1 hA
  have hB_unit : IsUnit B.toContinuousLinearMap := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]; exact hB
  have hM_nn : (0 : QuantumState.B ℋ) ≤
      star B.toContinuousLinearMap * CFC.rpow A.toContinuousLinearMap p *
        B.toContinuousLinearMap :=
    star_left_conjugate_nonneg CFC.rpow_nonneg _
  have h := rev_young_conj_neg hp0 _ X.toContinuousLinearMap
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hM_nn)
    ((hB_unit.star.mul (hA_pd.isUnit.cfcRpow p hA_pd.nonneg)).mul hB_unit)
    ((pdSet_membership_certificate X.toContinuousLinearMap).1 hX).nonneg
  rw [traceConjPowVar, traceConjPow_eq_clm_direct, liebTraceMapLM_as_bridge_trace,
    ← traceRe_via_toCLM X]
  exact h

omit [Nontrivial ℋ] in
/-- Variational attainment (p < 0):
    ∃ X_opt ∈ pdSetLM achieving equality; the optimizer is X_opt = (B†A^pB)^{1/p}. -/
private lemma exists_traceConjPowVar_eq_neg {p : ℝ} (hp0 : p < 0)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn : (0 : QuantumState.B ℋ) ≤ A.toContinuousLinearMap :=
    ((pdSet_membership_certificate A.toContinuousLinearMap).1 hA).nonneg
  have hB_unit : IsUnit B.toContinuousLinearMap := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
    exact hB
  set Ap := CFC.rpow A.toContinuousLinearMap p with hAp_def
  set M := star B.toContinuousLinearMap * Ap * B.toContinuousLinearMap with hM_def
  have hAp_unit : IsUnit Ap := by
    rw [hAp_def]
    exact ((pdSet_membership_certificate A.toContinuousLinearMap).1 hA).isUnit.cfcRpow p hA_nn
  have hM_unit : IsUnit M := by
    rw [hM_def]
    exact (hB_unit.star.mul hAp_unit).mul hB_unit
  have hM_nn : (0 : QuantumState.B ℋ) ≤ M := by
    rw [hM_def, hAp_def]
    exact star_left_conjugate_nonneg CFC.rpow_nonneg _
  set Xc := CFC.rpow M (1 / p) with hXc_def
  set X_opt := Xc.toLinearMap with hX_opt_def
  have hXc_pd : Xc ∈ pdSet (ℋ := ℋ) := by
    apply (pdSet_membership_certificate _).2
    exact ⟨CFC.rpow_nonneg, hM_unit.cfcRpow (1 / p) hM_nn⟩
  have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := by
    change X_opt.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only [hX_opt_def] using hXc_pd
  refine ⟨X_opt, hX_opt_pd, ?_⟩
  have hpne : p ≠ 0 := ne_of_lt hp0
  have hX_opt_clm : X_opt.toContinuousLinearMap = Xc := by
    rw [hX_opt_def, toCLM_toLinearMap]
  have hrpow_comp : CFC.rpow Xc (1 - p) = CFC.rpow M ((1 - p) / p) := by
    rw [hXc_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow M (1 / p) (1 - p) hM_unit (one_div_ne_zero hpne)]
    congr 1; ring
  have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = Xc := by
    have h1 : CFC.rpow M 1 = M :=
      CFC.rpow_one (A := QuantumState.B ℋ) M hM_nn
    have hexp : (1 : ℝ) + (1 - p) / p = 1 / p := by field_simp [hpne]; ring
    have hadd : CFC.rpow M 1 * CFC.rpow M ((1 - p) / p) =
        CFC.rpow M (1 + (1 - p) / p) := by
      simp only [CFC.rpow_eq_pow]
      exact (CFC.rpow_add hM_unit).symm
    conv_lhs => lhs; rw [← h1]
    rw [hadd, hexp, ← hXc_def]
  have hfun : traceConjPow (ℋ := ℋ) p B A = traceRe (ℋ := ℋ) Xc := by
    rw [traceConjPow_eq_clm_direct, ← hAp_def, ← hM_def, ← hXc_def]
  have hvar : traceConjPowVar (ℋ := ℋ) p B A X_opt = p * traceRe (ℋ := ℋ) Xc := by
    rw [traceConjPowVar, liebTraceMapLM_as_bridge_trace,
      ← traceRe_via_toCLM X_opt, hX_opt_clm]
    change traceRe (ℋ := ℋ) (M * CFC.rpow Xc (1 - p)) -
      (1 - p) * traceRe (ℋ := ℋ) Xc = _
    rw [hrpow_comp, hrpow_mul]
    ring
  rw [hfun, hvar]

omit [Nontrivial ℋ] in
/-- Variational inequality (0 < p ≤ 1):
    ∀ X ∈ pdSetLM, F(A,X) ≤ p · traceConjPow(p,B,A).
    Follows from the trace Young inequality. -/
private lemma traceConjPowVar_le_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A X : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    traceConjPowVar (ℋ := ℋ) p B A X ≤ p * traceConjPow (ℋ := ℋ) p B A := by
  -- `A ∈ pdSetLM` is part of the statement; the inequality itself only needs `0 ≤ A ^ p`.
  have _hA_nn : (0 : QuantumState.B ℋ) ≤ A.toContinuousLinearMap :=
    ((pdSet_membership_certificate A.toContinuousLinearMap).1 hA).nonneg
  have hX_nn : (0 : QuantumState.B ℋ) ≤ X.toContinuousLinearMap :=
    ((pdSet_membership_certificate X.toContinuousLinearMap).1 hX).nonneg
  have hM_nn : (0 : QuantumState.B ℋ) ≤
      star B.toContinuousLinearMap * CFC.rpow A.toContinuousLinearMap p *
        B.toContinuousLinearMap :=
    star_left_conjugate_nonneg CFC.rpow_nonneg _
  rw [traceConjPowVar, traceConjPow_eq_clm_direct, liebTraceMapLM_as_bridge_trace,
    ← traceRe_via_toCLM X]
  rcases lt_or_eq_of_le hp1 with hp1' | rfl
  · exact young_conj_pos hp0 hp1' _ X.toContinuousLinearMap
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hM_nn) hX_nn
  · have hN1 : CFC.rpow X.toContinuousLinearMap (1 - 1) = 1 := by
      rw [sub_self]
      exact CFC.rpow_zero (A := QuantumState.B ℋ) X.toContinuousLinearMap hX_nn
    have hM1 : CFC.rpow (star B.toContinuousLinearMap * CFC.rpow A.toContinuousLinearMap 1 *
        B.toContinuousLinearMap) 1 = star B.toContinuousLinearMap *
          CFC.rpow A.toContinuousLinearMap 1 * B.toContinuousLinearMap :=
      CFC.rpow_one (A := QuantumState.B ℋ) _ hM_nn
    rw [hN1, mul_one, sub_self, zero_mul, sub_zero, div_one, hM1, one_mul]

omit [Nontrivial ℋ] in
/-- Variational attainment (0 < p ≤ 1):
    ∃ X_opt ∈ pdSetLM achieving equality. -/
private lemma exists_traceConjPowVar_eq_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn : (0 : QuantumState.B ℋ) ≤ A.toContinuousLinearMap :=
    ((pdSet_membership_certificate A.toContinuousLinearMap).1 hA).nonneg
  have hB_unit : IsUnit B.toContinuousLinearMap := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
    exact hB
  set Ap := CFC.rpow A.toContinuousLinearMap p with hAp_def
  set M := star B.toContinuousLinearMap * Ap * B.toContinuousLinearMap with hM_def
  have hAp_unit : IsUnit Ap := by
    rw [hAp_def]
    exact ((pdSet_membership_certificate A.toContinuousLinearMap).1 hA).isUnit.cfcRpow p hA_nn
  have hM_unit : IsUnit M := by
    rw [hM_def]
    exact (hB_unit.star.mul hAp_unit).mul hB_unit
  have hM_nn : (0 : QuantumState.B ℋ) ≤ M := by
    rw [hM_def, hAp_def]
    exact star_left_conjugate_nonneg CFC.rpow_nonneg _
  set Xc := CFC.rpow M (1 / p) with hXc_def
  set X_opt := Xc.toLinearMap with hX_opt_def
  have hXc_pd : Xc ∈ pdSet (ℋ := ℋ) := by
    apply (pdSet_membership_certificate _).2
    exact ⟨CFC.rpow_nonneg, hM_unit.cfcRpow (1 / p) hM_nn⟩
  have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := by
    change X_opt.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only [hX_opt_def] using hXc_pd
  refine ⟨X_opt, hX_opt_pd, ?_⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hX_opt_clm : X_opt.toContinuousLinearMap = Xc := by
    rw [hX_opt_def, toCLM_toLinearMap]
  have hrpow_comp : CFC.rpow Xc (1 - p) = CFC.rpow M ((1 - p) / p) := by
    rw [hXc_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg M (1 / p) (1 - p)
      (one_div_nonneg.mpr hp0.le) (sub_nonneg.mpr hp1)]
    congr 1; ring
  have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = Xc := by
    have h1 : CFC.rpow M 1 = M :=
      CFC.rpow_one (A := QuantumState.B ℋ) M hM_nn
    have hexp : (1 : ℝ) + (1 - p) / p = 1 / p := by field_simp [hpne]; ring
    have hadd : CFC.rpow M 1 * CFC.rpow M ((1 - p) / p) =
        CFC.rpow M (1 + (1 - p) / p) := by
      simp only [CFC.rpow_eq_pow]
      exact (CFC.rpow_add hM_unit).symm
    conv_lhs => lhs; rw [← h1]
    rw [hadd, hexp, ← hXc_def]
  have hfun : traceConjPow (ℋ := ℋ) p B A = traceRe (ℋ := ℋ) Xc := by
    rw [traceConjPow_eq_clm_direct, ← hAp_def, ← hM_def, ← hXc_def]
  have hvar : traceConjPowVar (ℋ := ℋ) p B A X_opt = p * traceRe (ℋ := ℋ) Xc := by
    rw [traceConjPowVar, liebTraceMapLM_as_bridge_trace,
      ← traceRe_via_toCLM X_opt, hX_opt_clm]
    change traceRe (ℋ := ℋ) (M * CFC.rpow Xc (1 - p)) -
      (1 - p) * traceRe (ℋ := ℋ) Xc = _
    rw [hrpow_comp, hrpow_mul]
    ring
  rw [hfun, hvar]

omit [Nontrivial ℋ] in
/-- Cyclic trace: Tr(A^s K† B^{1-s} K) = Tr(B^{1-s} K A^s K†).
    Equivalently: liebTraceMapLM(s,K,A,B) = liebTraceMapLM(1−s,star K,B,A). -/
private lemma traceRe_mul_comm (X Y : QuantumState.B ℋ) :
    traceRe (ℋ := ℋ) (X * Y) = traceRe (ℋ := ℋ) (Y * X) := by
  exact traceRe_mul_comm_direct X Y

omit [Nontrivial ℋ] in
private lemma liebTraceMapLM_cyclic (s : ℝ) (K A B : L ℋ) :
    liebTraceMapLM (ℋ := ℋ) s K A B =
      liebTraceMapLM (ℋ := ℋ) (1 - s) (star K) B A := by
  rw [liebTraceMapLM_eq_direct, liebTraceMapLM_eq_direct]
  unfold liebTraceMap
  change traceRe (ℋ := ℋ) (A.toContinuousLinearMap ^ s *
      star K.toContinuousLinearMap * B.toContinuousLinearMap ^ (1 - s) *
      K.toContinuousLinearMap) =
    traceRe (ℋ := ℋ) (B.toContinuousLinearMap ^ (1 - s) *
      star (star K).toContinuousLinearMap *
      A.toContinuousLinearMap ^ (1 - (1 - s)) * (star K).toContinuousLinearMap)
  rw [star_toCLM, star_star, show (1 : ℝ) - (1 - s) = s from by ring]
  have h := traceRe_mul_comm (ℋ := ℋ)
    (A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap)
    (B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap)
  simp only [mul_assoc] at h ⊢
  exact h

omit [Nontrivial ℋ] in
private lemma traceConjPow_one_via_bridge (B A : L ℋ) (hA : (0 : L ℋ) ≤ A) :
    traceConjPow (ℋ := ℋ) 1 B A = (Tr (star B * A * B)).re := by
  have hinner_nn : (0 : L ℋ) ≤ star B * A * B :=
    star_left_conjugate_nonneg hA _
  rw [traceConjPow_eq_direct, show (1 : ℝ) / 1 = 1 from by norm_num]
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_one (A := L ℋ) A hA,
    CFC.rpow_one (A := L ℋ) (star B * A * B) hinner_nn]

/-! ### Frank-Lieb concavity of conjugated powers -/

private lemma traceConjPowVar_jointlyConvex {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0)
    (B : ℋ →L[ℂ] ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p
        (B : L ℋ) (A : L ℋ) (X : L ℋ)) := by
  have hvar (A X : ℋ →L[ℂ] ℋ) :
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap A.toLinearMap X.toLinearMap =
        liebTraceMap (ℋ := ℋ) p (star B) A X - (1 - p) * traceRe (ℋ := ℋ) X := by
    rw [traceConjPowVar, liebTraceMapLM_eq_direct]
    rw [star_toCLM]
    rfl
  have h_cyclic (A X : ℋ →L[ℂ] ℋ) :
      liebTraceMap (ℋ := ℋ) p (star B) A X =
        liebTraceMap (ℋ := ℋ) (1 - p) B X A := by
    unfold liebTraceMap
    rw [star_star, show (1 : ℝ) - (1 - p) = p from by ring]
    have h := traceRe_mul_comm (ℋ := ℋ)
      (A ^ p * B) (X ^ (1 - p) * star B)
    simp only [mul_assoc] at h ⊢
    exact h
  change JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
    (fun A X => traceConjPowVar (ℋ := ℋ) p B.toLinearMap A.toLinearMap X.toLinearMap)
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, hvar, h_cyclic]
  have h_ando := liebTrace_jointlyConvexOn_pdSet (show (1 : ℝ) ≤ 1 - p by linarith)
    (show 1 - p ≤ 2 by linarith) B
  have h_swap : JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (fun A X => liebTraceMap (ℋ := ℋ) (1 - p) B X A) :=
    fun _ _ _ _ _ h1 h2 h3 h4 h5 h6 => h_ando h3 h4 h1 h2 h5 h6
  have h_conv := h_swap hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_conv
  have h_tr := LiebAndoTrace.trace_re_convex_combo θ X₁ X₂
  nlinarith

/-- Joint concavity of `traceConjPowVar` for 0 < p < 1.
    By Lieb's concavity theorem liebTraceMapLM(p, B†, A, X) is jointly concave,
    and the trace penalty is linear, so the functional is jointly concave. -/
private lemma traceConjPowVar_jointlyConcave {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (B : ℋ →L[ℂ] ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p
        (B : L ℋ) (A : L ℋ) (X : L ℋ)) := by
  have hvar (A X : ℋ →L[ℂ] ℋ) :
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap A.toLinearMap X.toLinearMap =
        liebTraceMap (ℋ := ℋ) p (star B) A X - (1 - p) * traceRe (ℋ := ℋ) X := by
    rw [traceConjPowVar, liebTraceMapLM_eq_direct]
    rw [star_toCLM]
    rfl
  change JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
    (fun A X => traceConjPowVar (ℋ := ℋ) p B.toLinearMap A.toLinearMap X.toLinearMap)
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, hvar]
  have h_lieb := liebTrace_jointlyConcaveOn_pdSet hp0 hp1 (star B)
    hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_lieb
  have h_tr := LiebAndoTrace.trace_re_convex_combo θ X₁ X₂
  nlinarith

/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSet` for `−1 ≤ p < 0`.
    Proof: The variational functional `F(A, X)` is jointly convex in `(A, X)` by Ando's theorem.
    Since `p · traceConjPow = inf_X F`, the function `p · traceConjPow` is convex.
    Dividing by `p < 0` gives concavity of `traceConjPow`. -/
theorem traceConjPow_concave_neg {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0)
    (B : ℋ →L[ℂ] ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSet (ℋ := ℋ))
      (fun A => traceConjPow (ℋ := ℋ) p
        (B : L ℋ)
        (A : L ℋ)) := by
  have hB_lm : IsUnit B.toLinearMap :=
    (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (f := B)).mp hB
  have hpull : ∀ {A : ℋ →L[ℂ] ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap ∈ pdSetLM (ℋ := ℋ) := by
    intro A hA
    change A.toLinearMap.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only using hA
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSet_convexCombo hx hy hb (by linarith)
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  obtain ⟨XxLM, hXxLM_mem, hXx_eq⟩ :=
    exists_traceConjPowVar_eq_neg hp0 hB_lm (hpull hx)
  obtain ⟨XyLM, hXyLM_mem, hXy_eq⟩ :=
    exists_traceConjPowVar_eq_neg hp0 hB_lm (hpull hy)
  let Xx := XxLM.toContinuousLinearMap
  let Xy := XyLM.toContinuousLinearMap
  have hXx_mem : Xx ∈ pdSet (ℋ := ℋ) := by
    simpa only [Xx] using hXxLM_mem
  have hXy_mem : Xy ∈ pdSet (ℋ := ℋ) := by
    simpa only [Xy] using hXyLM_mem
  have hXx_eq' : p * traceConjPow (ℋ := ℋ) p B.toLinearMap x.toLinearMap =
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap x.toLinearMap Xx.toLinearMap := by
    simpa only [Xx] using hXx_eq
  have hXy_eq' : p * traceConjPow (ℋ := ℋ) p B.toLinearMap y.toLinearMap =
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap y.toLinearMap Xy.toLinearMap := by
    simpa only [Xy] using hXy_eq
  have h_combo : a • x + b • y ∈ pdSet (ℋ := ℋ) := by
    rw [hab']; exact pdSet_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSet (ℋ := ℋ) := by
    rw [hab']; exact pdSet_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : p * traceConjPow (ℋ := ℋ) p B.toLinearMap
        (a • x + b • y).toLinearMap ≤
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap (a • x + b • y).toLinearMap
        (a • Xx + b • Xy).toLinearMap := by
    exact traceConjPowVar_le_neg hp0 hB_lm (hpull h_combo) (hpull h_Xcombo)
  rw [hab'] at step1
  have step2 := traceConjPowVar_jointlyConvex hpm1 hp0 B hx hy hXx_mem hXy_mem hb hb1
  simp only [smul_eq_mul] at step2
  rw [← hXx_eq', ← hXy_eq'] at step2
  rw [hab']
  nlinarith [step1, step2]

/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSet` for `0 < p ≤ 1`.
    Proof: `F` is jointly concave by Lieb's theorem; `p · traceConjPow = sup_X F` is concave;
    dividing by `p > 0` preserves concavity. -/
theorem traceConjPow_concave_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : ℋ →L[ℂ] ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSet (ℋ := ℋ))
      (fun A => traceConjPow (ℋ := ℋ) p
        (B : L ℋ)
        (A : L ℋ)) := by
  have hB_lm : IsUnit B.toLinearMap :=
    (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (f := B)).mp hB
  have hpull : ∀ {A : ℋ →L[ℂ] ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap ∈ pdSetLM (ℋ := ℋ) := by
    intro A hA
    change A.toLinearMap.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only using hA
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSet_convexCombo hx hy hb (by linarith)
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  obtain ⟨XxLM, hXxLM_mem, hXx_eq⟩ :=
    exists_traceConjPowVar_eq_pos hp0 hp1 hB_lm (hpull hx)
  obtain ⟨XyLM, hXyLM_mem, hXy_eq⟩ :=
    exists_traceConjPowVar_eq_pos hp0 hp1 hB_lm (hpull hy)
  let Xx := XxLM.toContinuousLinearMap
  let Xy := XyLM.toContinuousLinearMap
  have hXx_mem : Xx ∈ pdSet (ℋ := ℋ) := by
    simpa only [Xx] using hXxLM_mem
  have hXy_mem : Xy ∈ pdSet (ℋ := ℋ) := by
    simpa only [Xy] using hXyLM_mem
  have hXx_eq' : p * traceConjPow (ℋ := ℋ) p B.toLinearMap x.toLinearMap =
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap x.toLinearMap Xx.toLinearMap := by
    simpa only [Xx] using hXx_eq
  have hXy_eq' : p * traceConjPow (ℋ := ℋ) p B.toLinearMap y.toLinearMap =
      traceConjPowVar (ℋ := ℋ) p B.toLinearMap y.toLinearMap Xy.toLinearMap := by
    simpa only [Xy] using hXy_eq
  have h_combo : a • x + b • y ∈ pdSet (ℋ := ℋ) := by
    rw [hab']; exact pdSet_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSet (ℋ := ℋ) := by
    rw [hab']; exact pdSet_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : traceConjPowVar (ℋ := ℋ) p B.toLinearMap
        (a • x + b • y).toLinearMap (a • Xx + b • Xy).toLinearMap ≤
      p * traceConjPow (ℋ := ℋ) p B.toLinearMap (a • x + b • y).toLinearMap := by
    exact traceConjPowVar_le_pos hp0 hp1 (hpull h_combo) (hpull h_Xcombo)
  rw [hab'] at step1
  rcases lt_or_eq_of_le hp1 with hp1 | rfl
  · have step2 := traceConjPowVar_jointlyConcave hp0 hp1 B hx hy hXx_mem hXy_mem hb hb1
    simp only [smul_eq_mul] at step2
    rw [← hXx_eq', ← hXy_eq'] at step2
    rw [hab']
    nlinarith [step1, step2]
  · -- p = 1: A ↦ Tr(B†AB) is affine, hence concave
    have hfun : ∀ {A : ℋ →L[ℂ] ℋ}, A ∈ pdSet (ℋ := ℋ) →
        traceConjPow (ℋ := ℋ) 1 B.toLinearMap A.toLinearMap =
          traceRe (ℋ := ℋ) (star B * A * B) := by
      intro A hA
      calc
        traceConjPow (ℋ := ℋ) 1 B.toLinearMap A.toLinearMap =
            (Tr (star B.toLinearMap * A.toLinearMap * B.toLinearMap)).re :=
          traceConjPow_one_via_bridge B.toLinearMap A.toLinearMap
            (nonneg_of_pdSetLM (hpull hA))
        _ = traceRe (ℋ := ℋ) (star B * A * B) := by
          have htrace :=
            traceRe_via_toCLM (star B.toLinearMap * A.toLinearMap * B.toLinearMap)
          rw [← htrace]
          change traceRe (ℋ := ℋ) ((star B.toLinearMap).toContinuousLinearMap *
              A.toLinearMap.toContinuousLinearMap * B.toLinearMap.toContinuousLinearMap) =
            traceRe (ℋ := ℋ) (star B * A * B)
          rw [star_toCLM, toCLM_toLinearMap, toCLM_toLinearMap]
    rw [hab'] at h_combo ⊢
    rw [hfun hx, hfun hy, hfun h_combo]
    have hmul : star B * ((1 - b) • x + b • y) * B =
        (1 - b) • (star B * x * B) + b • (star B * y * B) := by
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    rw [hmul, LiebAndoTrace.trace_re_convex_combo]

/-- For a fixed operator `B`, the map `A ↦ Tr((B† A^p B)^{1/p})` is concave
    on positive-definite operators for `−1 ≤ p ≤ 1`, `p ≠ 0` (Frank–Lieb concavity).

Source: arXiv:1306.5358v3, Lemma 5, p.3 (proof on p.5). Version using the real part of the trace,
restricted to positive definite inputs and invertible B. -/
theorem traceConjPow_concave {p : ℝ} (hp_neg : -1 ≤ p) (hp_pos : p ≤ 1)
    (hp_ne : p ≠ 0) (B : ℋ →L[ℂ] ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSet (ℋ := ℋ))
      (fun A => traceConjPow (ℋ := ℋ) p
        (B : L ℋ)
        (A : L ℋ)) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact traceConjPow_concave_neg hp_neg hp B hB
  · exact traceConjPow_concave_pos (lt_of_le_of_ne hp (Ne.symm hp_ne)) hp_pos B hB

end TraceConjPowConcavity

end SandwichedRenyiRelativeEntropy
