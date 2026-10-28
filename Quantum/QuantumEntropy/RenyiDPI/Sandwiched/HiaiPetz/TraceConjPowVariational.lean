/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumEntropy.Common.OperatorScalarTower
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumEntropy.YoungInequality
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.LiebTrace.Bridge


open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma c11_star_toCLM {H : Type u} [Qudit H] (A : L H) :
    (star A).toContinuousLinearMap = star A.toContinuousLinearMap := by
  change A.adjoint.toContinuousLinearMap = star A.toContinuousLinearMap
  rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

private lemma c11_traceConjPow_toCLM {H : Type u} [Qudit H] (p : ℝ) (B A : L H) :
    traceConjPow p B A =
      traceRe (ℋ := H) (CFC.rpow
        (star B.toContinuousLinearMap *
          CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap) (1 / p)) := by
  have hrpow (T : L H) (q : ℝ) :
      (CFC.rpow T q).toContinuousLinearMap = CFC.rpow T.toContinuousLinearMap q :=
    TensorCFC.rpow_toContinuousLinearMap_lm T q
  rw [traceConjPow_eq_direct]
  change traceRe (ℋ := H)
    (CFC.rpow (star B * CFC.rpow A p * B) (1 / p)).toContinuousLinearMap = _
  rw [hrpow]
  change traceRe (ℋ := H) (CFC.rpow
    ((star B).toContinuousLinearMap * (CFC.rpow A p).toContinuousLinearMap *
      B.toContinuousLinearMap) (1 / p)) = _
  rw [c11_star_toCLM, hrpow]

private lemma c11_liebTraceMapLM_toCLM {H : Type u} [Qudit H] (p : ℝ) (B A X : L H) :
    liebTraceMapLM p (star B) A X =
      traceRe (ℋ := H) (star B.toContinuousLinearMap *
        CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap *
        CFC.rpow X.toContinuousLinearMap (1 - p)) := by
  rw [liebTraceMapLM_eq_direct]
  unfold liebTraceMap
  change traceRe (ℋ := H) (A.toContinuousLinearMap ^ p *
    star (star B).toContinuousLinearMap * X.toContinuousLinearMap ^ (1 - p) *
    (star B).toContinuousLinearMap) = _
  rw [c11_star_toCLM, star_star, ← CFC.rpow_eq_pow, ← CFC.rpow_eq_pow]
  have h := congrArg Complex.re
    (LinearMap.trace_mul_comm (R := ℂ) (M := H)
      (CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap *
        CFC.rpow X.toContinuousLinearMap (1 - p)).toLinearMap
      (star B.toContinuousLinearMap).toLinearMap)
  simpa only [mul_assoc] using h

private lemma c11_young_traceRe {H : Type u} [Qudit H] {r s : ℝ}
    (hrs : r.HolderConjugate s) (M N : QuantumState.B H)
    (hM : M.IsPositive) (hN : N.IsPositive) :
    traceRe (ℋ := H) (M * N) ≤
      traceRe (ℋ := H) (CFC.rpow M r) / r +
        traceRe (ℋ := H) (CFC.rpow N s) / s := by
  have h := (RCLike.le_iff_re_im.mp (trace_young_inequality hrs M N hM hN)).1
  change traceRe (ℋ := H) (M * N) ≤
    (Tr (CFC.rpow M r).toLinearMap / ↑r +
      Tr (CFC.rpow N s).toLinearMap / ↑s).re at h
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re] at h
  exact h

theorem traceConjPowVar_le_pos :
∀ {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ} {B A X : L H},
  0 < p → p < 1 → A ∈ pdSetLM (ℋ := H) → X ∈ pdSetLM (ℋ := H) →
  traceConjPowVar p B A X ≤ p * traceConjPow p B A := by
  intro H _ _ p B A X hp0 hp1 _hA hX
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hX_nn : (0 : QuantumState.B H) ≤ X.toContinuousLinearMap :=
    ((pdSet_membership_certificate X.toContinuousLinearMap).1 hX).nonneg
  let M := star B.toContinuousLinearMap *
    CFC.rpow A.toContinuousLinearMap p * B.toContinuousLinearMap
  let N := CFC.rpow X.toContinuousLinearMap (1 - p)
  have hM : M.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (star_left_conjugate_nonneg CFC.rpow_nonneg _)
  have hN : N.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    CFC.rpow_nonneg
  have hrs := Real.holderConjugate_one_div hp0 h1p (by ring)
  have hYoung := c11_young_traceRe hrs M N hM hN
  have hNs : CFC.rpow N (1 / (1 - p)) = X.toContinuousLinearMap := by
    dsimp only [N]
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
      CFC.rpow_rpow_of_exponent_nonneg X.toContinuousLinearMap
        (1 - p) (1 / (1 - p)) h1p.le (by positivity) hX_nn]
    rw [show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
    exact CFC.rpow_one (A := QuantumState.B H) X.toContinuousLinearMap hX_nn
  rw [hNs, div_div_eq_mul_div, div_one, div_div_eq_mul_div, div_one] at hYoung
  change traceRe (ℋ := H) (M * N) ≤
    traceRe (ℋ := H) (CFC.rpow M (1 / p)) * p +
      traceRe (ℋ := H) X.toContinuousLinearMap * (1 - p) at hYoung
  rw [traceConjPowVar, c11_traceConjPow_toCLM, c11_liebTraceMapLM_toCLM]
  change traceRe (ℋ := H) (M * N) -
    (1 - p) * traceRe (ℋ := H) X.toContinuousLinearMap ≤
      p * traceRe (ℋ := H) (CFC.rpow M (1 / p))
  linarith

private lemma c12_rpow_toCLM_nonneg {H : Type u} [Qudit H] (A : L H) {p : ℝ}
    (hA : 0 ≤ A) (hp : 0 ≤ p) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  let e : L H ≃⋆ₐ[ℝ] QuantumState.B H :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  have heA : (0 : QuantumState.B H) ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff (0 : QuantumState.B H) A.toContinuousLinearMap).mp hA
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real heA]
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) e _ A
    (Real.continuous_rpow_const hp).continuousOn
    (StarAlgEquiv.isometry (linearToContinuousEndStarAlgEquiv H)).continuous
    (IsSelfAdjoint.of_nonneg hA)
    (IsSelfAdjoint.of_nonneg heA)

private lemma c12_liebTrace_eq_product {H : Type u} [Qudit H] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (B A X : L H) (hA : 0 ≤ A) (hX : 0 ≤ X) :
    liebTraceMapLM p (star B) A X =
      (Tr ((star B * CFC.rpow A p * B) * CFC.rpow X (1 - p))).re := by
  have hstar : (star B).toContinuousLinearMap = star B.toContinuousLinearMap := by
    change B.adjoint.toContinuousLinearMap = star B.toContinuousLinearMap
    rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]
  rw [liebTraceMapLM_eq_direct, liebTraceMap]
  change traceRe (CFC.rpow A.toContinuousLinearMap p *
    star (star B).toContinuousLinearMap * CFC.rpow X.toContinuousLinearMap (1 - p) *
    (star B).toContinuousLinearMap) = _
  rw [hstar, star_star, ← c12_rpow_toCLM_nonneg A hA hp0,
    ← c12_rpow_toCLM_nonneg X hX (sub_nonneg.mpr hp1), ← hstar]
  change (Tr ((CFC.rpow A p * B * CFC.rpow X (1 - p)) * star B)).re = _
  rw [LinearMap.trace_mul_comm]
  simp only [mul_assoc]

private lemma c12_optimal_product {H : Type u} [Qudit H] {M : L H} {p : ℝ}
    (hM : 0 ≤ M) (hMu : IsUnit M) (hp0 : 0 < p) (hp1 : p < 1) :
    M * CFC.rpow (CFC.rpow M (1 / p)) (1 - p) = CFC.rpow M (1 / p) := by
  have hexp : (1 : ℝ) + (1 / p) * (1 - p) = 1 / p := by
    field_simp
    ring
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
    CFC.rpow_rpow_of_exponent_nonneg M (1 / p) (1 - p)
      (one_div_nonneg.mpr hp0.le) (sub_nonneg.mpr hp1.le) hM]
  conv_lhs => lhs; rw [← CFC.rpow_one M hM]
  rw [← CFC.rpow_add hMu, hexp]

theorem exists_traceConjPowVar_eq_pos :
∀ {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ} {B A : L H},
  0 < p → p < 1 → IsUnit B → A ∈ pdSetLM (ℋ := H) →
  ∃ X ∈ pdSetLM (ℋ := H), p * traceConjPow p B A = traceConjPowVar p B A X := by
  intro H _ _ p B A hp0 hp1 hB hA
  have hAstr : IsStrictlyPositive A := (pdSetLM_strictPositivity_certificate A).mp hA
  let M := star B * CFC.rpow A p * B
  have hM : (0 : L H) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg B
  have hMu : IsUnit M :=
    (hB.star.mul (hAstr.isUnit.cfcRpow p hAstr.nonneg)).mul hB
  let X := CFC.rpow M (1 / p)
  have hX : (0 : L H) ≤ X := CFC.rpow_nonneg
  have hXu : IsUnit X := hMu.cfcRpow (1 / p) hM
  refine ⟨X, (pdSetLM_strictPositivity_certificate X).mpr ⟨hX, hXu⟩, ?_⟩
  have hprod : M * CFC.rpow X (1 - p) = X := c12_optimal_product hM hMu hp0 hp1
  rw [traceConjPowVar, c12_liebTrace_eq_product hp0.le hp1.le B A X hAstr.nonneg hX]
  change p * (Tr X).re = (Tr (M * CFC.rpow X (1 - p))).re - (1 - p) * (Tr X).re
  rw [hprod]
  ring

end RenyiDPI
