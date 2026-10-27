/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.DefinitionCore
import Quantum.QuantumEntropy.Common.TracePositiveDefinite
import Quantum.QuantumEntropy.Common.PositiveDefiniteTensor
import Quantum.TraceInequality.LiebAndo.LinearMapsCore

/-!
# Sandwiched Rényi relative entropy: joint convexity and tensor laws
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section JointConvexity

open LiebAndoTrace GeneralizedPerspectiveFunction
open scoped MatrixOrder

universe u₃

variable {ℋ : Type u₃} [Qudit ℋ]

private lemma rpow_conj_pdSetLM {β q : ℝ}
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    star (CFC.rpow σ β) * CFC.rpow (star (CFC.rpow σ β) * ρ *
      CFC.rpow σ β) q * CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := by
  have hrpow_pd : ∀ {A : L ℋ}, A ∈ pdSetLM (ℋ := ℋ) →
      ∀ p : ℝ, CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := by
    intro A hA p
    exact (pdSetLM_strictPositivity_certificate _).2
      (((pdSetLM_strictPositivity_certificate A).1 hA).rpow)
  have hP_pd : CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := hrpow_pd hσ β
  have hP_unit := isUnit_of_pdSetLM hP_pd
  exact pdSetLM_star_conjugate (hrpow_pd (pdSetLM_star_conjugate hρ hP_unit) q) hP_unit

-- The hypotheses restrict α to the Rényi domain `α > 0`, `α ≠ 1`.
-- Positive definiteness follows from the power factors in `quasiVarOpt`.
lemma quasiVarOpt_pdSetLM {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVarOpt α ρ σ ∈ pdSetLM (ℋ := ℋ) := by
  have _ : α ≠ 0 ∧ α - 1 ≠ 0 :=
    ⟨ne_of_gt hα0, sub_ne_zero.mpr hα_ne1⟩
  rw [quasiVarOpt_eq_direct]
  have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have key := rpow_conj_pdSetLM (β := (1 - α) / (2 * α)) (q := α - 1) hρ hσ
  rwa [hP_sa.star_eq] at key

private lemma isPositive_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    A.IsPositive :=
  (LinearMap.nonneg_iff_isPositive A).mp (nonneg_of_pdSetLM hA)

variable [Nontrivial ℋ]

/-! ### Variational concavity on linear endomorphisms -/

omit [Nontrivial ℋ] in
private lemma trace_re_convexCombo_linear (X Y : L ℋ) (θ : ℝ) :
    (Tr ((1 - θ) • X + θ • Y)).re = (1 - θ) * (Tr X).re + θ * (Tr Y).re := by
  have hsmul (r : ℝ) (A : L ℋ) : (Tr (r • A)).re = r * (Tr A).re := by
    change (Tr ((r : ℂ) • A)).re = _
    rw [map_smul]
    simp only [smul_eq_mul, Complex.re_ofReal_mul]
  rw [map_add, Complex.add_re, hsmul, hsmul]

omit [Nontrivial ℋ] in
private lemma pdSet_convexCombo_linear {A B : L ℋ} {t : ℝ}
    (hA : A ∈ pdSetLM (ℋ := ℋ)) (hB : B ∈ pdSetLM (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • A + t • B ∈ pdSetLM (ℋ := ℋ) := by
  have hA_pos := (pdSetLM_strictPositivity_certificate A).1 hA
  have hB_pos := (pdSetLM_strictPositivity_certificate B).1 hB
  apply (pdSetLM_strictPositivity_certificate _).2
  by_cases ht : t = 1
  · subst t
    simpa using hB_pos
  · exact (hA_pos.smul (sub_pos.mpr (lt_of_le_of_ne ht1 ht))).add_nonneg
      (smul_nonneg ht0 hB_pos.nonneg)

private noncomputable def conjugatePowerVar (p : ℝ) (B A X : L ℋ) : ℝ :=
  liebTraceMap p (star B) A X - (1 - p) * (Tr X).re

omit [Nontrivial ℋ] in
private lemma conjugatePowerVar_eq (p : ℝ) (B A X : L ℋ) :
    conjugatePowerVar p B A X =
      (Tr ((star B * CFC.rpow A p * B) * CFC.rpow X (1 - p))).re -
        (1 - p) * (Tr X).re := by
  unfold conjugatePowerVar liebTraceMap
  rw [star_star]
  congr 2
  have h := LinearMap.trace_mul_comm (R := ℂ) (M := ℋ)
    (CFC.rpow A p * B * CFC.rpow X (1 - p)) (star B)
  simpa only [mul_assoc, CFC.rpow_eq_pow] using h

omit [Nontrivial ℋ] in
private lemma conjugatePowerVar_le_neg {p : ℝ} (hp0 : p < 0)
    {B A X : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ))
    (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    p * traceConjPow p B A ≤ conjugatePowerVar p B A X := by
  let M := star B * CFC.rpow A p * B
  let N := CFC.rpow X (1 - p)
  have hM_nn : 0 ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg B
  have hM_unit : IsUnit M :=
    (hB.star.mul ((isUnit_of_pdSetLM hA).cfcRpow p (nonneg_of_pdSetLM hA))).mul hB
  have hM_pos := (LinearMap.nonneg_iff_isPositive M).mp hM_nn
  have hN_pos := (LinearMap.nonneg_iff_isPositive N).mp CFC.rpow_nonneg
  have h1p : 0 < 1 - p := by linarith
  have hr : 1 / p < 0 := div_neg_of_pos_of_neg one_pos hp0
  have hs0 : 0 < 1 / (1 - p) := by positivity
  have hs1 : 1 / (1 - p) < 1 := by rw [div_lt_one h1p]; linarith
  have hrs : 1 / (1 / p) + 1 / (1 / (1 - p)) = 1 := by field_simp; ring
  have hNs : CFC.rpow N (1 / (1 - p)) = X := by
    change CFC.rpow (CFC.rpow X (1 - p)) (1 / (1 - p)) = X
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
      CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p)) h1p.le hs0.le (nonneg_of_pdSetLM hX),
      show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
    exact CFC.rpow_one X (nonneg_of_pdSetLM hX)
  have h := (RCLike.le_iff_re_im.mp
    (trace_reverse_young_inequality hr hs0 hs1 hrs M N hM_pos hM_unit hN_pos)).1
  change (Tr (CFC.rpow M (1 / p)) / ↑(1 / p) +
    Tr (CFC.rpow N (1 / (1 - p))) / ↑(1 / (1 - p))).re ≤ (Tr (M * N)).re at h
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at h
  rw [conjugatePowerVar_eq, traceConjPow_eq_direct]
  change p * (Tr (CFC.rpow M (1 / p))).re ≤
    (Tr (M * N)).re - (1 - p) * (Tr X).re
  have hr_eq : (Tr (CFC.rpow M (1 / p))).re / (1 / p) =
      p * (Tr (CFC.rpow M (1 / p))).re := by field_simp
  have hs_eq : (Tr X).re / (1 / (1 - p)) = (1 - p) * (Tr X).re := by field_simp
  rw [hr_eq, hs_eq] at h
  linarith

omit [Nontrivial ℋ] in
private lemma conjugatePowerVar_le_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {B A X : L ℋ} (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    conjugatePowerVar p B A X ≤ p * traceConjPow p B A := by
  let M := star B * CFC.rpow A p * B
  let N := CFC.rpow X (1 - p)
  have hM_pos := (LinearMap.nonneg_iff_isPositive M).mp
    (star_left_conjugate_nonneg CFC.rpow_nonneg B)
  have hN_pos := (LinearMap.nonneg_iff_isPositive N).mp CFC.rpow_nonneg
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hpq : (1 / p).HolderConjugate (1 / (1 - p)) :=
    Real.holderConjugate_one_div hp0 h1p (by ring)
  have hNs : CFC.rpow N (1 / (1 - p)) = X := by
    change CFC.rpow (CFC.rpow X (1 - p)) (1 / (1 - p)) = X
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
      CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p)) h1p.le
        (by positivity) (nonneg_of_pdSetLM hX),
      show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
    exact CFC.rpow_one X (nonneg_of_pdSetLM hX)
  have h := (RCLike.le_iff_re_im.mp (trace_young_inequality hpq M N hM_pos hN_pos)).1
  change (Tr (M * N)).re ≤ (Tr (CFC.rpow M (1 / p)) / ↑(1 / p) +
    Tr (CFC.rpow N (1 / (1 - p))) / ↑(1 / (1 - p))).re at h
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at h
  rw [conjugatePowerVar_eq, traceConjPow_eq_direct]
  change (Tr (M * N)).re - (1 - p) * (Tr X).re ≤
    p * (Tr (CFC.rpow M (1 / p))).re
  have hr_eq : (Tr (CFC.rpow M (1 / p))).re / (1 / p) =
      p * (Tr (CFC.rpow M (1 / p))).re := by field_simp
  have hs_eq : (Tr X).re / (1 / (1 - p)) = (1 - p) * (Tr X).re := by field_simp
  rw [hr_eq, hs_eq] at h
  linarith

omit [Nontrivial ℋ] in
private lemma exists_conjugatePowerVar_eq {p : ℝ} (hp : p ≠ 0)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ), p * traceConjPow p B A = conjugatePowerVar p B A X := by
  let M := star B * CFC.rpow A p * B
  have hM_nn : 0 ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg B
  have hM_unit : IsUnit M :=
    (hB.star.mul ((isUnit_of_pdSetLM hA).cfcRpow p (nonneg_of_pdSetLM hA))).mul hB
  let X := CFC.rpow M (1 / p)
  have hX_pd : X ∈ pdSetLM (ℋ := ℋ) :=
    (pdSetLM_strictPositivity_certificate X).2
      ((IsStrictlyPositive.iff_of_unital).mpr ⟨hM_nn, hM_unit⟩).rpow
  refine ⟨X, hX_pd, ?_⟩
  have hXp : CFC.rpow X (1 - p) = CFC.rpow M ((1 - p) / p) := by
    change CFC.rpow (CFC.rpow M (1 / p)) (1 - p) = _
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
      CFC.rpow_rpow M (1 / p) (1 - p) hM_unit (one_div_ne_zero hp)]
    congr 1
    ring
  have hMX : M * CFC.rpow M ((1 - p) / p) = X := by
    conv_lhs => lhs; rw [← CFC.rpow_one M hM_nn]
    simp only [CFC.rpow_eq_pow]
    rw [← CFC.rpow_add hM_unit]
    change CFC.rpow M (1 + (1 - p) / p) = CFC.rpow M (1 / p)
    congr 1
    field_simp
    ring
  rw [conjugatePowerVar_eq, traceConjPow_eq_direct]
  change p * (Tr X).re = (Tr (M * CFC.rpow X (1 - p))).re - (1 - p) * (Tr X).re
  rw [hXp, hMX]
  ring

private lemma conjugatePowerVar_jointlyConvex {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0)
    (B : L ℋ) :
    JointlyConvexOn pdSetLM pdSetLM (conjugatePowerVar p B) := by
  have hcyc (A X : L ℋ) : liebTraceMap p (star B) A X =
      liebTraceMap (1 - p) B X A := by
    unfold liebTraceMap
    rw [star_star, show (1 : ℝ) - (1 - p) = p from by ring]
    have h := LinearMap.trace_mul_comm (R := ℂ) (M := ℋ)
      (CFC.rpow A p * B) (CFC.rpow X (1 - p) * star B)
    simpa only [mul_assoc] using congrArg Complex.re h
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [conjugatePowerVar, hcyc, smul_eq_mul]
  have h := jointlyConvexOn_liebTraceMap_pdSetLM (by linarith : 1 ≤ 1 - p)
    (by linarith : 1 - p ≤ 2) B hX₁ hX₂ hA₁ hA₂ hθ0 hθ1
  simp only [smul_eq_mul] at h
  have htr := trace_re_convexCombo_linear X₁ X₂ θ
  nlinarith

private lemma conjugatePowerVar_jointlyConcave {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (B : L ℋ) :
    JointlyConcaveOn pdSetLM pdSetLM (conjugatePowerVar p B) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [conjugatePowerVar, smul_eq_mul]
  have h := jointlyConcaveOn_liebTraceMap_pdSetLM hp0 hp1 (star B)
    hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h
  have htr := trace_re_convexCombo_linear X₁ X₂ θ
  nlinarith

private lemma traceConjPow_concave_linear {p : ℝ} (hpm1 : -1 ≤ p) (hp1 : p < 1)
    (hp : p ≠ 0) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ pdSetLM (traceConjPow p B) := by
  have hconv : Convex ℝ (pdSetLM (ℋ := ℋ)) := by
    intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSet_convexCombo_linear hx hy hb (by linarith)
  refine ⟨hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  obtain ⟨Xx, hXx, heqx⟩ := exists_conjugatePowerVar_eq hp hB hx
  obtain ⟨Xy, hXy, heqy⟩ := exists_conjugatePowerVar_eq hp hB hy
  have hcombo := hconv hx hy ha hb hab
  have hXcombo := hconv hXx hXy ha hb hab
  have haeq : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  rcases lt_or_gt_of_ne hp with hp0 | hp0
  · have hbound := conjugatePowerVar_le_neg hp0 hB hcombo hXcombo
    rw [haeq] at hbound
    have hjoint := conjugatePowerVar_jointlyConvex hpm1 hp0 B hx hy hXx hXy hb hb1
    simp only [smul_eq_mul] at hjoint
    rw [← heqx, ← heqy] at hjoint
    rw [haeq]
    nlinarith
  · have hbound := conjugatePowerVar_le_pos hp0 hp1 (B := B) (A := a • x + b • y) hXcombo
    rw [haeq] at hbound
    have hjoint := conjugatePowerVar_jointlyConcave hp0 hp1 B hx hy hXx hXy hb hb1
    simp only [smul_eq_mul] at hjoint
    rw [← heqx, ← heqy] at hjoint
    rw [haeq]
    nlinarith

private noncomputable abbrev traceLinear (A : L ℋ) : ℝ := (Tr A).re

omit [Nontrivial ℋ] in
private lemma trace_rpow_star_mul_comm_linear {C : L ℋ} (q : ℝ) :
    traceLinear (ℋ := ℋ) (CFC.rpow (star C * C) q) =
      traceLinear (ℋ := ℋ) (CFC.rpow (C * star C) q) := by
  have h1_nn : (0 : L ℋ) ≤ 1 := zero_le_one
  have h_sCC_nn : (0 : L ℋ) ≤ star C * C := by
    have := star_left_conjugate_nonneg h1_nn C
    rwa [mul_one] at this
  have h_CsC_nn : (0 : L ℋ) ≤ C * star C := by
    have := star_left_conjugate_nonneg h1_nn (star C)
    rwa [star_star, mul_one] at this
  let b := stdOrthonormalBasis ℂ ℋ
  set M := LinearMap.toMatrixOrthonormal b C
  have hH1 : (star M * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hH2 : (M * star M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hNN1 : 0 ≤ star M * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hNN2 : 0 ≤ M * star M := (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have h_matrix_sCC :
      LinearMap.toMatrixOrthonormal b (star C * C) = star M * M := by
    change LinearMap.toMatrixOrthonormal b (star C * C) =
      star M * M
    rw [map_mul, map_star]
  have h_matrix_CsC :
      LinearMap.toMatrixOrthonormal b (C * star C) = M * star M := by
    change LinearMap.toMatrixOrthonormal b (C * star C) =
      M * star M
    rw [map_mul, map_star]
  have h_eig : hH1.eigenvalues = hH2.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  apply congrArg Complex.re
  calc Tr (CFC.rpow (star C * C) q)
      = Matrix.trace (LinearMap.toMatrixOrthonormal b
          (CFC.rpow (star C * C) q)) :=
        tr_eq_matrix_trace_orthonormal b _
    _ = ∑ i, (((hH1.eigenvalues i) ^ q : ℝ) : ℂ) := by
        have hmap := congrArg Matrix.trace
          (toMatrixOrthonormal_rpow_of_nonneg b (star C * C) h_sCC_nn q)
        have htrace := matrix_trace_rpow_eq_sum_eigenvalues (star M * M) hH1 hNN1 q
        rw [h_matrix_sCC] at hmap
        exact hmap.trans htrace
    _ = ∑ i, (((hH2.eigenvalues i) ^ q : ℝ) : ℂ) := by rw [h_eig]
    _ = Matrix.trace (LinearMap.toMatrixOrthonormal b
        (CFC.rpow (C * star C) q)) := by
        have htrace := (matrix_trace_rpow_eq_sum_eigenvalues (M * star M) hH2 hNN2 q).symm
        have hmap := congrArg Matrix.trace
          (toMatrixOrthonormal_rpow_of_nonneg b (C * star C) h_CsC_nn q)
        rw [h_matrix_CsC] at hmap
        exact htrace.trans hmap.symm
    _ = Tr (CFC.rpow (C * star C) q) :=
        (tr_eq_matrix_trace_orthonormal b _).symm

omit [Nontrivial ℋ] in
/-- The σ-dependent part of quasiVar equals traceConjPow via eigenvalue similarity:
    Re Tr((σ^β H σ^β)^q) = traceConjPow((α-1)/α, H^{1/2}, σ)
    where β = (α-1)/(2α), q = α/(α-1). -/
private lemma quasiVar_sigma_eq_traceConjPow_linear {α : ℝ} (hα0 : 0 < α)
    {H σ : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1))) =
      traceConjPow (ℋ := ℋ) ((α - 1) / α)
        ((CFC.rpow H (1 / 2) : L ℋ) : L ℋ) (σ : L ℋ) := by
  set P := CFC.rpow σ ((α - 1) / (2 * α))
  set Q := CFC.rpow H (1 / 2)
  set C := P * Q
  have hH_nn : (0 : L ℋ) ≤ H := nonneg_of_pdSetLM hH
  have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM hσ
  have hH_unit : IsUnit H := isUnit_of_pdSetLM hH
  have hσ_unit : IsUnit σ := isUnit_of_pdSetLM hσ
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ_sa : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have h_QQ : Q * Q = H := by
    calc
      CFC.rpow H (1 / 2) * CFC.rpow H (1 / 2) =
          CFC.rpow H (1 / 2 + 1 / 2) :=
        (CFC.rpow_add hH_unit).symm
      _ = CFC.rpow H 1 := by norm_num
      _ = H := CFC.rpow_one H hH_nn
  have h_PP : P * P = CFC.rpow σ ((α - 1) / α) := by
    change CFC.rpow σ ((α - 1) / (2 * α)) *
        CFC.rpow σ ((α - 1) / (2 * α)) = CFC.rpow σ ((α - 1) / α)
    calc
      _ = CFC.rpow σ
          ((α - 1) / (2 * α) + (α - 1) / (2 * α)) :=
        (CFC.rpow_add hσ_unit).symm
      _ = CFC.rpow σ ((α - 1) / α) := by
        congr 1
        field_simp
        ring
  have h_star_C : star C = Q * P := by
    change star (P * Q) = Q * P
    rw [star_mul, hP_sa.star_eq, hQ_sa.star_eq]
  have h_CsC : C * star C = P * H * P := by
    rw [h_star_C]
    change P * Q * (Q * P) = P * H * P
    rw [← mul_assoc (P * Q) Q P, mul_assoc P Q Q, h_QQ]
  have h_sCC : star C * C = Q * CFC.rpow σ ((α - 1) / α) * Q := by
    rw [h_star_C]
    change Q * P * (P * Q) = Q * CFC.rpow σ ((α - 1) / α) * Q
    rw [← mul_assoc (Q * P) P Q, mul_assoc Q P P, h_PP]
  rw [traceConjPow_eq_direct,
    hQ_sa.star_eq,
    show (1 : ℝ) / ((α - 1) / α) = α / (α - 1) from by field_simp,
    ← h_CsC, ← h_sCC]
  exact (trace_rpow_star_mul_comm_linear _).symm

private lemma sigma_term_concaveOn_linear {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1) (hα_ge : 1 / 2 ≤ α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (fun σ =>
      traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1)))) := by
  set p := (α - 1) / α with hp_def
  have hp_ge : -1 ≤ p := by rw [hp_def]; rw [le_div_iff₀ hα0]; linarith
  have hp_lt : p < 1 := by rw [hp_def]; rw [div_lt_one hα0]; linarith
  have hp_ne : p ≠ 0 := by rw [hp_def]; exact div_ne_zero (sub_ne_zero.mpr hα_ne1) (ne_of_gt
    hα0)
  have hH_nn : (0 : L ℋ) ≤ H := nonneg_of_pdSetLM hH
  have hH_unit : IsUnit H := isUnit_of_pdSetLM hH
  have hHsq_unit : IsUnit (CFC.rpow H (1 / 2)) :=
    hH_unit.cfcRpow _ hH_nn
  have h_concave := traceConjPow_concave_linear hp_ge hp_lt hp_ne
    (CFC.rpow H (1 / 2)) hHsq_unit
  have hconvex : Convex ℝ (pdSetLM (ℋ := ℋ)) := by
    intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSet_convexCombo_linear hx hy hb (by linarith)
  refine ⟨hconvex, ?_⟩
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab
  simp only [smul_eq_mul]
  have h_combo : a • σ₁ + b • σ₂ ∈ pdSetLM (ℋ := ℋ) :=
    hconvex hσ₁ hσ₂ ha hb hab
  rw [quasiVar_sigma_eq_traceConjPow_linear hα0 hH hσ₁,
      quasiVar_sigma_eq_traceConjPow_linear hα0 hH hσ₂,
      quasiVar_sigma_eq_traceConjPow_linear hα0 hH h_combo]
  exact h_concave.2 hσ₁ hσ₂ ha hb hab

omit [Nontrivial ℋ] in
private lemma trace_mul_convexCombo_re_linear (H ρ₁ ρ₂ : L ℋ) (θ : ℝ) :
    (Tr (H * ((1 - θ) • ρ₁ + θ • ρ₂))).re =
      (1 - θ) * (Tr (H * ρ₁)).re + θ * (Tr (H * ρ₂)).re := by
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  exact trace_re_convexCombo_linear _ _ θ

private lemma quasiVar_re_jointlyConvex_linear {α : ℝ} (hα : 1 < α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (quasiVar α
        (ρ : L ℋ)
        (σ : L ℋ)
        (H : L ℋ)).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂ with hρc_def
  set σ_c := (1 - θ) • σ₁ + θ • σ₂ with hσc_def
  have h_sigma_concave := sigma_term_concaveOn_linear hα0 hα_ne1 hα_ge hH
  have h_sigma_ineq : (1 - θ) * traceLinear (ℋ := ℋ) (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2
    * α)) * H *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1))) +
      θ * traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1))) ≤
      traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ_c ((α - 1) / (2 * α)) * H *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1))) :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : traceLinear (ℋ := ℋ) (H * ρ_c) =
      (1 - θ) * traceLinear (ℋ := ℋ) (H * ρ₁) +
        θ * traceLinear (ℋ := ℋ) (H * ρ₂) := by
    change traceLinear (ℋ := ℋ) (H * ((1 - θ) • ρ₁ + θ • ρ₂)) = _
    exact trace_mul_convexCombo_re_linear H ρ₁ ρ₂ θ
  change (quasiVar α ρ_c σ_c H).re ≤
    (1 - θ) * (quasiVar α ρ₁ σ₁ H).re +
      θ * (quasiVar α ρ₂ σ₂ H).re
  rw [quasiVar_eq_direct α ρ_c σ_c H,
    quasiVar_eq_direct α ρ₁ σ₁ H,
    quasiVar_eq_direct α ρ₂ σ₂ H]
  simp only [Complex.sub_re, Complex.re_ofReal_mul]
  have hα1_pos : (0 : ℝ) < α - 1 := by linarith
  simp only [traceLinear] at h_trace_lin h_sigma_ineq
  nlinarith [h_trace_lin, h_sigma_ineq]

lemma jointlyConvexOn_quasiVar_re_pdSetLM {α : ℝ} (hα : 1 < α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (quasiVar α
        (ρ : L ℋ)
        (σ : L ℋ)
        (H : L ℋ)).re) := by
  exact quasiVar_re_jointlyConvex_linear hα hH

/-- Joint convexity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSetLM × pdSetLM` for `α > 1`
(linear endomorphisms). The proof fixes the variational optimizer at the convex
combination, applies joint convexity of the fixed-optimizer functional, and bounds its
endpoint values by the quasi-relative entropy. The functional's convexity follows from
concavity of its sigma term and linearity of its rho term.

Source: arXiv:1306.5358v3, Proposition 3 (convexity part), p.2.
Source: this paper, arXiv:2607.05492v1, joint convexity of the quasi-relative entropy in
§4.D, p.31 (the displayed theorem). -/
theorem jointlyConvexOn_sandwichedQuasi_re_pdSetLM {α : ℝ} (hα : 1 < α) :
    JointlyConvexOn pdSetLM pdSetLM (fun ρ σ : L ℋ => (sandwichedQuasi α ρ σ).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSetLM (ℋ := ℋ) := pdSet_convexCombo_linear hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSetLM (ℋ := ℋ) := pdSet_convexCombo_linear hσ₁ hσ₂ hθ0 hθ1
  set H_c := quasiVarOpt α ρ_c σ_c
  have hH_c_pd := quasiVarOpt_pdSetLM (by linarith : (0 : ℝ) < α) (ne_of_gt hα) hρ_c hσ_c
  have hH_c_pos := isPositive_of_pdSetLM hH_c_pd
  have hH_c_eq := quasiVarOpt_eq_quasi_gt hα
    (isPositive_of_pdSetLM hρ_c) (isPositive_of_pdSetLM hσ_c) (isUnit_of_pdSetLM hσ_c)
  have h_combo_eq : (sandwichedQuasi α ρ_c σ_c).re =
      (quasiVar α ρ_c σ_c H_c).re := by
    exact congrArg Complex.re hH_c_eq.symm
  have h_ub1 : (quasiVar α ρ₁ σ₁ H_c).re ≤
      (sandwichedQuasi α ρ₁ σ₁).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (isPositive_of_pdSetLM hρ₁)
      (isPositive_of_pdSetLM hσ₁) hH_c_pos (isUnit_of_pdSetLM hσ₁))).1
  have h_ub2 : (quasiVar α ρ₂ σ₂ H_c).re ≤
      (sandwichedQuasi α ρ₂ σ₂).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (isPositive_of_pdSetLM hρ₂)
      (isPositive_of_pdSetLM hσ₂) hH_c_pos (isUnit_of_pdSetLM hσ₂))).1
  have h_convex : (quasiVar α ρ_c σ_c H_c).re ≤
      (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re +
        θ * (quasiVar α ρ₂ σ₂ H_c).re := by
    exact (quasiVar_re_jointlyConvex_linear hα hH_c_pd)
      hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  rw [h_combo_eq]
  calc (quasiVar α ρ_c σ_c H_c).re
      ≤ (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re +
          θ * (quasiVar α ρ₂ σ₂ H_c).re := h_convex
    _ ≤ (1 - θ) * (sandwichedQuasi α ρ₁ σ₁).re +
        θ * (sandwichedQuasi α ρ₂ σ₂).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_ub1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_ub2 hθ0

/-- Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSetLM × pdSetLM` for `1/2 ≤ α < 1`
(linear endomorphisms). The proof fixes the variational optimizer at the convex
combination and bounds the endpoint quasi-relative entropies by the fixed-optimizer
functional. Concavity of its sigma term and linearity of its rho term give the required
concavity inequality, with equality at the convex combination.

Source: arXiv:1306.5358v3, Proposition 3 (concavity part), p.2.
Source: this paper, arXiv:2607.05492v1, joint concavity of the quasi-relative entropy in
§4.D, p.31 (the displayed theorem). -/
theorem jointlyConcaveOn_sandwichedQuasi_re_pdSetLM {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn pdSetLM pdSetLM (fun ρ σ : L ℋ => (sandwichedQuasi α ρ σ).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSetLM (ℋ := ℋ) := pdSet_convexCombo_linear hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSetLM (ℋ := ℋ) := pdSet_convexCombo_linear hσ₁ hσ₂ hθ0 hθ1
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_lt hα_lt
  set H_c := quasiVarOpt α ρ_c σ_c
  have hH_c_pd := quasiVarOpt_pdSetLM hα0 hα_ne1 hρ_c hσ_c
  have hH_c_pos := isPositive_of_pdSetLM hH_c_pd
  have hH_c_unit := isUnit_of_pdSetLM hH_c_pd
  have hH_c_eq := quasiVarOpt_eq_quasi_lt hα0 hα_lt
    (isPositive_of_pdSetLM hρ_c) (isPositive_of_pdSetLM hσ_c)
    (isUnit_of_pdSetLM hσ_c) (isUnit_of_pdSetLM hρ_c)
  have h_combo_eq : (sandwichedQuasi α ρ_c σ_c).re =
      (quasiVar α ρ_c σ_c H_c).re := by
    exact congrArg Complex.re hH_c_eq.symm
  have h_lb1 : (sandwichedQuasi α ρ₁ σ₁).re ≤
      (quasiVar α ρ₁ σ₁ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (isPositive_of_pdSetLM hρ₁)
      (isPositive_of_pdSetLM hσ₁) hH_c_pos (isUnit_of_pdSetLM hσ₁) hH_c_unit)).1
  have h_lb2 : (sandwichedQuasi α ρ₂ σ₂).re ≤
      (quasiVar α ρ₂ σ₂ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (isPositive_of_pdSetLM hρ₂)
      (isPositive_of_pdSetLM hσ₂) hH_c_pos (isUnit_of_pdSetLM hσ₂) hH_c_unit)).1
  have h_sigma_concave := sigma_term_concaveOn_linear hα0 hα_ne1 hα_ge hH_c_pd
  have h_sigma_ineq : (1 - θ) * traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1))) +
      θ * traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1))) ≤
      traceLinear (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ_c ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1))) :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : 0 ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : traceLinear (ℋ := ℋ) (H_c * ρ_c) =
      (1 - θ) * traceLinear (ℋ := ℋ) (H_c * ρ₁) +
        θ * traceLinear (ℋ := ℋ) (H_c * ρ₂) := by
    change traceLinear (ℋ := ℋ) (H_c * ((1 - θ) • ρ₁ + θ • ρ₂)) = _
    exact trace_mul_convexCombo_re_linear H_c ρ₁ ρ₂ θ
  have h_concave :
      (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re +
        θ * (quasiVar α ρ₂ σ₂ H_c).re ≤
      (quasiVar α ρ_c σ_c H_c).re := by
    rw [quasiVar_eq_direct α ρ₁ σ₁ H_c,
      quasiVar_eq_direct α ρ₂ σ₂ H_c,
      quasiVar_eq_direct α ρ_c σ_c H_c]
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hα1_neg : α - 1 < (0 : ℝ) := by linarith
    simp only [traceLinear] at h_trace_lin h_sigma_ineq
    nlinarith [h_trace_lin, h_sigma_ineq]
  rw [h_combo_eq]
  calc (1 - θ) * (sandwichedQuasi α ρ₁ σ₁).re +
      θ * (sandwichedQuasi α ρ₂ σ₂).re
      ≤ (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re +
          θ * (quasiVar α ρ₂ σ₂ H_c).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_lb1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_lb2 hθ0
    _ ≤ (quasiVar α ρ_c σ_c H_c).re := h_concave

end JointConvexity

section UnitaryInvariance

universe u₄

variable {ℋ : Type u₄} [Qudit ℋ]

open scoped NNReal

/-! ### Unitary invariance and tensor product laws -/
instance instIsScalarTowerNNRealComplexL : IsScalarTower ℝ≥0 ℂ (B ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ≥0 ℂ r * c) • x = (algebraMap ℝ≥0 ℂ r) • (c • x)
    rw [mul_smul]

/-- Trace is invariant under unitary conjugation: Tr(U A U†) = Tr(A). -/
lemma trace_unitary_conj (A : L ℋ) (U : unitary (L ℋ)) :
    Tr ((U : L ℋ) * A * (star U : L ℋ)) = Tr A := by
  calc
    Tr ((U : L ℋ) * A * (star U : L ℋ)) =
        Tr ((star U : L ℋ) * ((U : L ℋ) * A)) := LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) _ _
    _ = Tr A := by
      rw [← mul_assoc, (Unitary.mem_iff.mp U.property).1, one_mul]

/-- CFC.rpow commutes with unitary conjugation: (U A U†)^p = U A^p U†. -/
private lemma rpow_unitary_conj (U : unitary (L ℋ)) (A : L ℋ) (p : ℝ) :
    CFC.rpow ((U : L ℋ) * A * (star U : L ℋ)) p =
      (U : L ℋ) * CFC.rpow A p * (star U : L ℋ) := by
  letI : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let ψ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  simp only [CFC.rpow]
  let f : ℝ≥0 → ℝ≥0 := fun x => x ^ p
  change cfc f (ψ A) = ψ (cfc f A)
  have hnn : (0 : L ℋ) ≤ ψ A ↔ (0 : L ℋ) ≤ A := by
    conv_lhs => rw [show (0 : L ℋ) = ψ 0 from (map_zero ψ).symm]
    exact OrderIsoClass.map_le_map_iff ψ
  have hspec : spectrum ℝ≥0 (ψ A) = spectrum ℝ≥0 A :=
    AlgEquiv.spectrum_eq (ψ.restrictScalars ℝ≥0).toAlgEquiv A
  by_cases h : (0 ≤ A) ∧ ContinuousOn f (spectrum ℝ≥0 A)
  · exact (StarAlgHomClass.map_cfc (R := ℝ≥0) (S := ℂ) ψ f A h.2
      (map_continuous ψ) h.1 (hnn.mpr h.1)).symm
  · rw [cfc_apply_of_not_and A h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

/-- Unitary invariance of sandwichedQuasi:
    Q_α(U ρ U†‖U σ U†) = Q_α(ρ‖σ).

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedQuasi_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedQuasi α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedQuasi α ρ σ := by
  let ψ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  change sandwichedQuasi α (ψ ρ) (ψ σ) = sandwichedQuasi α ρ σ
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct]
  set β := (1 - α) / (2 * α)
  set P := CFC.rpow σ β
  rw [show CFC.rpow (ψ σ) β = ψ (CFC.rpow σ β) from rpow_unitary_conj U σ β]
  have h_inner : ψ P * ψ ρ * ψ P = ψ (P * ρ * P) := by
    simp only [map_mul]
  rw [h_inner, show CFC.rpow (ψ (P * ρ * P)) α = ψ (CFC.rpow (P * ρ * P) α)
    from rpow_unitary_conj U (P * ρ * P) α]
  exact trace_unitary_conj _ U

/-- Unitary invariance of sandwiched Rényi relative entropy:
    D_α(U ρ U†‖U σ U†) = D_α(ρ‖σ).

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedRenyiDiv_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedRenyiDiv α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedRenyiDiv α ρ σ := by
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_unitary_conj, trace_unitary_conj]

end UnitaryInvariance

section TensorMultiplicativity

open QuantumChannel TensorProduct

universe u₁ u₂

variable {ℋ₁ : Type u₁} {ℋ₂ : Type u₂} [Qudit ℋ₁] [Qudit ℋ₂]

/-- Tensor multiplicativity of sandwichedQuasi:
    Q_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q_α(ρ₁ ‖ σ₁) · Q_α(ρ₂ ‖ σ₂).

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedQuasi_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    sandwichedQuasi α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂ := by
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct,
    sandwichedQuasi_eq_direct]
  set β := (1 - α) / (2 * α)
  set P₁ := CFC.rpow σ₁ β
  set P₂ := CFC.rpow σ₂ β
  rw [TensorCFC.rpow_tensorProduct σ₁ σ₂ β hσ₁ hσ₂,
    show TensorProduct.map P₁ P₂ * TensorProduct.map ρ₁ ρ₂ * TensorProduct.map P₁ P₂ =
      TensorProduct.map (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) from by
        rw [← TensorProduct.map_mul, ← TensorProduct.map_mul],
    TensorCFC.rpow_tensorProduct (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) α
      (conjugate_nonneg_of_nonneg hρ₁ CFC.rpow_nonneg)
      (conjugate_nonneg_of_nonneg hρ₂ CFC.rpow_nonneg)]
  exact LinearMap.trace_tensorProduct'
    (CFC.rpow (P₁ * ρ₁ * P₁) α) (CFC.rpow (P₂ * ρ₂ * P₂) α)

/-- Tensor additivity of sandwichedRenyiDiv:
    D_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D_α(ρ₁ ‖ σ₁) + D_α(ρ₂ ‖ σ₂).

The real-valued version is defined for all PSD inputs, but agreement with the standard
finite-valued divergence for `α > 1` requires `supp ρ ⊆ supp σ`.
For example, for `α = 2`, `ρ = I₂/2`, and `σ = diag(1,0)`, we have `Q = 1/4` and
`D = log(1/4)`, but the NN version `sandwichedRenyiDivNN` is `⊤` because support
inclusion fails.

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedRenyiDiv_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂)
    (hQ₁ : (sandwichedQuasi α ρ₁ σ₁).re ≠ 0)
    (hQ₂ : (sandwichedQuasi α ρ₂ σ₂).re ≠ 0)
    (hT₁ : (Tr ρ₁).re ≠ 0) (hT₂ : (Tr ρ₂).re ≠ 0) :
    sandwichedRenyiDiv α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedRenyiDiv α ρ₁ σ₁ + sandwichedRenyiDiv α ρ₂ σ₂ := by
  have hQ₁im : (sandwichedQuasi α ρ₁ σ₁).im = 0 :=
    (Complex.nonneg_iff.mp
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).trace_nonneg).2.symm
  have hQ₂im : (sandwichedQuasi α ρ₂ σ₂).im = 0 :=
    (Complex.nonneg_iff.mp
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).trace_nonneg).2.symm
  have hT₁im : (Tr ρ₁).im = 0 :=
    (Complex.nonneg_iff.mp ((LinearMap.nonneg_iff_isPositive ρ₁).mp hρ₁).trace_nonneg).2.symm
  have hT₂im : (Tr ρ₂).im = 0 :=
    (Complex.nonneg_iff.mp ((LinearMap.nonneg_iff_isPositive ρ₂).mp hρ₂).trace_nonneg).2.symm
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_tensor α ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂,
    LinearMap.trace_tensorProduct' ρ₁ ρ₂]
  have hre_mul_Q : (sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂).re =
      (sandwichedQuasi α ρ₁ σ₁).re * (sandwichedQuasi α ρ₂ σ₂).re := by
    simp [Complex.mul_re, hQ₁im, hQ₂im]
  have hre_mul_T : ((Tr ρ₁) * (Tr ρ₂)).re = (Tr ρ₁).re * (Tr ρ₂).re := by
    simp [Complex.mul_re, hT₁im, hT₂im]
  rw [hre_mul_Q, hre_mul_T, mul_div_mul_comm, Real.log_mul
    (div_ne_zero hQ₁ hT₁) (div_ne_zero hQ₂ hT₂), mul_add]

end TensorMultiplicativity

end SandwichedRenyiRelativeEntropy

