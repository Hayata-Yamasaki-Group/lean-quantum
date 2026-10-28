/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.TraceConjPow
import Quantum.QuantumEntropy.SandwichedRenyiBase.Tensor.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.Defs


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

private lemma jc_star_toLinearMap (f : B ℋ) :
    ((star f : B ℋ) : L ℋ) = star (f : L ℋ) := by
  have h : (star f.toLinearMap).toContinuousLinearMap = star f := by
    simpa only [LinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint] using
      (LinearMap.adjoint_toContinuousLinearMap (A := f.toLinearMap))
  exact (congrArg ContinuousLinearMap.toLinearMap h).symm

private lemma jc_traceConjPow_eq_lm {p : ℝ} {B A : ℋ →L[ℂ] ℋ} (_hA : A.IsPositive) :
    traceConjPow (ℋ := ℋ) p (B : L ℋ) (A : L ℋ) =
      traceRe (ℋ := ℋ) (CFC.rpow (star B * CFC.rpow A p * B) (1 / p)) := by
  rw [traceConjPow_eq_direct]
  have h_inner :
      (star B * CFC.rpow A p * B).toLinearMap =
        star B.toLinearMap * CFC.rpow A.toLinearMap p * B.toLinearMap := by
    rw [show (star B * CFC.rpow A p * B).toLinearMap =
      (star B).toLinearMap * (CFC.rpow A p).toLinearMap * B.toLinearMap from rfl,
      jc_star_toLinearMap, TensorInternal.rpow_toLinearMap]
  change (Tr (CFC.rpow (star B.toLinearMap *
      CFC.rpow A.toLinearMap p * B.toLinearMap) (1 / p))).re =
    (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p)).toLinearMap).re
  rw [TensorInternal.rpow_toLinearMap, h_inner]

private lemma jc_quasiVar_eq_lm_direct (a : ℝ) (rho sigma H : B ℋ) :
    quasiVar a (rho : L ℋ) (sigma : L ℋ) (H : L ℋ) =
      (a : ℂ) * Tr ((H * rho : B ℋ) : L ℋ) -
        ((a - 1 : ℝ) : ℂ) * Tr
          ((CFC.rpow
            (CFC.rpow sigma ((a - 1) / (2 * a)) * H *
              CFC.rpow sigma ((a - 1) / (2 * a))) (a / (a - 1)) :
                B ℋ) : L ℋ) := by
  rw [quasiVar_eq_direct]
  change
    (a : ℂ) * Tr (H.toLinearMap * rho.toLinearMap) -
        ((a - 1 : ℝ) : ℂ) * Tr (CFC.rpow
          (CFC.rpow sigma.toLinearMap ((a - 1) / (2 * a)) * H.toLinearMap *
            CFC.rpow sigma.toLinearMap ((a - 1) / (2 * a))) (a / (a - 1))) =
      (a : ℂ) * Tr ((H * rho).toLinearMap) -
        ((a - 1 : ℝ) : ℂ) * Tr ((CFC.rpow
          (CFC.rpow sigma ((a - 1) / (2 * a)) * H *
            CFC.rpow sigma ((a - 1) / (2 * a))) (a / (a - 1))).toLinearMap)
  rw [TensorInternal.rpow_toLinearMap]
  change _ =
    (a : ℂ) * Tr (H.toLinearMap * rho.toLinearMap) -
      ((a - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        ((CFC.rpow sigma ((a - 1) / (2 * a))).toLinearMap * H.toLinearMap *
          (CFC.rpow sigma ((a - 1) / (2 * a))).toLinearMap) (a / (a - 1)))
  rw [TensorInternal.rpow_toLinearMap]

/-! ### Similarity reduction and the sigma-term variational optimizer -/
/-- Eigenvalue similarity: CC† and C†C have identical rpow traces.
    Both CC† and C†C have the same non-zero eigenvalues, so Tr(f(CC†)) = Tr(f(C†C))
    for any CFC function f (including rpow). -/
private lemma trace_rpow_star_mul_comm {C : B ℋ} (hC : IsUnit C) (q : ℝ) :
    traceRe (ℋ := ℋ) (CFC.rpow (star C * C) q) =
      traceRe (ℋ := ℋ) (CFC.rpow (C * star C) q) := by
  have h1_nn : (0 : B ℋ) ≤ 1 := zero_le_one
  have h_sCC_nn : (0 : B ℋ) ≤ star C * C := by
    have := star_left_conjugate_nonneg h1_nn C
    rwa [mul_one] at this
  have h_CsC_nn : (0 : B ℋ) ≤ C * star C := by
    have := star_left_conjugate_nonneg h1_nn (star C)
    rwa [star_star, mul_one] at this
  have h_sCC_pos := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_sCC_nn
  have h_CsC_pos := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_CsC_nn
  have h_sCC_unit : IsUnit (star C * C) := hC.star.mul hC
  have h_CsC_unit : IsUnit (C * star C) := hC.mul hC.star
  let b := stdOrthonormalBasis ℂ ℋ
  set M := LinearMap.toMatrixOrthonormal b C.toLinearMap
  have hH1 : (star M * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hH2 : (M * star M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hNN1 : 0 ≤ star M * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hNN2 : 0 ≤ M * star M := (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have h_matrix_sCC :
      LinearMap.toMatrixOrthonormal b (star C * C).toLinearMap = star M * M := by
    change LinearMap.toMatrixOrthonormal b (star C.toLinearMap * C.toLinearMap) =
      star M * M
    rw [map_mul, map_star]
  have h_matrix_CsC :
      LinearMap.toMatrixOrthonormal b (C * star C).toLinearMap = M * star M := by
    change LinearMap.toMatrixOrthonormal b (C.toLinearMap * star C.toLinearMap) =
      M * star M
    rw [map_mul, map_star]
  have h_eig : hH1.eigenvalues = hH2.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  apply congrArg Complex.re
  calc Tr (CFC.rpow (star C * C) q).toLinearMap
      = Matrix.trace (LinearMap.toMatrixOrthonormal b
          (CFC.rpow (star C * C) q).toLinearMap) :=
        tr_eq_matrix_trace_orthonormal b _
    _ = ∑ i, (((hH1.eigenvalues i) ^ q : ℝ) : ℂ) := by
        have hmap := congrArg Matrix.trace
          (toMatrixOrthonormal_rpow_pd b (star C * C) h_sCC_pos h_sCC_unit q)
        have htrace := matrix_trace_rpow_eq_sum_eigenvalues (star M * M) hH1 hNN1 q
        rw [h_matrix_sCC] at hmap
        exact hmap.trans htrace
    _ = ∑ i, (((hH2.eigenvalues i) ^ q : ℝ) : ℂ) := by rw [h_eig]
    _ = Matrix.trace (LinearMap.toMatrixOrthonormal b
        (CFC.rpow (C * star C) q).toLinearMap) := by
        have htrace := (matrix_trace_rpow_eq_sum_eigenvalues (M * star M) hH2 hNN2 q).symm
        have hmap := congrArg Matrix.trace
          (toMatrixOrthonormal_rpow_pd b (C * star C) h_CsC_pos h_CsC_unit q)
        rw [h_matrix_CsC] at hmap
        exact htrace.trans hmap.symm
    _ = Tr (CFC.rpow (C * star C) q).toLinearMap :=
        (tr_eq_matrix_trace_orthonormal b _).symm

/-- The σ-dependent part of quasiVar equals traceConjPow via eigenvalue similarity:
    Re Tr((σ^β H σ^β)^q) = traceConjPow((α-1)/α, H^{1/2}, σ)
    where β = (α-1)/(2α), q = α/(α-1). -/
private lemma quasiVar_sigma_eq_traceConjPow {α : ℝ} (hα0 : 0 < α)
    {H σ : B ℋ} (hH : H ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1))) =
      traceConjPow (ℋ := ℋ) ((α - 1) / α)
        ((CFC.rpow H (1 / 2) : B ℋ) : L ℋ) (σ : L ℋ) := by
  set P := CFC.rpow σ ((α - 1) / (2 * α))
  set Q := CFC.rpow H (1 / 2)
  set C := P * Q
  have hH_nn : (0 : B ℋ) ≤ H := ((pdSet_membership_certificate H).1 hH).nonneg
  have hσ_nn : (0 : B ℋ) ≤ σ := ((pdSet_membership_certificate σ).1 hσ).nonneg
  have hσ_pos := (ContinuousLinearMap.nonneg_iff_isPositive σ).1 hσ_nn
  have hH_unit : IsUnit H := ((pdSet_membership_certificate H).1 hH).isUnit
  have hσ_unit : IsUnit σ := ((pdSet_membership_certificate σ).1 hσ).isUnit
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ_sa : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hP_unit : IsUnit P := hσ_unit.cfcRpow _ hσ_nn
  have hQ_unit : IsUnit Q := hH_unit.cfcRpow _ hH_nn
  have hC_unit : IsUnit C := hP_unit.mul hQ_unit
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
  rw [jc_traceConjPow_eq_lm (p := (α - 1) / α) (B := Q) (A := σ) hσ_pos,
    hQ_sa.star_eq,
    show (1 : ℝ) / ((α - 1) / α) = α / (α - 1) from by field_simp,
    ← h_CsC, ← h_sCC]
  exact (trace_rpow_star_mul_comm hC_unit _).symm

section SigmaTerm

variable [Nontrivial ℋ]

/-- Concavity of the σ-term on `pdSet`: `σ ↦ Re Tr((σ^β H σ^β)^q)` is concave
    for `1/2 ≤ α`, `α ≠ 1` and `H ∈ pdSet`.
    Uses `traceConjPow_concave` and eigenvalue similarity. -/
lemma sigma_term_concaveOn {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1) (hα_ge : 1 / 2 ≤ α)
    {H : B ℋ} (hH : H ∈ pdSet (ℋ := ℋ)) :
    ConcaveOn ℝ (pdSet (ℋ := ℋ)) (fun σ =>
      traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1)))) := by
  set p := (α - 1) / α with hp_def
  have hp_ge : -1 ≤ p := by rw [hp_def]; rw [le_div_iff₀ hα0]; linarith
  have hp_le : p ≤ 1 := by rw [hp_def]; rw [div_le_one hα0]; linarith
  have hp_ne : p ≠ 0 := by rw [hp_def]; exact div_ne_zero (sub_ne_zero.mpr hα_ne1) (ne_of_gt
    hα0)
  have hH_nn : (0 : B ℋ) ≤ H := ((pdSet_membership_certificate H).1 hH).nonneg
  have hH_unit : IsUnit H := ((pdSet_membership_certificate H).1 hH).isUnit
  have hHsq_unit : IsUnit (CFC.rpow H (1 / 2)) :=
    hH_unit.cfcRpow _ hH_nn
  have h_concave := traceConjPow_concave hp_ge hp_le hp_ne
    (CFC.rpow H (1 / 2)) hHsq_unit
  have hconvex : Convex ℝ (pdSet (ℋ := ℋ)) := by
    intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSet_convexCombo hx hy hb (by linarith)
  refine ⟨hconvex, ?_⟩
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab
  simp only [smul_eq_mul]
  have h_combo : a • σ₁ + b • σ₂ ∈ pdSet (ℋ := ℋ) :=
    hconvex hσ₁ hσ₂ ha hb hab
  rw [quasiVar_sigma_eq_traceConjPow hα0 hH hσ₁,
      quasiVar_sigma_eq_traceConjPow hα0 hH hσ₂,
      quasiVar_sigma_eq_traceConjPow hα0 hH h_combo]
  exact h_concave.2 hσ₁ hσ₂ ha hb hab

end SigmaTerm

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
  exact pdSetLM_conj (hrpow_pd (pdSetLM_conj hρ hP_unit) q) hP_unit

-- The order satisfies α > 0 and α ≠ 1.
lemma quasiVarOpt_pdSetLM {α : ℝ} (_hα0 : 0 < α) (_hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVarOpt α ρ σ ∈ pdSetLM (ℋ := ℋ) := by
  rw [quasiVarOpt_eq_direct]
  have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have key := rpow_conj_pdSetLM (β := (1 - α) / (2 * α)) (q := α - 1) hρ hσ
  rwa [hP_sa.star_eq] at key

private lemma isPositive_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    A.IsPositive :=
  (LinearMap.nonneg_iff_isPositive A).mp (nonneg_of_pdSetLM hA)

lemma trace_mul_convexCombo_re (H ρ₁ ρ₂ : B ℋ) (θ : ℝ) :
    traceRe (ℋ := ℋ) (H * ((1 - θ) • ρ₁ + θ • ρ₂)) =
      (1 - θ) * traceRe (ℋ := ℋ) (H * ρ₁) +
        θ * traceRe (ℋ := ℋ) (H * ρ₂) := by
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  exact LiebAndoTrace.trace_re_convex_combo θ (H * ρ₁) (H * ρ₂)

/-! ### Joint convexity and concavity of the sandwiched quasi-entropy -/

variable [Nontrivial ℋ]
/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` on `pdSet × pdSet` for a fixed
    pd `H` and `α > 1`. The `ρ`-term is linear, the `σ`-term concave with coefficient
    `−(α−1) < 0`. (Used to extend joint convexity to the psd cone in the DPI proof.) -/
theorem quasiVar_re_jointlyConvex_pdSetLM {α : ℝ} (hα : 1 < α)
    {H : B ℋ} (hH : H ∈ pdSet (ℋ := ℋ)) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
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
  have hσ_c : σ_c ∈ pdSet (ℋ := ℋ) := pdSet_convexCombo hσ₁ hσ₂ hθ0 hθ1
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH
  have h_sigma_ineq : (1 - θ) * traceRe (ℋ := ℋ) (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2
    * α)) * H *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1))) +
      θ * traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1))) ≤
      traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ_c ((α - 1) / (2 * α)) * H *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1))) :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : traceRe (ℋ := ℋ) (H * ρ_c) =
      (1 - θ) * traceRe (ℋ := ℋ) (H * ρ₁) +
        θ * traceRe (ℋ := ℋ) (H * ρ₂) := by
    change traceRe (ℋ := ℋ) (H * ((1 - θ) • ρ₁ + θ • ρ₂)) = _
    exact trace_mul_convexCombo_re H ρ₁ ρ₂ θ
  change (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H.toLinearMap).re ≤
    (1 - θ) * (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H.toLinearMap).re +
      θ * (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H.toLinearMap).re
  rw [jc_quasiVar_eq_lm_direct α ρ_c σ_c H,
    jc_quasiVar_eq_lm_direct α ρ₁ σ₁ H,
    jc_quasiVar_eq_lm_direct α ρ₂ σ₂ H]
  simp only [Complex.sub_re, Complex.re_ofReal_mul]
  have hα1_pos : (0 : ℝ) < α - 1 := by linarith
  simp only [traceRe] at h_trace_lin h_sigma_ineq
  nlinarith [h_trace_lin, h_sigma_ineq]

/-- Joint convexity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSet × pdSet` for `α > 1`.

Source: arXiv:1306.5358v3, Proposition 3 (part 2: joint convexity), p.2. Version using the real part
of the trace on the positive definite cone.
Source: arXiv:2607.05492v1, joint convexity of the quasi-relative entropy in §4.D, p.31. Displayed
theorem `sandwichedQuasi_re_jointlyConvex` (no separate number). The displayed statement uses the
positive definite cone of linear maps (`L`); this declaration states it on the cone of bounded
operators (`B`). -/
theorem sandwichedQuasi_re_jointlyConvex {α : ℝ} (hα : 1 < α) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (fun ρ σ => (sandwichedQuasi (ℋ := ℋ) α
        (ρ : L ℋ)
        (σ : L ℋ)).re) := by
  have htoLM_pd : ∀ {A : B ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap ∈ pdSetLM (ℋ := ℋ) := by
    intro A hA
    change A.toLinearMap.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only [TensorInternal.toCLM_toLinearMap] using hA
  have htoLM_pos : ∀ {A : B ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap.IsPositive := by
    intro A hA
    exact isPositive_of_pdSetLM (htoLM_pd hA)
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSet (ℋ := ℋ) := pdSet_convexCombo hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSet (ℋ := ℋ) := pdSet_convexCombo hσ₁ hσ₂ hθ0 hθ1
  set H_c := (quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap).toContinuousLinearMap
  have hH_c_round :
      H_c.toLinearMap = quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap := by
    rfl
  have hH_c_lm_pd := quasiVarOpt_pdSetLM (by linarith : (0 : ℝ) < α) (ne_of_gt hα)
    (htoLM_pd hρ_c) (htoLM_pd hσ_c)
  have hH_c_pd : H_c ∈ pdSet (ℋ := ℋ) := by
    change (quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap).toContinuousLinearMap ∈
      pdSet (ℋ := ℋ)
    exact hH_c_lm_pd
  have hH_c_pos : H_c.toLinearMap.IsPositive := htoLM_pos hH_c_pd
  have hH_c_eq := quasiVarOpt_eq_quasi_gt hα
    (htoLM_pos hρ_c) (htoLM_pos hσ_c) (isUnit_of_pdSetLM (htoLM_pd hσ_c))
  have h_combo_eq : (sandwichedQuasi α ρ_c.toLinearMap σ_c.toLinearMap).re =
      (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re := by
    rw [hH_c_round, hH_c_eq]
  have h_ub1 : (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re ≤
      (sandwichedQuasi α ρ₁.toLinearMap σ₁.toLinearMap).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (htoLM_pos hρ₁)
      (htoLM_pos hσ₁) hH_c_pos (isUnit_of_pdSetLM (htoLM_pd hσ₁)))).1
  have h_ub2 : (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re ≤
      (sandwichedQuasi α ρ₂.toLinearMap σ₂.toLinearMap).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (htoLM_pos hρ₂)
      (htoLM_pos hσ₂) hH_c_pos (isUnit_of_pdSetLM (htoLM_pd hσ₂)))).1
  have h_convex : (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re ≤
      (1 - θ) * (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re +
        θ * (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re := by
    exact (quasiVar_re_jointlyConvex_pdSetLM hα hH_c_pd)
      hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  rw [h_combo_eq]
  calc (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re
      ≤ (1 - θ) * (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re +
          θ * (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re := h_convex
    _ ≤ (1 - θ) * (sandwichedQuasi α ρ₁.toLinearMap σ₁.toLinearMap).re +
        θ * (sandwichedQuasi α ρ₂.toLinearMap σ₂.toLinearMap).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_ub1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_ub2 hθ0

/-- Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSet × pdSet` for `1/2 ≤ α < 1`.

Source: arXiv:1306.5358v3, Proposition 3 (part 1: joint concavity), p.2. Version using the real part
of the trace on the positive definite cone.
Source: arXiv:2607.05492v1, joint concavity of the quasi-relative entropy in §4.D, p.31. Displayed
theorem `sandwichedQuasi_re_jointlyConcave` (no separate number). The displayed statement uses the
positive definite cone of linear maps (`L`); this declaration states it on the cone of bounded
operators (`B`). -/
theorem sandwichedQuasi_re_jointlyConcave {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (fun ρ σ => (sandwichedQuasi (ℋ := ℋ) α
        (ρ : L ℋ)
        (σ : L ℋ)).re) := by
  have htoLM_pd : ∀ {A : B ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap ∈ pdSetLM (ℋ := ℋ) := by
    intro A hA
    change A.toLinearMap.toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
    simpa only [TensorInternal.toCLM_toLinearMap] using hA
  have htoLM_pos : ∀ {A : B ℋ}, A ∈ pdSet (ℋ := ℋ) →
      A.toLinearMap.IsPositive := by
    intro A hA
    exact isPositive_of_pdSetLM (htoLM_pd hA)
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSet (ℋ := ℋ) := pdSet_convexCombo hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSet (ℋ := ℋ) := pdSet_convexCombo hσ₁ hσ₂ hθ0 hθ1
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_lt hα_lt
  set H_c := (quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap).toContinuousLinearMap
  have hH_c_round :
      H_c.toLinearMap = quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap := by
    rfl
  have hH_c_lm_pd := quasiVarOpt_pdSetLM hα0 hα_ne1
    (htoLM_pd hρ_c) (htoLM_pd hσ_c)
  have hH_c_pd : H_c ∈ pdSet (ℋ := ℋ) := by
    change (quasiVarOpt α ρ_c.toLinearMap σ_c.toLinearMap).toContinuousLinearMap ∈
      pdSet (ℋ := ℋ)
    exact hH_c_lm_pd
  have hH_c_pos : H_c.toLinearMap.IsPositive := htoLM_pos hH_c_pd
  have hH_c_unit : IsUnit H_c.toLinearMap := isUnit_of_pdSetLM (htoLM_pd hH_c_pd)
  have hH_c_eq := quasiVarOpt_eq_quasi_lt hα0 hα_lt
    (htoLM_pos hρ_c) (htoLM_pos hσ_c)
    (isUnit_of_pdSetLM (htoLM_pd hσ_c)) (isUnit_of_pdSetLM (htoLM_pd hρ_c))
  have h_combo_eq : (sandwichedQuasi α ρ_c.toLinearMap σ_c.toLinearMap).re =
      (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re := by
    rw [hH_c_round, hH_c_eq]
  have h_lb1 : (sandwichedQuasi α ρ₁.toLinearMap σ₁.toLinearMap).re ≤
      (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (htoLM_pos hρ₁)
      (htoLM_pos hσ₁) hH_c_pos (isUnit_of_pdSetLM (htoLM_pd hσ₁)) hH_c_unit)).1
  have h_lb2 : (sandwichedQuasi α ρ₂.toLinearMap σ₂.toLinearMap).re ≤
      (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (htoLM_pos hρ₂)
      (htoLM_pos hσ₂) hH_c_pos (isUnit_of_pdSetLM (htoLM_pd hσ₂)) hH_c_unit)).1
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH_c_pd
  have h_sigma_ineq : (1 - θ) * traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1))) +
      θ * traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1))) ≤
      traceRe (ℋ := ℋ) (CFC.rpow
        (CFC.rpow σ_c ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1))) :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : 0 ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : traceRe (ℋ := ℋ) (H_c * ρ_c) =
      (1 - θ) * traceRe (ℋ := ℋ) (H_c * ρ₁) +
        θ * traceRe (ℋ := ℋ) (H_c * ρ₂) := by
    change traceRe (ℋ := ℋ) (H_c * ((1 - θ) • ρ₁ + θ • ρ₂)) = _
    exact trace_mul_convexCombo_re H_c ρ₁ ρ₂ θ
  have h_concave :
      (1 - θ) * (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re +
        θ * (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re ≤
      (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re := by
    rw [jc_quasiVar_eq_lm_direct α ρ₁ σ₁ H_c,
      jc_quasiVar_eq_lm_direct α ρ₂ σ₂ H_c,
      jc_quasiVar_eq_lm_direct α ρ_c σ_c H_c]
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hα1_neg : α - 1 < (0 : ℝ) := by linarith
    simp only [traceRe] at h_trace_lin h_sigma_ineq
    nlinarith [h_trace_lin, h_sigma_ineq]
  rw [h_combo_eq]
  calc (1 - θ) * (sandwichedQuasi α ρ₁.toLinearMap σ₁.toLinearMap).re +
      θ * (sandwichedQuasi α ρ₂.toLinearMap σ₂.toLinearMap).re
      ≤ (1 - θ) * (quasiVar α ρ₁.toLinearMap σ₁.toLinearMap H_c.toLinearMap).re +
          θ * (quasiVar α ρ₂.toLinearMap σ₂.toLinearMap H_c.toLinearMap).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_lb1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_lb2 hθ0
    _ ≤ (quasiVar α ρ_c.toLinearMap σ_c.toLinearMap H_c.toLinearMap).re := h_concave

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

Source: arXiv:1306.3142v4, general reference (no numbered statement corresponds). -/
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

Source: arXiv:1306.3142v4, general reference (no numbered statement corresponds). -/
theorem sandwichedRenyiDiv_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedRenyiDiv α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedRenyiDiv α ρ σ := by
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_unitary_conj, trace_unitary_conj]

end UnitaryInvariance

end SandwichedRenyiRelativeEntropy
