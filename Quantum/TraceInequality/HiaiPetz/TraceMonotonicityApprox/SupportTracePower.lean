/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.MultiplicativeDomain
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.OutputSupportCorner
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.SupportPower

/-!
# Support-projected trace powers and the completed Theorem 6.3

The corner-model embedding, support projections of matrix powers, the
support-power form `multiplicativeDomainSupportTracePower`, and the completed
aggregate `supportTracePowerMonotonicity`.
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology Interval
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private noncomputable def matrixCornerModelEmbedding {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) : Mₙ model.dim →⋆ₙₐ[ℂ] Mₙ m where
  toFun := fun X => (model.toMat.symm X).1
  map_zero' := by simp
  map_add' := by
    intro X Y
    simp
  map_mul' := by
    intro X Y
    have h := congrArg Subtype.val (model.toMat_symm_mul X Y)
    simpa using h
  map_smul' := by
    intro c X
    simp
  map_star' := by
    intro X
    have h := congrArg Subtype.val (model.toMat_symm_star X)
    simpa [Matrix.star_eq_conjTranspose] using h

private theorem matrixCornerModelEmbedding_map_pow_succ {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X : Mₙ model.dim) (k : ℕ) :
    matrixCornerModelEmbedding model (X ^ (k + 1)) =
      (matrixCornerModelEmbedding model X) ^ (k + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        matrixCornerModelEmbedding model (X ^ (k + 1 + 1))
            = matrixCornerModelEmbedding model (X ^ (k + 1) * X) := by
                rw [pow_succ]
        _ = matrixCornerModelEmbedding model (X ^ (k + 1)) *
              matrixCornerModelEmbedding model X := by
                simp
        _ = (matrixCornerModelEmbedding model X) ^ (k + 1) *
              matrixCornerModelEmbedding model X := by
                rw [ih]
        _ = (matrixCornerModelEmbedding model X) ^ (k + 1 + 1) := by
              exact (pow_succ (matrixCornerModelEmbedding model X) (k + 1)).symm

private theorem matrixCornerModelEmbedding_map_polynomial_aeval_of_coeff_zero
    {m : ℕ} {P : Mₙ m} (model : MatrixCornerModel P) (q : Polynomial ℂ)
    (hq0 : q.coeff 0 = 0) (X : Mₙ model.dim) :
    matrixCornerModelEmbedding model (Polynomial.aeval X q) =
      Polynomial.aeval (matrixCornerModelEmbedding model X) q := by
  let E := matrixCornerModelEmbedding model
  let N := q.natDegree + 1
  have hleft :
      Polynomial.aeval X q = ∑ i ∈ Finset.range N, q.coeff i • X ^ i := by
    simpa [N] using
      (Polynomial.aeval_eq_sum_range' (p := q) (x := X)
        (hn := Nat.lt_succ_self q.natDegree))
  have hright :
      Polynomial.aeval (E X) q = ∑ i ∈ Finset.range N, q.coeff i • (E X) ^ i := by
    simpa [N, E] using
      (Polynomial.aeval_eq_sum_range' (p := q) (x := E X)
        (hn := Nat.lt_succ_self q.natDegree))
  calc
    E (Polynomial.aeval X q)
        = E (∑ i ∈ Finset.range N, q.coeff i • X ^ i) := by rw [hleft]
    _ = ∑ i ∈ Finset.range N, E (q.coeff i • X ^ i) := by
          rw [map_sum]
    _ = ∑ i ∈ Finset.range N, q.coeff i • E (X ^ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [E]
    _ = ∑ i ∈ Finset.range N, q.coeff i • (E X) ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          cases i with
          | zero =>
              simp [hq0]
          | succ k =>
              rw [matrixCornerModelEmbedding_map_pow_succ]
    _ = Polynomial.aeval (E X) q := by rw [hright]

private theorem matrixCornerProj_mem_self {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) :
    matrixCornerProj P X ∈ matrixCornerSubmodule P := by
  rw [mem_matrixCornerSubmodule_iff]
  rcases hP with ⟨hPidem, _⟩
  calc
    P * matrixCornerProj P X * P
        = P * (P * X * P) * P := by simp [matrixCornerProj_apply]
    _ = (P * P) * X * (P * P) := by simp [Matrix.mul_assoc]
    _ = P * X * P := by rw [hPidem]
    _ = matrixCornerProj P X := by simp [matrixCornerProj_apply]

private theorem matrixSupportSubspace_le_of_nonneg_le_smul {m : ℕ} {C D : Mₙ m}
    (hC : 0 ≤ C) (hD : 0 ≤ D) {β : ℝ} (hle : D ≤ β • C) :
    matrixSupportSubspace D ≤ matrixSupportSubspace C := by
  let T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) C
  let S : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) D
  have hker : T.ker ≤ S.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let x : Fin m → ℂ := WithLp.ofLp v
    have hxC : C.mulVec x = 0 := by
      simpa [T, x] using congrArg WithLp.ofLp hv
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
    have hDiffpsd : (β • C - D).PosSemidef := by
      exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hle)
    have hDre_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ D.mulVec x) :=
      hDpsd.re_dotProduct_nonneg x
    have hDiffre_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ (β • C - D).mulVec x) :=
      hDiffpsd.re_dotProduct_nonneg x
    have hDiffre_eq : Complex.re (star x ⬝ᵥ (β • C - D).mulVec x) =
        -Complex.re (star x ⬝ᵥ D.mulVec x) := by
      have hβCx : (β • C).mulVec x = 0 := by
        calc
          (β • C).mulVec x = (β : ℂ) • C.mulVec x := by
            simpa using (Matrix.smul_mulVec β C x)
          _ = (β : ℂ) • 0 := by rw [hxC]
          _ = 0 := by simp
      simp [Matrix.sub_mulVec, hβCx]
    have hDre_nonpos : Complex.re (star x ⬝ᵥ D.mulVec x) ≤ 0 := by
      linarith [hDiffre_nonneg]
    have hDre_zero : Complex.re (star x ⬝ᵥ D.mulVec x) = 0 :=
      le_antisymm hDre_nonpos hDre_nonneg
    have hDq_nonneg : 0 ≤ star x ⬝ᵥ D.mulVec x :=
      hDpsd.dotProduct_mulVec_nonneg x
    have hDq_zero : star x ⬝ᵥ D.mulVec x = 0 := by
      apply RCLike.ext
      · exact hDre_zero
      · exact (RCLike.nonneg_iff.mp hDq_nonneg).2
    have hxD : D.mulVec x = 0 := (hDpsd.dotProduct_mulVec_zero_iff x).1 hDq_zero
    apply WithLp.ofLp_injective
    simpa [S, x] using hxD
  have hTsymm : T.toLinearMap.IsSymmetric := by
    have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hC
    have hTpos : T.toLinearMap.IsPositive := by
      simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hCpsd)
    exact hTpos.isSymmetric
  have hSsymm : S.toLinearMap.IsSymmetric := by
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
    have hSpos : S.toLinearMap.IsPositive := by
      simpa [S, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hDpsd)
    exact hSpos.isSymmetric
  have hrange : S.range ≤ T.range :=
    (ContinuousLinearMap.ker_le_ker_iff_range_le_range hSsymm hTsymm).1 hker
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hEuclid : S (WithLp.toLp 2 y) ∈ T.range := by
    exact hrange ⟨WithLp.toLp 2 y, rfl⟩
  rcases hEuclid with ⟨u, hu⟩
  refine ⟨WithLp.ofLp u, ?_⟩
  simpa [T, S] using congrArg WithLp.ofLp hu

private theorem matrixSupportSubspace_le_of_pos_smul_le {m : ℕ} {C D : Mₙ m}
    (hC : 0 ≤ C) (hD : 0 ≤ D) {β : ℝ} (hβ : 0 < β) (hle : β • D ≤ C) :
    matrixSupportSubspace D ≤ matrixSupportSubspace C := by
  let T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) C
  let S : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) D
  have hker : T.ker ≤ S.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let x : Fin m → ℂ := WithLp.ofLp v
    have hxC : C.mulVec x = 0 := by
      simpa [T, x] using congrArg WithLp.ofLp hv
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
    have hDiffpsd : (C - β • D).PosSemidef := by
      exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hle)
    have hDre_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ D.mulVec x) :=
      hDpsd.re_dotProduct_nonneg x
    have hDiffre_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ (C - β • D).mulVec x) :=
      hDiffpsd.re_dotProduct_nonneg x
    have hDiffre_eq : Complex.re (star x ⬝ᵥ (C - β • D).mulVec x) =
        -β * Complex.re (star x ⬝ᵥ D.mulVec x) := by
      have hβDx : (β • D).mulVec x = (β : ℂ) • D.mulVec x := by
        simpa using (Matrix.smul_mulVec β D x)
      rw [Matrix.sub_mulVec, hxC, hβDx]
      simp only [zero_sub, dotProduct_neg, dotProduct_smul]
      change -Complex.re ((β : ℂ) * (star x ⬝ᵥ D.mulVec x)) =
        -β * Complex.re (star x ⬝ᵥ D.mulVec x)
      rw [Complex.re_ofReal_mul]
      ring
    have hDre_nonpos : Complex.re (star x ⬝ᵥ D.mulVec x) ≤ 0 := by
      have hnonneg_neg :
          0 ≤ -β * Complex.re (star x ⬝ᵥ D.mulVec x) := by
        simpa [hDiffre_eq] using hDiffre_nonneg
      nlinarith [hβ, hnonneg_neg]
    have hDre_zero : Complex.re (star x ⬝ᵥ D.mulVec x) = 0 :=
      le_antisymm hDre_nonpos hDre_nonneg
    have hDq_nonneg : 0 ≤ star x ⬝ᵥ D.mulVec x :=
      hDpsd.dotProduct_mulVec_nonneg x
    have hDq_zero : star x ⬝ᵥ D.mulVec x = 0 := by
      apply RCLike.ext
      · exact hDre_zero
      · exact (RCLike.nonneg_iff.mp hDq_nonneg).2
    have hxD : D.mulVec x = 0 := (hDpsd.dotProduct_mulVec_zero_iff x).1 hDq_zero
    apply WithLp.ofLp_injective
    simpa [S, x] using hxD
  have hTsymm : T.toLinearMap.IsSymmetric := by
    have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hC
    have hTpos : T.toLinearMap.IsPositive := by
      simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hCpsd)
    exact hTpos.isSymmetric
  have hSsymm : S.toLinearMap.IsSymmetric := by
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
    have hSpos : S.toLinearMap.IsPositive := by
      simpa [S, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hDpsd)
    exact hSpos.isSymmetric
  have hrange : S.range ≤ T.range :=
    (ContinuousLinearMap.ker_le_ker_iff_range_le_range hSsymm hTsymm).1 hker
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hEuclid : S (WithLp.toLp 2 y) ∈ T.range := by
    exact hrange ⟨WithLp.toLp 2 y, rfl⟩
  rcases hEuclid with ⟨u, hu⟩
  refine ⟨WithLp.ofLp u, ?_⟩
  simpa [T, S] using congrArg WithLp.ofLp hu

private theorem matrixSupportProj_eq_of_supportSubspace_eq {m : ℕ} {C D : Mₙ m}
    (h : matrixSupportSubspace C = matrixSupportSubspace D) :
    matrixSupportProj C = matrixSupportProj D := by
  apply Matrix.toEuclideanLin.injective
  rw [matrixSupportProj_toEuclideanLin, matrixSupportProj_toEuclideanLin]
  simp [h]

private theorem matrixSupportProj_image_posDef_eq_outputSupportProj
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : Matrix.PosDef A) :
    matrixSupportProj (Φ A) = outputSupportProj Φ := by
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hΦAnonneg : 0 ≤ Φ A := hPos hAnonneg
  have hΦ1nonneg : 0 ≤ Φ (1 : Mₙ n) := by
    exact hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hsub_forward : matrixSupportSubspace (Φ A) ≤ matrixSupportSubspace (Φ (1 : Mₙ n)) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have hmem := map_mem_outputCorner Φ hPos A
    have hPleft : outputSupportProj Φ * Φ A = Φ A := by
      exact OutputSupportProj.left_mul_eq_self_of_mem (Φ := Φ) hmem
    have hxfix : (outputSupportProj Φ).mulVec ((Φ A).mulVec y) = (Φ A).mulVec y := by
      simpa [Matrix.mulVec_mulVec] using congrArg (fun M : Mₙ m => M.mulVec y) hPleft
    exact (OutputSupportProj.mulVec_eq_self_iff Φ ((Φ A).mulVec y)).1 hxfix
  rcases Matrix.PosDef.exists_pos_algebraMap_le hA with ⟨c, hc, hc_le⟩
  have hdiff_nonneg : 0 ≤ A - algebraMap ℝ (Mₙ n) c := sub_nonneg.mpr hc_le
  have hΦdiff : 0 ≤ Φ (A - algebraMap ℝ (Mₙ n) c) := hPos hdiff_nonneg
  have hsub : 0 ≤ Φ A - c • Φ (1 : Mₙ n) := by
    rw [Algebra.algebraMap_eq_smul_one, Φ.map_sub, Φ.map_smul_of_tower] at hΦdiff
    exact hΦdiff
  have hle_c : c • Φ (1 : Mₙ n) ≤ Φ A := sub_nonneg.mp hsub
  have hsub_backward : matrixSupportSubspace (Φ (1 : Mₙ n)) ≤ matrixSupportSubspace (Φ A) :=
    matrixSupportSubspace_le_of_pos_smul_le hΦAnonneg hΦ1nonneg hc hle_c
  apply matrixSupportProj_eq_of_supportSubspace_eq
  exact le_antisymm hsub_forward hsub_backward

private theorem
    matrixCornerModelEmbedding_supportMatrixPower_outputSupportReducedMap_eq_supportMatrixPower
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) :
    matrixCornerModelEmbedding (outputSupportMatrixCornerModel Φ)
        (supportMatrixPower p (outputSupportReducedMap Φ hPos A)) =
      supportMatrixPower p (Φ A) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  let raw : Mₙ m := Φ A
  let red : Mₙ model.dim := Ψ A
  have hrawNonneg : 0 ≤ raw := by
    exact hPos hA
  have hΨpos : IsPositiveMap Ψ := by
    simpa [Ψ, model] using outputSupportReducedMap_isPositiveMap Φ hPos
  have hredNonneg : 0 ≤ red := hΨpos hA
  let rawEig : Fin m → ℝ :=
    fun i => (Matrix.nonneg_iff_posSemidef.mp hrawNonneg).1.eigenvalues i
  let redEig : Fin model.dim → ℝ :=
    fun i => (Matrix.nonneg_iff_posSemidef.mp hredNonneg).1.eigenvalues i
  let s : Finset ℝ :=
    insert 0 ((Finset.univ.image rawEig) ∪ (Finset.univ.image redEig))
  let q : Polynomial ℝ := Lagrange.interpolate s id (fun x : ℝ => supportPowerCoeff p x)
  have hvs : Set.InjOn id (s : Set ℝ) := by
    intro x hx y hy hxy
    exact hxy
  have hq_eval_mem {x : ℝ} (hx : x ∈ s) :
      Polynomial.eval x q = supportPowerCoeff p x := by
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun x : ℝ => supportPowerCoeff p x)
        hvs hx)
  have hq_raw : ∀ i : Fin m,
      Polynomial.eval (rawEig i) q = supportPowerCoeff p (rawEig i) := by
    intro i
    exact hq_eval_mem (by simp [s, rawEig])
  have hq_red : ∀ i : Fin model.dim,
      Polynomial.eval (redEig i) q = supportPowerCoeff p (redEig i) := by
    intro i
    exact hq_eval_mem (by simp [s, redEig])
  have hq0 : (Polynomial.map (algebraMap ℝ ℂ) q).coeff 0 = 0 := by
    have hqeval0 : Polynomial.eval 0 q = supportPowerCoeff p 0 :=
      hq_eval_mem (by simp [s])
    have hqcoeff0 : q.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa [supportPowerCoeff] using hqeval0
    simp [Polynomial.coeff_map, hqcoeff0]
  have hrawpoly :
      supportMatrixPower p raw =
        Polynomial.aeval raw (Polynomial.map (algebraMap ℝ ℂ) q) := by
    exact
      supportMatrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
        (A := raw) hrawNonneg p q hq_raw
  have hredpoly :
      supportMatrixPower p red =
        Polynomial.aeval red (Polynomial.map (algebraMap ℝ ℂ) q) := by
    exact
      supportMatrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
        (A := red) hredNonneg p q hq_red
  calc
    matrixCornerModelEmbedding model (supportMatrixPower p red)
        = matrixCornerModelEmbedding model
            (Polynomial.aeval red (Polynomial.map (algebraMap ℝ ℂ) q)) := by
            rw [hredpoly]
    _ = Polynomial.aeval (matrixCornerModelEmbedding model red)
          (Polynomial.map (algebraMap ℝ ℂ) q) := by
          exact matrixCornerModelEmbedding_map_polynomial_aeval_of_coeff_zero model
            (Polynomial.map (algebraMap ℝ ℂ) q) hq0 red
    _ = Polynomial.aeval raw (Polynomial.map (algebraMap ℝ ℂ) q) := by
          have hEred : matrixCornerModelEmbedding model red = raw := by
            have hred_def : red = model.toMat ⟨raw, map_mem_outputCorner Φ hPos A⟩ := by
              simp [model, Ψ, red, raw]
            rw [hred_def]
            change (model.toMat.symm
              (model.toMat ⟨raw, map_mem_outputCorner Φ hPos A⟩)).1 = raw
            simp
          rw [hEred]
    _ = supportMatrixPower p raw := by
          rw [hrawpoly]

private theorem supportMatrixPower_image_nonneg_mem_outputCorner
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPower p (Φ A) ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  let red : Mₙ model.dim := Ψ A
  have hmem :
      matrixCornerModelEmbedding model (supportMatrixPower p red) ∈
        matrixCornerSubmodule (outputSupportProj Φ) := by
    exact (model.toMat.symm (supportMatrixPower p red)).2
  have htransport :
      matrixCornerModelEmbedding model (supportMatrixPower p red) =
        supportMatrixPower p (Φ A) := by
    simpa [model, Ψ, red] using
      matrixCornerModelEmbedding_supportMatrixPower_outputSupportReducedMap_eq_supportMatrixPower
        Φ hPos hA p
  rw [htransport] at hmem
  exact hmem

private theorem supportMatrixPower_outputSupportReducedMap_toMat_of_nonneg
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) :
    (outputSupportMatrixCornerModel Φ).toMat
        ⟨supportMatrixPower p (Φ A),
          supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hA p⟩ =
      supportMatrixPower p (outputSupportReducedMap Φ hPos A) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  change model.toMat
      ⟨supportMatrixPower p (Φ A),
        supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hA p⟩ =
    supportMatrixPower p (outputSupportReducedMap Φ hPos A)
  apply model.toMat.symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  change supportMatrixPower p (Φ A) =
    matrixCornerModelEmbedding model
      (supportMatrixPower p (outputSupportReducedMap Φ hPos A))
  rw [matrixCornerModelEmbedding_supportMatrixPower_outputSupportReducedMap_eq_supportMatrixPower
    Φ hPos hA p]

private theorem supportMatrixPower_image_posDef_mem_outputCorner
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : Matrix.PosDef A) (p : ℝ) :
    supportMatrixPower p (Φ A) ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  have hΦAnonneg : 0 ≤ Φ A := hPos (Matrix.PosDef.nonneg hA)
  have hcorner :=
    matrixSupportProj_mul_supportMatrixPower_mul_matrixSupportProj_nonneg
      (A := Φ A) hΦAnonneg p
  simpa [matrixSupportProj_image_posDef_eq_outputSupportProj Φ hPos hA] using hcorner

private theorem matrixCornerModelEmbedding_matrixPower_outputSupportReducedMap_eq_supportMatrixPower
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : Matrix.PosDef A) (p : ℝ) :
    matrixCornerModelEmbedding (outputSupportMatrixCornerModel Φ)
        (matrixPower p (outputSupportReducedMap Φ hPos A)) =
      supportMatrixPower p (Φ A) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  let raw : Mₙ m := Φ A
  let red : Mₙ model.dim := Ψ A
  have hrawNonneg : 0 ≤ raw := by
    exact hPos (Matrix.PosDef.nonneg hA)
  have hΨpos : IsPositiveMap Ψ := by
    simpa [Ψ, model] using outputSupportReducedMap_isPositiveMap Φ hPos
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := by
    simpa [Ψ, model] using outputSupportReducedMap_one_posDef Φ hPos
  have hredPos : Matrix.PosDef red := by
    exact Matrix.PosDef.image_of_isPositiveMap Ψ hΨpos hA hΨ1
  have hredNonneg : 0 ≤ red := Matrix.PosDef.nonneg hredPos
  let rawEig : Fin m → ℝ :=
    fun i => (Matrix.nonneg_iff_posSemidef.mp hrawNonneg).1.eigenvalues i
  let redEig : Fin model.dim → ℝ :=
    fun i => (Matrix.nonneg_iff_posSemidef.mp hredNonneg).1.eigenvalues i
  let s : Finset ℝ :=
    insert 0 ((Finset.univ.image rawEig) ∪ (Finset.univ.image redEig))
  let q : Polynomial ℝ := Lagrange.interpolate s id (fun x : ℝ => supportPowerCoeff p x)
  have hvs : Set.InjOn id (s : Set ℝ) := by
    intro x hx y hy hxy
    exact hxy
  have hq_eval_mem {x : ℝ} (hx : x ∈ s) :
      Polynomial.eval x q = supportPowerCoeff p x := by
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun x : ℝ => supportPowerCoeff p x)
        hvs hx)
  have hq_raw : ∀ i : Fin m,
      Polynomial.eval (rawEig i) q = supportPowerCoeff p (rawEig i) := by
    intro i
    exact hq_eval_mem (by simp [s, rawEig])
  have hredPosDef : red.PosDef := hredPos
  have hq_red : ∀ i : Fin model.dim,
      Polynomial.eval (redEig i) q = powerFn p (redEig i) := by
    intro i
    have hqi : Polynomial.eval (redEig i) q = supportPowerCoeff p (redEig i) :=
      hq_eval_mem (by simp [s, redEig])
    have hpos : 0 < redEig i := by
      simpa [redEig] using
        (Matrix.nonneg_iff_posSemidef.mp hredNonneg).1.posDef_iff_eigenvalues_pos.mp
          hredPosDef i
    have hne : redEig i ≠ 0 := ne_of_gt hpos
    simpa [supportPowerCoeff, powerFn, hne] using hqi
  have hq0 : (Polynomial.map (algebraMap ℝ ℂ) q).coeff 0 = 0 := by
    have hqeval0 : Polynomial.eval 0 q = supportPowerCoeff p 0 :=
      hq_eval_mem (by simp [s])
    have hqcoeff0 : q.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa [supportPowerCoeff] using hqeval0
    simp [Polynomial.coeff_map, hqcoeff0]
  have hrawpoly :
      supportMatrixPower p raw =
        Polynomial.aeval raw (Polynomial.map (algebraMap ℝ ℂ) q) := by
    exact
      supportMatrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
        (A := raw) hrawNonneg p q hq_raw
  have hredpoly :
      matrixPower p red =
        Polynomial.aeval red (Polynomial.map (algebraMap ℝ ℂ) q) := by
    exact
      matrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
        (A := red) hredNonneg p q hq_red
  calc
    matrixCornerModelEmbedding model (matrixPower p red)
        = matrixCornerModelEmbedding model
            (Polynomial.aeval red (Polynomial.map (algebraMap ℝ ℂ) q)) := by
            rw [hredpoly]
    _ = Polynomial.aeval (matrixCornerModelEmbedding model red)
          (Polynomial.map (algebraMap ℝ ℂ) q) := by
          exact matrixCornerModelEmbedding_map_polynomial_aeval_of_coeff_zero model
            (Polynomial.map (algebraMap ℝ ℂ) q) hq0 red
    _ = Polynomial.aeval raw (Polynomial.map (algebraMap ℝ ℂ) q) := by
          have hEred : matrixCornerModelEmbedding model red = raw := by
            have hred_def : red = model.toMat ⟨raw, map_mem_outputCorner Φ hPos A⟩ := by
              simp [model, Ψ, red, raw]
            rw [hred_def]
            change (model.toMat.symm (model.toMat ⟨raw, map_mem_outputCorner Φ hPos A⟩)).1 =
              raw
            simp
          rw [hEred]
    _ = supportMatrixPower p raw := by
          rw [hrawpoly]

private theorem supportMatrixPower_outputSupportReducedMap_toMat
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A : Mₙ n} (hA : Matrix.PosDef A) (p : ℝ) :
    (outputSupportMatrixCornerModel Φ).toMat
        ⟨supportMatrixPower p (Φ A),
          supportMatrixPower_image_posDef_mem_outputCorner Φ hPos hA p⟩ =
      matrixPower p (outputSupportReducedMap Φ hPos A) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  change model.toMat
      ⟨supportMatrixPower p (Φ A),
        supportMatrixPower_image_posDef_mem_outputCorner Φ hPos hA p⟩ =
    matrixPower p (outputSupportReducedMap Φ hPos A)
  apply model.toMat.symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  change supportMatrixPower p (Φ A) =
    matrixCornerModelEmbedding model (matrixPower p (outputSupportReducedMap Φ hPos A))
  rw [matrixCornerModelEmbedding_matrixPower_outputSupportReducedMap_eq_supportMatrixPower
    Φ hPos hA p]

private theorem trace_mul_cornerProj_eq_of_mem {m : ℕ} {P X SA SB : Mₙ m}
    (hP : IsMatrixProj P) (hSA : SA ∈ matrixCornerSubmodule P)
    (hSB : SB ∈ matrixCornerSubmodule P) :
    Matrix.trace (Matrix.conjTranspose X * SA * X * SB) =
      Matrix.trace
        (Matrix.conjTranspose (matrixCornerProj P X) * SA * matrixCornerProj P X * SB) := by
  rcases hP with ⟨hPidem, hPselfAdj⟩
  have hPstar : Matrix.conjTranspose P = P := by
    simpa [Matrix.star_eq_conjTranspose] using hPselfAdj.star_eq
  have hSAleft : P * SA = SA :=
    matrixCornerSubmodule.left_fix ⟨hPidem, hPselfAdj⟩ hSA
  have hSAright : SA * P = SA :=
    matrixCornerSubmodule.right_fix ⟨hPidem, hPselfAdj⟩ hSA
  have hSBleft : P * SB = SB :=
    matrixCornerSubmodule.left_fix ⟨hPidem, hPselfAdj⟩ hSB
  have hSBright : SB * P = SB :=
    matrixCornerSubmodule.right_fix ⟨hPidem, hPselfAdj⟩ hSB
  let Y : Mₙ m := Matrix.conjTranspose X * SA * X * SB
  have hYright : Y * P = Y := by
    simp [Y, hSBright, Matrix.mul_assoc]
  have hmid : SA * (P * (X * SB)) = SA * (X * SB) := by
    rw [← Matrix.mul_assoc, hSAright]
  have hcorner :
      Matrix.conjTranspose (matrixCornerProj P X) * SA * matrixCornerProj P X * SB =
        P * Y := by
    simp [Y, matrixCornerProj_apply, Matrix.conjTranspose_mul, hPstar,
      hSAleft, hSBleft, hmid, Matrix.mul_assoc]
  calc
    Matrix.trace Y = Matrix.trace (Y * P) := by rw [hYright]
    _ = Matrix.trace (P * Y) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace
        (Matrix.conjTranspose (matrixCornerProj P X) * SA * matrixCornerProj P X * SB) := by
          rw [hcorner]

/-- A support-power trace expression on two positive images of `Φ` only depends on the
compression of its test matrix to the output support of `Φ`.  The exponents are arbitrary, so
this single producer covers the direct, inverse, and multiplicative-domain ranges.
Source: Hiai, Theorem 6.3 (output-support reduction). -/
theorem supportPowerTrace_outputSupport_cornerProj_eq
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {r s : ℝ} {A B : Mₙ n} {X : Mₙ m} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportPowerTrace r s (Φ A) (Φ B) X =
      supportPowerTrace r s (Φ A) (Φ B)
        (matrixCornerProj (outputSupportProj Φ) X) := by
  have hP : IsMatrixProj (outputSupportProj Φ) := OutputSupportProj.isProj Φ
  have hSA :
      supportMatrixPower r (Φ A) ∈ matrixCornerSubmodule (outputSupportProj Φ) :=
    supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hA r
  have hSB :
      supportMatrixPower s (Φ B) ∈ matrixCornerSubmodule (outputSupportProj Φ) :=
    supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hB s
  have htrace :=
    trace_mul_cornerProj_eq_of_mem (P := outputSupportProj Φ) (X := X)
      (SA := supportMatrixPower r (Φ A)) (SB := supportMatrixPower s (Φ B))
      hP hSA hSB
  simpa [supportPowerTrace] using congrArg Complex.re htrace

private theorem supportPowerTrace_outputSupportReducedMap_toMat_eq_of_nonneg
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {r s : ℝ} {A B : Mₙ n} {X : Mₙ m} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportPowerTrace r s (Φ A) (Φ B) X =
      supportPowerTrace r s
        (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B)
        ((outputSupportMatrixCornerModel Φ).toMat
          ⟨matrixCornerProj (outputSupportProj Φ) X,
            matrixCornerProj_mem_self (OutputSupportProj.isProj Φ)⟩) := by
  let P : Mₙ m := outputSupportProj Φ
  let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  have hP : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  let Xcorner : matrixCornerSubmodule P :=
    ⟨matrixCornerProj P X, matrixCornerProj_mem_self hP⟩
  let SAcorner : matrixCornerSubmodule P :=
    ⟨supportMatrixPower r (Φ A),
      by simpa [P] using
        supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hA r⟩
  let SBcorner : matrixCornerSubmodule P :=
    ⟨supportMatrixPower s (Φ B),
      by simpa [P] using
        supportMatrixPower_image_nonneg_mem_outputCorner Φ hPos hB s⟩
  let SAXcorner : matrixCornerSubmodule P :=
    ⟨SAcorner.1 * Xcorner.1, model.mul_mem_corner SAcorner Xcorner⟩
  let Vcorner : matrixCornerSubmodule P :=
    ⟨SAXcorner.1 * SBcorner.1, model.mul_mem_corner SAXcorner SBcorner⟩
  have hSAmap : model.toMat SAcorner = supportMatrixPower r (Ψ A) := by
    simpa [model, Ψ, P, SAcorner] using
      supportMatrixPower_outputSupportReducedMap_toMat_of_nonneg Φ hPos hA r
  have hSBmap : model.toMat SBcorner = supportMatrixPower s (Ψ B) := by
    simpa [model, Ψ, P, SBcorner] using
      supportMatrixPower_outputSupportReducedMap_toMat_of_nonneg Φ hPos hB s
  have hVmap :
      model.toMat Vcorner =
        supportMatrixPower r (Ψ A) * model.toMat Xcorner *
          supportMatrixPower s (Ψ B) := by
    calc
      model.toMat Vcorner = model.toMat SAXcorner * model.toMat SBcorner := by
        exact model.map_mul SAXcorner SBcorner
      _ = (model.toMat SAcorner * model.toMat Xcorner) * model.toMat SBcorner := by
        rw [← model.map_mul SAcorner Xcorner]
      _ = supportMatrixPower r (Ψ A) * model.toMat Xcorner *
            supportMatrixPower s (Ψ B) := by
        rw [hSAmap, hSBmap]
  have hrawCorner :
      Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower r (Φ A) * X *
            supportMatrixPower s (Φ B)) =
        Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
    simpa [P, Xcorner, SAcorner, SBcorner] using
      trace_mul_cornerProj_eq_of_mem (P := P) (X := X)
        (SA := supportMatrixPower r (Φ A)) (SB := supportMatrixPower s (Φ B))
        hP SAcorner.2 SBcorner.2
  have hredCorner :
      Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            supportMatrixPower r (Ψ A) * model.toMat Xcorner *
              supportMatrixPower s (Ψ B)) =
        Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
    calc
      Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            supportMatrixPower r (Ψ A) * model.toMat Xcorner *
              supportMatrixPower s (Ψ B)) =
        Matrix.trace (star (model.toMat Xcorner) * model.toMat Vcorner) := by
          rw [hVmap]
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = Matrix.trace (star Xcorner.1 * Vcorner.1) :=
        model.preservesTraceMul Xcorner Vcorner
      _ = Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
          simp [Vcorner, SAXcorner, SAcorner, SBcorner, Matrix.star_eq_conjTranspose,
            Matrix.mul_assoc]
  have htrace :
      Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower r (Φ A) * X *
            supportMatrixPower s (Φ B)) =
        Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            supportMatrixPower r (Ψ A) * model.toMat Xcorner *
              supportMatrixPower s (Ψ B)) :=
    hrawCorner.trans hredCorner.symm
  simpa [supportPowerTrace, P, model, Ψ, Xcorner] using congrArg Complex.re htrace

/-- PSD output-support reduction for the support-convention Lieb trace power.  Both the original
output and the reduced model retain `supportMatrixPower`, including at the semidefinite
endpoints.
Source: Hiai, Theorem 6.3(1) (output-support reduction). -/
theorem supportLiebTracePower_outputSupportReducedMap_toMat_eq_of_nonneg
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {p : ℝ} {A B : Mₙ n} {X : Mₙ m} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportLiebTracePower p (Φ A) (Φ B) X =
      supportLiebTracePower p
        (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B)
        ((outputSupportMatrixCornerModel Φ).toMat
          ⟨matrixCornerProj (outputSupportProj Φ) X,
            matrixCornerProj_mem_self (OutputSupportProj.isProj Φ)⟩) := by
  simpa [supportLiebTracePower] using
    supportPowerTrace_outputSupportReducedMap_toMat_eq_of_nonneg
      (Φ := Φ) hPos (r := p) (s := 1 - p) (A := A) (B := B) (X := X) hA hB

/-- The inverse trace-power expression with the book's support convention on zero eigenvalues.
Source: Hiai, Theorem 6.3(2). -/
noncomputable def supportInverseTracePower {n : ℕ}
    (p : ℝ) (A B X : Mₙ n) : ℝ :=
  supportPowerTrace (-p) (p - 1) A B X

/-- On positive-definite inputs, the support-convention inverse trace power is the ordinary
inverse trace power.
Source: Hiai, Theorem 6.3(2). -/
theorem supportInverseTracePower_eq_inverseTracePower_of_posDef
    {n : ℕ} {p : ℝ} {A B X : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    supportInverseTracePower p A B X = inverseTracePower p A B X := by
  rw [supportInverseTracePower, supportPowerTrace, inverseTracePower, powerTrace,
    supportMatrixPower_eq_matrixPower_of_posDef (-p) hA,
    supportMatrixPower_eq_matrixPower_of_posDef (p - 1) hB]

/-- Output-support reduction for the support-convention inverse trace power.  The input test
matrix is sent by `Φ`, and its corner coordinate is exactly the reduced-map image.
Source: Hiai, Theorem 6.3(2) (output-support reduction). -/
theorem supportInverseTracePower_outputSupportReducedMap_eq_of_nonneg
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {p : ℝ} {A B X : Mₙ n} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportInverseTracePower p (Φ A) (Φ B) (Φ X) =
      supportInverseTracePower p
        (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B)
        (outputSupportReducedMap Φ hPos X) := by
  simpa [supportInverseTracePower, phi_image_eq_outputCornerProj Φ hPos X] using
    supportPowerTrace_outputSupportReducedMap_toMat_eq_of_nonneg
      (Φ := Φ) hPos (r := -p) (s := p - 1) (A := A) (B := B) (X := Φ X) hA hB

/-- Alias of `directSupportTracePowerOutputSupport`, retained as the registered
output-support-model producer for the original-output-space surface. -/
alias directSupportTracePowerOutputSupportModel := directSupportTracePowerOutputSupport

/-- Alias of `inverseTracePowerOutputSupport`, retained as the registered
output-support-model producer for the original-output-space surface. -/
alias inverseTracePowerOutputSupportModel := inverseTracePowerOutputSupport

private theorem supportLiebTracePower_outputSupportReducedMap_toMat_eq
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {p : ℝ} {A B : Mₙ n} {X : Mₙ m}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    supportLiebTracePower p (Φ A) (Φ B) X =
      liebTracePower p (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B)
        ((outputSupportMatrixCornerModel Φ).toMat
          ⟨matrixCornerProj (outputSupportProj Φ) X,
            matrixCornerProj_mem_self (OutputSupportProj.isProj Φ)⟩) := by
  let P : Mₙ m := outputSupportProj Φ
  let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  have hP : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  let Xcorner : matrixCornerSubmodule P :=
    ⟨matrixCornerProj P X, matrixCornerProj_mem_self hP⟩
  let SAcorner : matrixCornerSubmodule P :=
    ⟨supportMatrixPower p (Φ A),
      by simpa [P] using supportMatrixPower_image_posDef_mem_outputCorner Φ hPos hA p⟩
  let SBcorner : matrixCornerSubmodule P :=
    ⟨supportMatrixPower (1 - p) (Φ B),
      by simpa [P] using supportMatrixPower_image_posDef_mem_outputCorner Φ hPos hB (1 - p)⟩
  let SAXcorner : matrixCornerSubmodule P :=
    ⟨SAcorner.1 * Xcorner.1, model.mul_mem_corner SAcorner Xcorner⟩
  let Vcorner : matrixCornerSubmodule P :=
    ⟨SAXcorner.1 * SBcorner.1, model.mul_mem_corner SAXcorner SBcorner⟩
  have hSAmap : model.toMat SAcorner = matrixPower p (Ψ A) := by
    simpa [model, Ψ, P, SAcorner] using
      supportMatrixPower_outputSupportReducedMap_toMat Φ hPos hA p
  have hSBmap : model.toMat SBcorner = matrixPower (1 - p) (Ψ B) := by
    simpa [model, Ψ, P, SBcorner] using
      supportMatrixPower_outputSupportReducedMap_toMat Φ hPos hB (1 - p)
  have hVmap :
      model.toMat Vcorner =
        matrixPower p (Ψ A) * model.toMat Xcorner * matrixPower (1 - p) (Ψ B) := by
    calc
      model.toMat Vcorner = model.toMat SAXcorner * model.toMat SBcorner := by
        exact model.map_mul SAXcorner SBcorner
      _ = (model.toMat SAcorner * model.toMat Xcorner) * model.toMat SBcorner := by
        rw [← model.map_mul SAcorner Xcorner]
      _ = matrixPower p (Ψ A) * model.toMat Xcorner * matrixPower (1 - p) (Ψ B) := by
        rw [hSAmap, hSBmap]
  have hrawCorner :
      Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower p (Φ A) * X *
            supportMatrixPower (1 - p) (Φ B)) =
        Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
    simpa [P, Xcorner, SAcorner, SBcorner] using
      trace_mul_cornerProj_eq_of_mem (P := P) (X := X)
        (SA := supportMatrixPower p (Φ A))
        (SB := supportMatrixPower (1 - p) (Φ B)) hP SAcorner.2 SBcorner.2
  have hredCorner :
      Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            matrixPower p (Ψ A) * model.toMat Xcorner * matrixPower (1 - p) (Ψ B)) =
        Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
    calc
      Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            matrixPower p (Ψ A) * model.toMat Xcorner * matrixPower (1 - p) (Ψ B)) =
        Matrix.trace (star (model.toMat Xcorner) * model.toMat Vcorner) := by
          rw [hVmap]
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = Matrix.trace (star Xcorner.1 * Vcorner.1) := model.preservesTraceMul Xcorner Vcorner
      _ = Matrix.trace
          (Matrix.conjTranspose Xcorner.1 * SAcorner.1 * Xcorner.1 * SBcorner.1) := by
          simp [Vcorner, SAXcorner, SAcorner, SBcorner, Matrix.star_eq_conjTranspose,
            Matrix.mul_assoc]
  have htrace :
      Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower p (Φ A) * X *
            supportMatrixPower (1 - p) (Φ B)) =
        Matrix.trace
          (Matrix.conjTranspose (model.toMat Xcorner) *
            matrixPower p (Ψ A) * model.toMat Xcorner * matrixPower (1 - p) (Ψ B)) :=
    hrawCorner.trans hredCorner.symm
  simpa [supportLiebTracePower, supportPowerTrace, liebTracePower, powerTrace,
    P, model, Ψ, Xcorner] using congrArg Complex.re htrace

private theorem hsAdjoint_outputSupportReducedMap_toMat_corner_eq
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    (Xcorner : matrixCornerSubmodule (outputSupportProj Φ)) :
    (hsAdjoint (outputSupportReducedMap Φ hPos))
        ((outputSupportMatrixCornerModel Φ).toMat Xcorner) =
      (hsAdjoint Φ) Xcorner.1 := by
  rw [outputSupportReducedMap_hsAdjoint_apply]
  simp

private theorem hsAdjoint_outputSupportReducedMap_toMat_matrixCornerProj_eq
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (X : Mₙ m)
    (Xcorner : matrixCornerSubmodule (outputSupportProj Φ))
    (hXcorner : Xcorner.1 = matrixCornerProj (outputSupportProj Φ) X) :
    (hsAdjoint (outputSupportReducedMap Φ hPos))
        ((outputSupportMatrixCornerModel Φ).toMat Xcorner) =
      (hsAdjoint Φ) X := by
  rw [hsAdjoint_outputSupportReducedMap_toMat_corner_eq Φ hPos Xcorner]
  rw [hXcorner]
  exact hsAdjoint_matrixCornerProj_eq Φ hPos X

/-- Original-output-space inverse support trace-power surface for Hiai Theorem 6.3(2).
Source: Hiai, Theorem 6.3(2). -/
def InverseSupportTracePower : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    supportInverseTracePower p (Φ A) (Φ B) (Φ X) ≤
      supportInverseTracePower p A B X

/-- Original-output-space direct support trace-power surface for Hiai Theorem 6.3(1).
Source: Hiai, Theorem 6.3(1). -/
def DirectSupportTracePower : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ}
      {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    0 ≤ A →
    0 ≤ B →
    supportLiebTracePower p A B ((hsAdjoint Φ) X) ≤
      supportLiebTracePower p (Φ A) (Φ B) X

/-- Original-output-space direct support trace-power theorem, transported from the chosen
output-support matrix model.
Source: Hiai, Theorem 6.3(1). -/
theorem directSupportTracePower : DirectSupportTracePower := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB
  let P : Mₙ m := outputSupportProj Φ
  let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  have hP : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  let Xcorner : matrixCornerSubmodule P :=
    ⟨matrixCornerProj P X, matrixCornerProj_mem_self hP⟩
  let Xc : Mₙ model.dim := model.toMat Xcorner
  have hXcorner : Xcorner.1 = matrixCornerProj (outputSupportProj Φ) X := by
    rfl
  have hred :
      supportLiebTracePower p A B ((hsAdjoint Ψ) Xc) ≤
        supportLiebTracePower p (Ψ A) (Ψ B) Xc := by
    simpa [P, model, Ψ, Xc] using
      (directSupportTracePowerOutputSupportModel Φ
        (p := p) (A := A) (B := B) hp hPos hTrace hSch hA hB (X := Xc))
  have hleft :
      supportLiebTracePower p (Φ A) (Φ B) X =
        supportLiebTracePower p (Ψ A) (Ψ B) Xc := by
    simpa [P, model, Ψ, Xcorner, Xc] using
      supportLiebTracePower_outputSupportReducedMap_toMat_eq_of_nonneg
        (Φ := Φ) hPos (p := p) (A := A) (B := B) (X := X) hA hB
  have hadj :
      (hsAdjoint Ψ) Xc = (hsAdjoint Φ) X := by
    simpa [P, model, Ψ, Xc] using
      hsAdjoint_outputSupportReducedMap_toMat_matrixCornerProj_eq
        (Φ := Φ) hPos X Xcorner hXcorner
  calc
    supportLiebTracePower p A B ((hsAdjoint Φ) X) =
        supportLiebTracePower p A B ((hsAdjoint Ψ) Xc) := by rw [hadj]
    _ ≤ supportLiebTracePower p (Ψ A) (Ψ B) Xc := hred
    _ = supportLiebTracePower p (Φ A) (Φ B) X := hleft.symm

/-- Original-output-space inverse support trace-power theorem, transported from the chosen
output-support matrix model.
Source: Hiai, Theorem 6.3(2). -/
theorem inverseSupportTracePower : InverseSupportTracePower := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  have hΨA : Matrix.PosDef (Ψ A) :=
    Matrix.PosDef.image_of_isPositiveMap Ψ hΨpos hA hΨ1
  have hΨB : Matrix.PosDef (Ψ B) :=
    Matrix.PosDef.image_of_isPositiveMap Ψ hΨpos hB hΨ1
  have htransport :
      supportInverseTracePower p (Φ A) (Φ B) (Φ X) =
        supportInverseTracePower p (Ψ A) (Ψ B) (Ψ X) := by
    simpa [Ψ] using
      supportInverseTracePower_outputSupportReducedMap_eq_of_nonneg
        (Φ := Φ) hPos (p := p) (A := A) (B := B) (X := X)
          (Matrix.PosDef.nonneg hA) (Matrix.PosDef.nonneg hB)
  have hred :
      inverseTracePower p (Ψ A) (Ψ B) (Ψ X) ≤ inverseTracePower p A B X := by
    simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
      MatrixCornerModel.transportMap] using
      (inverseTracePowerOutputSupportModel Φ
        (p := p) (A := A) (B := B) (X := X) hp hPos hTrace hSch hA hB)
  calc
    supportInverseTracePower p (Φ A) (Φ B) (Φ X) =
        supportInverseTracePower p (Ψ A) (Ψ B) (Ψ X) := htransport
    _ = inverseTracePower p (Ψ A) (Ψ B) (Ψ X) :=
      supportInverseTracePower_eq_inverseTracePower_of_posDef hΨA hΨB
    _ ≤ inverseTracePower p A B X := hred
    _ = supportInverseTracePower p A B X :=
      (supportInverseTracePower_eq_inverseTracePower_of_posDef hA hB).symm

/-- Theorem 6.3(3) with the book's support-power convention made explicit.

This is the book-facing replacement for the raw `matrixPower` statement when `Φ(1)` is not
invertible: no extra mathematical hypothesis is added, but the powers on the output side are read
through `supportLiebTracePower`.
Source: Hiai, Theorem 6.3. -/
def MultiplicativeDomainSupportTracePower : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    (p ∈ Set.Icc (-1 : ℝ) 0 ∨ p ∈ Set.Icc (1 : ℝ) 2) →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    InAdjointMultiplicativeDomain Φ X →
      supportLiebTracePower p (Φ A) (Φ B) X ≤
      supportLiebTracePower p A B ((hsAdjoint Φ) X)

/-- The book-facing support-power form of Hiai--Petz Theorem 6.3(3).
Source: Hiai, Theorem 6.3. -/
theorem multiplicativeDomainSupportTracePower :
    MultiplicativeDomainSupportTracePower := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hmd
  let P : Mₙ m := outputSupportProj Φ
  let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
  let Ψ : HSMap n model.dim := outputSupportReducedMap Φ hPos
  have hP : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  let Xcorner : matrixCornerSubmodule P :=
    ⟨matrixCornerProj P X, matrixCornerProj_mem_self hP⟩
  let Xc : Mₙ model.dim := model.toMat Xcorner
  have hXcorner : Xcorner.1 = matrixCornerProj (outputSupportProj Φ) X := by
    rfl
  have hmdΨ : InAdjointMultiplicativeDomain Ψ Xc := by
    simpa [P, model, Ψ, Xc] using
      inAdjointMultiplicativeDomain_outputSupportCorner
        (Φ := Φ) hPos hSch hmd Xcorner hXcorner
  have hpUnion : p ∈ Set.Icc (-1 : ℝ) 0 ∪ Set.Icc (1 : ℝ) 2 := by
    exact hp
  have hred :=
    liebTracePower_map_le_outputSupport_fullRange Φ (p := p) (A := A) (B := B)
      hpUnion hPos hTrace hSch hA hB (X := Xc) hmdΨ
  have hleft :
      supportLiebTracePower p (Φ A) (Φ B) X =
        liebTracePower p (Ψ A) (Ψ B) Xc := by
    simpa [P, model, Ψ, Xcorner, Xc] using
      supportLiebTracePower_outputSupportReducedMap_toMat_eq
        (Φ := Φ) hPos (p := p) (A := A) (B := B) (X := X) hA hB
  have hadj :
      (hsAdjoint Ψ) Xc = (hsAdjoint Φ) X := by
    simpa [P, model, Ψ, Xc] using
      hsAdjoint_outputSupportReducedMap_toMat_matrixCornerProj_eq
        (Φ := Φ) hPos X Xcorner hXcorner
  have hright :
      liebTracePower p A B ((hsAdjoint Ψ) Xc) =
        supportLiebTracePower p A B ((hsAdjoint Φ) X) := by
    rw [hadj]
    exact (supportLiebTracePower_eq_liebTracePower_of_posDef p hA hB).symm
  calc
    supportLiebTracePower p (Φ A) (Φ B) X =
        liebTracePower p (Ψ A) (Ψ B) Xc := hleft
    _ ≤ liebTracePower p A B ((hsAdjoint Ψ) Xc) := hred
    _ = supportLiebTracePower p A B ((hsAdjoint Φ) X) := hright


/-- Completed support-power surface for Hiai--Petz Theorem 6.3.

The separate `HiaiPetz.Frontier.TracePowerMonotonicityPosDefStatement` is only a
formalization-frontier statement for the literal `matrixPower` formulation and has no proof term.
This aggregate is the book-facing original-output-space statement: part (1) uses support powers
for semidefinite inputs, part (2) uses support inverse powers because positive images may be
singular off the output support, and part (3) uses `supportLiebTracePower` for the same convention.
Source: Hiai, Theorem 6.3. -/
theorem supportTracePowerMonotonicity :
    DirectSupportTracePower ∧
      InverseSupportTracePower ∧
        MultiplicativeDomainSupportTracePower := by
  exact ⟨directSupportTracePower,
    inverseSupportTracePower, multiplicativeDomainSupportTracePower⟩

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
