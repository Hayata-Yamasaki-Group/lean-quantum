/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic
import Quantum.TraceInequality.HiaiPetz.Support.OutputSupport
import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Output support corner of a positive map

For a positive Hilbert--Schmidt map `Φ`, the image lies in the corner cut out by the support
projection of `Φ(I)`. This file records that the cornering projection fixes every image and that
the Hilbert--Schmidt adjoint annihilates the orthogonal complement of the output support.
-/

namespace HiaiPetz

open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.L2Operator
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

private noncomputable def hermitianPosPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : Mₙ n :=
  hX.cfc (fun x : ℝ => max x 0)

private noncomputable def hermitianNegPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : Mₙ n :=
  hX.cfc (fun x : ℝ => max (-x) 0)

private theorem hermitianPosPartMatrix_posSemidef {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : (hermitianPosPartMatrix hX).PosSemidef := by
  dsimp [hermitianPosPartMatrix]
  rw [Matrix.IsHermitian.cfc]
  refine
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe (U := hX.eigenvectorUnitary))).2 ?_
  simp [Matrix.posSemidef_diagonal_iff]

private theorem hermitianNegPartMatrix_posSemidef {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : (hermitianNegPartMatrix hX).PosSemidef := by
  dsimp [hermitianNegPartMatrix]
  rw [Matrix.IsHermitian.cfc]
  refine
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe (U := hX.eigenvectorUnitary))).2 ?_
  simp [Matrix.posSemidef_diagonal_iff]

private theorem hermitian_sub_posPartMatrix_negPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) :
    X = hermitianPosPartMatrix hX - hermitianNegPartMatrix hX := by
  have hspec := hX.spectral_theorem
  calc
    X =
        Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary
          (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) :=
      hspec
    _ = hX.cfc (fun x : ℝ => max x 0) - hX.cfc (fun x : ℝ => max (-x) 0) := by
      rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_sub]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.coe_algebraMap,
          Matrix.sub_apply]
        exact_mod_cast (max_zero_sub_eq_self (hX.eigenvalues i)).symm
      · simp [Matrix.diagonal, hij]

private theorem posSemidef_le_trace_smul_one_mat {n : ℕ} {A : Mₙ n}
    (hA : A.PosSemidef) :
    A ≤ A.trace.re • (1 : Mₙ n) := by
  classical
  by_cases hn : Nonempty (Fin n)
  · letI := hn
    let β : ℝ := A.trace.re
    have hβ_ge : ∀ i : Fin n, hA.1.eigenvalues i ≤ β := by
      intro i
      have hi_le : hA.1.eigenvalues i ≤ ∑ j : Fin n, hA.1.eigenvalues j := by
        simpa using Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
      simpa [β, hA.1.trace_eq_sum_eigenvalues] using hi_le
    have hdiag :
        (Matrix.diagonal (fun i => Complex.ofReal (β - hA.1.eigenvalues i)) : Mₙ
          n).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (hβ_ge i)
    have hone :
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary (β • (1 : Mₙ n)) = β • (1
          : Mₙ n) := by
      simp [Unitary.conjStarAlgAut_apply]
    rw [← sub_nonneg]
    refine (Matrix.nonneg_iff_posSemidef).mpr ?_
    have hstep :
        (β • (1 : Mₙ n) - A) =
          Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
            (β • (1 : Mₙ n) - Matrix.diagonal (Complex.ofReal ∘ hA.1.eigenvalues)) := by
      calc
        β • (1 : Mₙ n) - A
            = β • (1 : Mₙ n) -
                Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
                  (Matrix.diagonal (Complex.ofReal ∘ hA.1.eigenvalues)) := by
                    exact congrArg (fun M : Mₙ n => β • (1 : Mₙ n) - M) hA.1.spectral_theorem
        _ = Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary (β • (1 : Mₙ n)) -
              Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
                (Matrix.diagonal (Complex.ofReal ∘ hA.1.eigenvalues)) := by
                  rw [hone]
        _ = Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
              (β • (1 : Mₙ n) - Matrix.diagonal (Complex.ofReal ∘ hA.1.eigenvalues)) := by
                rw [← map_sub]
    rw [hstep]
    refine (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe (U := hA.1.eigenvectorUnitary))).2 ?_
    convert hdiag using 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    exact le_of_eq (Subsingleton.elim _ _)

private theorem map_isSelfAdjoint_of_isPositiveMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {X : Mₙ n} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (Φ X) := by
  have hXH : X.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hX
  let pos : Mₙ n := hermitianPosPartMatrix hXH
  let neg : Mₙ n := hermitianNegPartMatrix hXH
  have hpos_psd : pos.PosSemidef := by
    dsimp [pos]
    exact hermitianPosPartMatrix_posSemidef hXH
  have hneg_psd : neg.PosSemidef := by
    dsimp [neg]
    exact hermitianNegPartMatrix_posSemidef hXH
  have hdecomp : X = pos - neg := by
    dsimp [pos, neg]
    exact hermitian_sub_posPartMatrix_negPartMatrix hXH
  have hΦpos_nonneg : 0 ≤ Φ pos := by
    exact hPos <| Matrix.nonneg_iff_posSemidef.mpr hpos_psd
  have hΦneg_nonneg : 0 ≤ Φ neg := by
    exact hPos <| Matrix.nonneg_iff_posSemidef.mpr hneg_psd
  have hΦpos_sa : IsSelfAdjoint (Φ pos) := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦpos_nonneg).1
  have hΦneg_sa : IsSelfAdjoint (Φ neg) := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦneg_nonneg).1
  rw [hdecomp, Φ.map_sub, sub_eq_add_neg]
  simpa [sub_eq_add_neg] using hΦpos_sa.add hΦneg_sa.neg

private theorem map_conjTranspose_of_isPositiveMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    Φ (Matrix.conjTranspose X) = Matrix.conjTranspose (Φ X) := by
  let H : Mₙ n := ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X)
  let K : Mₙ n := ((-(Complex.I) / 2 : ℂ)) • (X - Matrix.conjTranspose X)
  have hH : IsSelfAdjoint H := by
    change Matrix.conjTranspose H = H
    ext i j
    simp [H]
    ring_nf
  have hK : IsSelfAdjoint K := by
    change Matrix.conjTranspose K = K
    ext i j
    simp [K]
    ring_nf
  have hHU : Φ H = Matrix.conjTranspose (Φ H) := by
    simpa [Matrix.star_eq_conjTranspose] using
      (map_isSelfAdjoint_of_isPositiveMap Φ hPos hH).star_eq.symm
  have hKU : Φ K = Matrix.conjTranspose (Φ K) := by
    simpa [Matrix.star_eq_conjTranspose] using
      (map_isSelfAdjoint_of_isPositiveMap Φ hPos hK).star_eq.symm
  have hdecomp : X = H + Complex.I • K := by
    have hdecomp' : H + Complex.I • K = X := by
      have hcoef : (Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ) = (1 / 2 : ℂ) := by
        field_simp
        norm_num
      calc
        H + Complex.I • K
            = ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X) +
                (((Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ)) •
                  (X - Matrix.conjTranspose X)) := by
                    simp [H, K, smul_smul]
        _ = ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X) +
              ((1 / 2 : ℂ)) • (X - Matrix.conjTranspose X) := by
                rw [hcoef]
        _ = X := by
              ext i j
              simp [sub_eq_add_neg]
              ring_nf
    exact hdecomp'.symm
  have hdecomp_star : Matrix.conjTranspose X = H - Complex.I • K := by
    have hHct : Matrix.conjTranspose H = H := by
      simpa [Matrix.star_eq_conjTranspose] using hH.star_eq
    have hKct : Matrix.conjTranspose K = K := by
      simpa [Matrix.star_eq_conjTranspose] using hK.star_eq
    calc
      Matrix.conjTranspose X = Matrix.conjTranspose (H + Complex.I • K) := by
        simp [hdecomp]
      _ = Matrix.conjTranspose H + Matrix.conjTranspose (Complex.I • K) := by
          simp
      _ = H - Complex.I • K := by
          simp [hHct, hKct, sub_eq_add_neg]
  calc
    Φ (Matrix.conjTranspose X) = Φ H - Complex.I • (Φ K) := by
      rw [hdecomp_star, Φ.map_sub, Φ.map_smul, Φ.map_smul]
    _ = Matrix.conjTranspose (Φ H + Complex.I • (Φ K)) := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, ← hHU, ← hKU]
      simp [sub_eq_add_neg]
    _ = Matrix.conjTranspose (Φ X) := by
      rw [hdecomp]
      simp

private theorem outputSupportProj_mul_eq_self_of_nonneg {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : 0 ≤ A) :
    outputSupportProj Φ * Φ A = Φ A := by
  let C : Mₙ m := Φ (1 : Mₙ n)
  let D : Mₙ m := Φ A
  let P : Mₙ m := outputSupportProj Φ
  let T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) C
  let S : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) D
  let β : ℝ := A.trace.re
  have hAsa : IsSelfAdjoint A := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using (Matrix.nonneg_iff_posSemidef.mp hA).1
  have hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using hPos hA
  have hAupper : A ≤ β • (1 : Mₙ n) := by
    simpa [β] using posSemidef_le_trace_smul_one_mat hApsd
  have hDle : D ≤ β • C := by
    have hΦdiff : 0 ≤ Φ (β • (1 : Mₙ n) - A) :=
      hPos (sub_nonneg.mpr hAupper)
    rw [Φ.map_sub, Φ.map_smul_of_tower] at hΦdiff
    simpa [C, D] using sub_nonneg.mp hΦdiff
  have hker : T.ker ≤ S.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let x : Fin m → ℂ := WithLp.ofLp v
    have hxC : C.mulVec x = 0 := by
      simpa [T, x] using congrArg WithLp.ofLp hv
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hDnonneg
    have hDiffpsd : (β • C - D).PosSemidef := by
      exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hDle)
    have hDre_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ D.mulVec x) := hDpsd.re_dotProduct_nonneg x
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
    have hDq_nonneg : 0 ≤ star x ⬝ᵥ D.mulVec x := hDpsd.dotProduct_mulVec_nonneg x
    have hDq_zero : star x ⬝ᵥ D.mulVec x = 0 := by
      apply RCLike.ext
      · exact hDre_zero
      · exact (RCLike.nonneg_iff.mp hDq_nonneg).2
    have hxD : D.mulVec x = 0 := (hDpsd.dotProduct_mulVec_zero_iff x).1 hDq_zero
    apply WithLp.ofLp_injective
    simpa [S, x] using hxD
  have hTsymm : T.IsSymmetric := by
    have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
    have hTpos : T.toLinearMap.IsPositive := by
      simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hCpsd)
    exact hTpos.isSymmetric
  have hSsymm : S.IsSymmetric := by
    have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hDnonneg
    have hSpos : S.toLinearMap.IsPositive := by
      simpa [S, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hDpsd)
    exact hSpos.isSymmetric
  have hrange : S.range ≤ T.range :=
    (ContinuousLinearMap.ker_le_ker_iff_range_le_range hSsymm hTsymm).1 hker
  ext i j
  have hcol_range : S (WithLp.toLp 2 (Pi.single j 1)) ∈ T.range := by
    exact hrange ⟨WithLp.toLp 2 (Pi.single j 1), rfl⟩
  rcases hcol_range with ⟨u, hu⟩
  have hcol_mem : D.mulVec (Pi.single j 1) ∈ matrixSupportSubspace C := by
    refine ⟨WithLp.ofLp u, ?_⟩
    simpa [T, S] using congrArg WithLp.ofLp hu
  have hcol_fix : P.mulVec (D.mulVec (Pi.single j 1)) = D.mulVec (Pi.single j 1) :=
    (MatrixSupportProj.mulVec_eq_self_iff C (D.mulVec (Pi.single j 1))).2 hcol_mem
  have hmat_fix : (P * D).mulVec (Pi.single j 1) = D.mulVec (Pi.single j 1) := by
    simpa [Matrix.mulVec_mulVec] using hcol_fix
  simpa [P, D] using congrArg (fun v : Fin m → ℂ => v i) hmat_fix

private theorem outputSupportProj_mul_eq_self_of_selfAdjoint {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {X : Mₙ n} (hX : IsSelfAdjoint X) :
    outputSupportProj Φ * Φ X = Φ X := by
  have hXH : X.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hX
  let pos : Mₙ n := hermitianPosPartMatrix hXH
  let neg : Mₙ n := hermitianNegPartMatrix hXH
  have hpos :=
    outputSupportProj_mul_eq_self_of_nonneg Φ hPos (A := pos)
      (Matrix.nonneg_iff_posSemidef.mpr (by
        dsimp [pos]
        exact hermitianPosPartMatrix_posSemidef hXH))
  have hneg :=
    outputSupportProj_mul_eq_self_of_nonneg Φ hPos (A := neg)
      (Matrix.nonneg_iff_posSemidef.mpr (by
        dsimp [neg]
        exact hermitianNegPartMatrix_posSemidef hXH))
  calc
    outputSupportProj Φ * Φ X = outputSupportProj Φ * Φ (pos - neg) := by
      rw [hermitian_sub_posPartMatrix_negPartMatrix hXH]
    _ = outputSupportProj Φ * (Φ pos - Φ neg) := by
      rw [Φ.map_sub]
    _ = outputSupportProj Φ * Φ pos - outputSupportProj Φ * Φ neg := by
      simp [Matrix.mul_sub]
    _ = Φ pos - Φ neg := by
      rw [hpos, hneg]
    _ = Φ X := by
      rw [← Φ.map_sub, hermitian_sub_posPartMatrix_negPartMatrix hXH]

private theorem outputSupportProj_mul_eq_self {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    outputSupportProj Φ * Φ X = Φ X := by
  let H : Mₙ n := ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X)
  let K : Mₙ n := ((-(Complex.I) / 2 : ℂ)) • (X - Matrix.conjTranspose X)
  have hH : IsSelfAdjoint H := by
    change Matrix.conjTranspose H = H
    ext i j
    simp [H]
    ring_nf
  have hK : IsSelfAdjoint K := by
    change Matrix.conjTranspose K = K
    ext i j
    simp [K]
    ring_nf
  have hHU := outputSupportProj_mul_eq_self_of_selfAdjoint Φ hPos hH
  have hKU := outputSupportProj_mul_eq_self_of_selfAdjoint Φ hPos hK
  have hdecomp : X = H + Complex.I • K := by
    have hdecomp' : H + Complex.I • K = X := by
      have hcoef : (Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ) = (1 / 2 : ℂ) := by
        field_simp
        norm_num
      calc
        H + Complex.I • K
            = ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X) +
                (((Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ)) •
                  (X - Matrix.conjTranspose X)) := by
                    simp [H, K, smul_smul]
        _ = ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X) +
              ((1 / 2 : ℂ)) • (X - Matrix.conjTranspose X) := by
                rw [hcoef]
        _ = X := by
              calc
                ((1 / 2 : ℂ)) • (X + Matrix.conjTranspose X) +
                    ((1 / 2 : ℂ)) • (X - Matrix.conjTranspose X)
                    = (((1 / 2 : ℂ) + (1 / 2 : ℂ)) • X) +
                        (((1 / 2 : ℂ) + (-(1 / 2 : ℂ))) • Matrix.conjTranspose X) := by
                            ext i j
                            simp [sub_eq_add_neg]
                            ring_nf
                _ = X := by norm_num
    exact hdecomp'.symm
  calc
    outputSupportProj Φ * Φ X = outputSupportProj Φ * Φ (H + Complex.I • K) := by
      rw [hdecomp]
    _ = outputSupportProj Φ * (Φ H + Complex.I • Φ K) := by
      simp
    _ = outputSupportProj Φ * Φ H + Complex.I • (outputSupportProj Φ * Φ K) := by
      simp [Matrix.mul_add]
    _ = Φ H + Complex.I • Φ K := by
      rw [hHU, hKU]
    _ = Φ (H + Complex.I • K) := by
      simp
    _ = Φ X := by
      rw [hdecomp]

private theorem phi_mul_outputSupportProj_eq_self {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    Φ X * outputSupportProj Φ = Φ X := by
  have hPsa : IsSelfAdjoint (outputSupportProj Φ) :=
    OutputSupportProj.isSelfAdjoint Φ
  have hPstar : Matrix.conjTranspose (outputSupportProj Φ) = outputSupportProj Φ := by
    simpa [Matrix.star_eq_conjTranspose] using hPsa.star_eq
  have hleft :=
    outputSupportProj_mul_eq_self Φ hPos (Matrix.conjTranspose X)
  simpa [Matrix.conjTranspose_mul, hPstar, map_conjTranspose_of_isPositiveMap Φ hPos X] using
    congrArg Matrix.conjTranspose hleft

/-- The image of a positive map lies in the corner cut out by the support projection of `Φ(I)`. -/
theorem map_mem_outputCorner {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    (X : Mₙ n) :
    Φ X ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  calc
    outputSupportProj Φ * Φ X * outputSupportProj Φ
        = (outputSupportProj Φ * Φ X) * outputSupportProj Φ := by
            rw [Matrix.mul_assoc]
    _ = Φ X * outputSupportProj Φ := by
          rw [outputSupportProj_mul_eq_self Φ hPos X]
    _ = Φ X := phi_mul_outputSupportProj_eq_self Φ hPos X

/-- The cornering projection onto the output support fixes every image of the positive map:
`matrixCornerProj (outputSupportProj Φ) (Φ X) = Φ X`. -/
theorem phi_image_eq_outputCornerProj {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    (X : Mₙ n) :
    matrixCornerProj (outputSupportProj Φ) (Φ X) = Φ X := by
  have hmem := map_mem_outputCorner Φ hPos X
  rw [mem_matrixCornerSubmodule_iff] at hmem
  simpa [matrixCornerProj_apply] using hmem

private theorem inner_matrixCornerProj_eq_of_mem {m : ℕ} {P Y Z : Mₙ m}
    (hP : IsMatrixProj P) (hZ : Z ∈ matrixCornerSubmodule P) :
    inner ℂ (matrixCornerProj P Y) Z = inner ℂ Y Z := by
  rcases hP with ⟨hPidem, hPsa⟩
  rw [mem_matrixCornerSubmodule_iff] at hZ
  have hPstar : Matrix.conjTranspose P = P := by
    simpa [Matrix.star_eq_conjTranspose] using hPsa.star_eq
  have hZleft : P * Z = Z := by
    calc
      P * Z = P * (P * Z * P) := by rw [hZ]
      _ = (P * P) * Z * P := by simp [Matrix.mul_assoc]
      _ = P * Z * P := by rw [hPidem]
      _ = Z := hZ
  have hZright : Z * P = Z := by
    calc
      Z * P = (P * Z * P) * P := by rw [hZ]
      _ = P * Z * (P * P) := by simp [Matrix.mul_assoc]
      _ = P * Z * P := by rw [hPidem]
      _ = Z := hZ
  simp only [inner, matrixCornerProj_apply, Matrix.conjTranspose_mul, hPstar, Matrix.mul_assoc]
  calc
    Matrix.trace (Z * (P * (Matrix.conjTranspose Y * P)))
        = Matrix.trace ((Z * P) * Matrix.conjTranspose Y * P) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (Z * Matrix.conjTranspose Y * P) := by rw [hZright]
    _ = Matrix.trace (P * (Z * Matrix.conjTranspose Y)) := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm (Z * Matrix.conjTranspose Y) P
    _ = Matrix.trace ((P * Z) * Matrix.conjTranspose Y) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (Z * Matrix.conjTranspose Y) := by rw [hZleft]

/-- The Hilbert--Schmidt adjoint of `Φ` is unchanged after cornering the output by
`outputSupportProj Φ`. -/
theorem hsAdjoint_matrixCornerProj_eq {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ m) :
    hsAdjoint Φ (matrixCornerProj (outputSupportProj Φ) Y) = hsAdjoint Φ Y := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedAddCommGroup (Mₙ m) := instMatrixNormedAddCommGroup (n := m)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ m) := instMatrixInnerProductSpace (n := m)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace (Mₙ m) := instMatrixCompleteSpace (n := m)
  let P : Mₙ m := outputSupportProj Φ
  have hPproj : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  apply (@ext_inner_right ℂ (Mₙ n) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)))
  intro X
  have hcornerX : Φ X ∈ matrixCornerSubmodule P := by
    simpa [P] using map_mem_outputCorner Φ hPos X
  calc
    inner ℂ (hsAdjoint Φ (matrixCornerProj P Y)) X
        = inner ℂ (matrixCornerProj P Y) (Φ X) := by
            simpa [hsAdjoint] using
              (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ m)
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := n))
                (instMatrixNormedAddCommGroup (n := m))
                (instMatrixInnerProductSpace (n := n))
                (instMatrixInnerProductSpace (n := m))
                (instMatrixCompleteSpace (n := n))
                (instMatrixCompleteSpace (n := m))
                Φ X (matrixCornerProj P Y))
    _ = inner ℂ Y (Φ X) := inner_matrixCornerProj_eq_of_mem hPproj hcornerX
    _ = inner ℂ (hsAdjoint Φ Y) X := by
          simpa [hsAdjoint] using
            (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ m)
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedAddCommGroup (n := m))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixInnerProductSpace (n := m))
              (instMatrixCompleteSpace (n := n))
              (instMatrixCompleteSpace (n := m))
              Φ X Y).symm

/-- The Hilbert--Schmidt adjoint of a positive map annihilates the complement of the output
support projection: `hsAdjoint Φ (1 - outputSupportProj Φ) = 0`. -/
theorem hsAdjoint_outputSupportProj_compl_eq_zero {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    hsAdjoint Φ (1 - outputSupportProj Φ) = 0 := by
  have hPproj : IsMatrixProj (outputSupportProj Φ) :=
    OutputSupportProj.isProj Φ
  rcases hPproj with ⟨hPidem, _⟩
  have hcornerZero :
      matrixCornerProj (outputSupportProj Φ) (1 - outputSupportProj Φ) = 0 := by
    calc
      matrixCornerProj (outputSupportProj Φ) (1 - outputSupportProj Φ)
          = outputSupportProj Φ * (1 - outputSupportProj Φ) * outputSupportProj Φ := by
              simp [matrixCornerProj_apply]
      _ = (outputSupportProj Φ - outputSupportProj Φ * outputSupportProj Φ) *
            outputSupportProj Φ := by
              simp [Matrix.mul_sub]
      _ = 0 := by
            rw [hPidem]
            simp
  have hcornerEq := hsAdjoint_matrixCornerProj_eq Φ hPos
    (1 - outputSupportProj Φ)
  rw [hcornerZero, (hsAdjoint Φ).map_zero] at hcornerEq
  exact hcornerEq.symm

end HiaiPetz
