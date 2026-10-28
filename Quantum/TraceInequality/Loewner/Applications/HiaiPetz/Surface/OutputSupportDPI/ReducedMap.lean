/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.CornerModels
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map
import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.StrictOutput

/-!
# Hiai--Petz 6.2 output-support reduced map

This module contains the canonical reduced-map construction and strict-output
readiness API for the output-support stage of Hiai--Petz 6.2.
-/
namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOutputSupportHSOpCStarAlgebra
  instOutputSupportHSOpStarRing
  instOutputSupportHSOpComplexAlgebra
  instOutputSupportHSOpNormedAlgebra
  instOutputSupportHSOpPartialOrder
  instOutputSupportHSOpStarOrderedRing
  instOutputSupportHSOpNonnegSpectrumClass
  instOutputSupportHSOpComplexCFC
  instOutputSupportHSOpRealCFC
  outputSupportBridgeMatrixNormedAddCommGroup
  outputSupportBridgeMatrixNormedSpace
  outputSupportBridgeMatrixInnerProductSpace
  outputSupportBridgeMatrixCompleteSpace
  outputSupportBridgeMatrixFiniteDimensional

noncomputable section

/-! ### Positive Map Images Land in the Support Corner -/

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
        (Matrix.diagonal (fun i => Complex.ofReal (β - hA.1.eigenvalues i)) : Mₙ n).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (hβ_ge i)
    have hone :
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary (β • (1 : Mₙ n)) =
          β • (1 : Mₙ n) := by
      calc
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary (β • (1 : Mₙ n)) =
            β • (Unitary.conjStarAlgAut ℂ (Mₙ n) hA.1.eigenvectorUnitary (1 : Mₙ n)) := by
          let ψ := (Unitary.conjStarAlgAut ℂ (Mₙ n) hA.1.eigenvectorUnitary).toAlgEquiv
          let φ := ψ.toLinearEquiv.toLinearMap
          exact
            φ.map_smul_of_tower β (1 : Mₙ n)
        _ = β • (1 : Mₙ n) := by
          simp
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
  have hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using hPos hA
  have hAupper : A ≤ β • (1 : Mₙ n) := by
    simpa [β] using posSemidef_le_trace_smul_one_mat hApsd
  have hDle : D ≤ β • C := by
    have hΦdiff :=
      hPos (show 0 ≤ β • (1 : Mₙ n) - A from sub_nonneg.mpr hAupper)
    rw [Φ.map_sub, Φ.map_smul_of_tower] at hΦdiff
    exact sub_nonneg.mp (by simpa [C, D, β] using hΦdiff)
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
              ext i j
              simp [sub_eq_add_neg]
              ring_nf
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
  simpa [Matrix.conjTranspose_mul, hPstar, isPositiveMap_map_conjTranspose hPos X] using
    congrArg Matrix.conjTranspose hleft

/-- The image of a positive map lies in the corner cut out by the support projection of `Φ(I)`. -/
theorem phi_image_mem_outputCorner {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
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

theorem phi_image_eq_outputCornerProj {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    (X : Mₙ n) :
    matrixCornerProj (outputSupportProj Φ) (Φ X) = Φ X := by
  have hmem := phi_image_mem_outputCorner Φ hPos X
  rw [mem_matrixCornerSubmodule_iff] at hmem
  simpa [matrixCornerProj_apply] using hmem

section

open scoped Matrix.Norms.Frobenius

/-! ### Adjoint Cornering and Reduced Map Data -/

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
theorem phiAdjoint_eq_phiAdjoint_after_outputCorner {n m : ℕ} (Φ : HSMap n m)
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
    simpa [P] using phi_image_mem_outputCorner Φ hPos X
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

theorem phiAdjoint_outputSupportProj_compl_eq_zero {n m : ℕ} (Φ : HSMap n m)
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
              simp
      _ = (outputSupportProj Φ - outputSupportProj Φ * outputSupportProj Φ) *
            outputSupportProj Φ := by
              simp [Matrix.mul_sub]
      _ = 0 := by
            rw [hPidem]
            simp
  have hcornerEq := phiAdjoint_eq_phiAdjoint_after_outputCorner Φ hPos
    (1 - outputSupportProj Φ)
  rw [hcornerZero] at hcornerEq
  rw [(hsAdjoint Φ).map_zero] at hcornerEq
  exact hcornerEq.symm

/-! ### Reduced Map Strict-Output Readiness -/

noncomputable abbrev outputSupportUnitToEuclideanEnd {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ :=
  _root_.HiaiPetz.outputSupportUnitToEuclideanEnd Φ hPos

private theorem outputSupportUnitToEuclideanEnd_ker_eq_bot {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    LinearMap.ker (outputSupportUnitToEuclideanEnd Φ hPos) = ⊥ := by
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  have hTsymm : T.IsSymmetric := hTpos.isSymmetric
  ext u
  constructor
  · intro hu
    have hu0 :
        outputSupportUnitToEuclideanEnd Φ hPos u = 0 := by
      simpa [outputSupportUnitToEuclideanEnd, LinearMap.mem_ker] using hu
    have huTzero : T u.1 = 0 := by
      have hu0' :
          (((outputSupportUnitToEuclideanEnd Φ hPos) u :
                outputSupportEuclideanSubspace Φ) :
              EuclideanSpace ℂ (Fin m)) = 0 := by
        simpa using congrArg Subtype.val hu0
      simpa [outputSupportUnitToEuclideanEnd,
        _root_.HiaiPetz.outputSupportUnitToEuclideanEnd, C, T,
        outputCornerToEuclideanEndLinearEquiv_apply_coe] using hu0'
    have huKer : u.1 ∈ LinearMap.ker T := by
      simpa [LinearMap.mem_ker, T] using huTzero
    have huRange : u.1 ∈ LinearMap.range T := by
      rcases u.2 with ⟨v, hv, hvu⟩
      rcases hv with ⟨x, rfl⟩
      refine ⟨WithLp.toLp 2 x, ?_⟩
      exact (Matrix.toLpLin_toLp (p := 2) (q := 2) C x).trans hvu
    have huOrth : u.1 ∈ (LinearMap.range T)ᗮ := by
      simpa [LinearMap.IsSymmetric.orthogonal_range hTsymm] using huKer
    have huZero : u.1 = 0 := by
      exact (Submodule.disjoint_def.mp (LinearMap.range T).orthogonal_disjoint) _ huRange huOrth
    have : u = 0 := Subtype.ext huZero
    simpa [Submodule.mem_bot] using this
  · intro hu
    rw [Submodule.mem_bot] at hu
    simp [hu]

-- The theorem head expands the output-support subspace and transported matrix instances.
-- The corresponding matrix-model synthesis follows the same heavy path.
private theorem outputSupportUnitToEuclideanEnd_isPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _
      (outputSupportUnitToEuclideanEnd Φ hPos) := by
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨?_, ?_⟩
  · intro u v
    change inner ℂ (T u.1) v.1 = inner ℂ u.1 (T v.1)
    simpa [outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.isSymmetric u.1 v.1
  · intro u
    change 0 ≤ RCLike.re (inner ℂ (T u.1) u.1)
    simpa [outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.re_inner_nonneg_left u.1

/-- On the output-support corner, the image of the unit induces a positive operator with trivial
kernel. This is the corner-level strict-positivity datum used before defining the reduced map. -/
theorem phi_image_posDef_on_outputCorner {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    let C : Mₙ m := Φ (1 : Mₙ n)
    let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin C
    T.IsPositive ∧ ∀ u, u ∈ outputSupportEuclideanSubspace Φ → T u = 0 → u = 0 := by
  dsimp
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨hTpos, ?_⟩
  intro u hu huTzero
  let uu : outputSupportEuclideanSubspace Φ := ⟨u, hu⟩
  have huuZero :
      outputSupportUnitToEuclideanEnd Φ hPos uu = 0 := by
    apply Subtype.ext
    simpa [outputSupportUnitToEuclideanEnd,
      _root_.HiaiPetz.outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using huTzero
  have huuKer : uu ∈ LinearMap.ker (outputSupportUnitToEuclideanEnd Φ hPos) := by
    simpa [LinearMap.mem_ker] using huuZero
  have huuBot : uu ∈ (⊥ : Submodule ℂ (outputSupportEuclideanSubspace Φ)) := by
    simpa [outputSupportUnitToEuclideanEnd_ker_eq_bot Φ hPos] using huuKer
  have huuEqZero : uu = 0 := by
    simpa using huuBot
  simpa [uu] using congrArg Subtype.val huuEqZero

-- The theorem head expands `outputSupportEuclideanSubspace Φ` enough to be deterministic but heavy.
-- The associated output-corner instance search needs the same local budget.
private theorem outputSupportImageToEuclideanEnd_isPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : 0 ≤ A) :
    @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _
      (outputCornerToEuclideanEndLinearEquiv Φ
        ⟨Φ A, phi_image_mem_outputCorner Φ hPos A⟩) := by
  let C : Mₙ m := Φ A
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by simpa [C] using hPos hA
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨?_, ?_⟩
  · intro u v
    change inner ℂ (T u.1) v.1 = inner ℂ u.1 (T v.1)
    simpa [C, T, outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.isSymmetric u.1 v.1
  · intro u
    change 0 ≤ RCLike.re (inner ℂ (T u.1) u.1)
    simpa [C, T, outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.re_inner_nonneg_left u.1

end

noncomputable abbrev outputSupportReducedMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    HSMap n (outputSupportMatrixCornerModel Φ).dim :=
  _root_.HiaiPetz.outputSupportReducedMap Φ hPos

/-- Short canonical API for the reduced Hilbert--Schmidt map on the output support. -/
noncomputable abbrev outputSupportReducedHSMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    HSMap n (outputSupportMatrixCornerModel Φ).dim :=
  _root_.HiaiPetz.outputSupportReducedHSMap Φ hPos

@[simp]
theorem outputSupportReducedMap_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    outputSupportReducedMap Φ hPos X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, phi_image_mem_outputCorner Φ hPos X⟩ := by
  rfl

@[simp]
theorem outputSupportReducedHSMap_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    outputSupportReducedHSMap Φ hPos X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, phi_image_mem_outputCorner Φ hPos X⟩ := by
  rfl

-- The reduced-map positivity proof unfolds the corner model and its transport equivalence.
-- The same declaration needs extra budget for the transported matrix instances.
theorem outputSupportReducedMap_one_posDef {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    MatrixPosDef (outputSupportReducedMap Φ hPos (1 : Mₙ n)) := by
  let F : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ :=
    outputSupportUnitToEuclideanEnd Φ hPos
  have hFpos : @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _ F := by
    simpa [F] using outputSupportUnitToEuclideanEnd_isPositive Φ hPos
  have hFunit : IsUnit F := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    simpa [F] using outputSupportUnitToEuclideanEnd_ker_eq_bot Φ hPos
  have hMpsd : (outputSupportReducedMap Φ hPos (1 : Mₙ n)).PosSemidef := by
    rw [outputSupportReducedMap_apply]
    simpa [F] using
      (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff Φ F).2 hFpos
  have hMunit : IsUnit (outputSupportReducedMap Φ hPos (1 : Mₙ n)) := by
    rw [outputSupportReducedMap_apply]
    simpa [F] using
      (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_isUnit_iff Φ F).2 hFunit
  have hMposDef : (outputSupportReducedMap Φ hPos (1 : Mₙ n)).PosDef :=
    hMpsd.posDef_iff_isUnit.mpr hMunit
  refine ⟨?_, ?_⟩
  · simpa [Matrix.IsHermitian, IsSelfAdjoint] using hMposDef.1
  · intro x hx
    exact (RCLike.pos_iff.mp (hMposDef.dotProduct_mulVec_pos hx)).1

theorem outputSupportReducedMap_isPositiveMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    IsPositiveMap (outputSupportReducedMap Φ hPos) := by
  intro A hA
  rw [Matrix.nonneg_iff_posSemidef, outputSupportReducedMap_apply]
  exact
    (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff Φ
      (outputCornerToEuclideanEndLinearEquiv Φ
        ⟨Φ A, phi_image_mem_outputCorner Φ hPos A⟩)).2
      (outputSupportImageToEuclideanEnd_isPositive Φ hPos hA)

theorem outputSupportReducedMap_tracePreserving {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTrace : _root_.HiaiPetz.TracePreserving Φ) :
    _root_.HiaiPetz.TracePreserving (outputSupportReducedMap Φ hPos) := by
  intro X
  rw [outputSupportReducedMap_apply]
  exact
    (outputCornerToOrthonormalMatrixLinearEquiv_trace Φ
      ⟨Φ X, phi_image_mem_outputCorner Φ hPos X⟩).trans (hTrace X)

theorem outputSupportReducedMap_hsAdjoint_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    hsAdjoint (outputSupportReducedMap Φ hPos) Y =
      hsAdjoint Φ ((outputSupportMatrixCornerModel Φ).toMat.symm Y).1 := by
  simpa [outputSupportReducedMap] using
    MatrixCornerModel.hsAdjoint_transportMap_apply (outputSupportMatrixCornerModel Φ)
      Φ (phi_image_mem_outputCorner Φ hPos) Y

theorem outputSupportReducedMap_hsAdjointSchwarz {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ) :
    HSAdjointSchwarz (outputSupportReducedMap Φ hPos) := by
  intro Y
  let model := outputSupportMatrixCornerModel Φ
  let Z : matrixCornerSubmodule (outputSupportProj Φ) := model.toMat.symm Y
  have hZ := hSch Z.1
  have hR :
      hsAdjoint (outputSupportReducedMap Φ hPos) (Matrix.conjTranspose Y * Y) =
        hsAdjoint Φ (Matrix.conjTranspose Z.1 * Z.1) := by
    rw [outputSupportReducedMap_hsAdjoint_apply]
    have hZY :
        ((model.toMat.symm (Matrix.conjTranspose Y * Y)).1) =
          Matrix.conjTranspose Z.1 * Z.1 := by
      simpa [model, Z, Matrix.star_eq_conjTranspose] using
        congrArg Subtype.val (MatrixCornerModel.toMat_symm_star_mul model Y)
    rw [hZY]
  calc
    Matrix.conjTranspose ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y) *
          ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y)
        = Matrix.conjTranspose (hsAdjoint Φ Z.1) * hsAdjoint Φ Z.1 := by
            rw [outputSupportReducedMap_hsAdjoint_apply]
    _ ≤ hsAdjoint Φ (Matrix.conjTranspose Z.1 * Z.1) := hZ
    _ = hsAdjoint (outputSupportReducedMap Φ hPos) (Matrix.conjTranspose Y * Y) := hR.symm

/-- Bundled readiness facts for the Loewner-surface reduced map: the reduced map
`outputSupportReducedHSMap Φ hPos` is positive, trace-preserving and satisfies the
Hilbert--Schmidt adjoint Schwarz inequality, and its value at `1` is positive definite
in the sense of `MatrixPosDef`. -/
structure OutputSupportReducedMapReady {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ)
    (hTrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) :
    Prop where
  positive : IsPositiveMap (outputSupportReducedHSMap Φ hPos)
  tracePreserving : _root_.HiaiPetz.TracePreserving (outputSupportReducedHSMap Φ hPos)
  adjointSchwarz : HSAdjointSchwarz (outputSupportReducedHSMap Φ hPos)
  outputPosDef : MatrixPosDef (outputSupportReducedHSMap Φ hPos (1 : Mₙ n))

/-- The canonical reduced map on the output support, packaged as strict-output ready data. -/
theorem outputSupportReducedHSMap_ready {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ)
    (hTrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) :
    OutputSupportReducedMapReady Φ hPos hTrace hSch where
  positive := by
    simpa [outputSupportReducedHSMap] using outputSupportReducedMap_isPositiveMap Φ hPos
  tracePreserving := by
    simpa [outputSupportReducedHSMap] using
      outputSupportReducedMap_tracePreserving Φ hPos hTrace
  adjointSchwarz := by
    simpa [outputSupportReducedHSMap] using
      outputSupportReducedMap_hsAdjointSchwarz Φ hPos hSch
  outputPosDef := by
    simpa [outputSupportReducedHSMap] using outputSupportReducedMap_one_posDef Φ hPos

/-- The canonical reduced map on the output support satisfies exactly the strict-output input
hypotheses needed by the completed strict theorem package. -/
theorem outputSupportReducedMap_strictOutputReady {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ)
    (hTrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) :
    IsPositiveMap (outputSupportReducedMap Φ hPos) ∧
      _root_.HiaiPetz.TracePreserving (outputSupportReducedMap Φ hPos) ∧
      HSAdjointSchwarz (outputSupportReducedMap Φ hPos) ∧
      MatrixPosDef (outputSupportReducedMap Φ hPos (1 : Mₙ n)) := by
  let hready := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
  simpa [outputSupportReducedHSMap] using
    And.intro hready.positive
      (And.intro hready.tracePreserving
        (And.intro hready.adjointSchwarz hready.outputPosDef))

private theorem phi_image_mem_outputCorner_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (X : Mₙ n) :
    Φ X ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]

/-- Official full-support trivialization node: when `Φ(1)` is positive definite, the canonical
reduced map no longer needs a nontrivial support-corner witness. Because the canonical model still
uses an orthonormal-basis matrix representation of the codomain, the public statement is the
pointwise equality to that trivialized model transport of `Φ`. -/
theorem outputSupportReducedMap_eq_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (X : Mₙ n) :
    outputSupportReducedMap Φ hPos X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, phi_image_mem_outputCorner_of_posDef Φ hΦ1 X⟩ := by
  rw [outputSupportReducedMap_apply]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
