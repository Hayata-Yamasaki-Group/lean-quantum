/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI

/-!
# Hiai--Petz paper-support bridge surface

This file exposes the canonical support-corner / reduced-map surface for
Hiai--Petz paper notation.  The definitions here do not directly construct a
naked singular ambient operator `J_f(Φ A, Φ B)`.  Instead, they define the
support-corner representative transported through the output-support matrix
model.

The ambient-regularization bridge in `OpMontI.Regularization` identifies these
support-corner representatives with positive-identity regularized,
support-compressed quadratic-form limits.  Thus the raw paper-support conditions
closed here are the support-corner side of the paper notation, while the later
section supplies the regularized ambient reading.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section

/-- Positive-definite inputs stay positive-definite after canonical output-support reduction. -/
theorem outputSupportReducedHSMap_image_posDef_of_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : MatrixPosDef A) :
    MatrixPosDef (outputSupportReducedHSMap Φ hPos A) := by
  have hredPos : IsPositiveMap (outputSupportReducedHSMap Φ hPos) := by
    simpa [outputSupportReducedHSMap] using outputSupportReducedMap_isPositiveMap Φ hPos
  have hredOne : MatrixPosDef (outputSupportReducedHSMap Φ hPos (1 : Mₙ n)) := by
    simpa [outputSupportReducedHSMap] using outputSupportReducedMap_one_posDef Φ hPos
  exact isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
    (outputSupportReducedHSMap Φ hPos) hredPos hredOne hA

/-- Reduced support-side `J_f` operator used by the paper-support bridge. -/
noncomputable def paperSupportReducedJOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  jOperator f (outputSupportReducedHSMap Φ hPos A)
    (outputSupportReducedHSMap Φ hPos B)

/-- Reduced support-side inverse `J_f` operator used by the paper-support bridge. -/
noncomputable def paperSupportReducedJOperatorInv {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
    (outputSupportReducedHSMap Φ hPos B)

/-- The reduced support-side `J_f` has positive-definite inputs whenever the original inputs are
positive definite. -/
theorem paperSupportReducedJOperator_inputs_posDef {n m : ℕ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    MatrixPosDef (outputSupportReducedHSMap Φ hPos A) ∧
      MatrixPosDef (outputSupportReducedHSMap Φ hPos B) := by
  exact ⟨outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA,
    outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hB⟩

private theorem matrixSupportSubspace_le_of_proj_mul_eq_self {n : ℕ} {C D : Mₙ n}
    (h : matrixSupportProj C * D = D) :
    matrixSupportSubspace D ≤ matrixSupportSubspace C := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hfix : (matrixSupportProj C).mulVec (D.mulVec x) = D.mulVec x := by
    simpa [Matrix.mulVec_mulVec] using congrArg (fun M : Mₙ n => M.mulVec x) h
  exact (MatrixSupportProj.mulVec_eq_self_iff C (D.mulVec x)).1 hfix

private theorem matrixSupportProj_eq_of_mutual_proj_mul_eq_self {n : ℕ} {C D : Mₙ n}
    (hCD : matrixSupportProj C * D = D)
    (hDC : matrixSupportProj D * C = C) :
    matrixSupportProj C = matrixSupportProj D := by
  have hsubCD : matrixSupportSubspace D ≤ matrixSupportSubspace C :=
    matrixSupportSubspace_le_of_proj_mul_eq_self hCD
  have hsubDC : matrixSupportSubspace C ≤ matrixSupportSubspace D :=
    matrixSupportSubspace_le_of_proj_mul_eq_self hDC
  have hsub : matrixSupportSubspace C = matrixSupportSubspace D :=
    le_antisymm hsubDC hsubCD
  apply Matrix.toEuclideanLin.injective
  simp [hsub]

private theorem matrixSupportProj_mul_eq_self_of_pos_smul_le {n : ℕ} {C D : Mₙ n}
    (hC : 0 ≤ C) (hD : 0 ≤ D) {r : ℝ} (hr : 0 < r)
    (hle : (r : ℂ) • C ≤ D) :
    matrixSupportProj D * C = C := by
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) D
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hC
  have hDpsd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
  have hdiffpsd : (D - (r : ℂ) • C).PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hle)
  have hTsymm : T.IsSymmetric := by
    have hTpos : T.toLinearMap.IsPositive := by
      simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hDpsd)
    exact hTpos.isSymmetric
  have hSsymm : S.IsSymmetric := by
    have hSpos : S.toLinearMap.IsPositive := by
      simpa [S, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hCpsd)
    exact hSpos.isSymmetric
  have hker : T.ker ≤ S.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let x : Fin n → ℂ := WithLp.ofLp v
    have hxD : D.mulVec x = 0 := by
      simpa [T, x] using congrArg WithLp.ofLp hv
    have hCq_nonneg : 0 ≤ star x ⬝ᵥ C.mulVec x :=
      hCpsd.dotProduct_mulVec_nonneg x
    have hdiff_nonneg : 0 ≤ star x ⬝ᵥ (D - (r : ℂ) • C).mulVec x :=
      hdiffpsd.dotProduct_mulVec_nonneg x
    have hdiff_eq : star x ⬝ᵥ (D - (r : ℂ) • C).mulVec x =
        - (r : ℂ) * (star x ⬝ᵥ C.mulVec x) := by
      calc
        star x ⬝ᵥ (D - (r : ℂ) • C).mulVec x
            = star x ⬝ᵥ (D.mulVec x - ((r : ℂ) • C).mulVec x) := by
                rw [Matrix.sub_mulVec]
        _ = - (star x ⬝ᵥ ((r : ℂ) • C).mulVec x) := by
              simp [hxD]
        _ = - ((r : ℂ) * (star x ⬝ᵥ C.mulVec x)) := by
              rw [Matrix.smul_mulVec, dotProduct_smul]
              simp
        _ = - (r : ℂ) * (star x ⬝ᵥ C.mulVec x) := by ring
    have hCq_re_nonpos : Complex.re (star x ⬝ᵥ C.mulVec x) ≤ 0 := by
      have hdiff_re_nonneg :
          0 ≤ Complex.re (star x ⬝ᵥ (D - (r : ℂ) • C).mulVec x) :=
        (RCLike.nonneg_iff.mp hdiff_nonneg).1
      have hdiff_re_eq :
          Complex.re (star x ⬝ᵥ (D - (r : ℂ) • C).mulVec x) =
            - r * Complex.re (star x ⬝ᵥ C.mulVec x) := by
        rw [hdiff_eq]
        simp
      nlinarith
    have hCq_re_nonneg : 0 ≤ Complex.re (star x ⬝ᵥ C.mulVec x) :=
      (RCLike.nonneg_iff.mp hCq_nonneg).1
    have hCq_zero : star x ⬝ᵥ C.mulVec x = 0 := by
      apply RCLike.ext
      · exact le_antisymm hCq_re_nonpos hCq_re_nonneg
      · exact (RCLike.nonneg_iff.mp hCq_nonneg).2
    have hxC : C.mulVec x = 0 :=
      (hCpsd.dotProduct_mulVec_zero_iff x).1 hCq_zero
    apply WithLp.ofLp_injective
    simpa [S, x] using hxC
  have hrange : S.range ≤ T.range :=
    (ContinuousLinearMap.ker_le_ker_iff_range_le_range hSsymm hTsymm).1 hker
  ext i j
  have hcol_range : S (WithLp.toLp 2 (Pi.single j 1)) ∈ T.range := by
    exact hrange ⟨WithLp.toLp 2 (Pi.single j 1), rfl⟩
  rcases hcol_range with ⟨u, hu⟩
  have hcol_mem : C.mulVec (Pi.single j 1) ∈ matrixSupportSubspace D := by
    refine ⟨WithLp.ofLp u, ?_⟩
    simpa [T, S] using congrArg WithLp.ofLp hu
  have hcol_fix : (matrixSupportProj D).mulVec (C.mulVec (Pi.single j 1)) =
      C.mulVec (Pi.single j 1) :=
    (MatrixSupportProj.mulVec_eq_self_iff D (C.mulVec (Pi.single j 1))).2 hcol_mem
  have hmat_fix : (matrixSupportProj D * C).mulVec (Pi.single j 1) =
      C.mulVec (Pi.single j 1) := by
    rw [← Matrix.mulVec_mulVec]
    exact hcol_fix
  simpa using congrArg (fun v : Fin n → ℂ => v i) hmat_fix

/-- Positive-definite inputs have the same ambient output support as `Φ(1)`. -/
theorem phi_image_supportProj_eq_outputSupportProj_of_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : MatrixPosDef A) :
    matrixSupportProj (Φ A) = outputSupportProj Φ := by
  obtain ⟨r, hr_pos, hr_le⟩ := matrixPosDef_exists_pos_algebraMap_le hA
  have hC_nonneg : 0 ≤ Φ (1 : Mₙ n) := by
    simpa using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hA_nonneg : 0 ≤ A := by
    exact (Matrix.nonneg_iff_posSemidef).2 (matrixPosDef_posDef hA).posSemidef
  have hD_nonneg : 0 ≤ Φ A := hPos hA_nonneg
  have hmap_nonneg : 0 ≤ Φ (A - algebraMap ℝ (Mₙ n) r) :=
    hPos (sub_nonneg.mpr hr_le)
  have hle : (r : ℂ) • Φ (1 : Mₙ n) ≤ Φ A := by
    have hmap_nonneg' : 0 ≤ Φ A - (r : ℂ) • Φ (1 : Mₙ n) := by
      simpa [ContinuousLinearMap.map_sub, Algebra.algebraMap_eq_smul_one,
        Complex.real_smul] using hmap_nonneg
    exact sub_nonneg.mp hmap_nonneg'
  have hCD : matrixSupportProj (Φ (1 : Mₙ n)) * Φ A = Φ A := by
    simpa [outputSupportProj] using
      OutputSupportProj.left_mul_eq_self_of_mem (Φ := Φ)
        (phi_image_mem_outputCorner Φ hPos A)
  have hDC : matrixSupportProj (Φ A) * Φ (1 : Mₙ n) = Φ (1 : Mₙ n) :=
    matrixSupportProj_mul_eq_self_of_pos_smul_le hC_nonneg hD_nonneg hr_pos hle
  have hEq :
      matrixSupportProj (Φ (1 : Mₙ n)) = matrixSupportProj (Φ A) :=
    matrixSupportProj_eq_of_mutual_proj_mul_eq_self hCD hDC
  simpa [outputSupportProj] using hEq.symm

/-- Images of two positive-definite inputs have the same paper output support. -/
theorem phi_images_common_supportProj_of_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    matrixSupportProj (Φ A) = outputSupportProj Φ ∧
      matrixSupportProj (Φ B) = outputSupportProj Φ ∧
      matrixSupportProj (Φ A) = matrixSupportProj (Φ B) := by
  have hAeq := phi_image_supportProj_eq_outputSupportProj_of_matrixPosDef Φ hPos hA
  have hBeq := phi_image_supportProj_eq_outputSupportProj_of_matrixPosDef Φ hPos hB
  exact ⟨hAeq, hBeq, hAeq.trans hBeq.symm⟩

/-- Raw paper-support `J_f` as an operator on the actual output support corner. -/
noncomputable def rawSupportCornerJOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    matrixCornerSubmodule (outputSupportProj Φ) →L[ℂ]
      matrixCornerSubmodule (outputSupportProj Φ) :=
  (outputSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap.comp
    ((jOperator f (outputSupportReducedHSMap Φ hPos A)
      (outputSupportReducedHSMap Φ hPos B)).comp
      (outputSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Raw paper-support inverse `J_f` as an operator on the actual output support corner. -/
noncomputable def rawSupportCornerJOperatorInv {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    matrixCornerSubmodule (outputSupportProj Φ) →L[ℂ]
      matrixCornerSubmodule (outputSupportProj Φ) :=
  (outputSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap.comp
    ((jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
      (outputSupportReducedHSMap Φ hPos B)).comp
      (outputSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinate form of the raw support-corner `J_f`. -/
noncomputable def rawSupportCornerJOperatorModelConj {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  (outputSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((rawSupportCornerJOperator f Φ hPos A B).comp
      (outputSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap)

/-- Coordinate form of the raw support-corner inverse `J_f`. -/
noncomputable def rawSupportCornerJOperatorInvModelConj {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  (outputSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((rawSupportCornerJOperatorInv f Φ hPos A B).comp
      (outputSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap)

/-- Transporting the raw support-corner `J_f` to coordinates gives the reduced-map `J_f`. -/
theorem rawSupportCornerJOperator_conj_eq_reducedMap_jOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    rawSupportCornerJOperatorModelConj f Φ hPos A B =
      jOperator f (outputSupportReducedHSMap Φ hPos A)
        (outputSupportReducedHSMap Φ hPos B) := by
  ext X i j
  dsimp [rawSupportCornerJOperatorModelConj, rawSupportCornerJOperator]
  change ((outputSupportMatrixCornerModel Φ).toMat
      ((outputSupportMatrixCornerModel Φ).toMat.symm
        ((jOperator f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B))
          ((outputSupportMatrixCornerModel Φ).toMat
            ((outputSupportMatrixCornerModel Φ).toMat.symm X))))) i j =
    ((jOperator f (outputSupportReducedHSMap Φ hPos A)
      (outputSupportReducedHSMap Φ hPos B)) X) i j
  simp

/-- Transporting the raw support-corner inverse `J_f` to coordinates gives the reduced-map
inverse `J_f`. -/
theorem rawSupportCornerJOperatorInv_conj_eq_reducedMap_jOperatorInv {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    rawSupportCornerJOperatorInvModelConj f Φ hPos A B =
      jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
        (outputSupportReducedHSMap Φ hPos B) := by
  ext X i j
  dsimp [rawSupportCornerJOperatorInvModelConj, rawSupportCornerJOperatorInv]
  change ((outputSupportMatrixCornerModel Φ).toMat
      ((outputSupportMatrixCornerModel Φ).toMat.symm
        ((jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B))
          ((outputSupportMatrixCornerModel Φ).toMat
            ((outputSupportMatrixCornerModel Φ).toMat.symm X))))) i j =
    ((jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
      (outputSupportReducedHSMap Φ hPos B)) X) i j
  simp

/-- The named Hiai--Petz support-side `J_f` surface.  At this stage it is the canonical
reduced-map representative, not the raw ambient singular paper expression. -/
noncomputable def jOperatorSupport {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  paperSupportReducedJOperator f Φ hPos A B

/-- The named Hiai--Petz support-side inverse `J_f` surface.  At this stage it is the canonical
reduced-map representative, not the raw ambient singular paper expression. -/
noncomputable def jOperatorInvSupport {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  paperSupportReducedJOperatorInv f Φ hPos A B

/-- Output images of positive-definite inputs are positive-definite after transport to the
canonical output-support matrix model. -/
theorem phi_image_posDef_on_outputSupport_of_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : MatrixPosDef A) :
    MatrixPosDef (outputSupportReducedHSMap Φ hPos A) :=
  outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA

/-- The support-side `J_f` surface is definitionally the reduced-map `J_f`. -/
theorem jOperatorSupport_conj_eq_reducedMap_jOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    jOperatorSupport f Φ hPos A B =
      jOperator f (outputSupportReducedHSMap Φ hPos A)
        (outputSupportReducedHSMap Φ hPos B) := by
  rfl

/-- The support-side inverse `J_f` surface is definitionally the reduced-map inverse `J_f`. -/
theorem jOperatorInvSupport_conj_eq_reducedMap_jOperatorInv {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (A B : Mₙ n) :
    jOperatorInvSupport f Φ hPos A B =
      jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
        (outputSupportReducedHSMap Φ hPos B) := by
  rfl

/-- Paper-support inverse condition, currently exposed as the canonical reduced-map condition.
The ambient singular `J_f(Φ A, Φ B)` equality is not hidden in this definition. -/
def ConditionII_paperSupport (f : ℝ → ℝ) : Prop :=
  ConditionII_book f

/-- Paper-support direct condition, currently exposed as the canonical reduced-map condition.
The ambient singular `J_f(Φ A, Φ B)` equality is not hidden in this definition. -/
def ConditionIII_paperSupport (f : ℝ → ℝ) : Prop :=
  ConditionIII_book f

/-- The paper-support inverse condition is the already-verified reduced book condition. -/
theorem ConditionII_paperSupport_iff_ConditionII_book (f : ℝ → ℝ) :
    ConditionII_paperSupport f ↔ ConditionII_book f := by
  rfl

/-- The paper-support direct condition is the already-verified reduced book condition. -/
theorem ConditionIII_paperSupport_iff_ConditionIII_book (f : ℝ → ℝ) :
    ConditionIII_paperSupport f ↔ ConditionIII_book f := by
  rfl

/-- Raw paper-support inverse condition, phrased through the actual support-corner operator
transported to the canonical output-support matrix model. -/
def ConditionII_rawPaperSupport (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      HSLE
        ((hsAdjoint Ψ).comp ((rawSupportCornerJOperatorInvModelConj f Φ hPos A B).comp Ψ))
        (jOperatorInv f A B)

/-- Raw paper-support direct condition, phrased through the actual support-corner operator
transported to the canonical output-support matrix model. -/
def ConditionIII_rawPaperSupport (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      HSLE
        (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)))
        (rawSupportCornerJOperatorModelConj f Φ hPos A B)

/-- The raw paper-support inverse condition is equivalent to the reduced book condition. -/
theorem ConditionII_rawPaperSupport_iff_ConditionII_book (f : ℝ → ℝ) :
    ConditionII_rawPaperSupport f ↔ ConditionII_book f := by
  constructor
  · intro hII n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionII_rawPaperSupport,
      rawSupportCornerJOperatorInv_conj_eq_reducedMap_jOperatorInv] using
      (hII (n := n) (m := m) Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hII n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionII_rawPaperSupport,
      rawSupportCornerJOperatorInv_conj_eq_reducedMap_jOperatorInv] using
      (hII (n := n) (m := m) Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-- The raw paper-support direct condition is equivalent to the reduced book condition. -/
theorem ConditionIII_rawPaperSupport_iff_ConditionIII_book (f : ℝ → ℝ) :
    ConditionIII_rawPaperSupport f ↔ ConditionIII_book f := by
  constructor
  · intro hIII n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionIII_rawPaperSupport,
      rawSupportCornerJOperator_conj_eq_reducedMap_jOperator] using
      (hIII (n := n) (m := m) Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hIII n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionIII_rawPaperSupport,
      rawSupportCornerJOperator_conj_eq_reducedMap_jOperator] using
      (hIII (n := n) (m := m) Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-- The raw and canonical paper-support inverse conditions are equivalent. -/
theorem ConditionII_rawPaperSupport_iff_ConditionII_paperSupport (f : ℝ → ℝ) :
    ConditionII_rawPaperSupport f ↔ ConditionII_paperSupport f :=
  (ConditionII_rawPaperSupport_iff_ConditionII_book f).trans
    (ConditionII_paperSupport_iff_ConditionII_book f).symm

/-- The raw and canonical paper-support direct conditions are equivalent. -/
theorem ConditionIII_rawPaperSupport_iff_ConditionIII_paperSupport (f : ℝ → ℝ) :
    ConditionIII_rawPaperSupport f ↔ ConditionIII_paperSupport f :=
  (ConditionIII_rawPaperSupport_iff_ConditionIII_book f).trans
    (ConditionIII_paperSupport_iff_ConditionIII_book f).symm

/-- Paper-support aggregate statement, with the support-side conditions kept explicit. -/
def paperSupportQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (ConditionI f → ConditionIII_paperSupport f) ∧
    (ConditionII_paperSupport f ↔ ConditionIII_paperSupport f) ∧
    (ConditionIII_paperSupport f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f)

/-- Hiai--Petz 6.2 support-side wrapper via the Loewner route.  This closes the canonical
support-corner theorem; raw support-corner notation is transported by H4b/H5b, and
positive-identity ambient regularization is supplied by `OpMontI.Regularization`.
Theorem 6.2 of [hiai2025]. -/
theorem paper_support_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    paperSupportQuasiEntropyDpiPackageStmt f := by
  intro hf hposf
  rcases book_output_support_quasiEntropy_dpi_package_via_loewner (f := f) hf hposf with
    ⟨hI_to_III, hII_iff_III, hIII_to_IV, hIV_to_I_matrix, hI_matrix_to_I⟩
  refine ⟨?_, ?_, ?_, hIV_to_I_matrix, hI_matrix_to_I⟩
  · intro hI
    exact (ConditionIII_paperSupport_iff_ConditionIII_book f).2 (hI_to_III hI)
  · constructor
    · intro hII
      exact (ConditionIII_paperSupport_iff_ConditionIII_book f).2
        (hII_iff_III.1 ((ConditionII_paperSupport_iff_ConditionII_book f).1 hII))
    · intro hIII
      exact (ConditionII_paperSupport_iff_ConditionII_book f).2
        (hII_iff_III.2 ((ConditionIII_paperSupport_iff_ConditionIII_book f).1 hIII))
  · intro hIII
    exact hIII_to_IV ((ConditionIII_paperSupport_iff_ConditionIII_book f).1 hIII)

/-- Alias emphasizing the Carlen operator-monotonicity route for the support-side wrapper.
Theorem 6.2 of [hiai2025]. -/
theorem paper_support_quasiEntropy_dpi_package_via_carlen_opmontI {f : ℝ → ℝ} :
    paperSupportQuasiEntropyDpiPackageStmt f :=
  paper_support_quasiEntropy_dpi_package_via_loewner

/-- Raw paper-support aggregate statement, with the ambient support-corner conditions explicit. -/
def rawPaperSupportQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (ConditionI f → ConditionIII_rawPaperSupport f) ∧
    (ConditionII_rawPaperSupport f ↔ ConditionIII_rawPaperSupport f) ∧
    (ConditionIII_rawPaperSupport f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f)

/-- Hiai--Petz 6.2 support-side wrapper through raw support-corner paper notation.
Theorem 6.2 of [hiai2025]. -/
theorem raw_paper_support_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    rawPaperSupportQuasiEntropyDpiPackageStmt f := by
  intro hf hposf
  rcases paper_support_quasiEntropy_dpi_package_via_loewner (f := f) hf hposf with
    ⟨hI_to_III, hII_iff_III, hIII_to_IV, hIV_to_I_matrix, hI_matrix_to_I⟩
  refine ⟨?_, ?_, ?_, hIV_to_I_matrix, hI_matrix_to_I⟩
  · intro hI
    exact (ConditionIII_rawPaperSupport_iff_ConditionIII_paperSupport f).2
      (hI_to_III hI)
  · constructor
    · intro hIIraw
      exact (ConditionIII_rawPaperSupport_iff_ConditionIII_paperSupport f).2
        (hII_iff_III.1
          ((ConditionII_rawPaperSupport_iff_ConditionII_paperSupport f).1 hIIraw))
    · intro hIIIraw
      exact (ConditionII_rawPaperSupport_iff_ConditionII_paperSupport f).2
        (hII_iff_III.2
          ((ConditionIII_rawPaperSupport_iff_ConditionIII_paperSupport f).1 hIIIraw))
  · intro hIIIraw
    exact hIII_to_IV
      ((ConditionIII_rawPaperSupport_iff_ConditionIII_paperSupport f).1 hIIIraw)

/-- Alias emphasizing the Carlen operator-monotonicity route for the raw paper-support wrapper.
Theorem 6.2 of [hiai2025]. -/
theorem raw_paper_support_quasiEntropy_dpi_package_via_carlen_opmontI {f : ℝ → ℝ} :
    rawPaperSupportQuasiEntropyDpiPackageStmt f :=
  raw_paper_support_quasiEntropy_dpi_package_via_loewner

end

end Quantum.TraceInequality.Loewner.HiaiPetz
