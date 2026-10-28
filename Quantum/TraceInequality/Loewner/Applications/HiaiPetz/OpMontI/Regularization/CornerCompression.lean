/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.BoundarySupport

/-!
# Regularization corner compression

This module contains the corner coordinate compression API and the embedded
corner arithmetic used in the regularization stage of Carlen 2022, Theorem 1.46.
-/


namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder Matrix.Norms.Frobenius Topology
open Filter

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance regularizationHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- The adjoint operation on `HSOp n` is continuous. -/
noncomputable local instance regularizationHSOpContinuousStar {n : ℕ} :
    ContinuousStar (HSOp n) := by
  letI : NormedStarGroup (HSOp n) := CStarRing.to_normedStarGroup
  infer_instance

/-- `HSOp n` is a complex algebra. -/
noncomputable local instance regularizationHSOpComplexAlgebra {n : ℕ} :
    Algebra ℂ (HSOp n) :=
  ContinuousLinearMap.algebra

/-- `HSOp n` is a complex normed algebra. -/
noncomputable local instance regularizationHSOpNormedAlgebra {n : ℕ} :
    NormedAlgebra ℂ (HSOp n) :=
  ContinuousLinearMap.toNormedAlgebra

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance regularizationHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Complex scalar multiplication on `HSOp n` preserves zero. -/
noncomputable local instance regularizationHSOpSMulZeroClass {n : ℕ} :
    SMulZeroClass ℂ (HSOp n) :=
  inferInstanceAs (SMulZeroClass ℂ (HSOp n))

/-- Complex scalar multiplication on `HSOp n` is norm-bounded. -/
local instance regularizationHSOpIsBoundedSMul {n : ℕ} :
    IsBoundedSMul ℂ (HSOp n) :=
  IsBoundedSMul.of_norm_smul_le (fun r x => NormedSpace.norm_smul_le r x)

/-- Complex scalar multiplication on `HSOp n` is continuous. -/
local instance regularizationHSOpContinuousSMul {n : ℕ} :
    ContinuousSMul ℂ (HSOp n) :=
  IsBoundedSMul.continuousSMul

/-- Operator composition on `HSOp n` is continuous. -/
local instance regularizationHSOpContinuousMul {n : ℕ} :
    ContinuousMul (HSOp n) where
  continuous_mul := by
    change Continuous (fun p : HSOp n × HSOp n => p.1.comp p.2)
    exact continuous_fst.clm_comp continuous_snd
/-! ### Corner coordinate compression API -/
namespace MatrixCornerModel

/-- Embed the coordinate matrix algebra of a corner back into the ambient matrix algebra. -/
noncomputable def cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) :
    Mₙ model.dim →L[ℂ] Mₙ m :=
  (matrixCornerSubmodule P).subtypeL.comp
    model.toMat.symm.toContinuousLinearMap

@[simp] theorem cornerEmbed_apply {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X : Mₙ model.dim) :
    model.cornerEmbed X = (model.toMat.symm X).1 := by
  rfl

/-- The corner embedding lands in the corner submodule. -/
theorem cornerEmbed_mem {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X : Mₙ model.dim) :
    model.cornerEmbed X ∈ matrixCornerSubmodule P := by
  simp [cornerEmbed]

/-- Applying the raw corner projection `X ↦ PXP` lands in the corner when `P` is a projection. -/
theorem matrixCornerProj_mem {m : ℕ} {P Y : Mₙ m}
    (hP : IsMatrixProj P) :
    matrixCornerProj P Y ∈ matrixCornerSubmodule P := by
  rw [mem_matrixCornerSubmodule_iff, matrixCornerProj_apply]
  rcases hP with ⟨hPidem, _⟩
  calc
    P * (P * Y * P) * P = (P * P) * Y * (P * P) := by
      simp [Matrix.mul_assoc]
    _ = P * Y * P := by
      rw [hPidem]

/-- Corner projection is Hilbert--Schmidt orthogonal projection onto the corner, in the form
needed to move inner products against corner vectors. -/
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

/-- If a self-adjoint Hilbert--Schmidt operator preserves the matrix corner, then it commutes
with the raw corner projection. -/
theorem matrixCornerProj_commute_of_selfadjoint_maps_corner {m : ℕ} {P : Mₙ m}
    (hP : IsMatrixProj P) {T : HSOp m}
    (hT : IsSelfAdjoint T)
    (hcorner : ∀ Z : matrixCornerSubmodule P, T Z.1 ∈ matrixCornerSubmodule P) :
    Commute (matrixCornerProj P) T := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro V
  change matrixCornerProj P (T V) = T (matrixCornerProj P V)
  let Vcorner : Mₙ m := matrixCornerProj P V
  let Voff : Mₙ m := V - Vcorner
  have hV : V = Vcorner + Voff := by
    simp [Voff, Vcorner]
  have hVcorner_mem : Vcorner ∈ matrixCornerSubmodule P := matrixCornerProj_mem hP
  have hTcorner_mem : T Vcorner ∈ matrixCornerSubmodule P :=
    hcorner ⟨Vcorner, hVcorner_mem⟩
  have hproj_Tcorner : matrixCornerProj P (T Vcorner) = T Vcorner := by
    rw [matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hTcorner_mem
  have hproj_Toff : matrixCornerProj P (T Voff) = 0 := by
    let W : Mₙ m := matrixCornerProj P (T Voff)
    have hWmem : W ∈ matrixCornerSubmodule P := matrixCornerProj_mem hP
    have hTWmem : T W ∈ matrixCornerSubmodule P := hcorner ⟨W, hWmem⟩
    have horth : inner ℂ Voff (T W) = 0 := by
      have hproj_inner :
          inner ℂ Vcorner (T W) = inner ℂ V (T W) := by
        simpa [Vcorner] using
          inner_matrixCornerProj_eq_of_mem (P := P) hP hTWmem (Y := V)
      calc
        inner ℂ Voff (T W) = inner ℂ (V - Vcorner) (T W) := by rfl
        _ = inner ℂ V (T W) - inner ℂ Vcorner (T W) := by
          rw [inner_sub_left]
        _ = 0 := by rw [hproj_inner]; simp
    have hsym :=
      (@IsSelfAdjoint.isSymmetric ℂ (Mₙ m) inferInstance
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := m))
        (A := T) hT) Voff W
    have hinnerW : inner ℂ W W = 0 := by
      calc
        inner ℂ W W = inner ℂ (T Voff) W := by
          simpa [W] using
            inner_matrixCornerProj_eq_of_mem (P := P) hP hWmem (Y := T Voff)
        _ = inner ℂ Voff (T W) := hsym
        _ = 0 := horth
    have hWzero : W = 0 := by
      letI : NormedAddCommGroup (Mₙ m) := instMatrixNormedAddCommGroup (n := m)
      letI : InnerProductSpace ℂ (Mₙ m) := instMatrixInnerProductSpace (n := m)
      have hre : Complex.re (inner ℂ W W) = 0 := by
        rw [hinnerW]
        simp
      have hnorm_sq : ‖W‖ ^ 2 = 0 := by
        have hre' : Complex.re ((‖W‖ : ℂ) ^ 2) = 0 := by
          simpa only [inner_self_eq_norm_sq_to_K] using hre
        have hcast : Complex.re ((‖W‖ : ℂ) ^ 2) = ‖W‖ ^ 2 := by
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
        rwa [hcast] at hre'
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq)
    simpa [W] using hWzero
  calc
    matrixCornerProj P (T V) = matrixCornerProj P (T (Vcorner + Voff)) := by rw [hV]
    _ = matrixCornerProj P (T Vcorner + T Voff) := by simp
    _ = matrixCornerProj P (T Vcorner) + matrixCornerProj P (T Voff) := by
      simp [Matrix.add_mul, Matrix.mul_add]
    _ = T Vcorner := by rw [hproj_Tcorner, hproj_Toff, add_zero]
    _ = T (matrixCornerProj P V) := by rfl

/-- Compress an ambient Hilbert--Schmidt operator to the corner coordinate model. -/
noncomputable def cornerCompressHSOp {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (T : HSOp m) :
    HSOp model.dim :=
  model.toMat.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((matrixCornerProj P).comp (T.comp model.cornerEmbed)).codRestrict
      (matrixCornerSubmodule P) (fun _ => matrixCornerProj_mem hP))

@[simp] theorem cornerCompressHSOp_apply {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (T : HSOp m)
    (X : Mₙ model.dim) :
    model.cornerCompressHSOp hP T X =
      model.toMat ⟨matrixCornerProj P (T (model.cornerEmbed X)), matrixCornerProj_mem hP⟩ := by
  rfl

/-- Quadratic-form view of a corner-compressed ambient Hilbert--Schmidt operator. -/
noncomputable def cornerCompressedQF {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (T : HSOp m)
    (Z : Mₙ model.dim) : ℝ :=
  hsQF (model.cornerCompressHSOp hP T) Z

/-- The quadratic form of a corner-compressed operator is the ambient quadratic form
evaluated on the embedded corner vector. -/
theorem cornerCompressHSOp_hsQF_eq {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (T : HSOp m)
    (Z : Mₙ model.dim) :
    hsQF (model.cornerCompressHSOp hP T) Z = hsQF T (model.cornerEmbed Z) := by
  have hinner :
      inner ℂ Z (model.cornerCompressHSOp hP T Z) =
        inner ℂ (model.cornerEmbed Z) (matrixCornerProj P (T (model.cornerEmbed Z))) := by
    simpa [cornerCompressHSOp_apply, cornerEmbed] using
      model.inner_toMat_eq (model.toMat.symm Z)
        ⟨matrixCornerProj P (T (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩
  have hdrop :
      inner ℂ (model.cornerEmbed Z) (matrixCornerProj P (T (model.cornerEmbed Z))) =
        inner ℂ (model.cornerEmbed Z) (T (model.cornerEmbed Z)) := by
    have hproj :=
      inner_matrixCornerProj_eq_of_mem hP (model.cornerEmbed_mem Z)
        (Y := T (model.cornerEmbed Z))
    have hconj := congrArg star hproj
    simpa [inner_conj_symm] using hconj
  unfold hsQF
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose Z * model.cornerCompressHSOp hP T Z)) =
        Complex.re (inner ℂ Z (model.cornerCompressHSOp hP T Z)) := by
          change Complex.re
              (Matrix.trace
                (Matrix.conjTranspose Z * model.cornerCompressHSOp hP T Z)) =
            Complex.re
              (Matrix.trace
                (model.cornerCompressHSOp hP T Z * Matrix.conjTranspose Z))
          rw [Matrix.trace_mul_comm]
    _ =
        Complex.re
          (inner ℂ (model.cornerEmbed Z) (matrixCornerProj P (T (model.cornerEmbed Z)))) := by
          rw [hinner]
    _ = Complex.re (inner ℂ (model.cornerEmbed Z) (T (model.cornerEmbed Z))) := by
          rw [hdrop]
    _ =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (model.cornerEmbed Z) * T (model.cornerEmbed Z))) := by
          change Complex.re
              (Matrix.trace
                (T (model.cornerEmbed Z) * Matrix.conjTranspose (model.cornerEmbed Z))) =
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose (model.cornerEmbed Z) * T (model.cornerEmbed Z)))
          rw [Matrix.trace_mul_comm]

/-! ### Embedded corner arithmetic and positive inputs -/
/-- The corner embedding sends a positive square in coordinates to a positive square in ambient
coordinates. -/
theorem cornerEmbed_star_mul_self {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y : Mₙ model.dim) :
    model.cornerEmbed (star Y * Y) = star (model.cornerEmbed Y) * model.cornerEmbed Y := by
  ext i j
  change ((model.toMat.symm (star Y * Y)).1) i j =
    (star ((model.toMat.symm Y).1) * (model.toMat.symm Y).1) i j
  rw [MatrixCornerModel.toMat_symm_star_mul]

/-- The corner embedding preserves multiplication. -/
theorem cornerEmbed_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y Z : Mₙ model.dim) :
    model.cornerEmbed (Y * Z) = model.cornerEmbed Y * model.cornerEmbed Z := by
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  let Zcorner : matrixCornerSubmodule P := model.toMat.symm Z
  let YZcorner : matrixCornerSubmodule P :=
    ⟨Ycorner.1 * Zcorner.1, model.mul_mem_corner Ycorner Zcorner⟩
  have hYZ : model.toMat YZcorner = Y * Z := by
    calc
      model.toMat YZcorner = model.toMat Ycorner * model.toMat Zcorner :=
        model.map_mul Ycorner Zcorner
      _ = Y * Z := by simp [Ycorner, Zcorner]
  have hsub : model.toMat.symm (Y * Z) = YZcorner := by
    apply model.toMat.injective
    simp [hYZ]
  ext i j
  simpa [cornerEmbed, Ycorner, Zcorner, YZcorner] using congrFun (congrFun
    (congrArg Subtype.val hsub) i) j

/-- Embedded left regularized multiplication acts on embedded corner matrices as coordinate
left regularized multiplication. -/
theorem cornerEmbed_add_complex_smul_one_mul_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (A X : Mₙ model.dim) (c : ℂ) :
    (model.cornerEmbed A + c • (1 : Mₙ m)) * model.cornerEmbed X =
      model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) := by
  have hmul :
      model.cornerEmbed A * model.cornerEmbed X = model.cornerEmbed (A * X) :=
    (model.cornerEmbed_mul A X).symm
  have hlin :
      model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) =
        model.cornerEmbed (A * X) + c • model.cornerEmbed X := by
    calc
      model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) =
          model.cornerEmbed (A * X + c • X) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = model.cornerEmbed (A * X) + c • model.cornerEmbed X := by
        simp
  calc
    (model.cornerEmbed A + c • (1 : Mₙ m)) * model.cornerEmbed X =
        model.cornerEmbed A * model.cornerEmbed X + c • model.cornerEmbed X := by
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = model.cornerEmbed (A * X) + c • model.cornerEmbed X := by
      rw [hmul]
    _ = model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) := hlin.symm

/-- Embedded right regularized multiplication acts on embedded corner matrices as coordinate
right regularized multiplication. -/
theorem cornerEmbed_mul_cornerEmbed_add_complex_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X B : Mₙ model.dim) (c : ℂ) :
    model.cornerEmbed X * (model.cornerEmbed B + c • (1 : Mₙ m)) =
      model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) := by
  have hmul :
      model.cornerEmbed X * model.cornerEmbed B = model.cornerEmbed (X * B) :=
    (model.cornerEmbed_mul X B).symm
  have hlin :
      model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) =
        model.cornerEmbed (X * B) + c • model.cornerEmbed X := by
    calc
      model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) =
          model.cornerEmbed (X * B + c • X) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      _ = model.cornerEmbed (X * B) + c • model.cornerEmbed X := by
        simp
  calc
    model.cornerEmbed X * (model.cornerEmbed B + c • (1 : Mₙ m)) =
        model.cornerEmbed X * model.cornerEmbed B + c • model.cornerEmbed X := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    _ = model.cornerEmbed (X * B) + c • model.cornerEmbed X := by
      rw [hmul]
    _ = model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) := hlin.symm

/-- Real-parameter version of `cornerEmbed_add_complex_smul_one_mul_cornerEmbed`. -/
theorem cornerEmbed_add_real_smul_one_mul_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (A X : Mₙ model.dim) (ε : ℝ) :
    (model.cornerEmbed A + ε • (1 : Mₙ m)) * model.cornerEmbed X =
      model.cornerEmbed ((A + ε • (1 : Mₙ model.dim)) * X) := by
  simpa [Complex.real_smul] using
    model.cornerEmbed_add_complex_smul_one_mul_cornerEmbed A X (ε : ℂ)

/-- Real-parameter version of `cornerEmbed_mul_cornerEmbed_add_complex_smul_one`. -/
theorem cornerEmbed_mul_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X B : Mₙ model.dim) (ε : ℝ) :
    model.cornerEmbed X * (model.cornerEmbed B + ε • (1 : Mₙ m)) =
      model.cornerEmbed (X * (B + ε • (1 : Mₙ model.dim))) := by
  simpa [Complex.real_smul] using
    model.cornerEmbed_mul_cornerEmbed_add_complex_smul_one X B (ε : ℂ)

/-- Compressing left multiplication by an embedded corner matrix gives coordinate left
multiplication. -/
theorem cornerCompressHSOp_leftMul_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (A : Mₙ model.dim) :
    model.cornerCompressHSOp hP (leftMul (model.cornerEmbed A)) = leftMul A := by
  ext X i j
  have hprod :
      model.cornerEmbed A * model.cornerEmbed X = model.cornerEmbed (A * X) := by
    exact (model.cornerEmbed_mul A X).symm
  have hcorner : model.cornerEmbed (A * X) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (A * X)
  have hproj :
      matrixCornerProj P ((leftMul (model.cornerEmbed A)) (model.cornerEmbed X)) =
        model.cornerEmbed (A * X) := by
    rw [leftMul_apply, hprod, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((leftMul (model.cornerEmbed A)) (model.cornerEmbed X)), matrixCornerProj_mem hP⟩) i j =
    (leftMul A X) i j
  have hsub0 :
      (⟨matrixCornerProj P ((leftMul (model.cornerEmbed A)) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (A * X), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (A * X), hcorner⟩ :
        matrixCornerSubmodule P) = model.toMat.symm (A * X) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [Matrix.add_mul] using hpoint

/-- Compressing right multiplication by an embedded corner matrix gives coordinate right
multiplication. -/
theorem cornerCompressHSOp_rightMul_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (B : Mₙ model.dim) :
    model.cornerCompressHSOp hP (rightMul (model.cornerEmbed B)) = rightMul B := by
  ext X i j
  have hprod :
      model.cornerEmbed X * model.cornerEmbed B = model.cornerEmbed (X * B) := by
    exact (model.cornerEmbed_mul X B).symm
  have hcorner : model.cornerEmbed (X * B) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (X * B)
  have hproj :
      matrixCornerProj P ((rightMul (model.cornerEmbed B)) (model.cornerEmbed X)) =
        model.cornerEmbed (X * B) := by
    rw [rightMul_apply, hprod, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((rightMul (model.cornerEmbed B)) (model.cornerEmbed X)), matrixCornerProj_mem hP⟩) i j =
    (rightMul B X) i j
  have hsub0 :
      (⟨matrixCornerProj P ((rightMul (model.cornerEmbed B)) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (X * B), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (X * B), hcorner⟩ :
        matrixCornerSubmodule P) = model.toMat.symm (X * B) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [Matrix.mul_add] using hpoint

/-- Compressing left multiplication by an embedded corner matrix plus a scalar ambient identity
gives coordinate left multiplication by the same scalar identity regularization. -/
theorem cornerCompressHSOp_leftMul_cornerEmbed_add_complex_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (A : Mₙ model.dim) (c : ℂ) :
    model.cornerCompressHSOp hP (leftMul (model.cornerEmbed A + c • (1 : Mₙ m))) =
      leftMul (A + c • (1 : Mₙ model.dim)) := by
  ext X i j
  have hcorner : model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) ∈
      matrixCornerSubmodule P :=
    model.cornerEmbed_mem ((A + c • (1 : Mₙ model.dim)) * X)
  have hproj :
      matrixCornerProj P
          ((leftMul (model.cornerEmbed A + c • (1 : Mₙ m))) (model.cornerEmbed X)) =
        model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) := by
    have hXmem : model.cornerEmbed X ∈ matrixCornerSubmodule P :=
      model.cornerEmbed_mem X
    have hAXmem : model.cornerEmbed (A * X) ∈ matrixCornerSubmodule P :=
      model.cornerEmbed_mem (A * X)
    have hXright : model.cornerEmbed X * P = model.cornerEmbed X :=
      matrixCornerSubmodule_right_fix hP hXmem
    have hsum_mem :
        model.cornerEmbed (A * X) + c • model.cornerEmbed X ∈ matrixCornerSubmodule P :=
      Submodule.add_mem _ hAXmem (Submodule.smul_mem _ c hXmem)
    have hmul :
        model.cornerEmbed A * model.cornerEmbed X = model.cornerEmbed (A * X) :=
      (model.cornerEmbed_mul A X).symm
    have hlin :
        model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) =
          model.cornerEmbed (A * X) + c • model.cornerEmbed X := by
      calc
        model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) =
            model.cornerEmbed (A * X + c • X) := by
          rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
        _ = model.cornerEmbed (A * X) + c • model.cornerEmbed X := by
          simp
    calc
      matrixCornerProj P
          ((leftMul (model.cornerEmbed A + c • (1 : Mₙ m))) (model.cornerEmbed X))
          = P * ((model.cornerEmbed A + c • (1 : Mₙ m)) * model.cornerEmbed X) * P := by
            rw [matrixCornerProj_apply, leftMul_apply]
      _ = P * (model.cornerEmbed A * model.cornerEmbed X + c • model.cornerEmbed X) * P := by
            rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = P * (model.cornerEmbed (A * X) + c • model.cornerEmbed X) * P := by
            rw [hmul]
      _ = model.cornerEmbed (A * X) + c • model.cornerEmbed X :=
            mem_matrixCornerSubmodule_iff.mp hsum_mem
      _ = model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X) := hlin.symm
  change (model.toMat ⟨matrixCornerProj P
      ((leftMul (model.cornerEmbed A + c • (1 : Mₙ m))) (model.cornerEmbed X)),
        matrixCornerProj_mem hP⟩) i j =
    (leftMul (A + c • (1 : Mₙ model.dim)) X) i j
  have hsub0 :
      (⟨matrixCornerProj P
          ((leftMul (model.cornerEmbed A + c • (1 : Mₙ m))) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed ((A + c • (1 : Mₙ model.dim)) * X), hcorner⟩ :
        matrixCornerSubmodule P) =
        model.toMat.symm ((A + c • (1 : Mₙ model.dim)) * X) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [Matrix.add_mul] using hpoint

/-- Compressing right multiplication by an embedded corner matrix plus a scalar ambient identity
gives coordinate right multiplication by the same scalar identity regularization. -/
theorem cornerCompressHSOp_rightMul_cornerEmbed_add_complex_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (B : Mₙ model.dim) (c : ℂ) :
    model.cornerCompressHSOp hP (rightMul (model.cornerEmbed B + c • (1 : Mₙ m))) =
      rightMul (B + c • (1 : Mₙ model.dim)) := by
  ext X i j
  have hcorner : model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) ∈
      matrixCornerSubmodule P :=
    model.cornerEmbed_mem (X * (B + c • (1 : Mₙ model.dim)))
  have hproj :
      matrixCornerProj P
          ((rightMul (model.cornerEmbed B + c • (1 : Mₙ m))) (model.cornerEmbed X)) =
        model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) := by
    have hXmem : model.cornerEmbed X ∈ matrixCornerSubmodule P :=
      model.cornerEmbed_mem X
    have hXBmem : model.cornerEmbed (X * B) ∈ matrixCornerSubmodule P :=
      model.cornerEmbed_mem (X * B)
    have hXleft : P * model.cornerEmbed X = model.cornerEmbed X :=
      matrixCornerSubmodule_left_fix hP hXmem
    have hsum_mem :
        model.cornerEmbed (X * B) + c • model.cornerEmbed X ∈ matrixCornerSubmodule P :=
      Submodule.add_mem _ hXBmem (Submodule.smul_mem _ c hXmem)
    have hmul :
        model.cornerEmbed X * model.cornerEmbed B = model.cornerEmbed (X * B) :=
      (model.cornerEmbed_mul X B).symm
    have hlin :
        model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) =
          model.cornerEmbed (X * B) + c • model.cornerEmbed X := by
      calc
        model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) =
            model.cornerEmbed (X * B + c • X) := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
        _ = model.cornerEmbed (X * B) + c • model.cornerEmbed X := by
          simp
    calc
      matrixCornerProj P
          ((rightMul (model.cornerEmbed B + c • (1 : Mₙ m))) (model.cornerEmbed X))
          = P * (model.cornerEmbed X * (model.cornerEmbed B + c • (1 : Mₙ m))) * P := by
            rw [matrixCornerProj_apply, rightMul_apply]
      _ = P * (model.cornerEmbed X * model.cornerEmbed B + c • model.cornerEmbed X) * P := by
            rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      _ = P * (model.cornerEmbed (X * B) + c • model.cornerEmbed X) * P := by
            rw [hmul]
      _ = model.cornerEmbed (X * B) + c • model.cornerEmbed X :=
            mem_matrixCornerSubmodule_iff.mp hsum_mem
      _ = model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))) := hlin.symm
  change (model.toMat ⟨matrixCornerProj P
      ((rightMul (model.cornerEmbed B + c • (1 : Mₙ m))) (model.cornerEmbed X)),
        matrixCornerProj_mem hP⟩) i j =
    (rightMul (B + c • (1 : Mₙ model.dim)) X) i j
  have hsub0 :
      (⟨matrixCornerProj P
          ((rightMul (model.cornerEmbed B + c • (1 : Mₙ m))) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (X * (B + c • (1 : Mₙ model.dim))), hcorner⟩ :
        matrixCornerSubmodule P) =
        model.toMat.symm (X * (B + c • (1 : Mₙ model.dim))) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [Matrix.mul_add] using hpoint

/-- Real-scalar version of
`cornerCompressHSOp_leftMul_cornerEmbed_add_complex_smul_one`, matching the theorem-facing
positive identity regularization parameter. -/
theorem cornerCompressHSOp_leftMul_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (A : Mₙ model.dim) (ε : ℝ) :
    model.cornerCompressHSOp hP (leftMul (model.cornerEmbed A + ε • (1 : Mₙ m))) =
      leftMul (A + ε • (1 : Mₙ model.dim)) := by
  simpa [Complex.real_smul] using
    model.cornerCompressHSOp_leftMul_cornerEmbed_add_complex_smul_one hP A (ε : ℂ)

/-- Real-scalar version of
`cornerCompressHSOp_rightMul_cornerEmbed_add_complex_smul_one`, matching the theorem-facing
positive identity regularization parameter. -/
theorem cornerCompressHSOp_rightMul_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) (B : Mₙ model.dim) (ε : ℝ) :
    model.cornerCompressHSOp hP (rightMul (model.cornerEmbed B + ε • (1 : Mₙ m))) =
      rightMul (B + ε • (1 : Mₙ model.dim)) := by
  simpa only [Complex.real_smul] using
    model.cornerCompressHSOp_rightMul_cornerEmbed_add_complex_smul_one hP B (ε : ℂ)

/-- Positive-definite coordinate matrices embed as positive-semidefinite ambient matrices. -/
theorem cornerEmbed_posSemidef_of_matrixPosDef {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {X : Mₙ model.dim} (hX : MatrixPosDef X) :
    (model.cornerEmbed X).PosSemidef := by
  have hXpsd : X.PosSemidef := (matrixPosDef_posDef hX).posSemidef
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self hXpsd
  rw [hY]
  have hmul :
      model.cornerEmbed (Matrix.conjTranspose Y * Y) =
        Matrix.conjTranspose (model.cornerEmbed Y) * model.cornerEmbed Y := by
    simpa [Matrix.star_eq_conjTranspose] using model.cornerEmbed_star_mul_self Y
  rw [hmul]
  exact Matrix.posSemidef_conjTranspose_mul_self (model.cornerEmbed Y)

/-- Adding a positive scalar multiple of the ambient identity to an embedded corner-positive
matrix gives a positive-definite ambient matrix. -/
theorem cornerEmbed_add_pos_smul_one_matrixPosDef {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {X : Mₙ model.dim} (hX : MatrixPosDef X)
    {ε : ℝ} (hε : 0 < ε) :
    MatrixPosDef (model.cornerEmbed X + ε • (1 : Mₙ m)) := by
  apply matrixPosDef_of_posDef
  have hcorner : (model.cornerEmbed X).PosSemidef :=
    model.cornerEmbed_posSemidef_of_matrixPosDef hX
  have hεI : (ε • (1 : Mₙ m)).PosDef :=
    Matrix.PosDef.smul (Matrix.PosDef.one : (1 : Mₙ m).PosDef) hε
  exact Matrix.PosDef.posSemidef_add hcorner hεI

/-- Two-input version of `cornerEmbed_add_pos_smul_one_matrixPosDef`, matching the `G_f`/`J_f`
regularized domain checks. -/
theorem cornerEmbed_pair_add_pos_smul_one_matrixPosDef {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {A B : Mₙ model.dim}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) {ε : ℝ} (hε : 0 < ε) :
    MatrixPosDef (model.cornerEmbed A + ε • (1 : Mₙ m)) ∧
      MatrixPosDef (model.cornerEmbed B + ε • (1 : Mₙ m)) := by
  exact ⟨model.cornerEmbed_add_pos_smul_one_matrixPosDef hA hε,
    model.cornerEmbed_add_pos_smul_one_matrixPosDef hB hε⟩

@[simp]
theorem cornerCompressHSOp_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) :
    model.cornerCompressHSOp hP (1 : HSOp m) = (1 : HSOp model.dim) := by
  ext X i j
  have hcorner : model.cornerEmbed X ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem X
  have hproj : matrixCornerProj P (model.cornerEmbed X) = model.cornerEmbed X := by
    rw [matrixCornerProj_apply]
    exact (mem_matrixCornerSubmodule_iff.mp hcorner)
  change (model.toMat ⟨matrixCornerProj P ((1 : HSOp m) (model.cornerEmbed X)),
      matrixCornerProj_mem hP⟩) i j = X i j
  simp only [ContinuousLinearMap.one_apply]
  have hsub :
      (⟨matrixCornerProj P (model.cornerEmbed X), matrixCornerProj_mem hP⟩ :
        matrixCornerSubmodule P) = model.toMat.symm X := by
    ext a b
    simpa [cornerEmbed] using congrFun (congrFun hproj a) b
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) hsub
  simpa using hpoint

end MatrixCornerModel

end

end Quantum.TraceInequality.Loewner.HiaiPetz
