/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Regularization.CornerCompression

/-!
# Regularization corner inverses

This module contains positive identity regularization, positive inverses on
regularized corners, and real CFC transport on corner actions for the
regularization stage of Carlen 2022, Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder Matrix.Norms.Frobenius Topology
open Filter

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  regularizationHSOpCStarAlgebra
  regularizationHSOpComplexAlgebra
  regularizationHSOpNormedAlgebra
  regularizationHSOpRealCFC
  regularizationHSOpSMulZeroClass
  regularizationHSOpIsBoundedSMul
  regularizationHSOpContinuousSMul
  regularizationHSOpContinuousMul

noncomputable section

/-! ### Positive identity regularization basics -/
/-- Positive-definite matrices stay positive definite after adding a positive scalar identity. -/
theorem matrixPosDef_add_pos_smul_one {n : ℕ} {X : Mₙ n} (hX : MatrixPosDef X)
    {ε : ℝ} (hε : 0 < ε) :
    MatrixPosDef (X + ε • (1 : Mₙ n)) := by
  apply matrixPosDef_of_posDef
  have hXpos : X.PosDef := matrixPosDef_posDef hX
  have hεI : (ε • (1 : Mₙ n)).PosDef :=
    Matrix.PosDef.smul (Matrix.PosDef.one : (1 : Mₙ n).PosDef) hε
  exact Matrix.PosDef.add hXpos hεI

/-! ### Positive inverses on regularized corners -/
namespace MatrixCornerModel

/-- The positive inverse of an ambient left regularization acts on embedded corner matrices as
the embedded coordinate positive inverse. -/
theorem posInv_cornerEmbed_add_real_smul_one_mul_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {A : Mₙ model.dim} (hA : MatrixPosDef A)
    {ε : ℝ} (hε : 0 < ε) (X : Mₙ model.dim) :
    posInv (model.cornerEmbed A + ε • (1 : Mₙ m)) * model.cornerEmbed X =
      model.cornerEmbed (posInv (A + ε • (1 : Mₙ model.dim)) * X) := by
  let Aε : Mₙ m := model.cornerEmbed A + ε • (1 : Mₙ m)
  let aε : Mₙ model.dim := A + ε • (1 : Mₙ model.dim)
  have hcoord : MatrixPosDef aε := by
    simpa [aε] using matrixPosDef_add_pos_smul_one hA hε
  have hamb : MatrixPosDef Aε := by
    simpa [Aε] using model.cornerEmbed_add_pos_smul_one_matrixPosDef hA hε
  have hcoord_unit : IsUnit aε := matrixPosDef_isUnit hcoord
  have hamb_unit : IsUnit Aε := matrixPosDef_isUnit hamb
  have hcoord_cancel : aε * (posInv aε * X) = X := by
    calc
      aε * (posInv aε * X) = (aε * posInv aε) * X := by
        rw [Matrix.mul_assoc]
      _ = X := by
        have hmul : aε * posInv aε = 1 := by
          have hdet : IsUnit aε.det := (Matrix.isUnit_iff_isUnit_det aε).mp hcoord_unit
          simpa [posInv] using Matrix.mul_nonsing_inv aε hdet
        rw [hmul, Matrix.one_mul]
  have haction :
      Aε * model.cornerEmbed (posInv aε * X) =
        model.cornerEmbed (aε * (posInv aε * X)) := by
    simpa [Aε, aε] using
      model.cornerEmbed_add_real_smul_one_mul_cornerEmbed A (posInv aε * X) ε
  have haction_cancel :
      Aε * model.cornerEmbed (posInv aε * X) = model.cornerEmbed X := by
    rw [haction, hcoord_cancel]
  calc
    posInv Aε * model.cornerEmbed X =
        posInv Aε * (Aε * model.cornerEmbed (posInv aε * X)) := by
      rw [haction_cancel]
    _ = (posInv Aε * Aε) * model.cornerEmbed (posInv aε * X) := by
      rw [Matrix.mul_assoc]
    _ = model.cornerEmbed (posInv aε * X) := by
      have hmul : posInv Aε * Aε = 1 := by
        have hdet : IsUnit Aε.det := (Matrix.isUnit_iff_isUnit_det Aε).mp hamb_unit
        simpa [posInv] using Matrix.nonsing_inv_mul Aε hdet
      rw [hmul, Matrix.one_mul]

/-- The positive inverse of an ambient right regularization acts on embedded corner matrices as
the embedded coordinate positive inverse. -/
theorem cornerEmbed_mul_posInv_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {B : Mₙ model.dim} (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) (X : Mₙ model.dim) :
    model.cornerEmbed X * posInv (model.cornerEmbed B + ε • (1 : Mₙ m)) =
      model.cornerEmbed (X * posInv (B + ε • (1 : Mₙ model.dim))) := by
  let Bε : Mₙ m := model.cornerEmbed B + ε • (1 : Mₙ m)
  let bε : Mₙ model.dim := B + ε • (1 : Mₙ model.dim)
  have hcoord : MatrixPosDef bε := by
    simpa [bε] using matrixPosDef_add_pos_smul_one hB hε
  have hamb : MatrixPosDef Bε := by
    simpa [Bε] using model.cornerEmbed_add_pos_smul_one_matrixPosDef hB hε
  have hcoord_unit : IsUnit bε := matrixPosDef_isUnit hcoord
  have hamb_unit : IsUnit Bε := matrixPosDef_isUnit hamb
  have hcoord_cancel : (X * posInv bε) * bε = X := by
    calc
      (X * posInv bε) * bε = X * (posInv bε * bε) := by
        rw [Matrix.mul_assoc]
      _ = X := by
        have hmul : posInv bε * bε = 1 := by
          have hdet : IsUnit bε.det := (Matrix.isUnit_iff_isUnit_det bε).mp hcoord_unit
          simpa [posInv] using Matrix.nonsing_inv_mul bε hdet
        rw [hmul, Matrix.mul_one]
  have haction :
      model.cornerEmbed (X * posInv bε) * Bε =
        model.cornerEmbed ((X * posInv bε) * bε) := by
    simpa [Bε, bε] using
      model.cornerEmbed_mul_cornerEmbed_add_real_smul_one (X * posInv bε) B ε
  have haction_cancel :
      model.cornerEmbed (X * posInv bε) * Bε = model.cornerEmbed X := by
    rw [haction, hcoord_cancel]
  calc
    model.cornerEmbed X * posInv Bε =
        (model.cornerEmbed (X * posInv bε) * Bε) * posInv Bε := by
      rw [haction_cancel]
    _ = model.cornerEmbed (X * posInv bε) * (Bε * posInv Bε) := by
      rw [Matrix.mul_assoc]
    _ = model.cornerEmbed (X * posInv bε) := by
      have hmul : Bε * posInv Bε = 1 := by
        have hdet : IsUnit Bε.det := (Matrix.isUnit_iff_isUnit_det Bε).mp hamb_unit
        simpa [posInv] using Matrix.mul_nonsing_inv Bε hdet
      rw [hmul, Matrix.mul_one]

/-- Corner compression transports left multiplication by the positive inverse of an ambient
regularized embedded corner matrix to coordinate left multiplication by the positive inverse of
the coordinate regularization. -/
theorem cornerCompressHSOp_leftMul_posInv_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {A : Mₙ model.dim}
    (hA : MatrixPosDef A) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (leftMul (posInv (model.cornerEmbed A + ε • (1 : Mₙ m)))) =
      leftMul (posInv (A + ε • (1 : Mₙ model.dim))) := by
  let Aε : Mₙ m := model.cornerEmbed A + ε • (1 : Mₙ m)
  let aε : Mₙ model.dim := A + ε • (1 : Mₙ model.dim)
  have hcoord : MatrixPosDef aε := by
    simpa [aε] using matrixPosDef_add_pos_smul_one hA hε
  have hamb : MatrixPosDef Aε := by
    simpa [Aε] using model.cornerEmbed_add_pos_smul_one_matrixPosDef hA hε
  have hcoord_unit : IsUnit aε := matrixPosDef_isUnit hcoord
  have hamb_unit : IsUnit Aε := matrixPosDef_isUnit hamb
  ext X i j
  have hcoord_cancel : aε * (posInv aε * X) = X := by
    calc
      aε * (posInv aε * X) = (aε * posInv aε) * X := by
        rw [Matrix.mul_assoc]
      _ = X := by
        have hmul : aε * posInv aε = 1 := by
          have hdet : IsUnit aε.det := (Matrix.isUnit_iff_isUnit_det aε).mp hcoord_unit
          simpa [posInv] using Matrix.mul_nonsing_inv aε hdet
        rw [hmul, Matrix.one_mul]
  have haction :
      Aε * model.cornerEmbed (posInv aε * X) =
        model.cornerEmbed (aε * (posInv aε * X)) := by
    simpa [Aε, aε] using
      model.cornerEmbed_add_real_smul_one_mul_cornerEmbed A (posInv aε * X) ε
  have haction_cancel :
      Aε * model.cornerEmbed (posInv aε * X) = model.cornerEmbed X := by
    rw [haction, hcoord_cancel]
  have hsolve :
      posInv Aε * model.cornerEmbed X = model.cornerEmbed (posInv aε * X) := by
    calc
      posInv Aε * model.cornerEmbed X =
          posInv Aε * (Aε * model.cornerEmbed (posInv aε * X)) := by
        rw [haction_cancel]
      _ = (posInv Aε * Aε) * model.cornerEmbed (posInv aε * X) := by
        rw [Matrix.mul_assoc]
      _ = model.cornerEmbed (posInv aε * X) := by
        have hmul : posInv Aε * Aε = 1 := by
          have hdet : IsUnit Aε.det := (Matrix.isUnit_iff_isUnit_det Aε).mp hamb_unit
          simpa [posInv] using Matrix.nonsing_inv_mul Aε hdet
        rw [hmul, Matrix.one_mul]
  have hcorner : model.cornerEmbed (posInv aε * X) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (posInv aε * X)
  have hproj :
      matrixCornerProj P ((leftMul (posInv Aε)) (model.cornerEmbed X)) =
        model.cornerEmbed (posInv aε * X) := by
    rw [leftMul_apply, hsolve, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((leftMul (posInv Aε)) (model.cornerEmbed X)), matrixCornerProj_mem hP⟩) i j =
    (leftMul (posInv aε) X) i j
  have hsub0 :
      (⟨matrixCornerProj P ((leftMul (posInv Aε)) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (posInv aε * X), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (posInv aε * X), hcorner⟩ :
        matrixCornerSubmodule P) = model.toMat.symm (posInv aε * X) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [leftMul_apply, aε] using hpoint

/-- Corner compression transports right multiplication by the positive inverse of an ambient
regularized embedded corner matrix to coordinate right multiplication by the positive inverse of
the coordinate regularization. -/
theorem cornerCompressHSOp_rightMul_posInv_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {B : Mₙ model.dim}
    (hB : MatrixPosDef B) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (rightMul (posInv (model.cornerEmbed B + ε • (1 : Mₙ m)))) =
      rightMul (posInv (B + ε • (1 : Mₙ model.dim))) := by
  let Bε : Mₙ m := model.cornerEmbed B + ε • (1 : Mₙ m)
  let bε : Mₙ model.dim := B + ε • (1 : Mₙ model.dim)
  have hcoord : MatrixPosDef bε := by
    simpa [bε] using matrixPosDef_add_pos_smul_one hB hε
  have hamb : MatrixPosDef Bε := by
    simpa [Bε] using model.cornerEmbed_add_pos_smul_one_matrixPosDef hB hε
  have hcoord_unit : IsUnit bε := matrixPosDef_isUnit hcoord
  have hamb_unit : IsUnit Bε := matrixPosDef_isUnit hamb
  ext X i j
  have hcoord_cancel : (X * posInv bε) * bε = X := by
    calc
      (X * posInv bε) * bε = X * (posInv bε * bε) := by
        rw [Matrix.mul_assoc]
      _ = X := by
        have hmul : posInv bε * bε = 1 := by
          have hdet : IsUnit bε.det := (Matrix.isUnit_iff_isUnit_det bε).mp hcoord_unit
          simpa [posInv] using Matrix.nonsing_inv_mul bε hdet
        rw [hmul, Matrix.mul_one]
  have haction :
      model.cornerEmbed (X * posInv bε) * Bε =
        model.cornerEmbed ((X * posInv bε) * bε) := by
    simpa [Bε, bε] using
      model.cornerEmbed_mul_cornerEmbed_add_real_smul_one (X * posInv bε) B ε
  have haction_cancel :
      model.cornerEmbed (X * posInv bε) * Bε = model.cornerEmbed X := by
    rw [haction, hcoord_cancel]
  have hsolve :
      model.cornerEmbed X * posInv Bε = model.cornerEmbed (X * posInv bε) := by
    calc
      model.cornerEmbed X * posInv Bε =
          (model.cornerEmbed (X * posInv bε) * Bε) * posInv Bε := by
        rw [haction_cancel]
      _ = model.cornerEmbed (X * posInv bε) * (Bε * posInv Bε) := by
        rw [Matrix.mul_assoc]
      _ = model.cornerEmbed (X * posInv bε) := by
        have hmul : Bε * posInv Bε = 1 := by
          have hdet : IsUnit Bε.det := (Matrix.isUnit_iff_isUnit_det Bε).mp hamb_unit
          simpa [posInv] using Matrix.mul_nonsing_inv Bε hdet
        rw [hmul, Matrix.mul_one]
  have hcorner : model.cornerEmbed (X * posInv bε) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (X * posInv bε)
  have hproj :
      matrixCornerProj P ((rightMul (posInv Bε)) (model.cornerEmbed X)) =
        model.cornerEmbed (X * posInv bε) := by
    rw [rightMul_apply, hsolve, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((rightMul (posInv Bε)) (model.cornerEmbed X)), matrixCornerProj_mem hP⟩) i j =
    (rightMul (posInv bε) X) i j
  have hsub0 :
      (⟨matrixCornerProj P ((rightMul (posInv Bε)) (model.cornerEmbed X)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (X * posInv bε), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (X * posInv bε), hcorner⟩ :
        matrixCornerSubmodule P) = model.toMat.symm (X * posInv bε) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun Z : matrixCornerSubmodule P => model.toMat Z i j) (hsub0.trans hsub)
  simpa [rightMul_apply, bε] using hpoint

/-- Corner compression transports the regularized ambient Carlen argument `gArg` to the
coordinate regularized Carlen argument. -/
theorem cornerCompressHSOp_gArg_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {X Y : Mₙ model.dim}
    (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
          (model.cornerEmbed Y + ε • (1 : Mₙ m))) =
      gArg (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim)) := by
  let Xε : Mₙ m := model.cornerEmbed X + ε • (1 : Mₙ m)
  let xε : Mₙ model.dim := X + ε • (1 : Mₙ model.dim)
  let Yε : Mₙ m := model.cornerEmbed Y + ε • (1 : Mₙ m)
  let yε : Mₙ model.dim := Y + ε • (1 : Mₙ model.dim)
  ext Z i j
  have hleft :
      posInv Yε * model.cornerEmbed Z =
        model.cornerEmbed (posInv yε * Z) := by
    simpa [Yε, yε] using
      model.posInv_cornerEmbed_add_real_smul_one_mul_cornerEmbed hY hε Z
  have hright :
      model.cornerEmbed (posInv yε * Z) * Xε =
        model.cornerEmbed ((posInv yε * Z) * xε) := by
    simpa [Xε, xε] using
      model.cornerEmbed_mul_cornerEmbed_add_real_smul_one (posInv yε * Z) X ε
  have happly :
      (gArg Xε Yε) (model.cornerEmbed Z) =
        model.cornerEmbed ((posInv yε * Z) * xε) := by
    calc
      (gArg Xε Yε) (model.cornerEmbed Z) =
          (posInv Yε * model.cornerEmbed Z) * Xε := by
        simp [gArg, ContinuousLinearMap.comp_apply]
      _ = model.cornerEmbed (posInv yε * Z) * Xε := by
        rw [hleft]
      _ = model.cornerEmbed ((posInv yε * Z) * xε) := hright
  have hcorner :
      model.cornerEmbed ((posInv yε * Z) * xε) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem ((posInv yε * Z) * xε)
  have hproj :
      matrixCornerProj P ((gArg Xε Yε) (model.cornerEmbed Z)) =
        model.cornerEmbed ((posInv yε * Z) * xε) := by
    rw [happly, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((gArg Xε Yε) (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩) i j =
    (gArg xε yε Z) i j
  have hsub0 :
      (⟨matrixCornerProj P ((gArg Xε Yε) (model.cornerEmbed Z)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed ((posInv yε * Z) * xε), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed ((posInv yε * Z) * xε), hcorner⟩ :
        matrixCornerSubmodule P) = model.toMat.symm ((posInv yε * Z) * xε) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa [gArg, ContinuousLinearMap.comp_apply, xε, yε, Matrix.mul_add]
    using hpoint

/-- On embedded corner matrices, the regularized ambient Carlen argument `gArg` acts exactly as
the embedded coordinate regularized Carlen argument. -/
theorem gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {X Y : Mₙ model.dim}
    (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((gArg (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim))) Z) := by
  let Xε : Mₙ m := model.cornerEmbed X + ε • (1 : Mₙ m)
  let xε : Mₙ model.dim := X + ε • (1 : Mₙ model.dim)
  let Yε : Mₙ m := model.cornerEmbed Y + ε • (1 : Mₙ m)
  let yε : Mₙ model.dim := Y + ε • (1 : Mₙ model.dim)
  have hleft :
      posInv Yε * model.cornerEmbed Z =
        model.cornerEmbed (posInv yε * Z) := by
    simpa [Yε, yε] using
      model.posInv_cornerEmbed_add_real_smul_one_mul_cornerEmbed hY hε Z
  have hright :
      model.cornerEmbed (posInv yε * Z) * Xε =
        model.cornerEmbed ((posInv yε * Z) * xε) := by
    simpa [Xε, xε] using
      model.cornerEmbed_mul_cornerEmbed_add_real_smul_one (posInv yε * Z) X ε
  calc
    (gArg Xε Yε) (model.cornerEmbed Z) =
        (posInv Yε * model.cornerEmbed Z) * Xε := by
      simp [gArg, ContinuousLinearMap.comp_apply]
    _ = model.cornerEmbed (posInv yε * Z) * Xε := by
      rw [hleft]
    _ = model.cornerEmbed ((posInv yε * Z) * xε) := hright
    _ = model.cornerEmbed ((gArg xε yε) Z) := by
      simp [gArg, ContinuousLinearMap.comp_apply]

/-- The regularized ambient Carlen argument preserves the embedded support corner. -/
theorem gArg_cornerEmbed_add_real_smul_one_maps_corner {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {X Y : Mₙ model.dim}
    (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε)
    (Z : matrixCornerSubmodule P) :
    (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))) Z.1 ∈ matrixCornerSubmodule P := by
  have hZ : model.cornerEmbed (model.toMat Z) = Z.1 := by
    exact congrArg Subtype.val (LinearEquiv.symm_apply_apply model.toMat Z)
  rw [← hZ]
  rw [model.gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed hY hε (model.toMat Z)]
  exact model.cornerEmbed_mem _

/-- The regularized ambient Carlen argument commutes with the raw corner projection. -/
theorem matrixCornerProj_commute_gArg_cornerEmbed_add_real_smul_one {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {X Y : Mₙ model.dim}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    Commute (matrixCornerProj P)
      (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
        (model.cornerEmbed Y + ε • (1 : Mₙ m))) := by
  apply matrixCornerProj_commute_of_selfadjoint_maps_corner hP
  · exact gArg_isSelfAdjoint_of_matrixPosDef
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hX hε)
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hY hε)
  · intro Z
    exact model.gArg_cornerEmbed_add_real_smul_one_maps_corner hY hε Z

/-! ### Real CFC transport on corner actions -/
private theorem hsOp_real_algebraMap_apply {n : ℕ} (a : ℝ) (V : Mₙ n) :
    (algebraMap ℝ (HSOp n) a) V = (a : ℂ) • V := by
  rw [Algebra.algebraMap_eq_smul_one]
  change ((a : ℂ) • (1 : HSOp n)) V = (a : ℂ) • V
  rw [ContinuousLinearMap.smul_apply]
  simp

private theorem cornerAction_mul_embed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {S T : HSOp m} {S₀ T₀ : HSOp model.dim}
    (hS : ∀ V : Mₙ model.dim, S (model.cornerEmbed V) = model.cornerEmbed (S₀ V))
    (hT : ∀ V : Mₙ model.dim, T (model.cornerEmbed V) = model.cornerEmbed (T₀ V)) :
    ∀ V : Mₙ model.dim,
      (S * T) (model.cornerEmbed V) = model.cornerEmbed ((S₀ * T₀) V) := by
  intro V
  simp only [ContinuousLinearMap.mul_apply]
  rw [hT V]
  rw [hS (T₀ V)]

private theorem cornerAction_pow_embed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {T : HSOp m} {T₀ : HSOp model.dim}
    (hT : ∀ V : Mₙ model.dim, T (model.cornerEmbed V) = model.cornerEmbed (T₀ V)) :
    ∀ r : ℕ, ∀ V : Mₙ model.dim,
      (T ^ r) (model.cornerEmbed V) = model.cornerEmbed ((T₀ ^ r) V) := by
  intro r
  induction r with
  | zero =>
      intro V
      simp
  | succ r ih =>
      intro V
      have hmul :=
        model.cornerAction_mul_embed (S := T) (T := T ^ r) (S₀ := T₀) (T₀ := T₀ ^ r)
          hT ih V
      simpa [pow_succ'] using hmul

private theorem cornerAction_aeval_embed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {T : HSOp m} {T₀ : HSOp model.dim}
    (hT : ∀ V : Mₙ model.dim, T (model.cornerEmbed V) = model.cornerEmbed (T₀ V)) :
    ∀ q : Polynomial ℝ, ∀ V : Mₙ model.dim,
      (Polynomial.aeval T q) (model.cornerEmbed V) =
        model.cornerEmbed ((Polynomial.aeval T₀ q) V) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro V
      simp only [map_add, ContinuousLinearMap.add_apply]
      rw [hp V, hq V]
  | monomial r a =>
      intro V
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [ContinuousLinearMap.mul_apply]
      rw [model.cornerAction_pow_embed hT r V]
      rw [hsOp_real_algebraMap_apply (n := m) a]
      rw [hsOp_real_algebraMap_apply (n := model.dim) a]
      simpa using (model.cornerEmbed.map_smul (a : ℂ) ((T₀ ^ r) V)).symm

private theorem hsOp_real_spectrum_finite {n : ℕ} (T : HSOp n) :
    Set.Finite (spectrum ℝ T) := by
  haveI : FiniteDimensional ℂ (HSOp n) := ContinuousLinearMap.finiteDimensional
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    exact spectrum_finite_of_finiteDimensional (K := ℂ) (A := HSOp n) T
  rw [← spectrum.preimage_algebraMap ℂ]
  exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/--
If a Hilbert-Schmidt operator `T` restricts to `T₀` along the corner
embedding of a matrix corner model, then its real functional calculus
`hsCfcR k T` restricts to `hsCfcR k T₀` along the same embedding.
This transports the CFC through corner compression in the regularization
stage of the Hiai-Petz route (statement source: Theorem 6.2 of
[hiai2025]; proved via the Loewner route, Carlen 2022).
-/
theorem cornerAction_hsCfcR_embed {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {T : HSOp m} {T₀ : HSOp model.dim} (k : ℝ → ℝ)
    (hTsa : IsSelfAdjoint T) (hT₀sa : IsSelfAdjoint T₀)
    (hT : ∀ V : Mₙ model.dim, T (model.cornerEmbed V) = model.cornerEmbed (T₀ V)) :
    ∀ V : Mₙ model.dim,
      hsCfcR k T (model.cornerEmbed V) = model.cornerEmbed (hsCfcR k T₀ V) := by
  classical
  let sSet : Set ℝ := spectrum ℝ T ∪ spectrum ℝ T₀
  have hfin : Set.Finite sSet := by
    exact (hsOp_real_spectrum_finite T).union (hsOp_real_spectrum_finite T₀)
  let s : Finset ℝ := hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id fun y ↦ k y
  have hq_mem : ∀ ⦃x : ℝ⦄, x ∈ sSet → q.eval x = k x := by
    intro x hx
    have hx' : x ∈ s := by
      simpa [s] using hx
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun y ↦ k y) (i := x)
        (hvs := fun _ _ _ _ h => h) hx')
  have hq_T : (spectrum ℝ T).EqOn k q.eval := by
    intro x hx
    symm
    exact hq_mem (Set.mem_union_left (spectrum ℝ T₀) hx)
  have hq_T₀ : (spectrum ℝ T₀).EqOn k q.eval := by
    intro x hx
    symm
    exact hq_mem (Set.mem_union_right (spectrum ℝ T) hx)
  have hcfc_T : hsCfcR k T = hsCfcR q.eval T := by
    simpa [hsCfcR] using
      (cfc_congr (a := T) (f := k) (g := q.eval) hq_T)
  have hcfc_T₀ : hsCfcR k T₀ = hsCfcR q.eval T₀ := by
    simpa [hsCfcR] using
      (cfc_congr (a := T₀) (f := k) (g := q.eval) hq_T₀)
  have hpoly_T : hsCfcR q.eval T = Polynomial.aeval T q := by
    simpa [hsCfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hTsa)
  have hpoly_T₀ : hsCfcR q.eval T₀ = Polynomial.aeval T₀ q := by
    simpa [hsCfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T₀) hT₀sa)
  intro V
  calc
    hsCfcR k T (model.cornerEmbed V) =
        (Polynomial.aeval T q) (model.cornerEmbed V) := by
          rw [hcfc_T, hpoly_T]
    _ = model.cornerEmbed ((Polynomial.aeval T₀ q) V) := by
          exact model.cornerAction_aeval_embed hT q V
    _ = model.cornerEmbed (hsCfcR k T₀ V) := by
          rw [← hpoly_T₀, ← hcfc_T₀]

/-- If an ambient Hilbert--Schmidt operator commutes with the raw corner projection, then
every real CFC of it preserves the corner. -/
theorem matrixCornerProj_hsCfcR_of_commute_apply_of_mem {m : ℕ} {P : Mₙ m}
    {k : ℝ → ℝ} {T : HSOp m}
    (hcomm : Commute (matrixCornerProj P) T) {Z : Mₙ m}
    (hZ : Z ∈ matrixCornerSubmodule P) :
    matrixCornerProj P ((hsCfcR k T) Z) = (hsCfcR k T) Z := by
  let proj : HSOp m := matrixCornerProj P
  have hcomm_cfc : Commute (hsCfcR k T) proj := by
    simpa [hsCfcR, proj] using hcomm.symm.cfc_real k
  have hprojZ : proj Z = Z := by
    change matrixCornerProj P Z = Z
    rw [matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hZ
  rw [Commute] at hcomm_cfc
  have happly : (hsCfcR k T) (proj Z) = proj ((hsCfcR k T) Z) := by
    have hmul := congrArg (fun S : HSOp m => S Z) hcomm_cfc
    simpa [ContinuousLinearMap.mul_apply] using hmul
  calc
    matrixCornerProj P ((hsCfcR k T) Z) = proj ((hsCfcR k T) Z) := rfl
    _ = (hsCfcR k T) (proj Z) := happly.symm
    _ = (hsCfcR k T) Z := by rw [hprojZ]

/-- The real CFC of the regularized ambient Carlen argument preserves embedded corner
matrices. -/
theorem matrixCornerProj_hsCfcR_gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {k : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    matrixCornerProj P
        ((hsCfcR k
          (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
            (model.cornerEmbed Y + ε • (1 : Mₙ m))))
          (model.cornerEmbed Z)) =
      (hsCfcR k
        (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
        (model.cornerEmbed Y + ε • (1 : Mₙ m))))
        (model.cornerEmbed Z) := by
  exact matrixCornerProj_hsCfcR_of_commute_apply_of_mem
    (model.matrixCornerProj_commute_gArg_cornerEmbed_add_real_smul_one hP hX hY hε)
    (model.cornerEmbed_mem Z)

/-- On embedded corner matrices, the real CFC of the regularized ambient Carlen argument acts
as the embedded coordinate real CFC. -/
theorem hsCfcR_gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {k : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (hsCfcR k
      (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
        (model.cornerEmbed Y + ε • (1 : Mₙ m))))
      (model.cornerEmbed Z) =
      model.cornerEmbed
        ((hsCfcR k
          (gArg (X + ε • (1 : Mₙ model.dim))
            (Y + ε • (1 : Mₙ model.dim)))) Z) := by
  exact model.cornerAction_hsCfcR_embed k
    (gArg_isSelfAdjoint_of_matrixPosDef
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hX hε)
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hY hε))
    (gArg_isSelfAdjoint_of_matrixPosDef
      (matrixPosDef_add_pos_smul_one hX hε)
      (matrixPosDef_add_pos_smul_one hY hε))
    (model.gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed hY hε) Z

/-- Corner compression transports the real CFC of the regularized ambient Carlen argument to
the real CFC of the coordinate regularized Carlen argument. -/
theorem cornerCompressHSOp_hsCfcR_gArg_cornerEmbed_add_real_smul_one
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {k : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (hsCfcR k
          (gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
            (model.cornerEmbed Y + ε • (1 : Mₙ m)))) =
      hsCfcR k
        (gArg (X + ε • (1 : Mₙ model.dim))
          (Y + ε • (1 : Mₙ model.dim))) := by
  ext Z i j
  let Tamb : HSOp m :=
    gArg (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))
  let Tcoord : HSOp model.dim :=
    gArg (X + ε • (1 : Mₙ model.dim))
      (Y + ε • (1 : Mₙ model.dim))
  have hact :
      (hsCfcR k Tamb) (model.cornerEmbed Z) =
        model.cornerEmbed ((hsCfcR k Tcoord) Z) := by
    simpa [Tamb, Tcoord] using
      model.hsCfcR_gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed hX hY hε Z
  have hcorner :
      model.cornerEmbed ((hsCfcR k Tcoord) Z) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem ((hsCfcR k Tcoord) Z)
  have hproj :
      matrixCornerProj P ((hsCfcR k Tamb) (model.cornerEmbed Z)) =
        model.cornerEmbed ((hsCfcR k Tcoord) Z) := by
    rw [hact, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P
      ((hsCfcR k Tamb) (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩) i j =
    ((hsCfcR k Tcoord) Z) i j
  have hsub0 :
      (⟨matrixCornerProj P ((hsCfcR k Tamb) (model.cornerEmbed Z)),
          matrixCornerProj_mem hP⟩ : matrixCornerSubmodule P) =
        ⟨model.cornerEmbed ((hsCfcR k Tcoord) Z), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed ((hsCfcR k Tcoord) Z), hcorner⟩ :
        matrixCornerSubmodule P) =
        model.toMat.symm ((hsCfcR k Tcoord) Z) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa using hpoint


end MatrixCornerModel

end

end Quantum.TraceInequality.Loewner.HiaiPetz
