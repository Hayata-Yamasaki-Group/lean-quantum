/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Regularization.CornerInverses

/-!
# Regularization operator compression

This module contains the Carlen G-operator compression/inverse identities, the
Hiai--Petz J-operator corner compression identities, and the ambient strict
regularization continuity primitives for the regularization stage of Carlen
2022, Theorem 1.46.
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

namespace MatrixCornerModel

/-! ### Carlen G-operator compression and inverses -/
/-- On embedded corner matrices, the regularized ambient `G_f` acts as the embedded
coordinate regularized `G_f`. -/
theorem gOperator_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {f : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (gOperator f
      (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((gOperator f
          (X + ε • (1 : Mₙ model.dim))
          (Y + ε • (1 : Mₙ model.dim))) Z) := by
  let Xε : Mₙ m := model.cornerEmbed X + ε • (1 : Mₙ m)
  let Yε : Mₙ m := model.cornerEmbed Y + ε • (1 : Mₙ m)
  let xε : Mₙ model.dim := X + ε • (1 : Mₙ model.dim)
  let yε : Mₙ model.dim := Y + ε • (1 : Mₙ model.dim)
  have hleft : (leftMul Yε : HSOp m) (model.cornerEmbed Z) =
      model.cornerEmbed (yε * Z) := by
    simpa only [Yε, yε, leftMul_apply] using
      model.cornerEmbed_add_real_smul_one_mul_cornerEmbed Y Z ε
  calc
    (gOperator f Xε Yε) (model.cornerEmbed Z) =
        (hsCfcR f (gArg Xε Yε)) ((leftMul Yε : HSOp m) (model.cornerEmbed Z)) := by
          simp [gOperator, ContinuousLinearMap.mul_apply]
    _ = (hsCfcR f (gArg Xε Yε)) (model.cornerEmbed (yε * Z)) := by
          rw [hleft]
    _ = model.cornerEmbed ((hsCfcR f (gArg xε yε)) (yε * Z)) := by
          simpa [Xε, Yε, xε, yε] using
            model.hsCfcR_gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
              hX hY hε (yε * Z)
    _ = model.cornerEmbed ((gOperator f xε yε) Z) := by
          rfl

/-- Corner compression transports the regularized ambient `G_f` to the coordinate
regularized `G_f`. -/
theorem cornerCompressHSOp_gOperator_cornerEmbed_add_real_smul_one
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (gOperator f
          (model.cornerEmbed X + ε • (1 : Mₙ m))
          (model.cornerEmbed Y + ε • (1 : Mₙ m))) =
      gOperator f
        (X + ε • (1 : Mₙ model.dim))
        (Y + ε • (1 : Mₙ model.dim)) := by
  ext Z i j
  let Gamb : HSOp m :=
    gOperator f
      (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))
  let Gcoord : HSOp model.dim :=
    gOperator f
      (X + ε • (1 : Mₙ model.dim))
      (Y + ε • (1 : Mₙ model.dim))
  have hact : Gamb (model.cornerEmbed Z) = model.cornerEmbed (Gcoord Z) := by
    simpa [Gamb, Gcoord] using
      model.gOperator_cornerEmbed_add_real_smul_one_apply_cornerEmbed hX hY hε Z
  have hcorner : model.cornerEmbed (Gcoord Z) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (Gcoord Z)
  have hproj :
      matrixCornerProj P (Gamb (model.cornerEmbed Z)) =
        model.cornerEmbed (Gcoord Z) := by
    rw [hact, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P (Gamb (model.cornerEmbed Z)),
      matrixCornerProj_mem hP⟩) i j = (Gcoord Z) i j
  have hsub0 :
      (⟨matrixCornerProj P (Gamb (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩ :
        matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (Gcoord Z), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (Gcoord Z), hcorner⟩ : matrixCornerSubmodule P) =
        model.toMat.symm (Gcoord Z) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa using hpoint

/-- On embedded corner matrices, the regularized ambient theorem-facing `G_f^{-1}` acts as
the embedded coordinate regularized `G_f^{-1}`. -/
theorem gOperatorInv_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {f : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (gOperatorInv f
      (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((gOperatorInv f
          (X + ε • (1 : Mₙ model.dim))
          (Y + ε • (1 : Mₙ model.dim))) Z) := by
  let Xε : Mₙ m := model.cornerEmbed X + ε • (1 : Mₙ m)
  let Yε : Mₙ m := model.cornerEmbed Y + ε • (1 : Mₙ m)
  let xε : Mₙ model.dim := X + ε • (1 : Mₙ model.dim)
  let yε : Mₙ model.dim := Y + ε • (1 : Mₙ model.dim)
  have hleft : (leftMul (posInv Yε) : HSOp m) (model.cornerEmbed Z) =
      model.cornerEmbed (posInv yε * Z) := by
    simpa only [Yε, yε, leftMul_apply] using
      model.posInv_cornerEmbed_add_real_smul_one_mul_cornerEmbed hY hε Z
  calc
    (gOperatorInv f Xε Yε) (model.cornerEmbed Z) =
        (hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg Xε Yε))
          ((leftMul (posInv Yε) : HSOp m) (model.cornerEmbed Z)) := by
          simp [gOperatorInv, ContinuousLinearMap.mul_apply]
    _ = (hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg Xε Yε))
        (model.cornerEmbed (posInv yε * Z)) := by
          rw [hleft]
    _ = model.cornerEmbed
        ((hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg xε yε)) (posInv yε * Z)) := by
          simpa [Xε, Yε, xε, yε] using
            model.hsCfcR_gArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
              (k := fun x : ℝ => (f x)⁻¹) hX hY hε (posInv yε * Z)
    _ = model.cornerEmbed ((gOperatorInv f xε yε) Z) := by
          rfl

/-- Corner compression transports the regularized ambient theorem-facing `G_f^{-1}` to the
coordinate regularized `G_f^{-1}`. -/
theorem cornerCompressHSOp_gOperatorInv_cornerEmbed_add_real_smul_one
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {X Y : Mₙ model.dim} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (gOperatorInv f
          (model.cornerEmbed X + ε • (1 : Mₙ m))
          (model.cornerEmbed Y + ε • (1 : Mₙ m))) =
      gOperatorInv f
        (X + ε • (1 : Mₙ model.dim))
        (Y + ε • (1 : Mₙ model.dim)) := by
  ext Z i j
  let Gamb : HSOp m :=
    gOperatorInv f
      (model.cornerEmbed X + ε • (1 : Mₙ m))
      (model.cornerEmbed Y + ε • (1 : Mₙ m))
  let Gcoord : HSOp model.dim :=
    gOperatorInv f
      (X + ε • (1 : Mₙ model.dim))
      (Y + ε • (1 : Mₙ model.dim))
  have hact : Gamb (model.cornerEmbed Z) = model.cornerEmbed (Gcoord Z) := by
    simpa [Gamb, Gcoord] using
      model.gOperatorInv_cornerEmbed_add_real_smul_one_apply_cornerEmbed hX hY hε Z
  have hcorner : model.cornerEmbed (Gcoord Z) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (Gcoord Z)
  have hproj :
      matrixCornerProj P (Gamb (model.cornerEmbed Z)) =
        model.cornerEmbed (Gcoord Z) := by
    rw [hact, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P (Gamb (model.cornerEmbed Z)),
      matrixCornerProj_mem hP⟩) i j = (Gcoord Z) i j
  have hsub0 :
      (⟨matrixCornerProj P (Gamb (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩ :
        matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (Gcoord Z), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (Gcoord Z), hcorner⟩ : matrixCornerSubmodule P) =
        model.toMat.symm (Gcoord Z) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa using hpoint

/-- Version of `cornerCompressHSOp_gOperator_cornerEmbed_add_real_smul_one` where the
ambient inputs are supplied by explicit corner-embedding equalities. -/
theorem cornerCompressHSOp_gOperator_add_real_smul_one_of_cornerEmbed_eq
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ m} {X Y : Mₙ model.dim}
    (hXembed : model.cornerEmbed X = A) (hYembed : model.cornerEmbed Y = B)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (gOperator f (A + ε • (1 : Mₙ m)) (B + ε • (1 : Mₙ m))) =
      gOperator f
        (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim)) := by
  rw [← hXembed, ← hYembed]
  exact model.cornerCompressHSOp_gOperator_cornerEmbed_add_real_smul_one
    hP (f := f) hX hY hε

/-- Version of `cornerCompressHSOp_gOperatorInv_cornerEmbed_add_real_smul_one` where the
ambient inputs are supplied by explicit corner-embedding equalities. -/
theorem cornerCompressHSOp_gOperatorInv_add_real_smul_one_of_cornerEmbed_eq
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ m} {X Y : Mₙ model.dim}
    (hXembed : model.cornerEmbed X = A) (hYembed : model.cornerEmbed Y = B)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (gOperatorInv f (A + ε • (1 : Mₙ m)) (B + ε • (1 : Mₙ m))) =
      gOperatorInv f
        (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim)) := by
  rw [← hXembed, ← hYembed]
  exact model.cornerCompressHSOp_gOperatorInv_cornerEmbed_add_real_smul_one
    hP (f := f) hX hY hε

/-! ### Hiai-Petz J-operator corner compression -/
/-- On embedded corner matrices, the regularized ambient Hiai--Petz argument `jArg` acts as
the embedded coordinate regularized `jArg`. -/
theorem jArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {A B : Mₙ model.dim}
    (hB : MatrixPosDef B) {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (jArg (model.cornerEmbed A + ε • (1 : Mₙ m))
      (model.cornerEmbed B + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((jArg (A + ε • (1 : Mₙ model.dim)) (B + ε • (1 : Mₙ model.dim))) Z) := by
  let Aε : Mₙ m := model.cornerEmbed A + ε • (1 : Mₙ m)
  let Bε : Mₙ m := model.cornerEmbed B + ε • (1 : Mₙ m)
  let aε : Mₙ model.dim := A + ε • (1 : Mₙ model.dim)
  let bε : Mₙ model.dim := B + ε • (1 : Mₙ model.dim)
  have hright :
      model.cornerEmbed Z * posInv Bε =
        model.cornerEmbed (Z * posInv bε) := by
    simpa [Bε, bε] using
      model.cornerEmbed_mul_posInv_cornerEmbed_add_real_smul_one hB hε Z
  have hleft :
      Aε * model.cornerEmbed (Z * posInv bε) =
        model.cornerEmbed (aε * (Z * posInv bε)) := by
    simpa [Aε, aε] using
      model.cornerEmbed_add_real_smul_one_mul_cornerEmbed A (Z * posInv bε) ε
  calc
    (jArg Aε Bε) (model.cornerEmbed Z) =
        (Aε * model.cornerEmbed Z) * posInv Bε := by
      rfl
    _ = Aε * (model.cornerEmbed Z * posInv Bε) := by
      rw [Matrix.mul_assoc]
    _ = Aε * model.cornerEmbed (Z * posInv bε) := by
      rw [hright]
    _ = model.cornerEmbed (aε * (Z * posInv bε)) := hleft
    _ = model.cornerEmbed ((jArg aε bε) Z) := by
      change model.cornerEmbed (aε * (Z * posInv bε)) =
        model.cornerEmbed ((aε * Z) * posInv bε)
      rw [Matrix.mul_assoc]

/-- On embedded corner matrices, the real CFC of the regularized ambient Hiai--Petz argument
acts as the embedded coordinate real CFC. -/
theorem hsCfcR_jArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {k : ℝ → ℝ}
    {A B : Mₙ model.dim} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (hsCfcR k
      (jArg (model.cornerEmbed A + ε • (1 : Mₙ m))
        (model.cornerEmbed B + ε • (1 : Mₙ m))))
      (model.cornerEmbed Z) =
      model.cornerEmbed
        ((hsCfcR k
          (jArg (A + ε • (1 : Mₙ model.dim))
            (B + ε • (1 : Mₙ model.dim)))) Z) := by
  exact model.cornerAction_hsCfcR_embed k
    (jArg_isSelfAdjoint_of_matrixPosDef
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hA hε)
      (model.cornerEmbed_add_pos_smul_one_matrixPosDef hB hε))
    (jArg_isSelfAdjoint_of_matrixPosDef
      (matrixPosDef_add_pos_smul_one hA hε)
      (matrixPosDef_add_pos_smul_one hB hε))
    (model.jArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed hB hε) Z

/-- On embedded corner matrices, the regularized ambient `J_f` acts as the embedded coordinate
regularized `J_f`. -/
theorem jOperator_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {f : ℝ → ℝ}
    {A B : Mₙ model.dim} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (jOperator f
      (model.cornerEmbed A + ε • (1 : Mₙ m))
      (model.cornerEmbed B + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((jOperator f
          (A + ε • (1 : Mₙ model.dim))
          (B + ε • (1 : Mₙ model.dim))) Z) := by
  let Aε : Mₙ m := model.cornerEmbed A + ε • (1 : Mₙ m)
  let Bε : Mₙ m := model.cornerEmbed B + ε • (1 : Mₙ m)
  let aε : Mₙ model.dim := A + ε • (1 : Mₙ model.dim)
  let bε : Mₙ model.dim := B + ε • (1 : Mₙ model.dim)
  have hright : (rightMul Bε : HSOp m) (model.cornerEmbed Z) =
      model.cornerEmbed (Z * bε) := by
    simpa only [Bε, bε, rightMul_apply] using
      model.cornerEmbed_mul_cornerEmbed_add_real_smul_one Z B ε
  calc
    (jOperator f Aε Bε) (model.cornerEmbed Z) =
        (hsCfcR f (jArg Aε Bε)) ((rightMul Bε : HSOp m) (model.cornerEmbed Z)) := by
      rfl
    _ = (hsCfcR f (jArg Aε Bε)) (model.cornerEmbed (Z * bε)) := by
      rw [hright]
    _ = model.cornerEmbed ((hsCfcR f (jArg aε bε)) (Z * bε)) := by
      simpa [Aε, Bε, aε, bε] using
        model.hsCfcR_jArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
          hA hB hε (Z * bε)
    _ = model.cornerEmbed ((jOperator f aε bε) Z) := by
      rfl

/-- Corner compression transports the regularized ambient `J_f` to the coordinate regularized
`J_f`. -/
theorem cornerCompressHSOp_jOperator_cornerEmbed_add_real_smul_one
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ model.dim} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (jOperator f
          (model.cornerEmbed A + ε • (1 : Mₙ m))
          (model.cornerEmbed B + ε • (1 : Mₙ m))) =
      jOperator f
        (A + ε • (1 : Mₙ model.dim))
        (B + ε • (1 : Mₙ model.dim)) := by
  ext Z i j
  let Jamb : HSOp m :=
    jOperator f
      (model.cornerEmbed A + ε • (1 : Mₙ m))
      (model.cornerEmbed B + ε • (1 : Mₙ m))
  let Jcoord : HSOp model.dim :=
    jOperator f
      (A + ε • (1 : Mₙ model.dim))
      (B + ε • (1 : Mₙ model.dim))
  have hact : Jamb (model.cornerEmbed Z) = model.cornerEmbed (Jcoord Z) := by
    simpa [Jamb, Jcoord] using
      model.jOperator_cornerEmbed_add_real_smul_one_apply_cornerEmbed hA hB hε Z
  have hcorner : model.cornerEmbed (Jcoord Z) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (Jcoord Z)
  have hproj :
      matrixCornerProj P (Jamb (model.cornerEmbed Z)) =
        model.cornerEmbed (Jcoord Z) := by
    rw [hact, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P (Jamb (model.cornerEmbed Z)),
      matrixCornerProj_mem hP⟩) i j = (Jcoord Z) i j
  have hsub0 :
      (⟨matrixCornerProj P (Jamb (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩ :
        matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (Jcoord Z), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (Jcoord Z), hcorner⟩ : matrixCornerSubmodule P) =
        model.toMat.symm (Jcoord Z) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa using hpoint

/-- On embedded corner matrices, the regularized ambient theorem-facing `J_f^{-1}` acts as
the embedded coordinate regularized `J_f^{-1}`. -/
theorem jOperatorInv_cornerEmbed_add_real_smul_one_apply_cornerEmbed
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {f : ℝ → ℝ}
    {A B : Mₙ model.dim} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) (Z : Mₙ model.dim) :
    (jOperatorInv f
      (model.cornerEmbed A + ε • (1 : Mₙ m))
      (model.cornerEmbed B + ε • (1 : Mₙ m))) (model.cornerEmbed Z) =
      model.cornerEmbed
        ((jOperatorInv f
          (A + ε • (1 : Mₙ model.dim))
          (B + ε • (1 : Mₙ model.dim))) Z) := by
  let Aε : Mₙ m := model.cornerEmbed A + ε • (1 : Mₙ m)
  let Bε : Mₙ m := model.cornerEmbed B + ε • (1 : Mₙ m)
  let aε : Mₙ model.dim := A + ε • (1 : Mₙ model.dim)
  let bε : Mₙ model.dim := B + ε • (1 : Mₙ model.dim)
  have hright : (rightMul (posInv Bε) : HSOp m) (model.cornerEmbed Z) =
      model.cornerEmbed (Z * posInv bε) := by
    simpa only [Bε, bε, rightMul_apply] using
      model.cornerEmbed_mul_posInv_cornerEmbed_add_real_smul_one hB hε Z
  calc
    (jOperatorInv f Aε Bε) (model.cornerEmbed Z) =
        (hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg Aε Bε))
          ((rightMul (posInv Bε) : HSOp m) (model.cornerEmbed Z)) := by
      rfl
    _ = (hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg Aε Bε))
        (model.cornerEmbed (Z * posInv bε)) := by
      rw [hright]
    _ = model.cornerEmbed
        ((hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg aε bε)) (Z * posInv bε)) := by
      simpa [Aε, Bε, aε, bε] using
        model.hsCfcR_jArg_cornerEmbed_add_real_smul_one_apply_cornerEmbed
          (k := fun x : ℝ => (f x)⁻¹) hA hB hε (Z * posInv bε)
    _ = model.cornerEmbed ((jOperatorInv f aε bε) Z) := by
      rfl

/-- Corner compression transports the regularized ambient theorem-facing `J_f^{-1}` to the
coordinate regularized `J_f^{-1}`. -/
theorem cornerCompressHSOp_jOperatorInv_cornerEmbed_add_real_smul_one
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ model.dim} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (jOperatorInv f
          (model.cornerEmbed A + ε • (1 : Mₙ m))
          (model.cornerEmbed B + ε • (1 : Mₙ m))) =
      jOperatorInv f
        (A + ε • (1 : Mₙ model.dim))
        (B + ε • (1 : Mₙ model.dim)) := by
  ext Z i j
  let Jamb : HSOp m :=
    jOperatorInv f
      (model.cornerEmbed A + ε • (1 : Mₙ m))
      (model.cornerEmbed B + ε • (1 : Mₙ m))
  let Jcoord : HSOp model.dim :=
    jOperatorInv f
      (A + ε • (1 : Mₙ model.dim))
      (B + ε • (1 : Mₙ model.dim))
  have hact : Jamb (model.cornerEmbed Z) = model.cornerEmbed (Jcoord Z) := by
    simpa [Jamb, Jcoord] using
      model.jOperatorInv_cornerEmbed_add_real_smul_one_apply_cornerEmbed hA hB hε Z
  have hcorner : model.cornerEmbed (Jcoord Z) ∈ matrixCornerSubmodule P :=
    model.cornerEmbed_mem (Jcoord Z)
  have hproj :
      matrixCornerProj P (Jamb (model.cornerEmbed Z)) =
        model.cornerEmbed (Jcoord Z) := by
    rw [hact, matrixCornerProj_apply]
    exact mem_matrixCornerSubmodule_iff.mp hcorner
  change (model.toMat ⟨matrixCornerProj P (Jamb (model.cornerEmbed Z)),
      matrixCornerProj_mem hP⟩) i j = (Jcoord Z) i j
  have hsub0 :
      (⟨matrixCornerProj P (Jamb (model.cornerEmbed Z)), matrixCornerProj_mem hP⟩ :
        matrixCornerSubmodule P) =
        ⟨model.cornerEmbed (Jcoord Z), hcorner⟩ := by
    ext a b
    exact congrFun (congrFun hproj a) b
  have hsub :
      (⟨model.cornerEmbed (Jcoord Z), hcorner⟩ : matrixCornerSubmodule P) =
        model.toMat.symm (Jcoord Z) := by
    ext a b
    rfl
  have hpoint := congrArg
    (fun W : matrixCornerSubmodule P => model.toMat W i j) (hsub0.trans hsub)
  simpa using hpoint

/-- Version of `cornerCompressHSOp_jOperator_cornerEmbed_add_real_smul_one` where the ambient
inputs are supplied by explicit corner-embedding equalities. -/
theorem cornerCompressHSOp_jOperator_add_real_smul_one_of_cornerEmbed_eq
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ m} {X Y : Mₙ model.dim}
    (hXembed : model.cornerEmbed X = A) (hYembed : model.cornerEmbed Y = B)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (jOperator f (A + ε • (1 : Mₙ m)) (B + ε • (1 : Mₙ m))) =
      jOperator f
        (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim)) := by
  rw [← hXembed, ← hYembed]
  exact model.cornerCompressHSOp_jOperator_cornerEmbed_add_real_smul_one
    hP (f := f) hX hY hε

/-- Version of `cornerCompressHSOp_jOperatorInv_cornerEmbed_add_real_smul_one` where the
ambient inputs are supplied by explicit corner-embedding equalities. -/
theorem cornerCompressHSOp_jOperatorInv_add_real_smul_one_of_cornerEmbed_eq
    {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (hP : IsMatrixProj P) {f : ℝ → ℝ}
    {A B : Mₙ m} {X Y : Mₙ model.dim}
    (hXembed : model.cornerEmbed X = A) (hYembed : model.cornerEmbed Y = B)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) {ε : ℝ} (hε : 0 < ε) :
    model.cornerCompressHSOp hP
        (jOperatorInv f (A + ε • (1 : Mₙ m)) (B + ε • (1 : Mₙ m))) =
      jOperatorInv f
        (X + ε • (1 : Mₙ model.dim)) (Y + ε • (1 : Mₙ model.dim)) := by
  rw [← hXembed, ← hYembed]
  exact model.cornerCompressHSOp_jOperatorInv_cornerEmbed_add_real_smul_one
    hP (f := f) hX hY hε

end MatrixCornerModel

/-! ### Ambient strict regularization continuity primitives -/
/-- Adding `ε I` tends to the original matrix as `ε ↓ 0`. -/
theorem matrix_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} (X : Mₙ n) :
    Tendsto (fun ε : ℝ => X + ε • (1 : Mₙ n)) (𝓝[>] (0 : ℝ)) (𝓝 X) := by
  have hcont : ContinuousAt (fun ε : ℝ => X + ε • (1 : Mₙ n)) 0 := by
    fun_prop
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
  convert hcont.tendsto.mono_left hle using 1
  apply congrArg (fun Y : Mₙ n => 𝓝 Y)
  rw [show (0 : ℝ) • (1 : Mₙ n) = 0 from zero_smul ℝ (1 : Mₙ n), add_zero]

/-- Operator convergence implies convergence of each fixed Hilbert--Schmidt quadratic form. -/
theorem hsQF_tendsto_of_tendsto {n : ℕ} {α : Type*} {l : Filter α}
    {T : α → HSOp n} {T₀ : HSOp n}
    (hT : Tendsto T l (𝓝 T₀)) (Z : Mₙ n) :
    Tendsto (fun a : α => hsQF (T a) Z) l (𝓝 (hsQF T₀ Z)) := by
  have hcont :
      Continuous (fun T : HSOp n =>
        Complex.re (Matrix.trace (Matrix.conjTranspose Z * T Z))) := by
    fun_prop
  simpa [hsQF] using hcont.tendsto T₀ |>.comp hT

/-- Pointwise Hilbert--Schmidt quadratic-form domination gives `HSLE`. -/
theorem HSLE_of_hsQF_le {n : ℕ} {S T : HSOp n}
    (h : ∀ Z : Mₙ n, hsQF S Z ≤ hsQF T Z) :
    HSLE S T := by
  rw [HSLE, HSNonneg]
  intro Z
  have hZ := h Z
  unfold hsQF at hZ
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose Z * (T Z - S Z)))
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  exact sub_nonneg.mpr hZ

/-- The theorem-facing positive inverse is continuous along positive identity regularization. -/
theorem posInv_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {X : Mₙ n}
    (hX : MatrixPosDef X) :
    Tendsto (fun ε : ℝ => posInv (X + ε • (1 : Mₙ n))) (𝓝[>] (0 : ℝ))
      (𝓝 (posInv X)) := by
  have hinput :
      Tendsto (fun ε : ℝ => X + ε • (1 : Mₙ n)) (𝓝[>] (0 : ℝ)) (𝓝 X) :=
    matrix_tendsto_add_pos_smul_one_nhdsGT X
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp (matrixPosDef_isUnit hX)
  have hdet_cont : ContinuousAt Ring.inverse X.det :=
    NormedRing.inverse_continuousAt hdet.unit
  have hinv_cont : ContinuousAt (Inv.inv : Mₙ n → Mₙ n) X :=
    continuousAt_matrix_inv X hdet_cont
  simpa [posInv] using hinv_cont.tendsto.comp hinput

/-- Left multiplication depends linearly on the multiplying matrix. -/
noncomputable def leftMulParamLinear {n : ℕ} : Mₙ n →ₗ[ℂ] HSOp n where
  toFun A := leftMul A
  map_add' A B := by
    ext X i j
    change (((A + B) * X) i j) = ((A * X + B * X) i j)
    rw [Matrix.add_mul]
  map_smul' c A := by
    ext X i j
    change (((c • A) * X) i j) = ((c • (A * X)) i j)
    rw [Matrix.smul_mul]

/-- Right multiplication depends linearly on the multiplying matrix. -/
noncomputable def rightMulParamLinear {n : ℕ} : Mₙ n →ₗ[ℂ] HSOp n where
  toFun B := rightMul B
  map_add' A B := by
    ext X i j
    change ((X * (A + B)) i j) = ((X * A + X * B) i j)
    rw [Matrix.mul_add]
  map_smul' c A := by
    ext X i j
    change ((X * (c • A)) i j) = ((c • (X * A)) i j)
    rw [Matrix.mul_smul]

/-- Continuous-linear version of `A ↦ leftMul A`. -/
noncomputable def leftMulParamCLM {n : ℕ} : Mₙ n →L[ℂ] HSOp n :=
  (leftMulParamLinear (n := n)).toContinuousLinearMap

/-- Continuous-linear version of `B ↦ rightMul B`. -/
noncomputable def rightMulParamCLM {n : ℕ} : Mₙ n →L[ℂ] HSOp n :=
  (rightMulParamLinear (n := n)).toContinuousLinearMap

@[simp] theorem leftMulParamCLM_apply {n : ℕ} (A : Mₙ n) :
    leftMulParamCLM (n := n) A = leftMul A := by
  ext X i j
  unfold leftMulParamCLM
  change ((leftMulParamLinear (n := n) A) X) i j = (leftMul A X) i j
  rfl

@[simp] theorem rightMulParamCLM_apply {n : ℕ} (B : Mₙ n) :
    rightMulParamCLM (n := n) B = rightMul B := by
  ext X i j
  unfold rightMulParamCLM
  change ((rightMulParamLinear (n := n) B) X) i j = (rightMul B X) i j
  rfl

/-- Left multiplication is continuous along positive identity regularization. -/
theorem leftMul_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} (A : Mₙ n) :
    Tendsto (fun ε : ℝ => (leftMul (A + ε • (1 : Mₙ n)) : HSOp n))
      (𝓝[>] (0 : ℝ)) (𝓝 (leftMul A)) := by
  have hcont : Continuous (fun A : Mₙ n => (leftMul A : HSOp n)) := by
    simpa using (leftMulParamCLM (n := n)).continuous
  exact (hcont.tendsto A).comp (matrix_tendsto_add_pos_smul_one_nhdsGT A)

/-- Right multiplication is continuous along positive identity regularization. -/
theorem rightMul_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} (B : Mₙ n) :
    Tendsto (fun ε : ℝ => (rightMul (B + ε • (1 : Mₙ n)) : HSOp n))
      (𝓝[>] (0 : ℝ)) (𝓝 (rightMul B)) := by
  have hcont : Continuous (fun B : Mₙ n => (rightMul B : HSOp n)) := by
    simpa using (rightMulParamCLM (n := n)).continuous
  exact (hcont.tendsto B).comp (matrix_tendsto_add_pos_smul_one_nhdsGT B)

/-- Left multiplication by the regularized inverse tends to the unregularized inverse. -/
theorem leftMul_posInv_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {B : Mₙ n}
    (hB : MatrixPosDef B) :
    Tendsto (fun ε : ℝ => (leftMul (posInv (B + ε • (1 : Mₙ n))) : HSOp n))
      (𝓝[>] (0 : ℝ)) (𝓝 (leftMul (posInv B))) := by
  have hcont : Continuous (fun B : Mₙ n => (leftMul B : HSOp n)) := by
    simpa using (leftMulParamCLM (n := n)).continuous
  exact (hcont.tendsto (posInv B)).comp
    (posInv_tendsto_add_pos_smul_one_nhdsGT hB)

/-- Right multiplication by the regularized inverse tends to the unregularized inverse. -/
theorem rightMul_posInv_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {B : Mₙ n}
    (hB : MatrixPosDef B) :
    Tendsto (fun ε : ℝ => (rightMul (posInv (B + ε • (1 : Mₙ n))) : HSOp n))
      (𝓝[>] (0 : ℝ)) (𝓝 (rightMul (posInv B))) := by
  have hcont : Continuous (fun B : Mₙ n => (rightMul B : HSOp n)) := by
    simpa using (rightMulParamCLM (n := n)).continuous
  exact (hcont.tendsto (posInv B)).comp
    (posInv_tendsto_add_pos_smul_one_nhdsGT hB)

/-- The Carlen CFC argument `gArg` is continuous along positive identity regularization. -/
theorem gArg_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {X Y : Mₙ n}
    (hY : MatrixPosDef Y) :
    Tendsto (fun ε : ℝ => gArg (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (gArg X Y)) := by
  have hright :
      Tendsto (fun ε : ℝ => (rightMul (X + ε • (1 : Mₙ n)) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (rightMul X)) :=
    rightMul_tendsto_add_pos_smul_one_nhdsGT X
  have hleft :
      Tendsto (fun ε : ℝ => (leftMul (posInv (Y + ε • (1 : Mₙ n))) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (leftMul (posInv Y))) :=
    leftMul_posInv_tendsto_add_pos_smul_one_nhdsGT hY
  have hpair :
      Tendsto
        (fun ε : ℝ =>
          ((rightMul (X + ε • (1 : Mₙ n)) : HSOp n),
            (leftMul (posInv (Y + ε • (1 : Mₙ n))) : HSOp n)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((rightMul X : HSOp n), leftMul (posInv Y))) :=
    Filter.Tendsto.prodMk_nhds hright hleft
  have hcomp : ContinuousAt (fun p : HSOp n × HSOp n => p.1.comp p.2)
      ((rightMul X : HSOp n), leftMul (posInv Y)) := by
    exact (continuous_fst.clm_comp continuous_snd).continuousAt
  simpa [gArg] using hcomp.tendsto.comp hpair

/-- The Hiai--Petz CFC argument `jArg` is continuous along positive identity regularization. -/
theorem jArg_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {A B : Mₙ n}
    (hB : MatrixPosDef B) :
    Tendsto (fun ε : ℝ => jArg (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (jArg A B)) := by
  have hright :
      Tendsto (fun ε : ℝ => (rightMul (posInv (B + ε • (1 : Mₙ n))) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (rightMul (posInv B))) :=
    rightMul_posInv_tendsto_add_pos_smul_one_nhdsGT hB
  have hleft :
      Tendsto (fun ε : ℝ => (leftMul (A + ε • (1 : Mₙ n)) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (leftMul A)) :=
    leftMul_tendsto_add_pos_smul_one_nhdsGT A
  have hpair :
      Tendsto
        (fun ε : ℝ =>
          ((rightMul (posInv (B + ε • (1 : Mₙ n))) : HSOp n),
            (leftMul (A + ε • (1 : Mₙ n)) : HSOp n)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((rightMul (posInv B) : HSOp n), leftMul A)) :=
    Filter.Tendsto.prodMk_nhds hright hleft
  have hcomp : ContinuousAt (fun p : HSOp n × HSOp n => p.1.comp p.2)
      ((rightMul (posInv B) : HSOp n), leftMul A) := by
    exact (continuous_fst.clm_comp continuous_snd).continuousAt
  simpa only [jArg, _root_.HiaiPetz.jArg, posInv, Function.comp_def] using
    hcomp.tendsto.comp hpair


end

end Quantum.TraceInequality.Loewner.HiaiPetz
