/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.KernelG

/-!
# Carlen rectangle scalar Kubo identities

This module contains endpoint cancellations, scalar Kubo CFC identities, and
positive-ray kernel bounds with Bochner integrability facts.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
  instCarlenRectangleHSOpCStarAlgebra
  instCarlenRectangleHSOpPartialOrder
  instCarlenRectangleHSOpStarRing
  instCarlenRectangleHSOpStarOrderedRing
  instCarlenRectangleComplexCFC
  instCarlenRectangleRealCFC
  instCarlenRectangleHSOpNonnegSpectrumClass
  instCarlenRectangleHSOpSMulZeroClass
  instCarlenRectangleHSOpIsBoundedSMul
  instCarlenRectangleHSOpContinuousSMul
  instCarlenRectangleHSOpRealAlgebra
  instCarlenRectangleHSOpRealRealTower

noncomputable section

/-! ### Endpoint cancellations and scalar Kubo CFC identities for J -/
/-- Right multiplication by `B⁻¹` cancels right multiplication by `B`. -/
theorem rightMul_posInv_mul_rightMul_of_matrixPosDef {n : ℕ} {B : Mₙ n}
    (hB : MatrixPosDef B) :
    (rightMul (posInv B) : HSOp n) * rightMul B = 1 := by
  ext X i j
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp (matrixPosDef_isUnit hB)
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc, posInv,
    Matrix.mul_nonsing_inv B hdet]

/-- Right multiplication by `B` cancels right multiplication by `B⁻¹`. -/
theorem rightMul_mul_rightMul_posInv_of_matrixPosDef {n : ℕ} {B : Mₙ n}
    (hB : MatrixPosDef B) :
    (rightMul B : HSOp n) * rightMul (posInv B) = 1 := by
  ext X i j
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp (matrixPosDef_isUnit hB)
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc, posInv,
    Matrix.nonsing_inv_mul B hdet]

/-- Multiplying the Hiai--Petz CFC argument by the endpoint `R_B` leaves `L_A`. -/
theorem jArg_mul_rightMul_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hB : MatrixPosDef B) :
    (jArg A B) * rightMul B = leftMul A := by
  ext X i j
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp (matrixPosDef_isUnit hB)
  simp [jArg, ContinuousLinearMap.mul_apply, Matrix.mul_assoc, Matrix.mul_nonsing_inv B hdet]

/-- Left multiplication by `A⁻¹` cancels left multiplication by `A`. -/
theorem leftMul_posInv_mul_leftMul_of_matrixPosDef {n : ℕ} {A : Mₙ n}
    (hA : MatrixPosDef A) :
    (leftMul (posInv A) : HSOp n) * leftMul A = 1 := by
  ext X i j
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp (matrixPosDef_isUnit hA)
  calc
    (leftMul (posInv A) * leftMul A : HSOp n) X i j
        = ((A⁻¹ * A) * X) i j := by
            simp [ContinuousLinearMap.mul_apply, posInv, Matrix.mul_assoc]
    _ = X i j := by
          rw [Matrix.nonsing_inv_mul A hdet]
          simp

/-- Multiplying Carlen's direct CFC argument by the endpoint `L_Y` leaves `R_X`. -/
theorem gArg_mul_leftMul_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hY : MatrixPosDef Y) :
    (gArg X Y) * leftMul Y = rightMul X := by
  ext Z i j
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (matrixPosDef_isUnit hY)
  simp only [gArg, ContinuousLinearMap.coe_mul', Function.comp_apply,
    ContinuousLinearMap.comp_apply, leftMul_apply, rightMul_apply, posInv]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Y hdet, Matrix.one_mul]

/-- The product `R_X L_{Y⁻¹}` is the Carlen CFC argument. -/
theorem rightMul_mul_leftMul_posInv_eq_gArg {n : ℕ} {X Y : Mₙ n} :
    (rightMul X : HSOp n) * leftMul (posInv Y) = gArg X Y := by
  simpa using (gArg_eq_rightMul_mul_leftMul X Y).symm

/-- Left multiplication by `A` cancels left multiplication by `A⁻¹`. -/
theorem leftMul_mul_leftMul_posInv_of_matrixPosDef {n : ℕ} {A : Mₙ n}
    (hA : MatrixPosDef A) :
    (leftMul A : HSOp n) * leftMul (posInv A) = 1 := by
  ext X i j
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp (matrixPosDef_isUnit hA)
  calc
    (leftMul A * leftMul (posInv A) : HSOp n) X i j
        = ((A * A⁻¹) * X) i j := by
            simp [ContinuousLinearMap.mul_apply, posInv, Matrix.mul_assoc]
    _ = X i j := by
          rw [Matrix.mul_nonsing_inv A hdet]
          simp

/-- The product `L_A R_{B⁻¹}` is the Hiai--Petz CFC argument. -/
theorem leftMul_mul_rightMul_posInv_eq_jArg {n : ℕ} {A B : Mₙ n} :
    (leftMul A : HSOp n) * rightMul (posInv B) = jArg A B := by
  exact (leftMul_commute_rightMul A (posInv B)).eq.trans
    (jArg_eq_rightMul_mul_leftMul A B).symm

/-- Multiplying the inverse-form fixed kernel by `L_A` gives `jArg + t`. -/
theorem jKuboKernelInvForm_mul_leftMul_eq_jArg_add_scalar {n : ℕ}
    {t : ℝ} {A B : Mₙ n} (hA : MatrixPosDef A) :
    jKuboKernelInvForm t A B * leftMul A =
      jArg A B + ((t : ℂ) • (1 : HSOp n)) := by
  apply ContinuousLinearMap.ext
  intro X
  have hleftX :
      (leftMul (posInv A) : HSOp n) ((leftMul A : HSOp n) X) = X := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T X)
        (leftMul_posInv_mul_leftMul_of_matrixPosDef hA)
  change (t : ℂ) • ((leftMul (posInv A) : HSOp n) ((leftMul A : HSOp n) X)) +
      (rightMul (posInv B) : HSOp n) ((leftMul A : HSOp n) X) =
    (jArg A B) X + (((t : ℂ) • (1 : HSOp n)) X)
  rw [hleftX]
  change (t : ℂ) • X + (jArg A B) X = (jArg A B) X + (t : ℂ) • X
  rw [add_comm]

/-- Multiplying `L_A` by the inverse-form fixed kernel also gives `jArg + t`. -/
theorem leftMul_mul_jKuboKernelInvForm_eq_jArg_add_scalar {n : ℕ}
    {t : ℝ} {A B : Mₙ n} (hA : MatrixPosDef A) :
    (leftMul A : HSOp n) * jKuboKernelInvForm t A B =
      jArg A B + ((t : ℂ) • (1 : HSOp n)) := by
  apply ContinuousLinearMap.ext
  intro X
  have hleftX :
      (leftMul A : HSOp n) ((leftMul (posInv A) : HSOp n) X) = X := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T X)
        (leftMul_mul_leftMul_posInv_of_matrixPosDef hA)
  have hrightX :
      (leftMul A : HSOp n) ((rightMul (posInv B) : HSOp n) X) = (jArg A B) X := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T X)
        (leftMul_mul_rightMul_posInv_eq_jArg (A := A) (B := B))
  change (leftMul A : HSOp n)
      (((t : ℂ) • (leftMul (posInv A) : HSOp n) +
        rightMul (posInv B)) X) =
    (jArg A B) X + (((t : ℂ) • (1 : HSOp n)) X)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul]
  change (t : ℂ) • ((leftMul A : HSOp n) ((leftMul (posInv A) : HSOp n) X)) +
      (leftMul A : HSOp n) ((rightMul (posInv B) : HSOp n) X) =
    (jArg A B) X + (t : ℂ) • X
  rw [hleftX, hrightX]
  rw [add_comm]

/--
The scalar Kubo--Ando CFC of `jArg` is the resolvent expression
`(1+t) T (T+t)⁻¹`.
-/
theorem hsCfcR_positiveRayKuboAndoKernel_jArg_eq_resolvent {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (ht : 0 < t) (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B) =
      (((1 + t : ℝ) : ℂ) • jArg A B) *
        Ring.inverse (jArg A B + ((t : ℂ) • (1 : HSOp n))) := by
  have hT : IsSelfAdjoint (jArg A B) :=
    jArg_isSelfAdjoint_of_matrixPosDef hA hB
  have hσ : spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hden :
      ∀ x ∈ spectrum ℝ (jArg A B), (fun x : ℝ => x + t) x ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by simpa [Set.mem_Ioi] using hσ hx
    exact ne_of_gt (add_pos hx0 ht)
  calc
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B)
        = hsCfcR (fun x : ℝ => ((1 + t) * x) / (x + t)) (jArg A B) := by
            apply cfc_congr
            intro x hx
            simp [positiveRayKuboAndoKernel, mul_comm]
    _ = cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
          (fun x : ℝ => (1 + t) * x) (jArg A B) *
        Ring.inverse
          (cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (fun x : ℝ => x + t) (jArg A B)) := by
            simpa [hsCfcR] using
              (cfc_map_div (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                (f := fun x : ℝ => (1 + t) * x)
                (g := fun x : ℝ => x + t)
                (a := jArg A B) hden (ha := hT))
    _ = (((1 + t : ℝ) : ℂ) • jArg A B) *
        Ring.inverse (jArg A B + ((t : ℂ) • (1 : HSOp n))) := by
          congr 1
          · have hreal :
                cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                    (fun x : ℝ => (1 + t) * x) (jArg A B) =
                  (1 + t : ℝ) • jArg A B :=
              (cfc_const_mul_id (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                (r := 1 + t) (a := jArg A B) (ha := hT))
            rw [hreal]
            rfl
          · rw [cfc_add_const (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (r := t) (f := fun x : ℝ => x) (a := jArg A B) (ha := hT)]
            rw [cfc_id' (R := ℝ) (a := jArg A B) (ha := hT)]
            simp [Algebra.algebraMap_eq_smul_one]

/-- The fixed kernel times `R_{B⁻¹}` is the same resolvent expression. -/
theorem jKuboKernel_mul_rightMul_posInv_eq_jArg_mul_resolvent {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (ht : 0 < t) (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    jKuboKernel t A B * rightMul (posInv B) =
      jArg A B * Ring.inverse (jArg A B + ((t : ℂ) • (1 : HSOp n))) := by
  let H : HSOp n := jArg A B + ((t : ℂ) • (1 : HSOp n))
  have hH_eq : H = jArg A B + ((t : ℂ) • (1 : HSOp n)) := rfl
  have hInv : IsUnit (jKuboKernelInvForm t A B) :=
    jKuboKernelInvForm_isUnit_of_matrixPosDef (le_of_lt ht) hA hB
  have hL : IsUnit (leftMul A : HSOp n) :=
    leftMul_isUnit_of_matrix_isUnit (matrixPosDef_isUnit hA)
  have hH_mul : jKuboKernelInvForm t A B * leftMul A = H := by
    rw [hH_eq]
    exact jKuboKernelInvForm_mul_leftMul_eq_jArg_add_scalar
      (t := t) (B := B) hA
  have hH_unit : IsUnit H := by
    rw [← hH_mul]
    exact hInv.mul hL
  apply (hH_unit.mul_right_inj).mp
  have hleft_cancel :
      H * (jKuboKernel t A B * rightMul (posInv B)) = jArg A B := by
    have hHL : H * jKuboKernel t A B = leftMul A := by
      rw [jKuboKernel]
      have hLH : (leftMul A : HSOp n) * jKuboKernelInvForm t A B = H := by
        rw [hH_eq]
        exact leftMul_mul_jKuboKernelInvForm_eq_jArg_add_scalar
          (t := t) (B := B) hA
      exact
        ((Ring.eq_mul_inverse_iff_mul_eq
          (x := (leftMul A : HSOp n)) (y := H)
          (z := jKuboKernelInvForm t A B) hInv).2 hLH).symm
    calc
      H * (jKuboKernel t A B * rightMul (posInv B))
          = (H * jKuboKernel t A B) * rightMul (posInv B) := by
              rw [mul_assoc]
      _ = (leftMul A : HSOp n) * rightMul (posInv B) := by
              rw [hHL]
      _ = jArg A B := leftMul_mul_rightMul_posInv_eq_jArg
  have hright_cancel :
      H * (jArg A B * Ring.inverse H) = jArg A B := by
    have hcomm : Commute H (jArg A B) := by
      have hscalar : Commute (((t : ℂ) • (1 : HSOp n))) (jArg A B) := by
        rw [commute_iff_eq]
        apply ContinuousLinearMap.ext
        intro X
        change (t : ℂ) • ((jArg A B) X) = (jArg A B) ((t : ℂ) • X)
        exact (map_smul (jArg A B) (t : ℂ) X).symm
      rw [hH_eq]
      exact Commute.add_left (Commute.refl (jArg A B)) hscalar
    calc
      H * (jArg A B * Ring.inverse H)
          = (H * jArg A B) * Ring.inverse H := by rw [mul_assoc]
      _ = (jArg A B * H) * Ring.inverse H := by rw [hcomm.eq]
      _ = jArg A B * (H * Ring.inverse H) := by rw [mul_assoc]
      _ = jArg A B := by
          rw [Ring.mul_inverse_cancel H hH_unit, mul_one]
  rw [hleft_cancel, hright_cancel]

/--
For positive-definite endpoints, the scalar Kubo kernel CFC of `jArg` is the
weighted Carlen fixed kernel followed by `R_{B⁻¹}`.
-/
theorem hsCfcR_positiveRayKuboAndoKernel_jArg_eq_weighted_jKuboKernel_rightMul
    {n : ℕ} {t : ℝ} {A B : Mₙ n}
    (ht : 0 < t) (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B) =
      (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) * rightMul (posInv B) := by
  rw [hsCfcR_positiveRayKuboAndoKernel_jArg_eq_resolvent ht hA hB]
  have hfixed :=
    jKuboKernel_mul_rightMul_posInv_eq_jArg_mul_resolvent ht hA hB
  apply ContinuousLinearMap.ext
  intro X
  have hX := congrArg (fun T : HSOp n => (((1 + t : ℝ) : ℂ) • T) X) hfixed.symm
  change (((1 + t : ℝ) : ℂ) •
      (jArg A B * Ring.inverse (jArg A B + ((t : ℂ) • (1 : HSOp n)))) X) =
    ((((1 + t : ℝ) : ℂ) • jKuboKernel t A B) *
      rightMul (posInv B)) X
  simpa [ContinuousLinearMap.mul_apply] using hX

/-- The equivalent endpoint-multiplied form of the scalar Kubo CFC identity. -/
theorem weighted_jKuboKernel_eq_hsCfcR_positiveRayKuboAndoKernel_jArg_mul_rightMul
    {n : ℕ} {t : ℝ} {A B : Mₙ n}
    (ht : 0 < t) (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) =
      hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B) * rightMul B := by
  have hmain :=
    hsCfcR_positiveRayKuboAndoKernel_jArg_eq_weighted_jKuboKernel_rightMul
      ht hA hB
  have hright : (rightMul (posInv B) : HSOp n) * rightMul B = 1 :=
    rightMul_posInv_mul_rightMul_of_matrixPosDef hB
  calc
    (((1 + t : ℝ) : ℂ) • jKuboKernel t A B)
        = (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) * (1 : HSOp n) := by
            rw [mul_one]
    _ = (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) *
          ((rightMul (posInv B) : HSOp n) * rightMul B) := by
            rw [hright]
    _ = ((((1 + t : ℝ) : ℂ) • jKuboKernel t A B) * rightMul (posInv B)) *
          rightMul B := by
            rw [mul_assoc]
    _ = hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B) *
          rightMul B := by
            rw [← hmain]

/-! ### Scalar Kubo CFC identities for G -/
/-- Multiplying the direct inverse-form fixed kernel by `R_X` gives `gArg + t`. -/
theorem gKuboKernelInvForm_mul_rightMul_eq_gArg_add_scalar {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (hX : MatrixPosDef X) :
    gKuboKernelInvForm t X Y * rightMul X =
      gArg X Y + ((t : ℂ) • (1 : HSOp n)) := by
  apply ContinuousLinearMap.ext
  intro Z
  have hrightZ :
      (rightMul (posInv X) : HSOp n) ((rightMul X : HSOp n) Z) = Z := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T Z)
        (rightMul_posInv_mul_rightMul_of_matrixPosDef hX)
  change (t : ℂ) • ((rightMul (posInv X) : HSOp n) ((rightMul X : HSOp n) Z)) +
      (leftMul (posInv Y) : HSOp n) ((rightMul X : HSOp n) Z) =
    (gArg X Y) Z + (((t : ℂ) • (1 : HSOp n)) Z)
  rw [hrightZ]
  change (t : ℂ) • Z +
      (leftMul (posInv Y) : HSOp n) ((rightMul X : HSOp n) Z) =
    (gArg X Y) Z + (t : ℂ) • Z
  have hleftZ :
      (leftMul (posInv Y) : HSOp n) ((rightMul X : HSOp n) Z) =
        (gArg X Y) Z := by
    simp [gArg, ContinuousLinearMap.comp_apply, Matrix.mul_assoc]
  rw [hleftZ, add_comm]

/-- Multiplying `R_X` by the direct inverse-form fixed kernel also gives `gArg + t`. -/
theorem rightMul_mul_gKuboKernelInvForm_eq_gArg_add_scalar {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (hX : MatrixPosDef X) :
    (rightMul X : HSOp n) * gKuboKernelInvForm t X Y =
      gArg X Y + ((t : ℂ) • (1 : HSOp n)) := by
  apply ContinuousLinearMap.ext
  intro Z
  have hrightZ :
      (rightMul X : HSOp n) ((rightMul (posInv X) : HSOp n) Z) = Z := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T Z)
        (rightMul_mul_rightMul_posInv_of_matrixPosDef hX)
  have hleftZ :
      (rightMul X : HSOp n) ((leftMul (posInv Y) : HSOp n) Z) = (gArg X Y) Z := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T Z)
        (rightMul_mul_leftMul_posInv_eq_gArg (X := X) (Y := Y))
  change (rightMul X : HSOp n)
      (((t : ℂ) • (rightMul (posInv X) : HSOp n) +
        leftMul (posInv Y)) Z) =
    (gArg X Y) Z + (((t : ℂ) • (1 : HSOp n)) Z)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul]
  change (t : ℂ) • ((rightMul X : HSOp n) ((rightMul (posInv X) : HSOp n) Z)) +
      (rightMul X : HSOp n) ((leftMul (posInv Y) : HSOp n) Z) =
    (gArg X Y) Z + (t : ℂ) • Z
  rw [hrightZ, hleftZ]
  rw [add_comm]

/--
The scalar Kubo--Ando CFC of `gArg` is the resolvent expression
`(1+t) T (T+t)⁻¹`.
-/
theorem hsCfcR_positiveRayKuboAndoKernel_gArg_eq_resolvent {n : ℕ}
    {t : ℝ} {X Y : Mₙ n}
    (ht : 0 < t) (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y) =
      (((1 + t : ℝ) : ℂ) • gArg X Y) *
        Ring.inverse (gArg X Y + ((t : ℂ) • (1 : HSOp n))) := by
  have hT : IsSelfAdjoint (gArg X Y) :=
    gArg_isSelfAdjoint_of_matrixPosDef hX hY
  have hσ : spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) :=
    gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hden :
      ∀ x ∈ spectrum ℝ (gArg X Y), (fun x : ℝ => x + t) x ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by simpa [Set.mem_Ioi] using hσ hx
    exact ne_of_gt (add_pos hx0 ht)
  calc
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y)
        = hsCfcR (fun x : ℝ => ((1 + t) * x) / (x + t)) (gArg X Y) := by
            apply cfc_congr
            intro x hx
            simp [positiveRayKuboAndoKernel, mul_comm]
    _ = cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
          (fun x : ℝ => (1 + t) * x) (gArg X Y) *
        Ring.inverse
          (cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (fun x : ℝ => x + t) (gArg X Y)) := by
            simpa [hsCfcR] using
              (cfc_map_div (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                (f := fun x : ℝ => (1 + t) * x)
                (g := fun x : ℝ => x + t)
                (a := gArg X Y) hden (ha := hT))
    _ = (((1 + t : ℝ) : ℂ) • gArg X Y) *
        Ring.inverse (gArg X Y + ((t : ℂ) • (1 : HSOp n))) := by
          congr 1
          · have hreal :
                cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                    (fun x : ℝ => (1 + t) * x) (gArg X Y) =
                  (1 + t : ℝ) • gArg X Y :=
              (cfc_const_mul_id (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                (r := 1 + t) (a := gArg X Y) (ha := hT))
            rw [hreal]
            rfl
          · rw [cfc_add_const (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (r := t) (f := fun x : ℝ => x) (a := gArg X Y) (ha := hT)]
            rw [cfc_id' (R := ℝ) (a := gArg X Y) (ha := hT)]
            simp [Algebra.algebraMap_eq_smul_one]

/-- The direct fixed kernel times `L_{Y⁻¹}` is the same resolvent expression. -/
theorem gKuboKernel_mul_leftMul_posInv_eq_gArg_mul_resolvent {n : ℕ}
    {t : ℝ} {X Y : Mₙ n}
    (ht : 0 < t) (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gKuboKernel t X Y * leftMul (posInv Y) =
      gArg X Y * Ring.inverse (gArg X Y + ((t : ℂ) • (1 : HSOp n))) := by
  let H : HSOp n := gArg X Y + ((t : ℂ) • (1 : HSOp n))
  have hH_eq : H = gArg X Y + ((t : ℂ) • (1 : HSOp n)) := rfl
  have hInv : IsUnit (gKuboKernelInvForm t X Y) :=
    gKuboKernelInvForm_isUnit_of_matrixPosDef (le_of_lt ht) hX hY
  have hR : IsUnit (rightMul X : HSOp n) :=
    rightMul_isUnit_of_matrix_isUnit (matrixPosDef_isUnit hX)
  have hH_mul : gKuboKernelInvForm t X Y * rightMul X = H := by
    rw [hH_eq]
    exact gKuboKernelInvForm_mul_rightMul_eq_gArg_add_scalar
      (t := t) (Y := Y) hX
  have hH_unit : IsUnit H := by
    rw [← hH_mul]
    exact hInv.mul hR
  apply (hH_unit.mul_right_inj).mp
  have hleft_cancel :
      H * (gKuboKernel t X Y * leftMul (posInv Y)) = gArg X Y := by
    have hHR : H * gKuboKernel t X Y = rightMul X := by
      rw [gKuboKernel]
      have hRH : (rightMul X : HSOp n) * gKuboKernelInvForm t X Y = H := by
        rw [hH_eq]
        exact rightMul_mul_gKuboKernelInvForm_eq_gArg_add_scalar
          (t := t) (Y := Y) hX
      exact
        ((Ring.eq_mul_inverse_iff_mul_eq
          (x := (rightMul X : HSOp n)) (y := H)
          (z := gKuboKernelInvForm t X Y) hInv).2 hRH).symm
    calc
      H * (gKuboKernel t X Y * leftMul (posInv Y))
          = (H * gKuboKernel t X Y) * leftMul (posInv Y) := by
              rw [mul_assoc]
      _ = (rightMul X : HSOp n) * leftMul (posInv Y) := by
              rw [hHR]
      _ = gArg X Y := rightMul_mul_leftMul_posInv_eq_gArg
  have hright_cancel :
      H * (gArg X Y * Ring.inverse H) = gArg X Y := by
    have hcomm : Commute H (gArg X Y) := by
      have hscalar : Commute (((t : ℂ) • (1 : HSOp n))) (gArg X Y) := by
        rw [commute_iff_eq]
        apply ContinuousLinearMap.ext
        intro Z
        change (t : ℂ) • ((gArg X Y) Z) = (gArg X Y) ((t : ℂ) • Z)
        exact (map_smul (gArg X Y) (t : ℂ) Z).symm
      rw [hH_eq]
      exact Commute.add_left (Commute.refl (gArg X Y)) hscalar
    calc
      H * (gArg X Y * Ring.inverse H)
          = (H * gArg X Y) * Ring.inverse H := by rw [mul_assoc]
      _ = (gArg X Y * H) * Ring.inverse H := by rw [hcomm.eq]
      _ = gArg X Y * (H * Ring.inverse H) := by rw [mul_assoc]
      _ = gArg X Y := by
          rw [Ring.mul_inverse_cancel H hH_unit, mul_one]
  rw [hleft_cancel, hright_cancel]

/--
For positive-definite endpoints, the scalar Kubo kernel CFC of `gArg` is the
weighted direct fixed kernel followed by `L_{Y⁻¹}`.
-/
theorem hsCfcR_positiveRayKuboAndoKernel_gArg_eq_weighted_gKuboKernel_leftMul
    {n : ℕ} {t : ℝ} {X Y : Mₙ n}
    (ht : 0 < t) (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y) =
      (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) * leftMul (posInv Y) := by
  rw [hsCfcR_positiveRayKuboAndoKernel_gArg_eq_resolvent ht hX hY]
  have hfixed :=
    gKuboKernel_mul_leftMul_posInv_eq_gArg_mul_resolvent ht hX hY
  apply ContinuousLinearMap.ext
  intro Z
  have hZ := congrArg (fun T : HSOp n => (((1 + t : ℝ) : ℂ) • T) Z) hfixed.symm
  change (((1 + t : ℝ) : ℂ) •
      (gArg X Y * Ring.inverse (gArg X Y + ((t : ℂ) • (1 : HSOp n)))) Z) =
    ((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) *
      leftMul (posInv Y)) Z
  simpa [ContinuousLinearMap.mul_apply] using hZ

/-- The equivalent endpoint-multiplied form of the direct scalar Kubo CFC identity. -/
theorem weighted_gKuboKernel_eq_hsCfcR_positiveRayKuboAndoKernel_gArg_mul_leftMul
    {n : ℕ} {t : ℝ} {X Y : Mₙ n}
    (ht : 0 < t) (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) =
      hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y) * leftMul Y := by
  have hmain :=
    hsCfcR_positiveRayKuboAndoKernel_gArg_eq_weighted_gKuboKernel_leftMul
      ht hX hY
  have hleft : (leftMul (posInv Y) : HSOp n) * leftMul Y = 1 :=
    leftMul_posInv_mul_leftMul_of_matrixPosDef hY
  calc
    (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y)
        = (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) * (1 : HSOp n) := by
            rw [mul_one]
    _ = (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) *
          ((leftMul (posInv Y) : HSOp n) * leftMul Y) := by
            rw [hleft]
    _ = ((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) * leftMul (posInv Y)) *
          leftMul Y := by
            rw [mul_assoc]
    _ = hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y) *
          leftMul Y := by
            rw [← hmain]

/-! ### Positive-ray kernel bounds and Bochner integrability -/
private theorem positiveRayKuboAndoKernel_norm_le_max_of_pos
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    ‖positiveRayKuboAndoKernel x t‖ ≤ max x 1 := by
  by_cases hxzero : x = 0
  · subst x
    simp [positiveRayKuboAndoKernel]
  · have hxpos : 0 < x := lt_of_le_of_ne' hx hxzero
    have hden_pos : 0 < x + t := by linarith
    have hkernel_nonneg :
        0 ≤ positiveRayKuboAndoKernel x t := by
      unfold positiveRayKuboAndoKernel
      positivity
    rw [Real.norm_of_nonneg hkernel_nonneg]
    by_cases hxle : x ≤ 1
    · have hnum_le : x * (1 + t) ≤ 1 * (x + t) := by
        nlinarith
      have hle_one : positiveRayKuboAndoKernel x t ≤ 1 := by
        unfold positiveRayKuboAndoKernel
        rw [div_le_iff₀ hden_pos]
        simpa using hnum_le
      exact le_trans hle_one (le_max_right x 1)
    · have hxge : 1 ≤ x := le_of_not_ge hxle
      have hnum_le : x * (1 + t) ≤ x * (x + t) := by
        nlinarith
      have hle_x : positiveRayKuboAndoKernel x t ≤ x := by
        unfold positiveRayKuboAndoKernel
        rw [div_le_iff₀ hden_pos]
        simpa [mul_add, add_comm, add_left_comm, add_assoc] using hnum_le
      exact le_trans hle_x (le_max_left x 1)

private theorem jKuboKernel_continuousOn_Ioi_of_matrixPosDef
    {n : ℕ} {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    ContinuousOn (fun t : ℝ => jKuboKernel t A B) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  have hcont_inv : Continuous (fun t : ℝ => jKuboKernelInvForm t A B) := by
    unfold jKuboKernelInvForm
    exact (Complex.continuous_ofReal.smul continuous_const).add continuous_const
  have hunit : IsUnit (jKuboKernelInvForm t A B) :=
    jKuboKernelInvForm_isUnit_of_matrixPosDef (le_of_lt ht) hA hB
  have hinv_cont :
      ContinuousAt (fun T : HSOp n => Ring.inverse T) (jKuboKernelInvForm t A B) := by
    simpa using (NormedRing.inverse_continuousAt hunit.unit)
  simpa [jKuboKernel] using
    ContinuousAt.comp_continuousWithinAt hinv_cont
      (f := fun t : ℝ => jKuboKernelInvForm t A B) (x := t)
      (hcont_inv.continuousAt.continuousWithinAt)

private theorem weighted_jKuboKernel_continuousOn_Ioi_of_matrixPosDef
    {n : ℕ} {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    ContinuousOn
      (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
      (Set.Ioi (0 : ℝ)) := by
  have hk := jKuboKernel_continuousOn_Ioi_of_matrixPosDef hA hB
  have hcoeff : ContinuousOn (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) := by
    exact (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).continuousOn
  exact hcoeff.smul hk

/--
For a positive-ray Kubo--Ando representation, the endpoint-weighted fixed
kernel is Bochner integrable with respect to the representing finite measure.
-/
theorem weighted_jKuboKernel_integrable_of_positiveRayKuboAndoRep
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    MeasureTheory.Integrable
      (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
      (rep.ν : MeasureTheory.Measure ℝ) := by
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let F : ℝ → HSOp n := fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using weighted_jKuboKernel_continuousOn_Ioi_of_matrixPosDef hA hB
  have hF_restrict :
      AEStronglyMeasurable F (μ.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  let G : ℝ → HSOp n :=
    (Set.Ioi (0 : ℝ)).piecewise F (fun _ : ℝ => (0 : HSOp n))
  have hG : AEStronglyMeasurable G μ := by
    dsimp [G]
    exact AEStronglyMeasurable.piecewise measurableSet_Ioi hF_restrict
      aestronglyMeasurable_const
  have hFG : F =ᵐ[μ] G := by
    filter_upwards [hsupport] with t ht
    simp [G, ht]
  have hF_meas : AEStronglyMeasurable F μ := hG.congr hFG.symm
  let C : ℝ :=
    max (‖jArg A B‖ * ‖(1 : HSOp n)‖) 1 * ‖(rightMul B : HSOp n)‖
  have hC_bound : ∀ᵐ t ∂μ, ‖F t‖ ≤ C := by
    filter_upwards [hsupport] with t ht
    have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hEq :=
      weighted_jKuboKernel_eq_hsCfcR_positiveRayKuboAndoKernel_jArg_mul_rightMul
        (t := t) htpos hA hB
    have hCfc :
        ‖hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B)‖ ≤
          max (‖jArg A B‖ * ‖(1 : HSOp n)‖) 1 := by
      have hCnonneg :
          0 ≤ max (‖jArg A B‖ * ‖(1 : HSOp n)‖) 1 :=
        le_trans zero_le_one (le_max_right _ _)
      refine norm_cfc_le (a := jArg A B) hCnonneg ?_
      intro x hx
      have hxpos : 0 < x := by
        exact jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB hx
      have hxnorm : ‖x‖ ≤ ‖jArg A B‖ * ‖(1 : HSOp n)‖ :=
        spectrum.norm_le_norm_mul_of_mem hx
      have hxle : x ≤ ‖jArg A B‖ * ‖(1 : HSOp n)‖ := by
        have hxnorm_eq : ‖x‖ = x := Real.norm_of_nonneg (le_of_lt hxpos)
        simpa [hxnorm_eq] using hxnorm
      have hmax : max x 1 ≤ max (‖jArg A B‖ * ‖(1 : HSOp n)‖) 1 :=
        max_le_max hxle le_rfl
      exact (positiveRayKuboAndoKernel_norm_le_max_of_pos (le_of_lt hxpos) htpos).trans hmax
    have hmul :
        ‖hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (jArg A B) *
            rightMul B‖ ≤
          max (‖jArg A B‖ * ‖(1 : HSOp n)‖) 1 *
            ‖(rightMul B : HSOp n)‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right hCfc (norm_nonneg _))
    change ‖(((1 + t : ℝ) : ℂ) • jKuboKernel t A B)‖ ≤ C
    rw [hEq]
    simpa [C] using hmul
  exact MeasureTheory.Integrable.of_bound hF_meas C hC_bound

private theorem gKuboKernel_continuousOn_Ioi_of_matrixPosDef
    {n : ℕ} {X Y : Mₙ n} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    ContinuousOn (fun t : ℝ => gKuboKernel t X Y) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  have hcont_inv : Continuous (fun t : ℝ => gKuboKernelInvForm t X Y) := by
    unfold gKuboKernelInvForm
    exact (Complex.continuous_ofReal.smul continuous_const).add continuous_const
  have hunit : IsUnit (gKuboKernelInvForm t X Y) :=
    gKuboKernelInvForm_isUnit_of_matrixPosDef (le_of_lt ht) hX hY
  have hinv_cont :
      ContinuousAt (fun T : HSOp n => Ring.inverse T) (gKuboKernelInvForm t X Y) := by
    simpa using (NormedRing.inverse_continuousAt hunit.unit)
  simpa [gKuboKernel] using
    ContinuousAt.comp_continuousWithinAt hinv_cont
      (f := fun t : ℝ => gKuboKernelInvForm t X Y) (x := t)
      (hcont_inv.continuousAt.continuousWithinAt)

private theorem weighted_gKuboKernel_continuousOn_Ioi_of_matrixPosDef
    {n : ℕ} {X Y : Mₙ n} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    ContinuousOn
      (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y))
      (Set.Ioi (0 : ℝ)) := by
  have hk := gKuboKernel_continuousOn_Ioi_of_matrixPosDef hX hY
  have hcoeff : ContinuousOn (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) := by
    exact (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).continuousOn
  exact hcoeff.smul hk

/--
For a positive-ray Kubo--Ando representation, the endpoint-weighted direct
fixed kernel is Bochner integrable with respect to the representing finite
measure.
-/
theorem weighted_gKuboKernel_integrable_of_positiveRayKuboAndoRep
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ n} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    MeasureTheory.Integrable
      (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y))
      (rep.ν : MeasureTheory.Measure ℝ) := by
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let F : ℝ → HSOp n := fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    simpa [F] using weighted_gKuboKernel_continuousOn_Ioi_of_matrixPosDef hX hY
  have hF_restrict :
      AEStronglyMeasurable F (μ.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  let G : ℝ → HSOp n :=
    (Set.Ioi (0 : ℝ)).piecewise F (fun _ : ℝ => (0 : HSOp n))
  have hG : AEStronglyMeasurable G μ := by
    dsimp [G]
    exact AEStronglyMeasurable.piecewise measurableSet_Ioi hF_restrict
      aestronglyMeasurable_const
  have hFG : F =ᵐ[μ] G := by
    filter_upwards [hsupport] with t ht
    simp [G, ht]
  have hF_meas : AEStronglyMeasurable F μ := hG.congr hFG.symm
  let C : ℝ :=
    max (‖gArg X Y‖ * ‖(1 : HSOp n)‖) 1 * ‖(leftMul Y : HSOp n)‖
  have hC_bound : ∀ᵐ t ∂μ, ‖F t‖ ≤ C := by
    filter_upwards [hsupport] with t ht
    have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hEq :=
      weighted_gKuboKernel_eq_hsCfcR_positiveRayKuboAndoKernel_gArg_mul_leftMul
        (t := t) htpos hX hY
    have hCfc :
        ‖hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y)‖ ≤
          max (‖gArg X Y‖ * ‖(1 : HSOp n)‖) 1 := by
      have hCnonneg :
          0 ≤ max (‖gArg X Y‖ * ‖(1 : HSOp n)‖) 1 :=
        le_trans zero_le_one (le_max_right _ _)
      refine norm_cfc_le (a := gArg X Y) hCnonneg ?_
      intro x hx
      have hxpos : 0 < x := by
        exact gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY hx
      have hxnorm : ‖x‖ ≤ ‖gArg X Y‖ * ‖(1 : HSOp n)‖ :=
        spectrum.norm_le_norm_mul_of_mem hx
      have hxle : x ≤ ‖gArg X Y‖ * ‖(1 : HSOp n)‖ := by
        have hxnorm_eq : ‖x‖ = x := Real.norm_of_nonneg (le_of_lt hxpos)
        simpa [hxnorm_eq] using hxnorm
      have hmax : max x 1 ≤ max (‖gArg X Y‖ * ‖(1 : HSOp n)‖) 1 :=
        max_le_max hxle le_rfl
      exact (positiveRayKuboAndoKernel_norm_le_max_of_pos (le_of_lt hxpos) htpos).trans hmax
    have hmul :
        ‖hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) (gArg X Y) *
            leftMul Y‖ ≤
          max (‖gArg X Y‖ * ‖(1 : HSOp n)‖) 1 *
            ‖(leftMul Y : HSOp n)‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right hCfc (norm_nonneg _))
    change ‖(((1 + t : ℝ) : ℂ) • gKuboKernel t X Y)‖ ≤ C
    rw [hEq]
    simpa [C] using hmul
  exact MeasureTheory.Integrable.of_bound hF_meas C hC_bound

private theorem positiveRayKuboAndoKernel_continuousOn_spectrum_of_pos
    {n : ℕ} {T : HSOp n}
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ))
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun x : ℝ => positiveRayKuboAndoKernel x t) (spectrum ℝ T) := by
  unfold positiveRayKuboAndoKernel
  refine ((continuous_id.mul continuous_const).continuousOn).div
    ((continuous_id.add continuous_const).continuousOn) ?_
  intro x hx
  have hxpos : 0 < x := by simpa [Set.mem_Ioi] using hσT hx
  exact ne_of_gt (add_pos hxpos ht)

private theorem positiveRayKuboAndoKernel_uncurry_continuousOn_Ioi_spectrum
    {n : ℕ} {T : HSOp n}
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn
      (Function.uncurry (fun t x : ℝ => positiveRayKuboAndoKernel x t))
      (Set.Ioi (0 : ℝ) ×ˢ spectrum ℝ T) := by
  unfold Function.uncurry positiveRayKuboAndoKernel
  refine ((continuous_snd.mul (continuous_const.add continuous_fst)).continuousOn).div
    ((continuous_snd.add continuous_fst).continuousOn) ?_
  intro p hp
  have htpos : 0 < p.1 := by simpa [Set.mem_Ioi] using hp.1
  have hxpos : 0 < p.2 := by simpa [Set.mem_Ioi] using hσT hp.2
  exact ne_of_gt (add_pos hxpos htpos)

private theorem positiveRayKuboAndoRep_kernel_continuousMap_integrable
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {T : HSOp n} (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ContinuousMap.mkD
          ((spectrum ℝ T).restrict (fun x : ℝ => positiveRayKuboAndoKernel x t))
          (0 : C(spectrum ℝ T, ℝ)))
      (rep.ν : MeasureTheory.Measure ℝ) := by
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let F : ℝ → C(spectrum ℝ T, ℝ) := fun t : ℝ =>
    ContinuousMap.mkD
      ((spectrum ℝ T).restrict (fun x : ℝ => positiveRayKuboAndoKernel x t))
      (0 : C(spectrum ℝ T, ℝ))
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hF_restrict :
      AEStronglyMeasurable F (μ.restrict (Set.Ioi (0 : ℝ))) := by
    -- `ℝ` is second countable; give this directly instead of searching through `C(_, ℝ)`.
    haveI : SecondCountableTopologyEither ℝ C(spectrum ℝ T, ℝ) :=
      secondCountableTopologyEither_of_left _ _
    simpa [F] using
      (ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry
        (μ := μ)
        (s := Set.Ioi (0 : ℝ))
        (t := spectrum ℝ T)
        measurableSet_Ioi
        (fun t x : ℝ => positiveRayKuboAndoKernel x t)
        (0 : C(spectrum ℝ T, ℝ))
        (positiveRayKuboAndoKernel_uncurry_continuousOn_Ioi_spectrum
          (T := T) hσT))
  let G : ℝ → C(spectrum ℝ T, ℝ) :=
    (Set.Ioi (0 : ℝ)).piecewise F (fun _ : ℝ => (0 : C(spectrum ℝ T, ℝ)))
  have hG : AEStronglyMeasurable G μ := by
    dsimp [G]
    exact AEStronglyMeasurable.piecewise measurableSet_Ioi hF_restrict
      aestronglyMeasurable_const
  have hFG : F =ᵐ[μ] G := by
    filter_upwards [hsupport] with t ht
    simp [G, ht]
  have hF_meas : AEStronglyMeasurable F μ := hG.congr hFG.symm
  let Cb : ℝ := max (‖T‖ * ‖(1 : HSOp n)‖) 1
  have hCb_nonneg : 0 ≤ Cb := le_trans zero_le_one (le_max_right _ _)
  have hbound : ∀ᵐ t ∂μ, ∀ y : spectrum ℝ T, ‖F t y‖ ≤ Cb := by
    filter_upwards [hsupport] with t ht y
    have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hypos : 0 < (y : ℝ) := by
      simpa [Set.mem_Ioi] using hσT y.property
    have hval :
        F t y = positiveRayKuboAndoKernel (y : ℝ) t := by
      dsimp [F]
      rw [ContinuousMap.mkD_apply_of_continuousOn
        (positiveRayKuboAndoKernel_continuousOn_spectrum_of_pos
          (T := T) hσT htpos)]
    rw [hval]
    have hynorm : ‖(y : ℝ)‖ ≤ ‖T‖ * ‖(1 : HSOp n)‖ :=
      spectrum.norm_le_norm_mul_of_mem y.property
    have hyle : (y : ℝ) ≤ ‖T‖ * ‖(1 : HSOp n)‖ := by
      have hynorm_eq : ‖(y : ℝ)‖ = (y : ℝ) :=
        Real.norm_of_nonneg (le_of_lt hypos)
      simpa [hynorm_eq] using hynorm
    exact (positiveRayKuboAndoKernel_norm_le_max_of_pos (le_of_lt hypos) htpos).trans
      (max_le_max hyle le_rfl)
  have hfinite : HasFiniteIntegral F μ :=
    ContinuousMap.hasFiniteIntegral_of_bound F (fun _ : ℝ => Cb)
      (integrable_const Cb).hasFiniteIntegral hbound
  exact ⟨hF_meas, hfinite⟩

/--
The scalar Kubo-Ando kernel integrated against a positive-ray representation is
continuous on any positive real spectrum. This is the continuity input for the
CFC/Bochner integral exchange in Carlen's route [carlen2022].
-/
theorem positiveRayKuboAndoRep_integral_kernel_continuousOn_spectrum
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {T : HSOp n} (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ t : ℝ, positiveRayKuboAndoKernel x t
          ∂(rep.ν : MeasureTheory.Measure ℝ))
      (spectrum ℝ T) := by
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let F : ℝ → C(spectrum ℝ T, ℝ) := fun t : ℝ =>
    ContinuousMap.mkD
      ((spectrum ℝ T).restrict (fun x : ℝ => positiveRayKuboAndoKernel x t))
      (0 : C(spectrum ℝ T, ℝ))
  have hF : MeasureTheory.Integrable F μ := by
    simpa [F, μ] using
      (positiveRayKuboAndoRep_kernel_continuousMap_integrable
        (n := n) (T := T) rep hσT)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have key (z : spectrum ℝ T) :
      (∫ t : ℝ, positiveRayKuboAndoKernel (z : ℝ) t ∂μ) =
        (∫ t : ℝ, F t ∂μ) z := by
    have hval_ae :
        (fun t : ℝ => F t z) =ᵐ[μ]
          fun t : ℝ => positiveRayKuboAndoKernel (z : ℝ) t := by
      filter_upwards [hsupport] with t ht
      have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
      dsimp [F]
      rw [ContinuousMap.mkD_apply_of_continuousOn
        (positiveRayKuboAndoKernel_continuousOn_spectrum_of_pos
          (T := T) hσT htpos)]
    calc
      (∫ t : ℝ, positiveRayKuboAndoKernel (z : ℝ) t ∂μ)
          = ∫ t : ℝ, F t z ∂μ := by
              exact (integral_congr_ae hval_ae.symm)
      _ = (∫ t : ℝ, F t ∂μ) z := (ContinuousMap.integral_apply hF z).symm
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_congr key |>.mpr ?_
  exact map_continuous (∫ t : ℝ, F t ∂μ)

/--
Functional calculus of the integrated Kubo-Ando kernel equals the Bochner
integral of the pointwise functional calculi on positive spectrum. This is the
operator-side integral exchange used in the Carlen expansion [carlen2022].
-/
theorem hsCfcR_positiveRayKuboAndoRep_integral_kernel
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {T : HSOp n} (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsCfcR
        (fun x : ℝ =>
          ∫ t : ℝ, positiveRayKuboAndoKernel x t
            ∂(rep.ν : MeasureTheory.Measure ℝ))
        T =
      ∫ t : ℝ,
        hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T
          ∂(rep.ν : MeasureTheory.Measure ℝ) := by
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hf₁ :
      ∀ᵐ t ∂μ,
        ContinuousOn (fun x : ℝ => positiveRayKuboAndoKernel x t) (spectrum ℝ T) := by
    filter_upwards [hsupport] with t ht
    have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
    exact positiveRayKuboAndoKernel_continuousOn_spectrum_of_pos
      (T := T) hσT htpos
  have hf₂ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          ContinuousMap.mkD
            ((spectrum ℝ T).restrict
              (fun x : ℝ => positiveRayKuboAndoKernel x t))
            (0 : C(spectrum ℝ T, ℝ)))
        μ := by
    simpa [μ] using
      (positiveRayKuboAndoRep_kernel_continuousMap_integrable
        (n := n) (T := T) rep hσT)
  simpa [hsCfcR, μ] using
    (cfc_integral' (𝕜 := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (μ := μ)
      (f := fun t x : ℝ => positiveRayKuboAndoKernel x t)
      (a := T) hf₁ hf₂ (ha := hT))


end

end Quantum.TraceInequality.Loewner.HiaiPetz
