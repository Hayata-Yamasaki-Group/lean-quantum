/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Quantum.TraceInequality.HiaiPetz.FinMatrixCStar
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic

/-!
# Positivity input for Carlen's `G_f`

This file contains the first positivity layer of OMI-02. If the matrix inputs are positive
definite, the Carlen CFC input `R_X L_{Y⁻¹}` is a positive invertible self-adjoint operator
(IsStrictlyPositive in Lean), and hence has positive real spectrum.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance instOpMontIHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance instOpMontIHSOpStarRing {n : ℕ} : StarRing (HSOp n) :=
  (instOpMontIHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance instOpMontIHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance instOpMontIHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance instOpMontIHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (instOpMontIHSOpCStarAlgebra (n := n))
    (instOpMontIHSOpPartialOrder (n := n))
    (instOpMontIHSOpStarOrderedRing (n := n))

local instance instOpMontIHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable section

/-- `gArg X Y` is the product `R_X L_{Y⁻¹}`. -/
theorem gArg_eq_rightMul_mul_leftMul {n : ℕ} (X Y : Mₙ n) :
    gArg X Y = (rightMul X : HSOp n) * leftMul (posInv Y) := by
  ext Z i j
  simp [gArg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]

/-- The Carlen CFC argument is strictly positive for positive-definite inputs. -/
theorem gArg_isStrictlyPositive_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsStrictlyPositive (gArg X Y) := by
  have hright : IsStrictlyPositive (rightMul X : HSOp n) :=
    rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hX)
  have hleft : IsStrictlyPositive (leftMul (posInv Y) : HSOp n) :=
    leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posInv_posDef hY)
  have hcomm : Commute (rightMul X : HSOp n) (leftMul (posInv Y)) :=
    (leftMul_commute_rightMul (posInv Y) X).symm
  have hprod : IsStrictlyPositive ((rightMul X : HSOp n) * leftMul (posInv Y)) :=
    (@IsStrictlyPositive.commute_iff (HSOp n)
      inferInstance
      (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarRing (n := n))
      (instOpMontIHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIHSOpNonnegSpectrumClass (n := n))
      (rightMul X : HSOp n) (leftMul (posInv Y)) hright hleft).mp hcomm
  simpa [gArg_eq_rightMul_mul_leftMul X Y] using hprod

/-- The Carlen CFC input has positive real spectrum for positive definite inputs. -/
theorem gArg_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instOpMontIHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIHSOpNonnegSpectrumClass (n := n))
      (gArg X Y)
      (gArg_isStrictlyPositive_of_matrixPosDef hX hY) x hx

/-- The real CFC inverse formula for `f(gArg X Y)` under Carlen's function hypothesis. -/
theorem hsCfcR_inv_gArg_eq_inverse_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg X Y) =
      Ring.inverse (hsCfcR f (gArg X Y)) := by
  have hσ : spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) :=
    gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hcont : ContinuousOn f (spectrum ℝ (gArg X Y)) :=
    hf.1.mono hσ
  have hnonzero : ∀ x ∈ spectrum ℝ (gArg X Y), f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hf.2 (hσ hx))
  have hstrict : IsStrictlyPositive (gArg X Y) :=
    gArg_isStrictlyPositive_of_matrixPosDef hX hY
  have hsa : IsSelfAdjoint (gArg X Y) :=
    @IsStrictlyPositive.isSelfAdjoint (HSOp n)
      inferInstance
      (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarRing (n := n))
      (instOpMontIHSOpStarOrderedRing (n := n))
      (gArg X Y) hstrict
  simpa [hsCfcR] using
    (cfc_inv (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (f := f) (a := gArg X Y) hnonzero (hf := hcont) (ha := hsa))

/-- Left multiplication by `Y⁻¹` cancels left multiplication by `Y`. -/
theorem opMontI_leftMul_posInv_mul_leftMul_of_matrixPosDef {n : ℕ} {Y : Mₙ n}
    (hY : MatrixPosDef Y) :
    (leftMul (posInv Y) : HSOp n) * leftMul Y = 1 := by
  ext Z i j
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (matrixPosDef_isUnit hY)
  calc
    ((leftMul (posInv Y) : HSOp n) * leftMul Y) Z i j
        = ((Y⁻¹ * Y) * Z) i j := by
            simp [ContinuousLinearMap.mul_apply, posInv, Matrix.mul_assoc]
    _ = Z i j := by
          rw [Matrix.nonsing_inv_mul Y hdet]
          simp

/-- Left multiplication by `Y` cancels left multiplication by `Y⁻¹`. -/
theorem opMontI_leftMul_mul_leftMul_posInv_of_matrixPosDef {n : ℕ} {Y : Mₙ n}
    (hY : MatrixPosDef Y) :
    (leftMul Y : HSOp n) * leftMul (posInv Y) = 1 := by
  ext Z i j
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (matrixPosDef_isUnit hY)
  calc
    ((leftMul Y : HSOp n) * leftMul (posInv Y)) Z i j
        = ((Y * Y⁻¹) * Z) i j := by
            simp [ContinuousLinearMap.mul_apply, posInv, Matrix.mul_assoc]
    _ = Z i j := by
          rw [Matrix.mul_nonsing_inv Y hdet]
          simp

/-- The Carlen CFC argument commutes with the endpoint left multiplication `L_Y`. -/
theorem gArg_commute_leftMul_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hY : MatrixPosDef Y) :
    Commute (gArg X Y) (leftMul Y : HSOp n) := by
  rw [commute_iff_eq]
  ext Z i j
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (matrixPosDef_isUnit hY)
  calc
    ((gArg X Y) * leftMul Y : HSOp n) Z i j
        = ((Y⁻¹ * Y) * Z * X) i j := by
            simp [gArg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
              posInv, Matrix.mul_assoc]
    _ = (Z * X) i j := by
          rw [Matrix.nonsing_inv_mul Y hdet]
          simp
    _ = ((Y * Y⁻¹) * Z * X) i j := by
          rw [Matrix.mul_nonsing_inv Y hdet]
          simp
    _ = (leftMul Y * (gArg X Y) : HSOp n) Z i j := by
          simp [gArg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
            posInv, Matrix.mul_assoc]

/-- The Carlen CFC argument commutes with `L_{Y⁻¹}`. -/
theorem gArg_commute_leftMul_posInv {n : ℕ} (X Y : Mₙ n) :
    Commute (gArg X Y) (leftMul (posInv Y) : HSOp n) := by
  rw [commute_iff_eq]
  ext Z i j
  simp [gArg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
    posInv, Matrix.mul_assoc]

/-- Applying a positive function to the positive Carlen CFC argument is strictly positive. -/
theorem hsCfcR_gArg_isStrictlyPositive_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsStrictlyPositive (hsCfcR f (gArg X Y)) := by
  have hσ : spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) :=
    gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hcont : ContinuousOn f (spectrum ℝ (gArg X Y)) :=
    hf.1.mono hσ
  have hstrict : IsStrictlyPositive (gArg X Y) :=
    gArg_isStrictlyPositive_of_matrixPosDef hX hY
  have hsa : IsSelfAdjoint (gArg X Y) :=
    @IsStrictlyPositive.isSelfAdjoint (HSOp n)
      inferInstance
      (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarRing (n := n))
      (instOpMontIHSOpStarOrderedRing (n := n))
      (gArg X Y) hstrict
  rw [hsCfcR]
  exact
    (@cfc_isStrictlyPositive_iff ℝ (HSOp n) IsSelfAdjoint
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIHSOpStarRing (n := n))
      (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      (instOpMontIHSOpNonnegSpectrumClass (n := n))
      f (gArg X Y) hcont hsa).mpr
      (fun x hx => hf.2 (hσ hx))

/-- Carlen's perspective operator `G_f(X,Y)` is strictly positive. -/
theorem gOperator_isStrictlyPositive_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsStrictlyPositive (gOperator f X Y) := by
  have hF : IsStrictlyPositive (hsCfcR f (gArg X Y)) :=
    hsCfcR_gArg_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY
  have hL : IsStrictlyPositive (leftMul Y : HSOp n) :=
    leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hY)
  have hcomm :
      Commute (hsCfcR f (gArg X Y)) (leftMul Y : HSOp n) := by
    simpa [hsCfcR] using
      (gArg_commute_leftMul_of_matrixPosDef (X := X) hY).cfc_real f
  have hprod : IsStrictlyPositive (hsCfcR f (gArg X Y) * leftMul Y : HSOp n) :=
    (@IsStrictlyPositive.commute_iff (HSOp n)
      inferInstance
      (instOpMontIHSOpPartialOrder (n := n))
      (instOpMontIHSOpStarRing (n := n))
      (instOpMontIHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIHSOpNonnegSpectrumClass (n := n))
      (hsCfcR f (gArg X Y)) (leftMul Y : HSOp n) hF hL).mp hcomm
  simpa [gOperator] using hprod

/-- The theorem-facing inverse is a left inverse of Carlen's perspective operator. -/
theorem gOperatorInv_mul_gOperator_eq_one_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gOperatorInv f X Y * gOperator f X Y = 1 := by
  let F : HSOp n := hsCfcR f (gArg X Y)
  let Finv : HSOp n := hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg X Y)
  let L : HSOp n := leftMul Y
  let Linv : HSOp n := leftMul (posInv Y)
  have hFinv : Finv = Ring.inverse F := by
    simpa [F, Finv] using
      hsCfcR_inv_gArg_eq_inverse_of_carlenFunctionHypothesis hf hX hY
  have hFunit : IsUnit F := by
    exact
      (hsCfcR_gArg_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY).isUnit
  have hLinvL : Linv * L = 1 := by
    simpa [L, Linv] using opMontI_leftMul_posInv_mul_leftMul_of_matrixPosDef hY
  have hFinvF : Finv * F = 1 := by
    rw [hFinv]
    exact Ring.inverse_mul_cancel F hFunit
  have hcomm : Commute F Linv := by
    simpa [F, Linv, hsCfcR] using
      (gArg_commute_leftMul_posInv X Y).cfc_real f
  calc
    gOperatorInv f X Y * gOperator f X Y
        = (Finv * Linv) * (F * L) := by
            simp [gOperatorInv, gOperator, F, Finv, L, Linv]
    _ = (Finv * F) * (Linv * L) := by
          calc
            (Finv * Linv) * (F * L)
                = Finv * (Linv * F) * L := by
                    rw [mul_assoc, ← mul_assoc Linv F L, mul_assoc Finv (Linv * F) L]
            _ = Finv * (F * Linv) * L := by
                    rw [← hcomm.eq]
            _ = (Finv * F) * (Linv * L) := by
                    rw [← mul_assoc Finv F Linv, mul_assoc (Finv * F) Linv L]
    _ = 1 := by
          rw [hFinvF, hLinvL, one_mul]

/-- The theorem-facing inverse is a right inverse of Carlen's perspective operator. -/
theorem gOperator_mul_gOperatorInv_eq_one_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gOperator f X Y * gOperatorInv f X Y = 1 := by
  let F : HSOp n := hsCfcR f (gArg X Y)
  let Finv : HSOp n := hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg X Y)
  let L : HSOp n := leftMul Y
  let Linv : HSOp n := leftMul (posInv Y)
  have hFinv : Finv = Ring.inverse F := by
    simpa [F, Finv] using
      hsCfcR_inv_gArg_eq_inverse_of_carlenFunctionHypothesis hf hX hY
  have hFunit : IsUnit F := by
    exact
      (hsCfcR_gArg_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY).isUnit
  have hLLinv : L * Linv = 1 := by
    simpa [L, Linv] using opMontI_leftMul_mul_leftMul_posInv_of_matrixPosDef hY
  have hFFinv : F * Finv = 1 := by
    rw [hFinv]
    exact Ring.mul_inverse_cancel F hFunit
  have hcomm : Commute Finv L := by
    have hbase :
        Commute (gArg X Y) (leftMul Y : HSOp n) :=
      gArg_commute_leftMul_of_matrixPosDef hY
    have hcf :
        Commute (hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg X Y)) (leftMul Y : HSOp n) := by
      simpa [hsCfcR] using hbase.cfc_real (fun x : ℝ => (f x)⁻¹)
    simpa [Finv, L] using hcf
  calc
    gOperator f X Y * gOperatorInv f X Y
        = (F * L) * (Finv * Linv) := by
            simp [gOperatorInv, gOperator, F, Finv, L, Linv]
    _ = (F * Finv) * (L * Linv) := by
          calc
            (F * L) * (Finv * Linv)
                = F * (L * Finv) * Linv := by
                    rw [mul_assoc, ← mul_assoc L Finv Linv, mul_assoc F (L * Finv) Linv]
            _ = F * (Finv * L) * Linv := by
                    rw [hcomm.eq]
            _ = (F * Finv) * (L * Linv) := by
                    rw [← mul_assoc F Finv L, mul_assoc (F * Finv) L Linv]
    _ = 1 := by
          rw [hFFinv, hLLinv, one_mul]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
