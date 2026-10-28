/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions

/-!
# Carlen's `opmontI` conditions: weighted block action

This module contains the weighted inverse-action, weighted `gArg`, and
diagonal-compression stage used in Carlen 2022 Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOpMontIBaseHSOpCStarAlgebra
  instOpMontIBaseHSOpComplexAlgebra
  instOpMontIBaseMatrixRealModule
  instOpMontIBaseMatrixRealScalarTower
  instOpMontIBaseMatrixRealNormedSpace
  instOpMontIBaseMatrixRealFiniteDimensional
  instOpMontIBaseHSOpRealAlgebra
  instOpMontIBaseHSOpStarRing
  instOpMontIBaseHSOpPartialOrder
  instOpMontIBaseHSOpStarOrderedRing
  instOpMontIBaseHSOpNonnegSpectrumClass
  instOpMontIBaseHSOpRealCFC
  instOpMontIBaseMatrixOppRealCFC
  instOpMontIBaseHSOpProdCStarAlgebra
  instOpMontIBaseHSOpProdRealCFC
  instOpMontIBaseHSOpProdProdCStarAlgebra
  instOpMontIBaseHSOpProdProdRealCFC

noncomputable section

-- Keep the complex-to-real matrix algebra local to the weighted block simplifications.
noncomputable local instance instWeightedActionMatrixRealAlgebra {n : ℕ} :
    Algebra ℝ (Mₙ n) := Algebra.complexToReal

/-! ### Weighted inverse action on block inputs -/
/--
Left multiplication by the inverse of a weighted block-diagonal positive
matrix cancels the weights on a weighted block-diagonal vector.
-/
theorem leftMul_posInv_weightedBlockDiag_apply_weightedBlockDiag {n : ℕ}
    {θ : ℝ} {Y₀ Y₁ Z₀ Z₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (weightedBlockDiag θ Z₀ Z₁) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁)) := by
  let Y : Mₙ (n + n) := weightedBlockDiag θ Y₀ Y₁
  let Z : Mₙ (n + n) := weightedBlockDiag θ Z₀ Z₁
  let W : Mₙ (n + n) :=
    twoBlockReindex (n := n)
      (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))
  have hYdet : IsUnit Y.det := by
    exact (Matrix.isUnit_iff_isUnit_det Y).mp
      (matrixPosDef_isUnit
        (weightedBlockDiag_matrixPosDef
          (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1))
  have hY₀det : IsUnit Y₀.det :=
    (Matrix.isUnit_iff_isUnit_det Y₀).mp (matrixPosDef_isUnit hY₀)
  have hY₁det : IsUnit Y₁.det :=
    (Matrix.isUnit_iff_isUnit_det Y₁).mp (matrixPosDef_isUnit hY₁)
  have hYW : Y * W = Z := by
    change
      weightedBlockDiag θ Y₀ Y₁ *
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁)) =
        weightedBlockDiag θ Z₀ Z₁
    rw [weightedBlockDiag, weightedBlockDiag, ← map_mul]
    congr 1
    simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add,
      Complex.ofReal_sub, Complex.ofReal_one, posInv, Matrix.fromBlocks_inj]
    constructor
    · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₀ hY₀det]
    · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₁ hY₁det]
  calc
    (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (weightedBlockDiag θ Z₀ Z₁) =
        Y⁻¹ * Z := by
          change posInv (weightedBlockDiag θ Y₀ Y₁) *
              weightedBlockDiag θ Z₀ Z₁ = Y⁻¹ * Z
          simp [posInv, Y, Z]
    _ = Y⁻¹ * (Y * W) := by rw [hYW]
    _ = W := by
          simpa using Matrix.nonsing_inv_mul_cancel_left Y W hYdet

/-- Real multiplication by a nonzero scalar cancels complex multiplication by its inverse. -/
theorem matrix_real_smul_complex_inv_smul {n : ℕ} {θ : ℝ} (hθC : (θ : ℂ) ≠ 0)
    (A : Mₙ n) :
    θ • (((θ : ℂ)⁻¹) • A) = A := by
  ext i j
  simp [Complex.real_smul, hθC]

/-- In matrix multiplication, an inverse scalar on the left factor cancels the
same scalar on the right factor. -/
theorem matrix_complex_inv_smul_mul_smul {n : ℕ} {z : ℂ} (hz : z ≠ 0)
    (A B : Mₙ n) :
    (z⁻¹ • A) * (z • B) = A * B := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  calc
    z⁻¹ * A i x * (z * B x j) = (z⁻¹ * z) * (A i x * B x j) := by
      ring
    _ = A i x * B x j := by
      rw [inv_mul_cancel₀ hz, one_mul]

/-- In matrix multiplication, a scalar on the left factor cancels its inverse on
the right factor. -/
theorem matrix_complex_smul_mul_inv_smul {n : ℕ} {z : ℂ} (hz : z ≠ 0)
    (A B : Mₙ n) :
    (z • A) * (z⁻¹ • B) = A * B := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  calc
    z * A i x * (z⁻¹ * B x j) = (z * z⁻¹) * (A i x * B x j) := by
      ring
    _ = A i x * B x j := by
      rw [mul_inv_cancel₀ hz, one_mul]

/-- Scalars on the two factors of a matrix product combine into one scalar. -/
theorem matrix_complex_smul_mul_smul {n : ℕ} (z w : ℂ) (A B : Mₙ n) :
    (z • A) * (w • B) = (z * w) • (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/--
An unweighted block-diagonal matrix can be viewed as a weighted block-diagonal
matrix after rescaling the two diagonal blocks by the inverse weights.
-/
theorem weightedBlockDiag_inv_smul_eq_twoBlockReindex_fromBlocks {n : ℕ}
    {θ : ℝ} {V₀ V₁ : Mₙ n}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    weightedBlockDiag θ (((θ : ℂ)⁻¹) • V₀) ((((1 - θ : ℝ) : ℂ)⁻¹) • V₁) =
      twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁) := by
  have hθC : (θ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hθ0)
  have h1θC : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hθ1))
  have h1θC' : (1 : ℂ) - (θ : ℂ) ≠ 0 := by
    simpa using h1θC
  rw [weightedBlockDiag]
  congr 1
  simp [hθC, h1θC', smul_smul]

/--
Left multiplication by the inverse of a weighted block-diagonal positive
matrix on an unweighted block vector produces inverse weights on the two
blocks.
-/
theorem leftMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks {n : ℕ}
    {θ : ℝ} {Y₀ Y₁ V₀ V₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀)) 0 0
          ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁))) := by
  rw [← weightedBlockDiag_inv_smul_eq_twoBlockReindex_fromBlocks
    (n := n) (θ := θ) (V₀ := V₀) (V₁ := V₁) hθ0 hθ1]
  rw [leftMul_posInv_weightedBlockDiag_apply_weightedBlockDiag
    (n := n) (θ := θ) (Y₀ := Y₀) (Y₁ := Y₁)
    (Z₀ := ((θ : ℂ)⁻¹) • V₀)
    (Z₁ := (((1 - θ : ℝ) : ℂ)⁻¹) • V₁)
    hY₀ hY₁ hθ0 hθ1]
  congr 1
  simp

/--
Left multiplication by the inverse of a weighted block-diagonal positive
matrix acts on a full `2 × 2` block matrix row by row: the first block row gets
`θ⁻¹Y₀⁻¹`, and the second block row gets `(1-θ)⁻¹Y₁⁻¹`.
-/
theorem leftMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks_all {n : ℕ}
    {θ : ℝ} {Y₀ Y₁ V₀₀ V₀₁ V₁₀ V₁₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
          (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
          ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀))
          ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁))) := by
  let Y : Mₙ (n + n) := weightedBlockDiag θ Y₀ Y₁
  let V : Mₙ (n + n) := twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)
  let W : Mₙ (n + n) :=
    twoBlockReindex (n := n)
      (Matrix.fromBlocks
        (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
        (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
        ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀))
        ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁)))
  have hθC : (θ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hθ0)
  have h1θC : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hθ1))
  have h1θC' : (1 : ℂ) - (θ : ℂ) ≠ 0 := by
    simpa using h1θC
  have hYdet : IsUnit Y.det := by
    exact (Matrix.isUnit_iff_isUnit_det Y).mp
      (matrixPosDef_isUnit
        (weightedBlockDiag_matrixPosDef
          (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1))
  have hY₀det : IsUnit Y₀.det :=
    (Matrix.isUnit_iff_isUnit_det Y₀).mp (matrixPosDef_isUnit hY₀)
  have hY₁det : IsUnit Y₁.det :=
    (Matrix.isUnit_iff_isUnit_det Y₁).mp (matrixPosDef_isUnit hY₁)
  have hYW : Y * W = V := by
    change
      weightedBlockDiag θ Y₀ Y₁ *
          twoBlockReindex (n := n)
            (Matrix.fromBlocks
              (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
              (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
              ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀))
              ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁))) =
        twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)
    rw [weightedBlockDiag, ← map_mul]
    congr 1
    simp only [Matrix.fromBlocks_multiply, zero_mul, add_zero, zero_add,
      Complex.ofReal_sub, Complex.ofReal_one, Matrix.fromBlocks_inj]
    constructor
    · calc
        ((θ : ℂ) • Y₀) * (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
            = Y₀ * (posInv Y₀ * V₀₀) := by
                exact matrix_complex_smul_mul_inv_smul hθC Y₀ (posInv Y₀ * V₀₀)
        _ = V₀₀ := by
              simp [posInv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₀ hY₀det]
    constructor
    · calc
        ((θ : ℂ) • Y₀) * (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
            = Y₀ * (posInv Y₀ * V₀₁) := by
                exact matrix_complex_smul_mul_inv_smul hθC Y₀ (posInv Y₀ * V₀₁)
        _ = V₀₁ := by
              simp [posInv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₀ hY₀det]
    constructor
    · calc
        (((1 : ℂ) - (θ : ℂ)) • Y₁) *
            (((1 : ℂ) - (θ : ℂ))⁻¹ • (posInv Y₁ * V₁₀))
            = Y₁ * (posInv Y₁ * V₁₀) := by
                exact matrix_complex_smul_mul_inv_smul h1θC' Y₁ (posInv Y₁ * V₁₀)
        _ = V₁₀ := by
              simp [posInv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₁ hY₁det]
    · calc
        (((1 : ℂ) - (θ : ℂ)) • Y₁) *
            (((1 : ℂ) - (θ : ℂ))⁻¹ • (posInv Y₁ * V₁₁))
            = Y₁ * (posInv Y₁ * V₁₁) := by
                exact matrix_complex_smul_mul_inv_smul h1θC' Y₁ (posInv Y₁ * V₁₁)
        _ = V₁₁ := by
              simp [posInv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y₁ hY₁det]
  calc
    (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)) =
        Y⁻¹ * V := by
          change posInv (weightedBlockDiag θ Y₀ Y₁) *
              twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁) = Y⁻¹ * V
          simp [posInv, Y, V]
    _ = Y⁻¹ * (Y * W) := by rw [hYW]
    _ = W := by
          simpa using Matrix.nonsing_inv_mul_cancel_left Y W hYdet

/-! ### Weighted gArg formulas -/
/--
The Carlen CFC argument `gArg` of weighted block inputs acts on unweighted
block-diagonal vectors blockwise as the direct sum of the two original
arguments.
-/
theorem weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks {n : ℕ}
    {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀ V₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks ((gArg X₀ Y₀ : HSOp n) V₀) 0 0 ((gArg X₁ Y₁ : HSOp n) V₁)) := by
  have hθC : (θ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hθ0)
  have h1θC : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hθ1))
  have h1θC' : (1 : ℂ) - (θ : ℂ) ≠ 0 := by
    simpa using h1θC
  calc
    (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))
        =
      (rightMul (weightedBlockDiag θ X₀ X₁) : HSOp (n + n))
        ((leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))) := by
        rfl
    _ =
      (rightMul (weightedBlockDiag θ X₀ X₁) : HSOp (n + n))
        (twoBlockReindex (n := n)
          (Matrix.fromBlocks
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀)) 0 0
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁)))) := by
        rw [leftMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks
          (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1]
    _ =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks ((gArg X₀ Y₀ : HSOp n) V₀) 0 0 ((gArg X₁ Y₁ : HSOp n) V₁)) := by
        rw [weightedBlockDiag]
        change
          twoBlockReindex (n := n)
              (Matrix.fromBlocks
                (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀)) 0 0
                ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁))) *
              twoBlockReindex (n := n)
                (Matrix.fromBlocks ((θ : ℂ) • X₀) 0 0 (((1 - θ : ℝ) : ℂ) • X₁)) =
            twoBlockReindex (n := n)
              (Matrix.fromBlocks ((gArg X₀ Y₀ : HSOp n) V₀) 0 0
                ((gArg X₁ Y₁ : HSOp n) V₁))
        rw [← map_mul]
        congr 1
        simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add,
          Matrix.fromBlocks_inj, true_and]
        constructor
        · calc
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀)) * ((θ : ℂ) • X₀)
                = (posInv Y₀ * V₀) * X₀ := by
                    exact matrix_complex_inv_smul_mul_smul
                      (n := n) (z := (θ : ℂ)) hθC (posInv Y₀ * V₀) X₀
            _ = (gArg X₀ Y₀ : HSOp n) V₀ := by
                    rfl
        · calc
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁)) *
                ((((1 - θ : ℝ) : ℂ)) • X₁)
                = (posInv Y₁ * V₁) * X₁ := by
                    exact matrix_complex_inv_smul_mul_smul
                      (n := n) (z := (((1 - θ : ℝ) : ℂ))) h1θC
                      (posInv Y₁ * V₁) X₁
            _ = (gArg X₁ Y₁ : HSOp n) V₁ := by
                    rfl

/--
The weighted-block `gArg` acts on the full four-block decomposition. The two
diagonal block components are the original `gArg` operators, and the
off-diagonal components acquire the ratios of the two weights.
-/
theorem weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks_all {n : ℕ}
    {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀₀ V₀₁ V₁₀ V₁₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          ((gArg X₀ Y₀ : HSOp n) V₀₀)
          (((θ : ℂ)⁻¹ * ((1 - θ : ℝ) : ℂ)) • (posInv Y₀ * V₀₁ * X₁))
          ((((1 - θ : ℝ) : ℂ)⁻¹ * (θ : ℂ)) • (posInv Y₁ * V₁₀ * X₀))
          ((gArg X₁ Y₁ : HSOp n) V₁₁)) := by
  have hθC : (θ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hθ0)
  have h1θC : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hθ1))
  calc
    (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁))
        =
      (rightMul (weightedBlockDiag θ X₀ X₁) : HSOp (n + n))
        ((leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁))) := by
        rfl
    _ =
      (rightMul (weightedBlockDiag θ X₀ X₁) : HSOp (n + n))
        (twoBlockReindex (n := n)
          (Matrix.fromBlocks
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀))
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁)))) := by
        rw [leftMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks_all
          (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1]
    _ =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          ((gArg X₀ Y₀ : HSOp n) V₀₀)
          (((θ : ℂ)⁻¹ * ((1 - θ : ℝ) : ℂ)) • (posInv Y₀ * V₀₁ * X₁))
          ((((1 - θ : ℝ) : ℂ)⁻¹ * (θ : ℂ)) • (posInv Y₁ * V₁₀ * X₀))
          ((gArg X₁ Y₁ : HSOp n) V₁₁)) := by
        rw [weightedBlockDiag]
        change
          twoBlockReindex (n := n)
              (Matrix.fromBlocks
                (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀))
                (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁))
                ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀))
                ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁))) *
              twoBlockReindex (n := n)
                (Matrix.fromBlocks ((θ : ℂ) • X₀) 0 0 (((1 - θ : ℝ) : ℂ) • X₁)) =
            twoBlockReindex (n := n)
              (Matrix.fromBlocks
                ((gArg X₀ Y₀ : HSOp n) V₀₀)
                (((θ : ℂ)⁻¹ * ((1 - θ : ℝ) : ℂ)) • (posInv Y₀ * V₀₁ * X₁))
                ((((1 - θ : ℝ) : ℂ)⁻¹ * (θ : ℂ)) • (posInv Y₁ * V₁₀ * X₀))
                ((gArg X₁ Y₁ : HSOp n) V₁₁))
        rw [← map_mul]
        congr 1
        simp only [Matrix.fromBlocks_multiply, mul_zero, add_zero, zero_add,
          Matrix.fromBlocks_inj]
        constructor
        · calc
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₀)) * ((θ : ℂ) • X₀)
                = (posInv Y₀ * V₀₀) * X₀ := by
                    exact matrix_complex_inv_smul_mul_smul
                      (n := n) (z := (θ : ℂ)) hθC (posInv Y₀ * V₀₀) X₀
            _ = (gArg X₀ Y₀ : HSOp n) V₀₀ := by
                    rfl
        constructor
        · calc
            (((θ : ℂ)⁻¹) • (posInv Y₀ * V₀₁)) *
                ((((1 - θ : ℝ) : ℂ)) • X₁)
                =
              (((θ : ℂ)⁻¹) * (((1 - θ : ℝ) : ℂ))) •
                ((posInv Y₀ * V₀₁) * X₁) := by
                    exact matrix_complex_smul_mul_smul
                      (n := n) ((θ : ℂ)⁻¹) (((1 - θ : ℝ) : ℂ))
                      (posInv Y₀ * V₀₁) X₁
            _ =
              (((θ : ℂ)⁻¹) * (((1 - θ : ℝ) : ℂ))) •
                (posInv Y₀ * V₀₁ * X₁) := by
                    rw [Matrix.mul_assoc]
        constructor
        · calc
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₀)) *
                ((θ : ℂ) • X₀)
                =
              ((((1 - θ : ℝ) : ℂ)⁻¹) * (θ : ℂ)) •
                ((posInv Y₁ * V₁₀) * X₀) := by
                    exact matrix_complex_smul_mul_smul
                      (n := n) (((1 - θ : ℝ) : ℂ)⁻¹) (θ : ℂ)
                      (posInv Y₁ * V₁₀) X₀
            _ =
              ((((1 - θ : ℝ) : ℂ)⁻¹) * (θ : ℂ)) •
                (posInv Y₁ * V₁₀ * X₀) := by
                    rw [Matrix.mul_assoc]
        · calc
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (posInv Y₁ * V₁₁)) *
                ((((1 - θ : ℝ) : ℂ)) • X₁)
                = (posInv Y₁ * V₁₁) * X₁ := by
                    exact matrix_complex_inv_smul_mul_smul
                      (n := n) (z := (((1 - θ : ℝ) : ℂ))) h1θC
                      (posInv Y₁ * V₁₁) X₁
            _ = (gArg X₁ Y₁ : HSOp n) V₁₁ := by
                    rfl

/-! ### Diagonal block projection and compression -/
/-- The linear map that keeps only the diagonal blocks of a `2 × 2` block matrix. -/
noncomputable def twoBlockDiagonalPart {n : ℕ} :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ where
  toFun F := Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂
  map_add' := by
    intro F G
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
  map_smul' := by
    intro c F
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/--
The projection onto diagonal blocks in the fixed two-block decomposition.
It keeps the `00` and `11` blocks and kills the two off-diagonal blocks.
-/
noncomputable def twoBlockDiagonalProjection {n : ℕ} : HSOp (n + n) :=
  (((twoBlockReindex (n := n)).toLinearMap).comp
    ((twoBlockDiagonalPart (n := n)).comp
      ((twoBlockReindex (n := n)).symm.toLinearMap))).toContinuousLinearMap

/-- Applying the diagonal projection to a block matrix keeps only its diagonal blocks. -/
@[simp]
theorem twoBlockDiagonalProjection_apply_fromBlocks {n : ℕ}
    (V₀₀ V₀₁ V₁₀ V₁₁ : Mₙ n) :
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)) =
      twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ 0 0 V₁₁) := by
  change
    twoBlockReindex (n := n)
        ((twoBlockDiagonalPart (n := n))
          ((twoBlockReindex (n := n)).symm
            (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁)))) =
      twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ 0 0 V₁₁)
  simp [twoBlockDiagonalPart]

/-- Embed a pair of `n × n` matrices as the two diagonal blocks of a `2 × 2` block matrix. -/
noncomputable def twoBlockDiagonalEmbed {n : ℕ} :
    Mₙ n × Mₙ n →ₗ[ℂ] Mₙ (n + n) where
  toFun V := twoBlockReindex (n := n) (Matrix.fromBlocks V.1 0 0 V.2)
  map_add' := by
    intro V W
    change
      twoBlockReindex (n := n)
          (Matrix.fromBlocks (V.1 + W.1) 0 0 (V.2 + W.2)) =
        twoBlockReindex (n := n) (Matrix.fromBlocks V.1 0 0 V.2) +
          twoBlockReindex (n := n) (Matrix.fromBlocks W.1 0 0 W.2)
    rw [← map_add]
    congr 1
    simp [Matrix.fromBlocks_add]
  map_smul' := by
    intro c V
    change
      twoBlockReindex (n := n) (Matrix.fromBlocks (c • V.1) 0 0 (c • V.2)) =
        c • twoBlockReindex (n := n) (Matrix.fromBlocks V.1 0 0 V.2)
    rw [← map_smul]
    congr 1
    simp [Matrix.fromBlocks_smul]

/-- Read off the two diagonal blocks of a matrix in the fixed `2 × 2` block decomposition. -/
noncomputable def twoBlockDiagonalBlocks {n : ℕ} :
    Mₙ (n + n) →ₗ[ℂ] Mₙ n × Mₙ n where
  toFun V :=
    let F := (twoBlockReindex (n := n)).symm V
    (F.toBlocks₁₁, F.toBlocks₂₂)
  map_add' := by
    intro V W
    ext i j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
  map_smul' := by
    intro c V
    ext i j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

@[simp]
theorem twoBlockDiagonalBlocks_embed {n : ℕ} (V₀ V₁ : Mₙ n) :
    twoBlockDiagonalBlocks (n := n)
        (twoBlockDiagonalEmbed (n := n) (V₀, V₁)) =
      (V₀, V₁) := by
  ext i j <;> simp [twoBlockDiagonalBlocks, twoBlockDiagonalEmbed]

/--
The diagonal block embedding sends the Hilbert--Schmidt inner product to the
sum of the two diagonal Hilbert--Schmidt inner products.
-/
theorem twoBlockDiagonalEmbed_inner_eq {n : ℕ} (V W : Mₙ n × Mₙ n) :
    @inner ℂ (Mₙ (n + n)) inferInstance
      (twoBlockDiagonalEmbed (n := n) V)
      (twoBlockDiagonalEmbed (n := n) W) =
      @inner ℂ (Mₙ n) inferInstance V.1 W.1 +
        @inner ℂ (Mₙ n) inferInstance V.2 W.2 := by
  rcases V with ⟨V₀, V₁⟩
  rcases W with ⟨W₀, W₁⟩
  change
    Matrix.trace
        (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁) *
          Matrix.conjTranspose
            (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))) =
      Matrix.trace (W₀ * Matrix.conjTranspose V₀) +
        Matrix.trace (W₁ * Matrix.conjTranspose V₁)
  rw [trace_twoBlockReindex_mul_conjTranspose]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    trace_fromBlocks_diagonal]

/--
The same diagonal block embedding is inner-product preserving from the `L²`
Hilbert direct sum of the two Hilbert--Schmidt matrix spaces.
-/
theorem twoBlockDiagonalEmbed_withLp_inner_eq {n : ℕ}
    (V W : WithLp 2 (Mₙ n × Mₙ n)) :
    @inner ℂ (Mₙ (n + n)) inferInstance
      (twoBlockDiagonalEmbed (n := n) (WithLp.ofLp V))
      (twoBlockDiagonalEmbed (n := n) (WithLp.ofLp W)) =
      @inner ℂ (Mₙ n) inferInstance (WithLp.ofLp V).1 (WithLp.ofLp W).1 +
        @inner ℂ (Mₙ n) inferInstance (WithLp.ofLp V).2 (WithLp.ofLp W).2 := by
  rw [twoBlockDiagonalEmbed_inner_eq]

/-- Embedding the read-off diagonal blocks is the same as diagonal projection. -/
theorem twoBlockDiagonalEmbed_blocks_eq_projection {n : ℕ} (V : Mₙ (n + n)) :
    twoBlockDiagonalEmbed (n := n) (twoBlockDiagonalBlocks (n := n) V) =
      (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) V := by
  let F := (twoBlockReindex (n := n)).symm V
  have hV :
      V =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
    calc
      V = twoBlockReindex (n := n) ((twoBlockReindex (n := n)).symm V) := by
          simp
      _ =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
          simp [F, Matrix.fromBlocks_toBlocks]
  rw [hV]
  simp [twoBlockDiagonalEmbed, twoBlockDiagonalBlocks, F]

/-- If a matrix is fixed by diagonal projection, it is reconstructed from its blocks. -/
theorem twoBlockDiagonalEmbed_blocks_of_projection_eq_self {n : ℕ} {V : Mₙ (n + n)}
    (hV : (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) V = V) :
    twoBlockDiagonalEmbed (n := n) (twoBlockDiagonalBlocks (n := n) V) = V := by
  rw [twoBlockDiagonalEmbed_blocks_eq_projection, hV]

/--
If an operator acts on diagonal block vectors as the direct sum of two smaller
operators, then reading diagonal blocks transports its action to the product
action.
-/
theorem twoBlockDiagonalBlocks_apply_of_direct_sum_action {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n}
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁)))
    (V₀ V₁ : Mₙ n) :
    twoBlockDiagonalBlocks (n := n)
        (T (twoBlockDiagonalEmbed (n := n) (V₀, V₁))) =
      (T₀ V₀, T₁ V₁) := by
  change
    twoBlockDiagonalBlocks (n := n)
        (T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))) =
      (T₀ V₀, T₁ V₁)
  rw [hdiag V₀ V₁]
  simpa [twoBlockDiagonalEmbed] using
    (twoBlockDiagonalBlocks_embed (n := n) (T₀ V₀) (T₁ V₁))

/--
Compress an operator on the large two-block matrix space to the diagonal block
subspace, read through the product identification.
-/
noncomputable def twoBlockDiagonalCompression {n : ℕ} (S : HSOp (n + n)) :
    Mₙ n × Mₙ n →ₗ[ℂ] Mₙ n × Mₙ n :=
  (twoBlockDiagonalBlocks (n := n)).comp
    (S.toLinearMap.comp (twoBlockDiagonalEmbed (n := n)))

@[simp]
theorem twoBlockDiagonalCompression_apply {n : ℕ} (S : HSOp (n + n))
    (V : Mₙ n × Mₙ n) :
    twoBlockDiagonalCompression (n := n) S V =
      twoBlockDiagonalBlocks (n := n)
        (S (twoBlockDiagonalEmbed (n := n) V)) :=
  rfl

/--
If the large operator acts on diagonal blocks as the direct sum of two smaller
operators, then its diagonal compression is the product-space operator
`T₀.prodMap T₁`.
-/
theorem twoBlockDiagonalCompression_eq_prodMap_of_direct_sum_action {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n}
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) :
    twoBlockDiagonalCompression (n := n) T =
      T₀.toLinearMap.prodMap T₁.toLinearMap := by
  apply LinearMap.ext
  rintro ⟨V₀, V₁⟩
  exact twoBlockDiagonalBlocks_apply_of_direct_sum_action
    (n := n) (T := T) (T₀ := T₀) (T₁ := T₁) hdiag V₀ V₁

private theorem hsOp_real_algebraMap_apply {n : ℕ} (a : ℝ) (V : Mₙ n) :
    (algebraMap ℝ (HSOp n) a) V = (a : ℂ) • V := by
  rw [Algebra.algebraMap_eq_smul_one]
  change ((a : ℂ) • (1 : HSOp n)) V = (a : ℂ) • V
  rw [ContinuousLinearMap.smul_apply]
  simp

private theorem directSumAction_mul_embed {n : ℕ}
    {S T : HSOp (n + n)} {S₀ S₁ T₀ T₁ : HSOp n}
    (hS : ∀ V : Mₙ n × Mₙ n,
      S (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (S₀ V.1, S₁ V.2))
    (hT : ∀ V : Mₙ n × Mₙ n,
      T (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (T₀ V.1, T₁ V.2)) :
    ∀ V : Mₙ n × Mₙ n,
      (S * T) (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) ((S₀ * T₀) V.1, (S₁ * T₁) V.2) := by
  intro V
  simp only [ContinuousLinearMap.mul_apply]
  rw [hT V]
  rw [hS (T₀ V.1, T₁ V.2)]

private theorem directSumAction_pow_embed {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n}
    (hT : ∀ V : Mₙ n × Mₙ n,
      T (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (T₀ V.1, T₁ V.2)) :
    ∀ m : ℕ, ∀ V : Mₙ n × Mₙ n,
      (T ^ m) (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) ((T₀ ^ m) V.1, (T₁ ^ m) V.2) := by
  intro m
  induction m with
  | zero =>
      intro V
      simp
  | succ m ih =>
      intro V
      have hmul :=
        directSumAction_mul_embed (n := n)
          (S := T) (T := T ^ m) (S₀ := T₀) (S₁ := T₁)
          (T₀ := T₀ ^ m) (T₁ := T₁ ^ m) hT ih V
      simpa [pow_succ'] using hmul

private theorem directSumAction_aeval_embed {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n}
    (hT : ∀ V : Mₙ n × Mₙ n,
      T (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (T₀ V.1, T₁ V.2)) :
    ∀ q : Polynomial ℝ, ∀ V : Mₙ n × Mₙ n,
      (Polynomial.aeval T q) (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n)
          ((Polynomial.aeval T₀ q) V.1, (Polynomial.aeval T₁ q) V.2) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      intro V
      simp only [map_add, ContinuousLinearMap.add_apply]
      rw [hp V, hq V]
      simpa using
        ((twoBlockDiagonalEmbed (n := n)).map_add
          (((Polynomial.aeval T₀ p) V.1, (Polynomial.aeval T₁ p) V.2))
          (((Polynomial.aeval T₀ q) V.1, (Polynomial.aeval T₁ q) V.2))).symm
  | monomial m a =>
      intro V
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [ContinuousLinearMap.mul_apply]
      rw [directSumAction_pow_embed (n := n) (T := T) (T₀ := T₀) (T₁ := T₁) hT m V]
      rw [hsOp_real_algebraMap_apply (n := n + n) a]
      rw [hsOp_real_algebraMap_apply (n := n) a]
      rw [hsOp_real_algebraMap_apply (n := n) a]
      simpa using
        ((twoBlockDiagonalEmbed (n := n)).map_smul (a : ℂ)
          (((T₀ ^ m) V.1, (T₁ ^ m) V.2))).symm

private theorem hsOp_real_spectrum_finite {n : ℕ} (T : HSOp n) :
    Set.Finite (spectrum ℝ T) := by
  haveI : FiniteDimensional ℂ (HSOp n) := ContinuousLinearMap.finiteDimensional
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    exact spectrum_finite_of_finiteDimensional (K := ℂ) (A := HSOp n) T
  rw [← spectrum.preimage_algebraMap ℂ]
  exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem directSumAction_hsCfcR_embed {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n} (k : ℝ → ℝ)
    (hT : IsSelfAdjoint T) (hT₀ : IsSelfAdjoint T₀) (hT₁ : IsSelfAdjoint T₁)
    (hdiag : ∀ V : Mₙ n × Mₙ n,
      T (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (T₀ V.1, T₁ V.2)) :
    ∀ V : Mₙ n × Mₙ n,
      hsCfcR k T (twoBlockDiagonalEmbed (n := n) V) =
        twoBlockDiagonalEmbed (n := n) (hsCfcR k T₀ V.1, hsCfcR k T₁ V.2) := by
  classical
  let sSet : Set ℝ := (spectrum ℝ T ∪ spectrum ℝ T₀) ∪ spectrum ℝ T₁
  have hfin : Set.Finite sSet := by
    exact ((hsOp_real_spectrum_finite T).union
      (hsOp_real_spectrum_finite T₀)).union (hsOp_real_spectrum_finite T₁)
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
    exact hq_mem (by
      exact Set.mem_union_left (spectrum ℝ T₁)
        (Set.mem_union_left (spectrum ℝ T₀) hx))
  have hq_T₀ : (spectrum ℝ T₀).EqOn k q.eval := by
    intro x hx
    symm
    exact hq_mem (by
      exact Set.mem_union_left (spectrum ℝ T₁)
        (Set.mem_union_right (spectrum ℝ T) hx))
  have hq_T₁ : (spectrum ℝ T₁).EqOn k q.eval := by
    intro x hx
    symm
    exact hq_mem (by
      exact Set.mem_union_right (spectrum ℝ T ∪ spectrum ℝ T₀) hx)
  have hcfc_T : hsCfcR k T = hsCfcR q.eval T := by
    simpa [hsCfcR] using
      (cfc_congr (a := T) (f := k) (g := q.eval) hq_T)
  have hcfc_T₀ : hsCfcR k T₀ = hsCfcR q.eval T₀ := by
    simpa [hsCfcR] using
      (cfc_congr (a := T₀) (f := k) (g := q.eval) hq_T₀)
  have hcfc_T₁ : hsCfcR k T₁ = hsCfcR q.eval T₁ := by
    simpa [hsCfcR] using
      (cfc_congr (a := T₁) (f := k) (g := q.eval) hq_T₁)
  have hpoly_T : hsCfcR q.eval T = Polynomial.aeval T q := by
    simpa [hsCfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
  have hpoly_T₀ : hsCfcR q.eval T₀ = Polynomial.aeval T₀ q := by
    simpa [hsCfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T₀) hT₀)
  have hpoly_T₁ : hsCfcR q.eval T₁ = Polynomial.aeval T₁ q := by
    simpa [hsCfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T₁) hT₁)
  intro V
  calc
    hsCfcR k T (twoBlockDiagonalEmbed (n := n) V)
        = (Polynomial.aeval T q) (twoBlockDiagonalEmbed (n := n) V) := by
            rw [hcfc_T, hpoly_T]
    _ =
        twoBlockDiagonalEmbed (n := n)
          ((Polynomial.aeval T₀ q) V.1, (Polynomial.aeval T₁ q) V.2) := by
            exact directSumAction_aeval_embed (n := n)
              (T := T) (T₀ := T₀) (T₁ := T₁) hdiag q V
    _ =
        twoBlockDiagonalEmbed (n := n) (hsCfcR k T₀ V.1, hsCfcR k T₁ V.2) := by
            rw [← hpoly_T₀, ← hpoly_T₁, ← hcfc_T₀, ← hcfc_T₁]

/--
If a self-adjoint operator acts as a direct sum on diagonal blocks, then its
real functional calculus restricts to the functional calculi of the summands.
This is the direct-sum CFC transport used in Carlen's opmontI route
[carlen2022].
-/
theorem selfadjoint_cfc_restrict_of_direct_sum_action {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n} {V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hT : IsSelfAdjoint T) (hT₀ : IsSelfAdjoint T₀) (hT₁ : IsSelfAdjoint T₁)
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) :
    (((twoBlockReindex (n := n)).symm
      (hsCfcR k T
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
        hsCfcR k T₀ V₀) ∧
      (((twoBlockReindex (n := n)).symm
        (hsCfcR k T
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
        hsCfcR k T₁ V₁) := by
  have hdiag_embed :
      ∀ V : Mₙ n × Mₙ n,
        T (twoBlockDiagonalEmbed (n := n) V) =
          twoBlockDiagonalEmbed (n := n) (T₀ V.1, T₁ V.2) := by
    rintro ⟨W₀, W₁⟩
    simpa [twoBlockDiagonalEmbed] using hdiag W₀ W₁
  have happly :=
    directSumAction_hsCfcR_embed (n := n) (T := T) (T₀ := T₀) (T₁ := T₁)
      k hT hT₀ hT₁ hdiag_embed (V₀, V₁)
  have hblocks := congrArg (twoBlockDiagonalBlocks (n := n)) happly
  constructor
  · have hfst := congrArg Prod.fst hblocks
    simpa [twoBlockDiagonalBlocks, twoBlockDiagonalEmbed] using hfst
  · have hsnd := congrArg Prod.snd hblocks
    simpa [twoBlockDiagonalBlocks, twoBlockDiagonalEmbed] using hsnd

end

end Quantum.TraceInequality.Loewner.HiaiPetz
