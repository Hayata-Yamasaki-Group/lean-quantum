/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.SharedStageCompatibility
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBound
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.WeightedAction

/-!
# Quasi-entropy bridge for Hiai's Theorem 6.2 (route through Löwner's theorem)

This file contains the bridge declarations for the quasi-entropy part of Hiai's
Theorem 6.2 on the route through Löwner's theorem (H2).  The central result is that the
strict-output direct data-processing inequality implies joint concavity of the `J_f`
quasi-entropy.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace

noncomputable section

-- Keep the complex-to-real matrix algebra local to the block-sum scalar identities.
noncomputable local instance quasiEntropyBlockSumMatrixRealAlgebra {n : ℕ} :
    Algebra ℝ (Mₙ n) := Algebra.complexToReal

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance quasiEntropyDpiHSOpCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance quasiEntropyDpiHSOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance quasiEntropyDpiHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The block-sum map used in the quasi-entropy concavity argument.
Theorem 6.2 of [hiai2025]. -/
noncomputable def quasiEntropyBlockSumMap {n : ℕ} : HSMap (n + n) n :=
  hsAdjoint (blockDiagDuplicateMap (n := n))

/-- On block matrices, the quasi-entropy block-sum map adds the diagonal blocks.
Theorem 6.2 of [hiai2025]. -/
@[simp]
theorem quasiEntropyBlockSumMap_apply_fromBlocks {n : ℕ}
    (A B C D : Mₙ n) :
    quasiEntropyBlockSumMap
        (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D)) =
      A + D := by
  simpa [quasiEntropyBlockSumMap] using
    hsAdjoint_blockDiagDuplicateMap_fromBlocks (n := n) A B C D

/-- The Hilbert--Schmidt adjoint of the block-sum map is block duplication.
Theorem 6.2 of [hiai2025]. -/
theorem hsAdjoint_quasiEntropyBlockSumMap {n : ℕ} :
    hsAdjoint (quasiEntropyBlockSumMap (n := n)) = blockDiagDuplicateMap (n := n) := by
  ext X
  simp [quasiEntropyBlockSumMap, hsAdjoint]

/-- The block-sum map adds the two diagonal blocks.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_apply {n : ℕ} (X : Mₙ (n + n)) :
    quasiEntropyBlockSumMap (n := n) X =
      let F := (twoBlockReindex (n := n)).symm X
      F.toBlocks₁₁ + F.toBlocks₂₂ := by
  let F := (twoBlockReindex (n := n)).symm X
  have hX : X = twoBlockReindex (n := n) F := by
    simp [F]
  have hF :
      F = Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂ := by
    simp [Matrix.fromBlocks_toBlocks]
  calc
    quasiEntropyBlockSumMap (n := n) X =
        quasiEntropyBlockSumMap (n := n) (twoBlockReindex (n := n) F) := by
          rw [hX]
    _ =
        quasiEntropyBlockSumMap (n := n)
          (twoBlockReindex (n := n)
            (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂)) := by
          rw [← hF]
    _ = F.toBlocks₁₁ + F.toBlocks₂₂ := by
          simp

/-- The block-sum map is positive.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_positive {n : ℕ} :
    IsPositiveMap (quasiEntropyBlockSumMap (n := n)) := by
  intro X hX
  let F := (twoBlockReindex (n := n)).symm X
  have hFpsd : F.PosSemidef := by
    have hXpsd : X.PosSemidef := by
      simpa [Matrix.nonneg_iff_posSemidef] using hX
    have hre : (twoBlockReindex (n := n) F).PosSemidef := by
      simpa [F] using hXpsd
    exact (twoBlockReindex_posSemidef_iff (n := n) (A := F)).1 hre
  have h₁₁ : 0 ≤ F.toBlocks₁₁ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.toBlocks₁₁] using Matrix.PosSemidef.submatrix hFpsd Sum.inl
  have h₂₂ : 0 ≤ F.toBlocks₂₂ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [Matrix.toBlocks₂₂] using Matrix.PosSemidef.submatrix hFpsd Sum.inr
  rw [quasiEntropyBlockSumMap_apply]
  change 0 ≤ F.toBlocks₁₁ + F.toBlocks₂₂
  exact add_nonneg h₁₁ h₂₂

/-- The block-sum map preserves the matrix trace.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_tracePreserving {n : ℕ} :
    _root_.HiaiPetz.TracePreserving (quasiEntropyBlockSumMap (n := n)) := by
  intro X
  let F := (twoBlockReindex (n := n)).symm X
  have hX : X = twoBlockReindex (n := n) F := by
    simp [F]
  calc
    Matrix.trace (quasiEntropyBlockSumMap (n := n) X)
        = Matrix.trace (F.toBlocks₁₁ + F.toBlocks₂₂) := by
            rw [quasiEntropyBlockSumMap_apply]
    _ = Matrix.trace F := by
          rw [Matrix.trace_add]
          symm
          simp [Matrix.trace, Matrix.diag, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂,
            Fintype.sum_sum_type]
    _ = Matrix.trace X := by
          rw [hX, trace_twoBlockReindex]

/-- Duplicating a matrix preserves the product `X* X` on diagonal blocks. -/
theorem blockDiagDuplicateMap_conjTranspose_mul {n : ℕ} (X : Mₙ n) :
    Matrix.conjTranspose (blockDiagDuplicateMap (n := n) X) *
        blockDiagDuplicateMap (n := n) X =
      blockDiagDuplicateMap (n := n) (Matrix.conjTranspose X * X) := by
  change
    Matrix.conjTranspose (twoBlockReindex (n := n) (Matrix.fromBlocks X 0 0 X)) *
        twoBlockReindex (n := n) (Matrix.fromBlocks X 0 0 X) =
      twoBlockReindex (n := n) (Matrix.fromBlocks (Matrix.conjTranspose X * X) 0 0
        (Matrix.conjTranspose X * X))
  rw [conjTranspose_twoBlockReindex]
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- The block-sum map satisfies the Schwarz condition required by `ConditionIII_strict`.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_hsAdjointSchwarz {n : ℕ} :
    HSAdjointSchwarz (quasiEntropyBlockSumMap (n := n)) := by
  intro X
  change
    Matrix.conjTranspose (hsAdjoint (quasiEntropyBlockSumMap (n := n)) X) *
        hsAdjoint (quasiEntropyBlockSumMap (n := n)) X ≤
      hsAdjoint (quasiEntropyBlockSumMap (n := n)) (Matrix.conjTranspose X * X)
  rw [hsAdjoint_quasiEntropyBlockSumMap]
  rw [blockDiagDuplicateMap_conjTranspose_mul]

/-- The block-sum map sends the two-block identity to `2 • 1`.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_one {n : ℕ} :
    quasiEntropyBlockSumMap (n := n) (1 : Mₙ (n + n)) = (2 : ℂ) • (1 : Mₙ n) := by
  have hone :
      (1 : Mₙ (n + n)) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks (1 : Mₙ n) 0 0 (1 : Mₙ n)) := by
    simp [twoBlockReindex]
  rw [hone]
  rw [quasiEntropyBlockSumMap_apply_fromBlocks]
  ext i j
  by_cases hij : i = j
  · subst hij
    norm_num
  · simp [hij]

/-- The block-sum map sends the two-block identity to a positive-definite matrix.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropyBlockSumMap_one_posDef {n : ℕ} :
    MatrixPosDef (quasiEntropyBlockSumMap (n := n) (1 : Mₙ (n + n))) := by
  rw [quasiEntropyBlockSumMap_one]
  have hpos : (((2 : ℂ) • (1 : Mₙ n)) : Mₙ n).PosDef := by
    exact Matrix.PosDef.one.smul (by positivity)
  exact matrixPosDef_of_posDef hpos

/-- Inverting a positive real scalar multiple scales the inverse by `r⁻¹`. -/
theorem posInv_smul {n : ℕ} {B : Mₙ n} {r : ℝ} (hr : 0 < r) :
    posInv (r • B) = (r⁻¹) • posInv B := by
  by_cases hB : IsUnit B.det
  · letI : Invertible (r : ℂ) := invertibleOfNonzero (by exact_mod_cast hr.ne')
    change ((r : ℂ) • B)⁻¹ = (((r⁻¹ : ℝ) : ℂ) • B⁻¹)
    simpa [posInv] using Matrix.inv_smul (A := B) (k := (r : ℂ)) hB
  · have hsmul : ¬ IsUnit (Matrix.det (r • B)) := by
      have hdetB : Matrix.det B = 0 := by
        simpa [isUnit_iff_ne_zero] using hB
      have hdetSmul : Matrix.det (r • B) = 0 := by
        change Matrix.det (((r : ℂ)) • B) = 0
        rw [Matrix.det_smul B (r : ℂ), hdetB]
        simp
      simp [isUnit_iff_ne_zero, hdetSmul]
    rw [posInv, posInv, Matrix.nonsing_inv_apply_not_isUnit _ hsmul,
      Matrix.nonsing_inv_apply_not_isUnit _ hB]
    ext i j
    simp

/-- Left multiplication is homogeneous in its matrix parameter. -/
theorem leftMul_smul {n : ℕ} {A : Mₙ n} {r : ℝ} :
    leftMul (r • A) = (r : ℂ) • leftMul A := by
  ext X i j
  change (((r : ℂ) • A) * X) i j = ((r : ℂ) • (A * X)) i j
  rw [smul_mul_assoc]

/-- Right multiplication is homogeneous in its matrix parameter. -/
theorem rightMul_smul {n : ℕ} {B : Mₙ n} {r : ℝ} :
    rightMul (r • B) = (r : ℂ) • rightMul B := by
  ext X i j
  change ∑ x, X i x * (((r : ℂ) * B x j)) = (r : ℂ) * ∑ x, X i x * B x j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

/-- The positive argument `L_A R_{B^{-1}}` is homogeneous under common scaling. -/
theorem jArg_smul {n : ℕ} {A B : Mₙ n} {r : ℝ} (hr : 0 < r) :
    jArg (r • A) (r • B) = jArg A B := by
  change (rightMul (posInv (r • B))).comp (leftMul (r • A)) =
    (rightMul (posInv B)).comp (leftMul A)
  rw [posInv_smul hr, leftMul_smul, rightMul_smul]
  ext X
  have hmul : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
    have hmulR : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    exact_mod_cast hmulR
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  rw [map_smul]
  rw [smul_smul, hmul, one_smul]

/-- The perspective operator `J_f` is homogeneous under common scaling. -/
theorem jOperator_homogeneous {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n} {r : ℝ} :
    0 < r →
    jOperator f (r • A) (r • B) = r • jOperator f A B := by
  intro hr
  change hsCfcR f (jArg (r • A) (r • B)) * rightMul (r • B) =
    r • (hsCfcR f (jArg A B) * rightMul B)
  rw [jArg_smul hr, rightMul_smul]
  change
    hsCfcR f (jArg A B) * ((r : ℂ) • rightMul B) =
      (r : ℂ) • (hsCfcR f (jArg A B) * rightMul B)
  ext X i j
  change
    (hsCfcR f (jArg A B)) ((r : ℂ) • rightMul B X) i j =
      ((r : ℂ) • (hsCfcR f (jArg A B)) (rightMul B X)) i j
  rw [map_smul]

/-- The `J_f` quasi-entropy is homogeneous under common scaling of `A` and `B`. -/
theorem quasiEntropy_homogeneous {n : ℕ} {f : ℝ → ℝ} {A B X : Mₙ n} {r : ℝ} :
    0 < r →
    QuasiEntropyDPI.quasiEntropy f (r • A) (r • B) X =
      r * QuasiEntropyDPI.quasiEntropy f A B X := by
  intro hr
  change hsQF (jOperator f (r • A) (r • B)) X = r * hsQF (jOperator f A B) X
  rw [jOperator_homogeneous (f := f) (A := A) (B := B) hr]
  change
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (((r : ℂ) • jOperator f A B) X))) =
      r * Complex.re (Matrix.trace (Matrix.conjTranspose X * jOperator f A B X))
  rw [ContinuousLinearMap.smul_apply]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  change
    Complex.re (((r : ℂ) * (Matrix.conjTranspose X * jOperator f A B X).trace)) =
      r * Complex.re ((Matrix.conjTranspose X * jOperator f A B X).trace)
  rw [Complex.mul_re]
  simp

/--
Right multiplication by the inverse of a weighted block-diagonal positive
matrix on an unweighted block vector produces inverse weights on the two
blocks.
-/
theorem rightMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks {n : ℕ}
    {θ : ℝ} {Y₀ Y₁ V₀ V₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (rightMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (((θ : ℂ)⁻¹) • (V₀ * posInv Y₀)) 0 0
          ((((1 - θ : ℝ) : ℂ)⁻¹) • (V₁ * posInv Y₁))) := by
  let Y : Mₙ (n + n) := weightedBlockDiag θ Y₀ Y₁
  let Z : Mₙ (n + n) := twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)
  let W : Mₙ (n + n) :=
    twoBlockReindex (n := n)
      (Matrix.fromBlocks
        (((θ : ℂ)⁻¹) • (V₀ * posInv Y₀)) 0 0
        ((((1 - θ : ℝ) : ℂ)⁻¹) • (V₁ * posInv Y₁)))
  have hYdet : IsUnit Y.det := by
    exact (Matrix.isUnit_iff_isUnit_det Y).mp
      (matrixPosDef_isUnit
        (weightedBlockDiag_matrixPosDef
          (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1))
  have hY₀det : IsUnit Y₀.det :=
    (Matrix.isUnit_iff_isUnit_det Y₀).mp (matrixPosDef_isUnit hY₀)
  have hY₁det : IsUnit Y₁.det :=
    (Matrix.isUnit_iff_isUnit_det Y₁).mp (matrixPosDef_isUnit hY₁)
  have hWY : W * Y = Z := by
    change
      twoBlockReindex (n := n)
          (Matrix.fromBlocks
            (((θ : ℂ)⁻¹) • (V₀ * posInv Y₀)) 0 0
            ((((1 - θ : ℝ) : ℂ)⁻¹) • (V₁ * posInv Y₁))) *
          weightedBlockDiag θ Y₀ Y₁ =
        twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)
    rw [weightedBlockDiag, ← map_mul]
    congr 1
    simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add,
      Complex.ofReal_sub, Complex.ofReal_one, posInv, Matrix.fromBlocks_inj]
    constructor
    · have hθC : (θ : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt hθ0
      change ((θ : ℂ)⁻¹ • (V₀ * Y₀⁻¹)) * ((θ : ℂ) • Y₀) = V₀
      rw [matrix_complex_inv_smul_mul_smul hθC]
      simpa [Matrix.mul_assoc] using
        Matrix.nonsing_inv_mul_cancel_right Y₀ V₀ hY₀det
    · constructor
      · simp
      constructor
      · simp
      · have h1θC : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast ne_of_gt (sub_pos.mpr hθ1)
        have h1θC' : (1 : ℂ) - (θ : ℂ) ≠ 0 := by
          simpa using h1θC
        change
          (((1 : ℂ) - (θ : ℂ))⁻¹ • (V₁ * Y₁⁻¹)) *
              (((1 : ℂ) - (θ : ℂ)) • Y₁) = V₁
        rw [matrix_complex_inv_smul_mul_smul h1θC']
        simpa [Matrix.mul_assoc] using
          Matrix.nonsing_inv_mul_cancel_right Y₁ V₁ hY₁det
  calc
    (rightMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
        Z * Y⁻¹ := by
          change
            twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁) *
                posInv (weightedBlockDiag θ Y₀ Y₁) =
              Z * Y⁻¹
          simp [posInv, Y, Z]
    _ = (W * Y) * Y⁻¹ := by rw [hWY]
    _ = W := by
          simpa using Matrix.mul_nonsing_inv_cancel_right Y W hYdet

/--
The weighted two-block `jArg` restricts on diagonal-block inputs to the direct
sum of the two endpoint `jArg` operators.
-/
theorem weightedBlockDiag_jArg_apply_twoBlockReindex_fromBlocks {n : ℕ}
    {θ : ℝ} {A₁ A₂ B₁ B₂ V₁ V₂ : Mₙ n}
    (hB₁ : MatrixPosDef B₁) (hB₂ : MatrixPosDef B₂)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (jArg (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂) : HSOp (n + n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₁ 0 0 V₂)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks ((jArg A₁ B₁) V₁) 0 0 ((jArg A₂ B₂) V₂)) := by
  have hleft :
      (leftMul (weightedBlockDiag θ A₁ A₂) : HSOp (n + n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₁ 0 0 V₂)) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks ((θ : ℂ) • (A₁ * V₁)) 0 0
            (((1 - θ : ℝ) : ℂ) • (A₂ * V₂))) := by
    change
      weightedBlockDiag θ A₁ A₂ *
          twoBlockReindex (n := n) (Matrix.fromBlocks V₁ 0 0 V₂) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks ((θ : ℂ) • (A₁ * V₁)) 0 0
            (((1 - θ : ℝ) : ℂ) • (A₂ * V₂)))
    rw [weightedBlockDiag, ← map_mul]
    congr 1
    simp [Matrix.fromBlocks_multiply]
  change (rightMul (posInv (weightedBlockDiag θ B₁ B₂))).comp
    (leftMul (weightedBlockDiag θ A₁ A₂))
      (twoBlockReindex (Matrix.fromBlocks V₁ 0 0 V₂)) = _
  rw [ContinuousLinearMap.comp_apply, hleft]
  rw [rightMul_posInv_weightedBlockDiag_apply_twoBlockReindex_fromBlocks
    (n := n) (θ := θ) hB₁ hB₂ hθ0 hθ1]
  congr 1
  simp only [Matrix.fromBlocks_inj]
  constructor
  · have hθC : (θ : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hθ0
    rw [smul_mul_assoc]
    change
      (θ : ℂ)⁻¹ • ((θ : ℂ) • ((A₁ * V₁) * posInv B₁)) =
        (A₁ * V₁) * posInv B₁
    rw [smul_smul, inv_mul_cancel₀ hθC, one_smul]
  · constructor
    · simp
    constructor
    · simp
    · have h1θC : (1 : ℂ) - (θ : ℂ) ≠ 0 := by
        have h : (((1 - θ : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast ne_of_gt (sub_pos.mpr hθ1)
        simpa using h
      rw [smul_mul_assoc]
      change
        (((1 - θ : ℝ) : ℂ)⁻¹ •
            (((1 - θ : ℝ) : ℂ) • ((A₂ * V₂) * posInv B₂))) =
          (A₂ * V₂) * posInv B₂
      rw [smul_smul, inv_mul_cancel₀ (by simpa using h1θC), one_smul]

/--
If a self-adjoint operator on the two-block Hilbert--Schmidt space acts as a
direct sum on diagonal-block inputs, then its real CFC acts componentwise on
such inputs.
-/
theorem hsCfcR_apply_twoBlockReindex_fromBlocks_of_selfadjoint_direct_sum_action
    {n : ℕ} {T : HSOp (n + n)} {T₀ T₁ : HSOp n} (k : ℝ → ℝ)
    (hT : IsSelfAdjoint T) (hT₀ : IsSelfAdjoint T₀) (hT₁ : IsSelfAdjoint T₁)
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁)))
    (V₀ V₁ : Mₙ n) :
    hsCfcR k T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks (hsCfcR k T₀ V₀) 0 0 (hsCfcR k T₁ V₁)) := by
  let W : Mₙ (n + n) :=
    hsCfcR k T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))
  have hproj : (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) W = W := by
    simpa [W] using
      twoBlockDiagonalProjection_hsCfcR_of_selfadjoint_direct_sum_action_apply_fromBlocks
        (n := n) (T := T) (T₀ := T₀) (T₁ := T₁) k hT hdiag V₀ V₁
  have hblocks_pair :=
    selfadjoint_cfc_restrict_of_direct_sum_action
      (n := n) (T := T) (T₀ := T₀) (T₁ := T₁)
      (V₀ := V₀) (V₁ := V₁) k hT hT₀ hT₁ hdiag
  have hblocks :
      twoBlockDiagonalBlocks (n := n) W =
        (hsCfcR k T₀ V₀, hsCfcR k T₁ V₁) := by
    ext <;> simp [twoBlockDiagonalBlocks, W, hblocks_pair.1, hblocks_pair.2]
  calc
    hsCfcR k T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) = W := rfl
    _ = twoBlockDiagonalEmbed (n := n) (twoBlockDiagonalBlocks (n := n) W) := by
          exact (twoBlockDiagonalEmbed_blocks_of_projection_eq_self hproj).symm
    _ = twoBlockReindex (n := n)
        (Matrix.fromBlocks (hsCfcR k T₀ V₀) 0 0 (hsCfcR k T₁ V₁)) := by
          rw [hblocks]
          rfl

/-- The real CFC of the weighted-block `jArg` acts componentwise on diagonal blocks. -/
theorem hsCfcR_weightedBlockDiag_jArg_apply_fromBlocks {n : ℕ}
    {θ : ℝ} {A₁ A₂ B₁ B₂ V₁ V₂ : Mₙ n} (f : ℝ → ℝ)
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂)
    (hB₁ : MatrixPosDef B₁) (hB₂ : MatrixPosDef B₂)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    hsCfcR f (jArg (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₁ 0 0 V₂)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (hsCfcR f (jArg A₁ B₁) V₁) 0 0
          (hsCfcR f (jArg A₂ B₂) V₂)) := by
  have hA : MatrixPosDef (weightedBlockDiag θ A₁ A₂) :=
    weightedBlockDiag_matrixPosDef hA₁ hA₂ hθ0 hθ1
  have hB : MatrixPosDef (weightedBlockDiag θ B₁ B₂) :=
    weightedBlockDiag_matrixPosDef hB₁ hB₂ hθ0 hθ1
  exact
    hsCfcR_apply_twoBlockReindex_fromBlocks_of_selfadjoint_direct_sum_action
      (n := n)
      (T := jArg (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
      (T₀ := jArg A₁ B₁) (T₁ := jArg A₂ B₂)
      f
      (jArg_isSelfAdjoint_of_matrixPosDef hA hB)
      (jArg_isSelfAdjoint_of_matrixPosDef hA₁ hB₁)
      (jArg_isSelfAdjoint_of_matrixPosDef hA₂ hB₂)
      (fun W₀ W₁ =>
        weightedBlockDiag_jArg_apply_twoBlockReindex_fromBlocks
          (n := n) (θ := θ) (A₁ := A₁) (A₂ := A₂)
          (B₁ := B₁) (B₂ := B₂) (V₁ := W₀) (V₂ := W₁)
          hB₁ hB₂ hθ0 hθ1)
      V₁ V₂

/-- Right multiplication by a weighted block diagonal on a duplicated vector. -/
theorem rightMul_weightedBlockDiag_apply_blockDiagDuplicateMap {n : ℕ}
    {θ : ℝ} {B₁ B₂ X : Mₙ n} :
    (rightMul (weightedBlockDiag θ B₁ B₂) : HSOp (n + n))
        (blockDiagDuplicateMap (n := n) X) =
      weightedBlockDiag θ (X * B₁) (X * B₂) := by
  change
    blockDiagDuplicateMap (n := n) X * weightedBlockDiag θ B₁ B₂ =
      weightedBlockDiag θ (X * B₁) (X * B₂)
  rw [blockDiagDuplicateMap_apply, weightedBlockDiag, weightedBlockDiag, ← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

/--
Block-sum action of `J_f` on weighted two-block inputs.  This is the hard
block-CFC step, the counterpart of the private lemma
`blockSumMap_jOperator_twoBlockDiag_of_posDef` in
`Quantum/TraceInequality/HiaiPetz/QuasiEntropyDataProcessing/DirectToConcavity.lean`.

Theorem 6.2 of [hiai2025].
-/
theorem quasiEntropyBlockSumMap_jOperator_weightedBlockDiag_duplicate_of_posDef {n : ℕ}
    {f : ℝ → ℝ} (_hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂)
    (hB₁ : MatrixPosDef B₁) (hB₂ : MatrixPosDef B₂) :
    quasiEntropyBlockSumMap
        ((jOperator f (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
          (blockDiagDuplicateMap (n := n) X)) =
      jOperator f (θ • A₁) (θ • B₁) X +
        jOperator f ((1 - θ) • A₂) ((1 - θ) • B₂) X := by
  have h1θ0 : 0 < 1 - θ := sub_pos.mpr hθ1
  have hJ :
      (jOperator f (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
          (blockDiagDuplicateMap (n := n) X) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks
            ((hsCfcR f (jArg A₁ B₁)) ((θ : ℂ) • (X * B₁))) 0 0
            ((hsCfcR f (jArg A₂ B₂)) (((1 - θ : ℝ) : ℂ) • (X * B₂)))) := by
    rw [jOperator]
    change
      hsCfcR f (jArg (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
          ((rightMul (weightedBlockDiag θ B₁ B₂) : HSOp (n + n))
            (blockDiagDuplicateMap (n := n) X)) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks
            ((hsCfcR f (jArg A₁ B₁)) ((θ : ℂ) • (X * B₁))) 0 0
            ((hsCfcR f (jArg A₂ B₂)) (((1 - θ : ℝ) : ℂ) • (X * B₂))))
    rw [rightMul_weightedBlockDiag_apply_blockDiagDuplicateMap]
    simpa [weightedBlockDiag] using
      hsCfcR_weightedBlockDiag_jArg_apply_fromBlocks
        (n := n) (θ := θ) (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁) (B₂ := B₂)
        (V₁ := (θ : ℂ) • (X * B₁))
        (V₂ := (((1 - θ : ℝ) : ℂ) • (X * B₂))) f
        hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  rw [hJ]
  simp only [quasiEntropyBlockSumMap_apply_fromBlocks]
  rw [jOperator_homogeneous (f := f) (A := A₁) (B := B₁) hθ0,
    jOperator_homogeneous (f := f) (A := A₂) (B := B₂) h1θ0]
  simp only [Complex.ofReal_sub,
    Complex.ofReal_one, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  have hcoeff : (1 : ℂ) - (θ : ℂ) = ((1 - θ : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_sub, Complex.ofReal_one]
  rw [hcoeff]
  ext i j
  change
    (θ : ℂ) * (hsCfcR f (jArg A₁ B₁) (X * B₁)) i j +
        ((1 - θ : ℝ) : ℂ) *
          (hsCfcR f (jArg A₂ B₂) (X * B₂)) i j =
      (θ : ℂ) * (hsCfcR f (jArg A₁ B₁) (X * B₁)) i j +
        ((1 - θ : ℝ) : ℂ) *
          (hsCfcR f (jArg A₂ B₂) (X * B₂)) i j
  rfl

/--
Source-side quadratic-form decomposition for the block-sum proof of HP62
condition `(iii') → (iv)`.  This is the block-CFC bridge: applying
`J_f` to the weighted two-block input and then summing the two output blocks
gives the sum of the two scaled endpoint quasi-entropies.

Theorem 6.2 of [hiai2025].
-/
theorem weightedBlockDiag_direct_dpi_source_qform {n : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂)
    (hB₁ : MatrixPosDef B₁) (hB₂ : MatrixPosDef B₂) :
    hsQF
        ((quasiEntropyBlockSumMap (n := n)).comp
          ((jOperator f (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂)).comp
            (hsAdjoint (quasiEntropyBlockSumMap (n := n)))))
        X =
      QuasiEntropyDPI.quasiEntropy f (θ • A₁) (θ • B₁) X +
        QuasiEntropyDPI.quasiEntropy f ((1 - θ) • A₂) ((1 - θ) • B₂) X := by
  rw [hsAdjoint_quasiEntropyBlockSumMap]
  change
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            quasiEntropyBlockSumMap
              ((jOperator f (weightedBlockDiag θ A₁ A₂) (weightedBlockDiag θ B₁ B₂))
                (blockDiagDuplicateMap (n := n) X)))) =
      QuasiEntropyDPI.quasiEntropy f (θ • A₁) (θ • B₁) X +
        QuasiEntropyDPI.quasiEntropy f ((1 - θ) • A₂) ((1 - θ) • B₂) X
  rw [quasiEntropyBlockSumMap_jOperator_weightedBlockDiag_duplicate_of_posDef
    (n := n) (f := f) hf hθ0 hθ1 hA₁ hA₂ hB₁ hB₂]
  simp [_root_.HiaiPetz.quasiEntropy, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
