/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.TraceFunctionMonotonicity.MatrixFunctionalCalculus.TracePowerBridge

/-!
# Provider-independent trace-power bridges

This module contains the functional-calculus identities identifying the
J-operator trace functionals with the Lieb and inverse trace-power functionals.
It deliberately contains no Hiai--Petz 6.2 implication or provider package.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

private lemma inv_powerFn_mul_inv_mul_inv_eq
    (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (powerFn p (α * β⁻¹))⁻¹ * β⁻¹ = powerFn (-p) α * powerFn (p - 1) β := by
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hαnonneg : 0 ≤ α := le_of_lt hα
  have hβinv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβnonneg
  have hmulpos : 0 < α * β⁻¹ := mul_pos hα (inv_pos.mpr hβ)
  have hβne : β ≠ 0 := hβ.ne'
  calc
    (powerFn p (α * β⁻¹))⁻¹ * β⁻¹
        = (α * β⁻¹) ^ (-p) * β⁻¹ := by
            rw [powerFn, Real.rpow_neg (le_of_lt hmulpos)]
    _ = (α ^ (-p) * (β⁻¹) ^ (-p)) * β⁻¹ := by
            rw [Real.mul_rpow hαnonneg hβinv_nonneg]
    _ = (α ^ (-p) * β ^ p) * β⁻¹ := by
            rw [Real.inv_rpow hβnonneg, ← Real.rpow_neg hβnonneg]
            simp
    _ = α ^ (-p) * (β ^ p * β⁻¹) := by ring
    _ = α ^ (-p) * β ^ (p - 1) := by
            rw [Real.rpow_sub hβ p 1, Real.rpow_one]
            field_simp [hβne]
    _ = powerFn (-p) α * powerFn (p - 1) β := by rfl

private theorem jArg_invPowerFn_mul_posInv_apply_eigenmatrix
    {n : ℕ} (p : ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i j : Fin n) :
    hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B)
        (Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
        B⁻¹ =
      matrixPower (-p) A *
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
        matrixPower (p - 1) B := by
  let E : Mₙ n :=
    Matrix.vecMulVec
      ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
      (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
  let α : ℝ := hA.isHermitian.eigenvalues i
  let β : ℝ := hB.isHermitian.eigenvalues j
  have hApos : A.PosDef := hA
  have hBpos : B.PosDef := hB
  have hαpos : 0 < α := hA.isHermitian.posDef_iff_eigenvalues_pos.mp hApos i
  have hβpos : 0 < β := hB.isHermitian.posDef_iff_eigenvalues_pos.mp hBpos j
  have hscalarℝ :
      (powerFn p (α * β⁻¹))⁻¹ * β⁻¹ = powerFn (-p) α * powerFn (p - 1) β :=
    inv_powerFn_mul_inv_mul_inv_eq p α β hαpos hβpos
  have hscalarℂ :
      ((powerFn p (α * β⁻¹))⁻¹ : ℂ) * ((β : ℂ)⁻¹) =
        (powerFn (-p) α : ℂ) * (powerFn (p - 1) β : ℂ) := by
    exact_mod_cast hscalarℝ
  calc
    hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B)
        (Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
        B⁻¹ =
      (((powerFn p (α * β⁻¹))⁻¹ : ℂ) • E) * B⁻¹ := by
        simpa [E, α, β] using
          congrArg (fun Y : Mₙ n => Y * B⁻¹)
            (jArg_cfcR_apply_eigenmatrix
              (f := fun x : ℝ => (powerFn p x)⁻¹) (A := A) (B := B) hA hB i j)
    _ =
      ((powerFn p (α * β⁻¹))⁻¹ : ℂ) • (E * B⁻¹) := by
        rw [smul_mul_assoc]
    _ =
      ((powerFn p (α * β⁻¹))⁻¹ : ℂ) • (((β : ℂ)⁻¹) • E) := by
        have hEInv : E * B⁻¹ = ((β : ℂ)⁻¹) • E := by
          change
            Matrix.vecMulVec
                ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
                (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) * B⁻¹ =
              ((β : ℂ)⁻¹) •
                Matrix.vecMulVec
                  ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
                  (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
          rw [Matrix.vecMulVec_mul, eigenrow_posInv (B := B) hB j, Matrix.vecMulVec_smul]
        rw [hEInv]
    _ =
      ((powerFn (-p) α : ℂ) * (powerFn (p - 1) β : ℂ)) • E := by
        rw [smul_smul, hscalarℂ]
    _ =
      (powerFn (-p) α : ℂ) • ((powerFn (p - 1) β : ℂ) • E) := by
        rw [smul_smul]
    _ =
      matrixPower (-p) A *
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
        matrixPower (p - 1) B := by
        rw [matrixPower_apply_eigenmatrix (r := -p) (s := p - 1) (A := A) (B := B) hA hB i j]

private theorem jArg_invPowerFn_mul_posInv_eq_matrixPower_mul
    {n : ℕ} (p : ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (X : Mₙ n) :
    hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B) X * B⁻¹ =
      matrixPower (-p) A * X * matrixPower (p - 1) B := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  let T : HSOp n :=
    (rightMul (B⁻¹)).comp (hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B))
  let S : HSOp n := (rightMul (matrixPower (p - 1) B)).comp (leftMul (matrixPower (-p) A))
  let c : Fin n → Fin n → ℂ := fun j i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr
      (WithLp.toLp 2 (X *ᵥ (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) i : ℂ)
  let E : Fin n → Fin n → Mₙ n := fun j i =>
    Matrix.vecMulVec
      ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
      (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
  have hXj : ∀ j : Fin n,
      Matrix.vecMulVec (X *ᵥ (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) =
        ∑ i : Fin n, c j i • E j i := by
    intro j
    simpa [c, E] using
      bridge_vecMulVec_left_eq_sum_eigenbasis (hA := hA.1)
        (X *ᵥ (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
        (star (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
  have hX : X = ∑ j : Fin n, ∑ i : Fin n, c j i • E j i := by
    rw [matrix_eq_sum_eigenmatrix_right (B := B) hB X]
    exact Finset.sum_congr rfl (fun j _ => hXj j)
  have hTS : ∀ j i : Fin n, T (E j i) = S (E j i) := by
    intro j i
    change
      hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B) (E j i) * B⁻¹ =
        matrixPower (-p) A * E j i * matrixPower (p - 1) B
    simpa [E] using
      jArg_invPowerFn_mul_posInv_apply_eigenmatrix (p := p) (A := A) (B := B) hA hB i j
  change T X = S X
  rw [hX]
  calc
    T (∑ j : Fin n, ∑ i : Fin n, c j i • E j i) =
      ∑ j : Fin n, T (∑ i : Fin n, c j i • E j i) := by
        simpa using
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            T Finset.univ (fun _ => (1 : ℂ))
            (fun j => ∑ i : Fin n, c j i • E j i))
    _ =
      ∑ j : Fin n, ∑ i : Fin n, c j i • T (E j i) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simpa using
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            T Finset.univ (c j) (E j))
    _ =
      ∑ j : Fin n, ∑ i : Fin n, c j i • S (E j i) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hTS j i]
    _ =
      ∑ j : Fin n, S (∑ i : Fin n, c j i • E j i) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        symm
        simpa using
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            S Finset.univ (c j) (E j))
    _ =
      S (∑ j : Fin n, ∑ i : Fin n, c j i • E j i) := by
        symm
        simpa using
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            S Finset.univ (fun _ => (1 : ℂ))
            (fun j => ∑ i : Fin n, c j i • E j i))

/-- Closed inverse trace-power bridge for positive-definite right input. -/
theorem jInversePowerTrace_eq_inverseTracePower_of_posDef
    {n : ℕ} (p : ℝ) {A B X : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    jInversePowerTrace p A B X = inverseTracePower p A B X := by
  have hop :=
    jArg_invPowerFn_mul_posInv_eq_matrixPower_mul (p := p) (A := A) (B := B) hA hB X
  rw [jInversePowerTrace, inverseTracePower, powerTrace]
  rw [Matrix.mul_assoc]
  rw [hop]
  simp [Matrix.mul_assoc]

end HiaiPetz
