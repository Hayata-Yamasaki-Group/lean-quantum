/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridge

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

lemma clm_map_sum_smul
    {ι : Type*} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (s : Finset ι) (c : ι → ℂ) (x : ι → E) :
    T (Finset.sum s fun i => c i • x i) = Finset.sum s fun i => c i • T (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, map_add, map_smul]

private lemma bridge_vecMulVec_sum_smul_right
    {n : ℕ} (s : Finset (Fin n)) (c : Fin n → ℂ)
    (v : Fin n → Fin n → ℂ) (r : Fin n → ℂ) :
    Matrix.vecMulVec (Finset.sum s fun i => c i • v i) r =
      Finset.sum s fun i => c i • Matrix.vecMulVec (v i) r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]

lemma bridge_vecMulVec_left_eq_sum_eigenbasis
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (x r : Fin n → ℂ) :
    Matrix.vecMulVec x r =
      ∑ i : Fin n,
        (((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)) •
          Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) r := by
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  have hsum :=
    congrArg (fun v : EuclideanSpace ℂ (Fin n) => Matrix.vecMulVec v r)
      ((hA.isHermitian.eigenvectorBasis.toBasis).sum_repr (WithLp.toLp 2 x)).symm
  simpa [c, bridge_vecMulVec_sum_smul_right] using hsum

private theorem posInv_mulVec_eigenvectorBasis
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (j : Fin n) :
    (B⁻¹) *ᵥ ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) =
      ((hB.isHermitian.eigenvalues j : ℂ)⁻¹) •
        (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ) := by
  let hBh := hB.isHermitian
  let v : Fin n → ℂ := hBh.eigenvectorBasis j
  let β : ℂ := hBh.eigenvalues j
  have hBpos : B.PosDef := hB
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBpos.isUnit
  have hβpos : 0 < hBh.eigenvalues j :=
    hBh.posDef_iff_eigenvalues_pos.mp hBpos j
  have hβne : β ≠ 0 := by
    change ((hBh.eigenvalues j : ℂ) ≠ 0)
    exact_mod_cast hβpos.ne'
  have hmul : B *ᵥ v = β • v := by
    simpa [v, β] using hBh.mulVec_eigenvectorBasis j
  have hpre : B *ᵥ (β⁻¹ • v) = v := by
    rw [Matrix.mulVec_smul, hmul, smul_smul]
    simp [hβne]
  calc
    (B⁻¹) *ᵥ ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
        = B⁻¹ *ᵥ v := by rfl
    _ = B⁻¹ *ᵥ (B *ᵥ (β⁻¹ • v)) := by rw [hpre]
    _ = (B⁻¹ * B) *ᵥ (β⁻¹ • v) := by rw [Matrix.mulVec_mulVec]
    _ = β⁻¹ • v := by rw [Matrix.nonsing_inv_mul B hdet, Matrix.one_mulVec]
    _ = ((hB.isHermitian.eigenvalues j : ℂ)⁻¹) •
        (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ) := by rfl

theorem eigenrow_posInv
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (j : Fin n) :
    star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) ᵥ* B⁻¹ =
      ((hB.isHermitian.eigenvalues j : ℂ)⁻¹) •
        star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  have hinv := posInv_mulVec_eigenvectorBasis (B := B) hB j
  have hstar := congrArg star hinv
  rw [Matrix.star_mulVec] at hstar
  have hhinv : (B⁻¹)ᴴ = B⁻¹ := by
    simpa using hB.isHermitian.inv.eq
  rw [hhinv] at hstar
  simpa using hstar

private theorem rightMul_posInv_apply_eigenmatrix
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (u : Fin n → ℂ) (j : Fin n) :
    rightMul (B⁻¹)
      (Matrix.vecMulVec u (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) =
      ((hB.isHermitian.eigenvalues j : ℂ)⁻¹) •
        Matrix.vecMulVec u (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) := by
  rw [rightMul_apply, Matrix.vecMulVec_mul, eigenrow_posInv (B := B) hB j,
    Matrix.vecMulVec_smul]

private theorem jArg_eigenmatrix_mem_eigenspace
    {n : ℕ} {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i j : Fin n) :
    Matrix.vecMulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) ∈
      Module.End.eigenspace (jArg A B).toLinearMap
        ((hA.isHermitian.eigenvalues i *
          (hB.isHermitian.eigenvalues j)⁻¹ : ℝ) : ℂ) := by
  rw [Module.End.mem_eigenspace_iff]
  change
    rightMul (B⁻¹)
      (leftMul A
        (Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))))) =
      ((hA.isHermitian.eigenvalues i *
        (hB.isHermitian.eigenvalues j)⁻¹ : ℝ) : ℂ) •
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
  rw [leftMul_apply, Matrix.mul_vecMulVec]
  have hAmul := hA.isHermitian.mulVec_eigenvectorBasis i
  rw [hAmul, Matrix.smul_vecMulVec]
  change
    rightMul (B⁻¹)
      ((hA.isHermitian.eigenvalues i : ℂ) •
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) =
      ((hA.isHermitian.eigenvalues i *
        (hB.isHermitian.eigenvalues j)⁻¹ : ℝ) : ℂ) •
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
  rw [ContinuousLinearMap.map_smul]
  rw [rightMul_posInv_apply_eigenmatrix (B := B) hB]
  simp [smul_smul]

theorem jArg_cfcR_apply_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i j : Fin n) :
    hsCfcR f (jArg A B)
      (Matrix.vecMulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) =
      (f (hA.isHermitian.eigenvalues i *
          (hB.isHermitian.eigenvalues j)⁻¹) : ℂ) •
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) := by
  simpa [hsCfcR] using
    (@HiaiPetz.cfcR_apply_of_mem_eigenspace_real_transport (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Matrix.finiteDimensional)
      (IsSelfAdjoint.instContinuousFunctionalCalculus :
        ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint)
      f (jArg A B) (jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB)
      (hA.isHermitian.eigenvalues i *
        (hB.isHermitian.eigenvalues j)⁻¹)
      (Matrix.vecMulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))))
      (jArg_eigenmatrix_mem_eigenspace (A := A) (B := B) hA hB i j))

/-- Left multiplication of `matrixCfcR f B` by the conjugated eigenvector row
scales it by `f` of the eigenvalue. -/
theorem eigenrow_matrixCfcR
    {n : ℕ} (f : ℝ → ℝ) {B : Mₙ n} (hB : IsSelfAdjoint B) (j : Fin n) :
    star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) ᵥ*
        HansenPedersen.matrixCfcR f B =
      (f (hB.isHermitian.eigenvalues j) : ℂ) •
        star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  have hmul :=
    HiaiPetz.matrixCfcR_mulVec_eigenvectorBasis_transport (f := f) (A := B) hB j
  have hstar := congrArg star hmul
  rw [Matrix.star_mulVec] at hstar
  have hself : (HansenPedersen.matrixCfcR f B)ᴴ = HansenPedersen.matrixCfcR f B := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using matrixCfcR_isSelfAdjoint (f := f) hB
  rw [hself] at hstar
  simpa using hstar

/-- Applying `matrixPower r A` to the eigen-dyad
`vecMulVec (A-basis i) (B-basis j)` multiplies it by the `r`-th power of the eigenvalue. -/
theorem matrixPower_apply_eigenmatrix
    {n : ℕ} (r s : ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i j : Fin n) :
    matrixPower r A *
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
        matrixPower s B =
      (powerFn r (hA.isHermitian.eigenvalues i) : ℂ) •
        ((powerFn s (hB.isHermitian.eigenvalues j) : ℂ) •
          Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) := by
  calc
    matrixPower r A *
          Matrix.vecMulVec
            ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
          matrixPower s B =
        ((powerFn r (hA.isHermitian.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
          matrixPower s B := by
            rw [matrixPower, Matrix.mul_vecMulVec,
              HiaiPetz.matrixCfcR_mulVec_eigenvectorBasis_transport
                (f := powerFn r) (A := A) hA.1,
              Matrix.smul_vecMulVec]
    _ =
        (powerFn r (hA.isHermitian.eigenvalues i) : ℂ) •
          (Matrix.vecMulVec
            ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
          matrixPower s B) := by
            rw [smul_mul_assoc]
    _ =
        (powerFn r (hA.isHermitian.eigenvalues i) : ℂ) •
          ((powerFn s (hB.isHermitian.eigenvalues j) : ℂ) •
            Matrix.vecMulVec
              ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
              (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) := by
            rw [matrixPower, Matrix.vecMulVec_mul,
              eigenrow_matrixCfcR (f := powerFn s) (B := B) hB.1]
            rw [Matrix.vecMulVec_smul]

lemma matrix_eq_sum_eigenmatrix_right
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (X : Mₙ n) :
    X =
      ∑ j : Fin n,
        Matrix.vecMulVec (X *ᵥ (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  let U : Mₙ n := hB.isHermitian.eigenvectorUnitary
  have hU : U * star U = (1 : Mₙ n) := by
    simp [U]
  calc
    X = X * (1 : Mₙ n) := by rw [Matrix.mul_one]
    _ = X * (U * star U) := by rw [hU]
    _ = (X * U) * star U := by rw [Matrix.mul_assoc]
    _ =
      ∑ j : Fin n,
        Matrix.vecMulVec (X *ᵥ (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
        ext a b
        rw [Matrix.sum_apply]
        simp [U, Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
          Matrix.IsHermitian.eigenvectorUnitary_apply]

private theorem eigenrow_self
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (j : Fin n) :
    star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) ᵥ* B =
      (hB.isHermitian.eigenvalues j : ℂ) •
        star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  have hmul := hB.isHermitian.mulVec_eigenvectorBasis j
  have hstar := congrArg star hmul
  rw [Matrix.star_mulVec] at hstar
  rw [hB.isHermitian.eq] at hstar
  simpa using hstar

private lemma powerFn_mul_inv_mul_self_eq
    (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    powerFn p (α * β⁻¹) * β = powerFn p α * powerFn (1 - p) β := by
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hαnonneg : 0 ≤ α := le_of_lt hα
  have hβne : β ≠ 0 := hβ.ne'
  calc
    powerFn p (α * β⁻¹) * β
        = (α ^ p * (β⁻¹) ^ p) * β := by
            rw [powerFn, Real.mul_rpow hαnonneg (inv_nonneg.mpr hβnonneg)]
    _ = (α ^ p * β ^ (-p)) * β := by
            rw [Real.rpow_neg_eq_inv_rpow]
    _ = α ^ p * (β ^ (-p) * β) := by ring
    _ = α ^ p * β ^ (1 - p) := by
            rw [Real.rpow_sub hβ 1 p, Real.rpow_one]
            rw [Real.rpow_neg hβnonneg]
            field_simp [hβne]
    _ = powerFn p α * powerFn (1 - p) β := by rfl

private theorem jArg_powerFn_mul_right_apply_eigenmatrix
    {n : ℕ} (p : ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i j : Fin n) :
    hsCfcR (powerFn p) (jArg A B)
        (Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
        B =
      matrixPower p A *
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
        matrixPower (1 - p) B := by
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
      powerFn p (α * β⁻¹) * β = powerFn p α * powerFn (1 - p) β :=
    powerFn_mul_inv_mul_self_eq p α β hαpos hβpos
  have hscalarℂ :
      (powerFn p (α * β⁻¹) : ℂ) * (β : ℂ) =
        (powerFn p α : ℂ) * (powerFn (1 - p) β : ℂ) := by
    exact_mod_cast hscalarℝ
  calc
    hsCfcR (powerFn p) (jArg A B)
        (Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
        B =
      ((powerFn p (α * β⁻¹) : ℂ) • E) * B := by
        rw [jArg_cfcR_apply_eigenmatrix (f := powerFn p) (A := A) (B := B) hA hB i j]
    _ =
      (powerFn p (α * β⁻¹) : ℂ) • (E * B) := by
        rw [smul_mul_assoc]
    _ =
      (powerFn p (α * β⁻¹) : ℂ) • ((β : ℂ) • E) := by
        have hEB : E * B = (β : ℂ) • E := by
          change
            Matrix.vecMulVec
                ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
                (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) * B =
              (β : ℂ) •
                Matrix.vecMulVec
                  ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
                  (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
          rw [Matrix.vecMulVec_mul, eigenrow_self (B := B) hB j, Matrix.vecMulVec_smul]
        rw [hEB]
    _ =
      ((powerFn p α : ℂ) * (powerFn (1 - p) β : ℂ)) • E := by
        rw [smul_smul, hscalarℂ]
    _ =
      (powerFn p α : ℂ) • ((powerFn (1 - p) β : ℂ) • E) := by
        rw [smul_smul]
    _ =
      matrixPower p A *
        Matrix.vecMulVec
          ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
          (star ((hB.isHermitian.eigenvectorBasis j : Fin n → ℂ))) *
        matrixPower (1 - p) B := by
        rw [matrixPower_apply_eigenmatrix (r := p) (s := 1 - p) (A := A) (B := B) hA hB i j]

private theorem jArg_powerFn_mul_right_eq_matrixPower_mul
    {n : ℕ} (p : ℝ) {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (X : Mₙ n) :
    hsCfcR (powerFn p) (jArg A B) X * B =
      matrixPower p A * X * matrixPower (1 - p) B := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  let T : HSOp n := (rightMul B).comp (hsCfcR (powerFn p) (jArg A B))
  let S : HSOp n := (rightMul (matrixPower (1 - p) B)).comp (leftMul (matrixPower p A))
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
      hsCfcR (powerFn p) (jArg A B) (E j i) * B =
        matrixPower p A * E j i * matrixPower (1 - p) B
    simpa [E] using jArg_powerFn_mul_right_apply_eigenmatrix (p := p) (A := A) (B := B) hA hB i j
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

/-- Closed direct trace-power bridge for positive-definite right input. -/
theorem jPowerTrace_eq_liebTracePower_of_posDef
    {n : ℕ} (p : ℝ) {A B X : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    jPowerTrace p A B X = liebTracePower p A B X := by
  have hop :=
    jArg_powerFn_mul_right_eq_matrixPower_mul (p := p) (A := A) (B := B) hA hB X
  rw [jPowerTrace, liebTracePower, powerTrace]
  rw [Matrix.mul_assoc]
  rw [hop]
  simp [Matrix.mul_assoc]

end HiaiPetz
