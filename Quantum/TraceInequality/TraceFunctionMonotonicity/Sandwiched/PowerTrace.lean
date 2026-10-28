/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace

/-!
# Power trace expressions

Matrix powers and trace expressions used in the Hiai--Petz power-specialized
quasi-entropy arguments.  The file provides both the ordinary real-functional-
calculus powers and the book-facing support convention at zero eigenvalues,
then relates them to spectral sums, support projections, `J`-quadratic forms,
and semidefinite regularization limits.

## Main results

* `supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg`: the
  support-convention power is real CFC with the support coefficient on
  nonnegative matrices.
* `supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo`: on the open
  parameter interval, support and ordinary trace powers agree for semidefinite
  inputs.
* `matrixPower_tendsto_of_tendsto_nonneg`: nonnegative matrix powers are
  continuous along filters for nonnegative exponents.

## References

* Hiai, Theorem 6.3.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/-- Scalar power coefficient with the book's support convention at the zero eigenvalue. -/
noncomputable def supportPowerCoeff (p x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ p

/-- Support-convention matrix power on positive semidefinite matrices.

The non-positive fallback is only present to keep the API total; theorem statements should use this
definition together with a semidefinite or positive-definite hypothesis. -/
private noncomputable def supportMatrixPowerCore {n : ℕ} (p : ℝ) {A : Mₙ n} (hA : 0 ≤ A) :
    Mₙ n :=
  ∑ i : Fin n,
    (supportPowerCoeff p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i) : ℂ) •
      Matrix.vecMulVec
        ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ)
        (star ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ))

/-- Matrix power with the book's support convention.

On positive semidefinite matrices this is the finite-dimensional spectral definition with the
zero-eigenvalue support convention.  On other inputs it falls back to the raw `matrixPower` only
to keep the definition total.  Mathematical statements should use this through hypotheses such as
`0 ≤ A` or `Matrix.PosDef A`, or use `supportMatrixPowerOfNonneg` directly. -/
noncomputable def supportMatrixPower {n : ℕ} (p : ℝ) (A : Mₙ n) : Mₙ n :=
  by
    classical
    exact if hA : 0 ≤ A then supportMatrixPowerCore p hA else matrixPower p A

/-- Support-convention matrix power for an explicitly positive semidefinite matrix. -/
noncomputable def supportMatrixPowerOfNonneg {n : ℕ} (p : ℝ) {A : Mₙ n} (hA : 0 ≤ A) :
    Mₙ n :=
  supportMatrixPowerCore p hA

/-- The public support-power API agrees with the explicit nonnegative version
whenever `A` is Loewner-nonnegative. -/
theorem supportMatrixPower_eq_of_nonneg {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPower p A = supportMatrixPowerOfNonneg p hA := by
  simp [supportMatrixPower, supportMatrixPowerOfNonneg, hA]

/-- Trace expression `Tr X^* A^r X B^s`, read through support-convention powers.

As with `supportMatrixPower`, the intended mathematical use is on positive semidefinite inputs;
the total fallback exists only to keep the expression available as a Lean function. -/
noncomputable def supportPowerTrace (r s : ℝ) (A B X : Mₙ n) : ℝ :=
  Complex.re
    (Matrix.trace
      (Matrix.conjTranspose X * supportMatrixPower r A * X * supportMatrixPower s B))

/-- Trace expression `Tr X^* A^r X B^s` with explicit semidefinite hypotheses. -/
noncomputable def supportPowerTraceOfNonneg {n : ℕ} (r s : ℝ) {A B : Mₙ n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (X : Mₙ n) : ℝ :=
  Complex.re
    (Matrix.trace
      (Matrix.conjTranspose X * supportMatrixPowerOfNonneg r hA * X *
        supportMatrixPowerOfNonneg s hB))

/-- The expression `Tr X^* A^p X B^(1-p)` with support-convention powers.

This is the book-facing total function.  Theorems should carry semidefinite or positive-definite
hypotheses so that the fallback branch of `supportMatrixPower` is never used mathematically. -/
noncomputable def supportLiebTracePower (p : ℝ) (A B X : Mₙ n) : ℝ :=
  supportPowerTrace p (1 - p) A B X

/-- The expression `Tr X^* A^p X B^(1-p)` with explicit semidefinite hypotheses. -/
noncomputable def supportLiebTracePowerOfNonneg {n : ℕ} (p : ℝ) {A B : Mₙ n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (X : Mₙ n) : ℝ :=
  supportPowerTraceOfNonneg p (1 - p) hA hB X

/-- The expression `Tr X^* A^(-p) X B^(p-1)` appearing in Theorem 6.3(2). -/
noncomputable def inverseTracePower (p : ℝ) (A B X : Mₙ n) : ℝ :=
  powerTrace (-p) (p - 1) A B X

/-- Spectral expansion of `supportMatrixPower` on a nonnegative matrix, using
the support convention for the zero eigenvalue. -/
theorem supportMatrixPower_eq_sum_eigenmatrix_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPower p A =
      ∑ i : Fin n,
        (supportPowerCoeff p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ)) := by
  simp [supportMatrixPower, supportMatrixPowerCore, hA]

/-- Spectral expansion of the explicit nonnegative support-power definition. -/
theorem supportMatrixPowerOfNonneg_eq_sum_eigenmatrix {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPowerOfNonneg p hA =
      ∑ i : Fin n,
        (supportPowerCoeff p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvectorBasis i : Fin n → ℂ)) := by
  rfl

private lemma matrixPolynomialAeval_mulVec_eigenvectorBasis_support
    {n : ℕ} (q : Polynomial ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i : Fin n) :
    (Polynomial.aeval A (Polynomial.map (algebraMap ℝ ℂ) q)).mulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) =
      (((Polynomial.eval (hA.isHermitian.eigenvalues i : ℝ) q : ℝ) : ℂ) •
        (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
  let φ :
      Mₙ n ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hx :
      (hA.isHermitian.eigenvectorBasis i : EuclideanSpace ℂ (Fin n)) ∈
        Module.End.eigenspace
          (φ A).toLinearMap
          (hA.isHermitian.eigenvalues i : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    ext k
    simpa [φ] using congrArg (fun v : Fin n → ℂ => v k)
      (hA.isHermitian.mulVec_eigenvectorBasis i)
  have hcalc :
      Polynomial.aeval (φ A) (Polynomial.map (algebraMap ℝ ℂ) q)
          (hA.isHermitian.eigenvectorBasis i) =
        (Polynomial.eval (hA.isHermitian.eigenvalues i : ℂ)
            (Polynomial.map (algebraMap ℝ ℂ) q)) •
          (hA.isHermitian.eigenvectorBasis i : EuclideanSpace ℂ (Fin n)) :=
    aeval_apply_of_mem_eigenspace_realpoly_transport
      (T := φ A) (r := hA.isHermitian.eigenvalues i) (x := hA.isHermitian.eigenvectorBasis i)
      hx q
  have hmapPoly :
      φ (Polynomial.aeval A (Polynomial.map (algebraMap ℝ ℂ) q)) =
        Polynomial.aeval (φ A) (Polynomial.map (algebraMap ℝ ℂ) q) := by
    simpa [φ] using
      (Polynomial.aeval_algHom_apply φ A (Polynomial.map (algebraMap ℝ ℂ) q)).symm
  ext k
  calc
    ((Polynomial.aeval A (Polynomial.map (algebraMap ℝ ℂ) q)).mulVec
        (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) k
        = (Polynomial.aeval (φ A) (Polynomial.map (algebraMap ℝ ℂ) q)
            (hA.isHermitian.eigenvectorBasis i)) k := by
          simpa [φ] using congrArg
            (fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
              T (hA.isHermitian.eigenvectorBasis i) k) hmapPoly
    _ = ((Polynomial.eval (hA.isHermitian.eigenvalues i : ℂ)
            (Polynomial.map (algebraMap ℝ ℂ) q) •
          (hA.isHermitian.eigenvectorBasis i : EuclideanSpace ℂ (Fin n))) k) :=
          congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k) hcalc
    _ = (((Polynomial.eval (hA.isHermitian.eigenvalues i : ℝ) q : ℝ) : ℂ) •
          (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) k := by
          have heval :
              Polynomial.eval (hA.isHermitian.eigenvalues i : ℂ)
                  (Polynomial.map (algebraMap ℝ ℂ) q) =
                ((Polynomial.eval (hA.isHermitian.eigenvalues i : ℝ) q : ℝ) : ℂ) := by
            calc
              Polynomial.eval (hA.isHermitian.eigenvalues i : ℂ)
                  (Polynomial.map (algebraMap ℝ ℂ) q) =
                  Polynomial.aeval (R := ℝ) (A := ℂ)
                    (hA.isHermitian.eigenvalues i : ℂ) q := by
                    rw [Polynomial.eval_map_algebraMap]
              _ = ((Polynomial.eval (hA.isHermitian.eigenvalues i : ℝ) q : ℝ) : ℂ) := by
                    simpa using
                      (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ)
                        (x := hA.isHermitian.eigenvalues i) (p := q))
          rw [heval]
          rfl

private lemma matrix_eq_sum_eigenmatrix_right_selfAdjoint_support
    {n : ℕ} {C : Mₙ n} (hC : IsSelfAdjoint C) (X : Mₙ n) :
    X =
      ∑ j : Fin n,
        Matrix.vecMulVec (Matrix.mulVec X (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  let U : Mₙ n := hC.isHermitian.eigenvectorUnitary
  have hU : U * star U = (1 : Mₙ n) := by
    simp [U]
  calc
    X = X * (1 : Mₙ n) := by rw [Matrix.mul_one]
    _ = X * (U * star U) := by rw [hU]
    _ = (X * U) * star U := by rw [Matrix.mul_assoc]
    _ =
      ∑ j : Fin n,
        Matrix.vecMulVec (Matrix.mulVec X (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
        ext a b
        rw [Matrix.sum_apply]
        simp [U, Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
          Matrix.IsHermitian.eigenvectorUnitary_apply]

private lemma matrixPower_eq_sum_eigenmatrix_nonneg_support {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (p : ℝ) :
    matrixPower p C =
      ∑ i : Fin n,
        (powerFn p ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    matrixPower p C =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (matrixPower p C) (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint_support hsa (matrixPower p C)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixPower, matrixCfcR_mulVec_eigenvectorBasis_transport
          (f := powerFn p) (A := C) hsa i, Matrix.smul_vecMulVec]

/-- Polynomial functional calculus on a nonnegative matrix expands over the
eigenbasis with coefficients given by evaluating the real polynomial on the
real eigenvalues. -/
theorem matrixPolynomialAeval_eq_sum_eigenmatrix_nonneg {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (q : Polynomial ℝ) :
    Polynomial.aeval C (Polynomial.map (algebraMap ℝ ℂ) q) =
      ∑ i : Fin n,
        ((Polynomial.eval ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i : ℝ) q : ℝ) :
          ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    Polynomial.aeval C (Polynomial.map (algebraMap ℝ ℂ) q) =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (Polynomial.aeval C (Polynomial.map (algebraMap ℝ ℂ) q))
              (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint_support hsa
            (Polynomial.aeval C (Polynomial.map (algebraMap ℝ ℂ) q))
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixPolynomialAeval_mulVec_eigenvectorBasis_support
          (q := q) (A := C) hsa i, Matrix.smul_vecMulVec]

private lemma matrixCfcR_eq_sum_eigenmatrix_nonneg_support {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (f : ℝ → ℝ) :
    HansenPedersen.matrixCfcR f C =
      ∑ i : Fin n,
        (f ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    HansenPedersen.matrixCfcR f C =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (HansenPedersen.matrixCfcR f C)
              (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint_support hsa
            (HansenPedersen.matrixCfcR f C)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixCfcR_mulVec_eigenvectorBasis_transport
          (f := f) (A := C) hsa i, Matrix.smul_vecMulVec]

/-- For nonnegative matrices, the support-convention power is the real
functional calculus for `supportPowerCoeff p`. -/
theorem supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPower p A =
      HansenPedersen.matrixCfcR (supportPowerCoeff p) A := by
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA,
    matrixCfcR_eq_sum_eigenmatrix_nonneg_support hA (supportPowerCoeff p)]

/-- Explicit nonnegative support powers also coincide with real CFC for
`supportPowerCoeff p`. -/
theorem supportMatrixPowerOfNonneg_eq_matrixCfcR_supportPowerCoeff
    {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPowerOfNonneg p hA =
      HansenPedersen.matrixCfcR (supportPowerCoeff p) A := by
  rw [← supportMatrixPower_eq_of_nonneg hA,
    supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg hA]

/-- If a real polynomial agrees with the support-power coefficient on the
eigenvalues of a nonnegative matrix, its polynomial functional calculus equals
the support-convention matrix power. -/
theorem supportMatrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
    {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) (q : Polynomial ℝ)
    (hq : ∀ i : Fin n,
      Polynomial.eval ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i : ℝ) q =
        supportPowerCoeff p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i)) :
    supportMatrixPower p A =
      Polynomial.aeval A (Polynomial.map (algebraMap ℝ ℂ) q) := by
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA,
    matrixPolynomialAeval_eq_sum_eigenmatrix_nonneg hA q]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq i]

/-- If a real polynomial agrees with `x ^ p` on the eigenvalues of a
nonnegative matrix, its polynomial functional calculus equals `matrixPower`. -/
theorem matrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg
    {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) (p : ℝ) (q : Polynomial ℝ)
    (hq : ∀ i : Fin n,
      Polynomial.eval ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i : ℝ) q =
        powerFn p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i)) :
    matrixPower p A =
      Polynomial.aeval A (Polynomial.map (algebraMap ℝ ℂ) q) := by
  rw [matrixPower_eq_sum_eigenmatrix_nonneg_support hA,
    matrixPolynomialAeval_eq_sum_eigenmatrix_nonneg hA q]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq i]

private lemma supportEuclideanSubspace_eq_range_for_powerTrace {n : ℕ} (C : Mₙ n) :
    (let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
      EuclideanSpace.equiv (Fin n) ℂ
     (matrixSupportSubspace C).map e.symm.toLinearMap) =
      LinearMap.range (Matrix.toEuclideanLin C) := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  ext y
  constructor
  · intro hy
    rcases hy with ⟨v, hv, rfl⟩
    rcases hv with ⟨w, rfl⟩
    refine ⟨WithLp.toLp 2 w, ?_⟩
    simp [Matrix.mulVecLin]
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨C.mulVec (e z), ?_, ?_⟩
    · exact ⟨e z, rfl⟩
    · rw [← hz]
      rw [Matrix.toLpLin_apply]
      rfl

private lemma matrixSupportProj_mulVec_zero_of_selfAdjoint_support {n : ℕ} {C : Mₙ n}
    (hC : IsSelfAdjoint C) {x : Fin n → ℂ} (hx : C.mulVec x = 0) :
    (matrixSupportProj C).mulVec x = 0 := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  have hUeq : U = LinearMap.range (Matrix.toEuclideanLin C) := by
    simp [e, U, supportEuclideanSubspace_eq_range_for_powerTrace C]
  have hproj : Matrix.toEuclideanLin (matrixSupportProj C) = U.starProjection := by
    simp [e, U]
  have hxKer : WithLp.toLp 2 x ∈ (Matrix.toEuclideanLin C).ker := by
    rw [LinearMap.mem_ker]
    simp [hx]
  have hsymm : (Matrix.toEuclideanLin C).IsSymmetric := by
    rw [← Matrix.isHermitian_iff_isSymmetric]
    simpa [IsSelfAdjoint, Matrix.IsHermitian] using hC
  have hxOrthRange : WithLp.toLp 2 x ∈ (LinearMap.range (Matrix.toEuclideanLin C))ᗮ := by
    simpa [LinearMap.IsSymmetric.orthogonal_range hsymm] using hxKer
  have hxOrthU : e.symm x ∈ Uᗮ := by
    change WithLp.toLp 2 x ∈ Uᗮ
    simpa [hUeq] using hxOrthRange
  have hzero : U.starProjection (e.symm x) = 0 := by
    rw [Submodule.starProjection_apply]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hxOrthU)
  have hxEuclid : Matrix.toEuclideanLin (matrixSupportProj C) (WithLp.toLp 2 x) = 0 := by
    simpa [e, hproj] using hzero
  have hxFunc :
      WithLp.toLp 2 ((matrixSupportProj C).mulVec x) =
        WithLp.toLp 2 (0 : Fin n → ℂ) := by
    simpa only [Matrix.toLpLin_toLp] using hxEuclid
  simpa using congrArg WithLp.ofLp hxFunc

private lemma matrixSupportProj_mulVec_eigenvectorBasis_nonneg_support {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (i : Fin n) :
    (matrixSupportProj C).mulVec
        ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ) =
      (if (Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i = 0 then (0 : ℂ) else 1) •
        ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let μ : ℝ := hherm.eigenvalues i
  let v : Fin n → ℂ := hherm.eigenvectorBasis i
  have hmul : C.mulVec v = (μ : ℂ) • v := by
    simpa [hherm, μ, v] using hherm.mulVec_eigenvectorBasis i
  by_cases hμ : μ = 0
  · have hx : C.mulVec v = 0 := by simp [hmul, hμ]
    have hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hherm
    have hz := matrixSupportProj_mulVec_zero_of_selfAdjoint_support (C := C) hsa hx
    simp [μ, v, hμ, hz]
  · have hv_mem : v ∈ matrixSupportSubspace C := by
      refine ⟨((μ : ℂ)⁻¹) • v, ?_⟩
      calc
        C.mulVec (((μ : ℂ)⁻¹) • v)
            = ((μ : ℂ)⁻¹) • C.mulVec v := by simp [Matrix.mulVec_smul]
        _ = ((μ : ℂ)⁻¹) • ((μ : ℂ) • v) := by rw [hmul]
        _ = v := by
            have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
            ext k
            change (μ : ℂ)⁻¹ * ((μ : ℂ) * v k) = v k
            field_simp [hμC]
    have hprojv : (matrixSupportProj C).mulVec v = v :=
      (MatrixSupportProj.mulVec_eq_self_iff C v).2 hv_mem
    simp [μ, v, hμ, hprojv]

private lemma matrixSupportProj_eq_sum_eigenmatrix_nonneg_support {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) :
    matrixSupportProj C =
      ∑ i : Fin n,
        (if (Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i = 0 then (0 : ℂ) else 1) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    matrixSupportProj C =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (matrixSupportProj C)
              (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint_support hsa (matrixSupportProj C)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixSupportProj_mulVec_eigenvectorBasis_nonneg_support (C := C) hC i,
          Matrix.smul_vecMulVec]

/-- At exponent zero, the support-convention matrix power is the support
projection rather than the identity on the kernel. -/
theorem supportMatrixPower_zero_eq_matrixSupportProj {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) :
    supportMatrixPower 0 A = matrixSupportProj A := by
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA,
    matrixSupportProj_eq_sum_eigenmatrix_nonneg_support hA]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  by_cases hμ : (Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i = 0
  · simp [supportPowerCoeff, hμ]
  · simp [supportPowerCoeff, hμ]

/-- The support projection is a left identity on any support-convention power
of a nonnegative matrix. -/
theorem matrixSupportProj_mul_supportMatrixPower_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    matrixSupportProj A * supportMatrixPower p A = supportMatrixPower p A := by
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA p]
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec,
    matrixSupportProj_mulVec_eigenvectorBasis_nonneg_support (C := A) hA i]
  by_cases hμ : (Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i = 0
  · simp [supportPowerCoeff, hμ]
  · simp [supportPowerCoeff, hμ]

/-- Support-convention powers of nonnegative matrices are self-adjoint. -/
theorem supportMatrixPower_isSelfAdjoint_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    IsSelfAdjoint (supportMatrixPower p A) := by
  change Matrix.conjTranspose (supportMatrixPower p A) = supportMatrixPower p A
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA p]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
  simp

/-- The support projection is also a right identity on support-convention
powers of a nonnegative matrix. -/
theorem supportMatrixPower_mul_matrixSupportProj_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    supportMatrixPower p A * matrixSupportProj A = supportMatrixPower p A := by
  have hleft := matrixSupportProj_mul_supportMatrixPower_nonneg (A := A) hA p
  have hPsa : Matrix.conjTranspose (matrixSupportProj A) = matrixSupportProj A := by
    simpa [Matrix.star_eq_conjTranspose] using (MatrixSupportProj.isSelfAdjoint A).star_eq
  have hSsa : Matrix.conjTranspose (supportMatrixPower p A) = supportMatrixPower p A := by
    simpa [IsSelfAdjoint] using (supportMatrixPower_isSelfAdjoint_nonneg (A := A) hA p).star_eq
  simpa [Matrix.conjTranspose_mul, hPsa, hSsa] using congrArg Matrix.conjTranspose hleft

/-- Compressing a support-convention power by the support projection on both
sides leaves the power unchanged. -/
theorem matrixSupportProj_mul_supportMatrixPower_mul_matrixSupportProj_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    matrixSupportProj A * supportMatrixPower p A * matrixSupportProj A =
      supportMatrixPower p A := by
  calc
    matrixSupportProj A * supportMatrixPower p A * matrixSupportProj A
        = supportMatrixPower p A * matrixSupportProj A := by
            rw [matrixSupportProj_mul_supportMatrixPower_nonneg (A := A) hA p]
    _ = supportMatrixPower p A := by
          rw [supportMatrixPower_mul_matrixSupportProj_nonneg (A := A) hA p]

/-- On positive definite matrices, the support convention never sees a zero
eigenvalue, so support powers agree with ordinary matrix powers. -/
theorem supportMatrixPower_eq_matrixPower_of_posDef {n : ℕ} {A : Mₙ n} (p : ℝ)
    (hA : Matrix.PosDef A) :
    supportMatrixPower p A = matrixPower p A := by
  let hApos : A.PosDef := hA
  let hAnonneg : 0 ≤ A := hApos.posSemidef.nonneg
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hAnonneg,
    matrixPower_eq_sum_eigenmatrix_nonneg_support hAnonneg]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  let hpsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hAnonneg
  have hpos : 0 < hpsd.1.eigenvalues i :=
    hpsd.1.posDef_iff_eigenvalues_pos.mp hApos i
  have hne : hpsd.1.eigenvalues i ≠ 0 := ne_of_gt hpos
  simp [supportPowerCoeff, powerFn, hne]

/-- For positive exponents and nonnegative matrices, the support convention at
zero agrees with the ordinary real-power convention. -/
theorem supportMatrixPower_eq_matrixPower_of_pos_nonneg {n : ℕ} {A : Mₙ n} {p : ℝ}
    (hp : 0 < p) (hA : 0 ≤ A) :
    supportMatrixPower p A = matrixPower p A := by
  rw [supportMatrixPower_eq_sum_eigenmatrix_nonneg hA,
    matrixPower_eq_sum_eigenmatrix_nonneg_support hA]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hreal :
      supportPowerCoeff p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i) =
        powerFn p ((Matrix.nonneg_iff_posSemidef.mp hA).1.eigenvalues i) := by
    dsimp [supportPowerCoeff, powerFn]
    split_ifs with hμ
    · rw [hμ]
      exact (Real.zero_rpow hp.ne').symm
    · rfl
  exact_mod_cast hreal

/-- The total support trace expression agrees with the explicit nonnegative
version when both matrix arguments are Loewner-nonnegative. -/
theorem supportPowerTrace_eq_of_nonneg {n : ℕ} {A B X : Mₙ n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (r s : ℝ) :
    supportPowerTrace r s A B X = supportPowerTraceOfNonneg r s hA hB X := by
  rw [supportPowerTrace, supportPowerTraceOfNonneg,
    supportMatrixPower_eq_of_nonneg hA, supportMatrixPower_eq_of_nonneg hB]

/-- The total support Lieb trace expression agrees with the explicit
nonnegative version under semidefinite hypotheses. -/
theorem supportLiebTracePower_eq_of_nonneg {n : ℕ} {A B X : Mₙ n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℝ) :
    supportLiebTracePower p A B X = supportLiebTracePowerOfNonneg p hA hB X := by
  rw [supportLiebTracePower, supportLiebTracePowerOfNonneg,
    supportPowerTrace_eq_of_nonneg hA hB]

/-- For positive definite inputs, support-convention Lieb trace powers reduce
to ordinary Lieb trace powers for all real exponents. -/
theorem supportLiebTracePower_eq_liebTracePower_of_posDef {n : ℕ} {A B X : Mₙ n}
    (p : ℝ) (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    supportLiebTracePower p A B X = liebTracePower p A B X := by
  rw [supportLiebTracePower, supportPowerTrace, liebTracePower, powerTrace,
    supportMatrixPower_eq_matrixPower_of_posDef p hA,
    supportMatrixPower_eq_matrixPower_of_posDef (1 - p) hB]

/-- On the open interval `0 < p < 1`, support-convention Lieb trace powers
agree with ordinary Lieb trace powers for semidefinite inputs. -/
theorem supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo {n : ℕ}
    {A B X : Mₙ n} {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportLiebTracePower p A B X = liebTracePower p A B X := by
  rw [supportLiebTracePower, supportPowerTrace, liebTracePower, powerTrace,
    supportMatrixPower_eq_matrixPower_of_pos_nonneg hp.1 hA,
    supportMatrixPower_eq_matrixPower_of_pos_nonneg (sub_pos.mpr hp.2) hB]

/-- Endpoint `p = 0` support Lieb trace expression, where the left power is the
support projection of `A`. -/
theorem supportLiebTracePower_zero_eq_trace_supportProj {n : ℕ}
    {A B X : Mₙ n} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportLiebTracePower 0 A B X =
      Complex.re
        (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj A * X *
          matrixPower 1 B)) := by
  rw [supportLiebTracePower, supportPowerTrace, supportMatrixPower_zero_eq_matrixSupportProj hA]
  rw [show (1 : ℝ) - 0 = 1 by norm_num]
  rw [supportMatrixPower_eq_matrixPower_of_pos_nonneg zero_lt_one hB]

/-- Endpoint `p = 1` support Lieb trace expression, where the right power is
the support projection of `B`. -/
theorem supportLiebTracePower_one_eq_trace_supportProj {n : ℕ}
    {A B X : Mₙ n} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    supportLiebTracePower 1 A B X =
      Complex.re
        (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 A * X *
          matrixSupportProj B)) := by
  rw [supportLiebTracePower, supportPowerTrace]
  rw [supportMatrixPower_eq_matrixPower_of_pos_nonneg zero_lt_one hA]
  rw [show (1 : ℝ) - 1 = 0 by norm_num]
  rw [supportMatrixPower_zero_eq_matrixSupportProj hB]

/-- The `jOperatorInv` quadratic form for the power function, used as the inverse
strict-output intermediate form of Hiai-Petz Theorem 6.3. -/
noncomputable def jInversePowerTrace (p : ℝ) (A B X : Mₙ n) : ℝ :=
  Complex.re
    (Matrix.trace
      ((Matrix.conjTranspose X *
          hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (jArg A B) X) *
        B⁻¹))

/-- The power-specialized `J_f` quadratic form is the existing quasi-entropy
with `f x = x^p`, written in the trace-shifted form used by Theorem 6.3. -/
theorem quasiEntropy_powerFn_eq_jPowerTrace (p : ℝ) {A B X : Mₙ n}
    (hB : Matrix.PosDef B) :
    quasiEntropy (powerFn p) A B X = jPowerTrace p A B X := by
  simpa [quasiEntropy, jPowerTrace] using
    hsQForm_jOperator_of_posDef (f := powerFn p) (A := A) (B := B) hB X X

/-- Rewriting orientation from the Theorem 6.3 `J`-form back to quasi-entropy. -/
theorem jPowerTrace_eq_quasiEntropy_powerFn (p : ℝ) {A B X : Mₙ n}
    (hB : Matrix.PosDef B) :
    jPowerTrace p A B X = quasiEntropy (powerFn p) A B X :=
  (quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := A) (B := B) (X := X) hB).symm

end MatrixScopedInstances

noncomputable section MatrixPowerLimits

open scoped Topology

variable {n : ℕ}

/-- The real spectrum of a CLM on a finite-dimensional space is finite. -/
theorem finite_real_spectrum_clm {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [FiniteDimensional ℂ K]
    (T : K →L[ℂ] K) :
    Set.Finite (spectrum ℝ T) := by
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite (spectrum ℂ ((Module.End.toContinuousLinearMap K) T.toLinearMap))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := K) T.toLinearMap
  rw [← spectrum.preimage_algebraMap ℂ]
  exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- `powerFn (g a) → powerFn p₀` uniformly on a finite positive set as `g a → p₀`. -/
theorem powerFn_tendstoUniformlyOn_of_finite_pos {α : Type*} {l : Filter α}
    {g : α → ℝ} {p₀ : ℝ} {s : Set ℝ}
    (hfin : Set.Finite s) (hpos : s ⊆ Set.Ioi (0 : ℝ))
    (hg : Filter.Tendsto g l (𝓝 p₀)) :
    TendstoUniformlyOn (fun a : α => powerFn (g a)) (powerFn p₀) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact hfin.eventually_all.mpr fun x hx => by
    have hxne : x ≠ 0 := ne_of_gt (hpos hx)
    have ht : Filter.Tendsto (fun a : α => x ^ g a) l (𝓝 (x ^ p₀)) :=
      (Real.continuousAt_const_rpow hxne).tendsto.comp hg
    have hdist :
        Filter.Tendsto (fun a : α => dist (powerFn p₀ x) (powerFn (g a) x))
          l (𝓝 (dist (powerFn p₀ x) (powerFn p₀ x))) := by
      exact (tendsto_const_nhds (x := powerFn p₀ x)).dist (by simpa [powerFn] using ht)
    simpa using hdist.eventually (Iio_mem_nhds (by simpa using hε))

end MatrixPowerLimits

end HiaiPetz
