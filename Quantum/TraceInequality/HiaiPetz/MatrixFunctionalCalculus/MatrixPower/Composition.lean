/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.SupportPower

/-!
# Composition laws for matrix real powers

This file proves algebraic laws for the finite-dimensional matrix power
`matrixPower`, using transport through `Matrix.toEuclideanCLM` to reuse the
continuous functional calculus real-power API for operators. Positive
semidefinite inputs support nonnegative exponent composition, while positive
definite inputs allow arbitrary real exponents with the usual inverse-power
behavior.

## Main results

* `matrixPower_toEuclideanCLM_rpow`: transport of matrix powers to CLM real
  powers.
* `matrixPower_comp_nonneg` and `supportMatrixPower_comp_pos_nonneg`:
  composition laws on positive semidefinite inputs.
* `matrixPower_posDef_of_posDef`, `matrixPower_comp_posDef`,
  `matrixPower_one_posDef`, `matrixPower_zero_posDef`, and
  `matrixPower_mul_matrixPower_posDef`: positive-definite matrix-power algebra.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, matrix power calculus used in
  Lieb-type trace expressions.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/- Instance caches: CFC real powers on `Matrix.toEuclideanCLM` trigger deep
`synthInstance` searches (`HPow _ ℝ _` via the C⋆-algebra `Rpow` route, and the
`Algebra ℝ _` structure feeding `cfc`), each exceeding the default heartbeat
budget on its own and re-run at every use site. Caching them as section-level
reducible instances makes each search a head-match; `@[reducible]` keeps the
aliases transparent so statements stay syntactically compatible with Mathlib
lemmas (a non-reducible alias breaks `rw` against `CFC.rpow_*`). -/

/-- Local cached real algebra structure on Euclidean continuous linear maps,
used so transported CFC real-power goals elaborate predictably. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealEuclideanCLMScoped :
    Algebra ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Local cached real-power structure on Euclidean continuous linear maps,
matching the CFC `Rpow` route used by Mathlib real powers. -/
@[reducible, local instance]
private noncomputable def instPowEuclideanCLMRealScoped :
    Pow (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ℝ :=
  inferInstance

-- CFC rpow transport through `Matrix.toEuclideanCLM`.
-- Real-power transport through the matrix/CLM equivalence.
/-- Transport of matrix real powers through `Matrix.toEuclideanCLM`: for a
nonnegative matrix, `matrixPower p A` corresponds to the CLM real power
`(toEuclideanCLM A) ^ p`. -/
theorem matrixPower_toEuclideanCLM_rpow {n : ℕ} {p : ℝ} {A : Mₙ n}
    (hA : 0 ≤ A) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (matrixPower p A) =
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A) ^ p := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hA
  rw [CFC.rpow_eq_cfc_real (a := φ A) (y := p) (ha := hφA_nonneg)]
  simp only [matrixPower, HansenPedersen.matrixCfcR, φ, StarAlgEquiv.apply_symm_apply]
  change cfc (fun x : ℝ => x ^ p) (φ A) = cfc (fun x : ℝ => x ^ p) (φ A)
  rfl

-- CFC rpow composition through CLM equivalence.
-- Matrix-power composition on positive semidefinite inputs.
/-- For a nonnegative matrix, composing a positive real power with a
nonnegative real power multiplies the exponents. -/
theorem matrixPower_comp_nonneg {n : ℕ} {r s : ℝ} {A : Mₙ n}
    (hr : 0 < r) (hs : 0 ≤ s) (hA : 0 ≤ A) :
    matrixPower s (matrixPower r A) = matrixPower (r * s) A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAr_nonneg : 0 ≤ matrixPower r A := by
    have hsupport : supportMatrixPower r A = matrixPower r A :=
      supportMatrixPower_eq_matrixPower_of_pos_nonneg hr hA
    rw [← hsupport]
    exact supportMatrixPower_nonneg hA r
  apply φ.injective
  calc
    φ (matrixPower s (matrixPower r A))
        = (φ (matrixPower r A)) ^ s :=
            matrixPower_toEuclideanCLM_rpow hAr_nonneg
    _ = ((φ A) ^ r) ^ s := by
          rw [matrixPower_toEuclideanCLM_rpow hA]
    _ = (φ A) ^ (r * s) := by
          rw [CFC.rpow_rpow_of_exponent_nonneg (a := φ A) (x := r) (y := s)
            hr.le hs (toEuclideanCLM_nonneg_of_matrix_nonneg hA)]
    _ = φ (matrixPower (r * s) A) := by
          rw [matrixPower_toEuclideanCLM_rpow hA]

-- CFC rpow composition through CLM equivalence.
-- Support-power composition on positive semidefinite inputs.
/-- The support-sensitive matrix power satisfies the same exponent-composition
law for positive exponents on nonnegative matrices. -/
theorem supportMatrixPower_comp_pos_nonneg {n : ℕ} {r s : ℝ} {A : Mₙ n}
    (hr : 0 < r) (hs : 0 < s) (hA : 0 ≤ A) :
    supportMatrixPower s (supportMatrixPower r A) =
      supportMatrixPower (r * s) A := by
  have hAr_nonneg : 0 ≤ supportMatrixPower r A :=
    supportMatrixPower_nonneg hA r
  rw [supportMatrixPower_eq_matrixPower_of_pos_nonneg hs hAr_nonneg,
    supportMatrixPower_eq_matrixPower_of_pos_nonneg hr hA,
    supportMatrixPower_eq_matrixPower_of_pos_nonneg (mul_pos hr hs) hA]
  exact matrixPower_comp_nonneg hr hs.le hA

/-- Composing the right support power in the Lieb trace expression multiplies
the right exponent by the outer support-power exponent. -/
theorem supportLiebTracePower_right_comp_pos {n : ℕ}
    {p r : ℝ} {A B X : Mₙ n}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r) (hB : 0 ≤ B) :
    supportLiebTracePower p A (supportMatrixPower r B) X =
      supportPowerTrace p (r * (1 - p)) A B X := by
  have hs : 0 < 1 - p := sub_pos.mpr hp.2
  simp only [supportLiebTracePower, supportPowerTrace]
  rw [supportMatrixPower_comp_pos_nonneg hr hs hB]

-- CLM real-power unit construction needs the `HPow` instance through CFC.
-- Positivity and invertibility of real powers transported through CFC.
/-- Any real power of a positive-definite matrix is again positive definite. -/
theorem matrixPower_posDef_of_posDef {n : ℕ} {r : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    Matrix.PosDef (matrixPower r A) := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hpow_nonneg : 0 ≤ matrixPower r A := by
    have hsupport := supportMatrixPower_eq_matrixPower_of_posDef r hA
    simpa [hsupport] using supportMatrixPower_nonneg hAnonneg r
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hAnonneg
  have hφA_unit : IsUnit (φ A) := by
    simpa [φ] using IsUnit.map φ hA.isUnit
  have hφ_unit : IsUnit (φ (matrixPower r A)) := by
    have hφ_eq := matrixPower_toEuclideanCLM_rpow (p := r) hAnonneg
    rw [hφ_eq]
    let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := φ A
    have hTunit : IsUnit T := by
      simpa [T] using hφA_unit
    have hTnonneg : 0 ≤ T := by
      simpa [T] using hφA_nonneg
    suffices IsUnit (T ^ r) by
      simpa [T] using this
    refine ⟨{
      val := T ^ r
      inv := T ^ (-r)
      val_inv := ?_
      inv_val := ?_ }, rfl⟩
    · simpa using CFC.rpow_mul_rpow_neg (a := T) r hTunit hTnonneg
    · simpa using CFC.rpow_neg_mul_rpow (a := T) r hTunit hTnonneg
  have hunit : IsUnit (matrixPower r A) := by
    have hpre : IsUnit (φ.symm (φ (matrixPower r A))) := IsUnit.map φ.symm hφ_unit
    simpa [φ] using hpre
  exact (((Matrix.nonneg_iff_posSemidef).mp hpow_nonneg).posDef_iff_isUnit.mpr hunit)

-- CFC real powers on `Matrix.toEuclideanCLM` need deep `HPow` synthesis.
/-- The zeroth real power of a positive-definite matrix is the identity matrix. -/
theorem matrixPower_zero_posDef {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower 0 A = 1 := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hAnonneg
  apply φ.injective
  calc
    φ (matrixPower 0 A)
        = (φ A) ^ (0 : ℝ) := matrixPower_toEuclideanCLM_rpow hAnonneg
    _ = 1 := CFC.rpow_zero (φ A) hφA_nonneg
    _ = φ (1 : Mₙ n) := by simp

-- CFC rpow composition through CLM equivalence for invertible matrices.
-- Matrix-power composition on positive definite inputs.
/-- For positive-definite matrices, real powers satisfy the usual composition
law for arbitrary real inner and outer exponents. -/
theorem matrixPower_comp_posDef {n : ℕ} {r s : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower s (matrixPower r A) = matrixPower (r * s) A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hAunit : IsUnit (φ A) := by
    simpa [φ] using IsUnit.map φ hA.isUnit
  have hAr_nonneg : 0 ≤ matrixPower r A :=
    Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := r) hA)
  apply φ.injective
  by_cases hr : r = 0
  · subst r
    rw [matrixPower_zero_posDef hA, zero_mul, matrixPower_zero_posDef hA]
    have hOneNonneg : 0 ≤ (1 : Mₙ n) := by simp
    calc
      φ (matrixPower s (1 : Mₙ n))
          = (φ (1 : Mₙ n)) ^ s := matrixPower_toEuclideanCLM_rpow hOneNonneg
      _ = 1 := by simp
      _ = φ (1 : Mₙ n) := by simp
  · calc
      φ (matrixPower s (matrixPower r A))
          = (φ (matrixPower r A)) ^ s :=
              matrixPower_toEuclideanCLM_rpow hAr_nonneg
      _ = ((φ A) ^ r) ^ s := by
            rw [matrixPower_toEuclideanCLM_rpow hAnonneg]
      _ = (φ A) ^ (r * s) := by
            rw [CFC.rpow_rpow (a := φ A) r s hAunit hr
              (toEuclideanCLM_nonneg_of_matrix_nonneg hAnonneg)]
      _ = φ (matrixPower (r * s) A) := by
            rw [matrixPower_toEuclideanCLM_rpow hAnonneg]

-- CFC real powers on `Matrix.toEuclideanCLM` need deep `HPow` synthesis.
/-- The first real power of a positive-definite matrix is the matrix itself. -/
theorem matrixPower_one_posDef {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower 1 A = A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hAnonneg
  apply φ.injective
  calc
    φ (matrixPower 1 A)
        = (φ A) ^ (1 : ℝ) := matrixPower_toEuclideanCLM_rpow hAnonneg
    _ = φ A := CFC.rpow_one (φ A) hφA_nonneg

-- CFC real powers on `Matrix.toEuclideanCLM` need deep `HPow` synthesis.
/-- Products of real powers of the same positive-definite matrix add the
exponents. -/
theorem matrixPower_mul_matrixPower_posDef {n : ℕ} {r s : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower r A * matrixPower s A = matrixPower (r + s) A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hAnonneg
  have hφA_unit : IsUnit (φ A) := by
    simpa [φ] using IsUnit.map φ hA.isUnit
  apply φ.injective
  calc
    φ (matrixPower r A * matrixPower s A)
        = φ (matrixPower r A) * φ (matrixPower s A) := by simp
    _ = (φ A) ^ r * (φ A) ^ s := by
          rw [matrixPower_toEuclideanCLM_rpow hAnonneg,
            matrixPower_toEuclideanCLM_rpow hAnonneg]
    _ = (φ A) ^ (r + s) := (CFC.rpow_add (a := φ A) (x := r) (y := s) hφA_unit).symm
    _ = φ (matrixPower (r + s) A) := by
          rw [matrixPower_toEuclideanCLM_rpow hAnonneg]

end MatrixScopedInstances

end HiaiPetz
