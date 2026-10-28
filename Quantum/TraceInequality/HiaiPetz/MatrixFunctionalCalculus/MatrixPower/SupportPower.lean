/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.Basic

/-!
# Positivity of support-convention matrix powers

This file proves that the book-facing support-convention matrix power remains
nonnegative on nonnegative matrices for every real exponent. The proof
transports the support-power real functional calculus through
`Matrix.toEuclideanCLM`, checks scalar nonnegativity on the real spectrum, and
then reflects the resulting operator inequality back to matrices.

## Main results

* `supportMatrixPower_nonneg`: if `0 ≤ A`, then `supportMatrixPower p A` is
  nonnegative for every real exponent `p`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Theorem 6.3 support-power convention.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

-- CFC positivity through the matrix/CLM equivalence uses deep scalar-tower instances.
-- Support-power CFC positivity is localized here for downstream trace monotonicity.
/-- The support-convention matrix power of a nonnegative matrix is
nonnegative for any real exponent. -/
theorem supportMatrixPower_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) (p : ℝ) :
    0 ≤ supportMatrixPower p A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hφ :
      φ (supportMatrixPower p A) =
        LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n))
          (supportPowerCoeff p) (φ A) := by
    have h0 := congrArg φ
      (supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg (A := A) hA p)
    simpa [HansenPedersen.matrixCfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR,
      φ] using h0
  have hφA_nonneg : 0 ≤ φ A :=
    toEuclideanCLM_nonneg_of_matrix_nonneg hA
  have hnonnegCoeff :
      ∀ x ∈ spectrum ℝ (φ A), 0 ≤ supportPowerCoeff p x := by
    intro x hx
    have hx0 : 0 ≤ x :=
      spectrum_nonneg_of_nonneg
        (𝕜 := ℝ)
        (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        (a := φ A) hφA_nonneg hx
    by_cases hzero : x = 0
    · simp [supportPowerCoeff, hzero]
    · exact by
        dsimp [supportPowerCoeff]
        rw [if_neg hzero]
        exact Real.rpow_nonneg hx0 p
  have hcfc_nonneg :
      0 ≤ LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n))
        (supportPowerCoeff p) (φ A) := by
    rw [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
    exact cfc_nonneg
      (R := ℝ) (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (p := IsSelfAdjoint) (a := φ A) hnonnegCoeff
  have hmap : 0 ≤ φ (supportMatrixPower p A) := by
    simpa [hφ] using hcfc_nonneg
  exact ((show φ 0 ≤ φ (supportMatrixPower p A) ↔ 0 ≤ supportMatrixPower p A
      from by simpa using (map_le_map_iff φ :
        φ 0 ≤ φ (supportMatrixPower p A) ↔ 0 ≤ supportMatrixPower p A))).1
    (by simpa using hmap)

end MatrixScopedInstances

end HiaiPetz
