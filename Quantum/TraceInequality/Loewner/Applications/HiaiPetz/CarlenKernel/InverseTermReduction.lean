/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.AdjointHelpers

/-!
# Carlen fixed-kernel DPI: inverse-term reduction stage

This module contains the fixed-kernel DPI stage of Carlen 2022 covering the
Hilbert--Schmidt adjoint orientation, matrix inverse-term reduction, and the
Lieb--Ruskai/Schwarz endpoint inputs.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instCarlenKernelHSOpCStarAlgebra
  instCarlenKernelHSOpStarRing
  instCarlenKernelHSOpPartialOrder
  instCarlenKernelHSOpStarOrderedRing
  instCarlenKernelHSOpNonnegSpectrumClass

noncomputable section

/-! ### Hilbert--Schmidt Adjoint Orientation -/

/-- The trace quadratic form for `hsAdjoint` agrees with the pushed-forward form. -/
theorem re_trace_hsAdjoint_eq {n m : ℕ} (Φ : HSMap n m) (X : Mₙ n) (Y : Mₙ m) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y)) =
      Complex.re (Matrix.trace (Matrix.conjTranspose (Φ X) * Y)) :=
  congrArg Complex.re (trace_hsAdjoint_eq Φ X Y)

/-- The Hilbert--Schmidt adjoint is involutive for the Frobenius inner product. -/
theorem hsAdjoint_hsAdjoint {n m : ℕ} (Ψ : HSMap n m) :
    hsAdjoint (hsAdjoint Ψ) = Ψ := by
  simp [hsAdjoint]

/-! ### Matrix Inverse-Term Reduction -/
/--
A left inverse-term matrix inequality, together with trace preservation, gives
the corresponding Hilbert--Schmidt quadratic-form inequality.
-/
theorem left_inverse_term_HSLE_of_matrix_inequality {n m : ℕ}
    {Φ : HSMap n m} {A : Mₙ n} {A' : Mₙ m}
    (htrace : ∀ Z : Mₙ n, Matrix.trace (Φ Z) = Matrix.trace Z)
    (hleft : ∀ X : Mₙ n,
      (Φ (Matrix.conjTranspose X * posInv A * X) -
        Matrix.conjTranspose (Φ X) * posInv A' * Φ X).PosSemidef) :
    HSLE ((hsAdjoint Φ).comp ((leftMul (posInv A')).comp Φ))
      (leftMul (posInv A)) := by
  change HSNonneg
    (leftMul (posInv A) - ((hsAdjoint Φ).comp ((leftMul (posInv A')).comp Φ)))
  intro X
  change 0 ≤ Complex.re (Matrix.trace
    (Matrix.conjTranspose X *
      ((leftMul (posInv A)) X -
        (hsAdjoint Φ) (((leftMul (posInv A')).comp Φ) X))))
  have hnonneg : 0 ≤ Complex.re (Matrix.trace
      (Φ (Matrix.conjTranspose X * posInv A * X) -
        Matrix.conjTranspose (Φ X) * posInv A' * Φ X)) :=
    re_trace_nonneg_of_posSemidef (hleft X)
  have hfirst :
      Complex.re (Matrix.trace (Φ (Matrix.conjTranspose X * posInv A * X))) =
        Complex.re (Matrix.trace (Matrix.conjTranspose X * (posInv A * X))) := by
    rw [htrace]
    congr 1
    rw [Matrix.mul_assoc]
  have hsecond :
      Complex.re (Matrix.trace
          (Matrix.conjTranspose X *
            hsAdjoint Φ (((leftMul (posInv A')).comp Φ) X))) =
        Complex.re (Matrix.trace (Matrix.conjTranspose (Φ X) * (posInv A' * Φ X))) :=
    by
      simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply, leftMul_apply] using
        re_trace_hsAdjoint_eq Φ X (posInv A' * Φ X)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, leftMul_apply] at hsecond
  have hgoal :
      Complex.re (Matrix.trace
          (Matrix.conjTranspose X *
            ((leftMul (posInv A)) X -
              (hsAdjoint Φ) (((leftMul (posInv A')).comp Φ) X)))) =
        Complex.re (Matrix.trace
          (Φ (Matrix.conjTranspose X * posInv A * X) -
            Matrix.conjTranspose (Φ X) * posInv A' * Φ X)) := by
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, leftMul_apply]
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
    rw [Complex.sub_re, Complex.sub_re]
    rw [hfirst, hsecond]
    congr 2
    rw [Matrix.mul_assoc]
  rw [hgoal]
  exact hnonneg

/--
A right inverse-term matrix inequality, together with trace preservation, gives
the corresponding Hilbert--Schmidt quadratic-form inequality.
-/
theorem right_inverse_term_HSLE_of_matrix_inequality {n m : ℕ}
    {Φ : HSMap n m} {B : Mₙ n} {B' : Mₙ m}
    (htrace : ∀ Z : Mₙ n, Matrix.trace (Φ Z) = Matrix.trace Z)
    (hright : ∀ X : Mₙ n,
      (Φ (X * posInv B * Matrix.conjTranspose X) -
        Φ X * posInv B' * Matrix.conjTranspose (Φ X)).PosSemidef) :
    HSLE ((hsAdjoint Φ).comp ((rightMul (posInv B')).comp Φ))
      (rightMul (posInv B)) := by
  change HSNonneg
    (rightMul (posInv B) - ((hsAdjoint Φ).comp ((rightMul (posInv B')).comp Φ)))
  intro X
  change 0 ≤ Complex.re (Matrix.trace
    (Matrix.conjTranspose X *
      ((rightMul (posInv B)) X -
        (hsAdjoint Φ) (((rightMul (posInv B')).comp Φ) X))))
  have hnonneg : 0 ≤ Complex.re (Matrix.trace
      (Φ (X * posInv B * Matrix.conjTranspose X) -
        Φ X * posInv B' * Matrix.conjTranspose (Φ X))) :=
    re_trace_nonneg_of_posSemidef (hright X)
  have hfirst :
      Complex.re (Matrix.trace (Φ (X * posInv B * Matrix.conjTranspose X))) =
        Complex.re (Matrix.trace (Matrix.conjTranspose X * (X * posInv B))) := by
    rw [htrace]
    rw [Matrix.trace_mul_cycle]
    rw [Matrix.mul_assoc]
  have hsecond :
      Complex.re (Matrix.trace
          (Matrix.conjTranspose X *
            hsAdjoint Φ (((rightMul (posInv B')).comp Φ) X))) =
        Complex.re (Matrix.trace (Φ X * posInv B' * Matrix.conjTranspose (Φ X))) := by
    calc
      Complex.re (Matrix.trace
          (Matrix.conjTranspose X *
            hsAdjoint Φ (((rightMul (posInv B')).comp Φ) X)))
          = Complex.re (Matrix.trace
              (Matrix.conjTranspose (Φ X) * (Φ X * posInv B'))) :=
            by
              simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply, rightMul_apply] using
                re_trace_hsAdjoint_eq Φ X (Φ X * posInv B')
      _ = Complex.re (Matrix.trace (Φ X * posInv B' * Matrix.conjTranspose (Φ X))) := by
            rw [Matrix.trace_mul_cycle]
            rw [Matrix.mul_assoc]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, rightMul_apply] at hsecond
  have hgoal :
      Complex.re (Matrix.trace
          (Matrix.conjTranspose X *
            ((rightMul (posInv B)) X -
              (hsAdjoint Φ) (((rightMul (posInv B')).comp Φ) X)))) =
        Complex.re (Matrix.trace
          (Φ (X * posInv B * Matrix.conjTranspose X) -
            Φ X * posInv B' * Matrix.conjTranspose (Φ X))) := by
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, rightMul_apply]
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
    rw [Complex.sub_re, Complex.sub_re]
    rw [hfirst, hsecond]
  rw [hgoal]
  exact hnonneg

/--
Matrix-level left and right inverse-term inequalities imply the inverse-form
fixed-kernel data-processing inequality.
-/
theorem jKuboKernelInvForm_dpi_of_matrix_inverse_terms {n m : ℕ} (Φ : HSMap n m)
    {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ n} {A' B' : Mₙ m}
    (htrace : ∀ Z : Mₙ n, Matrix.trace (Φ Z) = Matrix.trace Z)
    (hleft : ∀ X : Mₙ n,
      (Φ (Matrix.conjTranspose X * posInv A * X) -
        Matrix.conjTranspose (Φ X) * posInv A' * Φ X).PosSemidef)
    (hright : ∀ X : Mₙ n,
      (Φ (X * posInv B * Matrix.conjTranspose X) -
        Φ X * posInv B' * Matrix.conjTranspose (Φ X)).PosSemidef) :
    HSLE ((hsAdjoint Φ).comp ((jKuboKernelInvForm t A' B').comp Φ))
      (jKuboKernelInvForm t A B) :=
  jKuboKernelInvForm_dpi_of_inverse_terms Φ ht
    (left_inverse_term_HSLE_of_matrix_inequality htrace hleft)
    (right_inverse_term_HSLE_of_matrix_inequality htrace hright)

/--
The Schwarz inequality alone gives the Hilbert--Schmidt quadratic-form
inequality for the right-multiplication endpoint term.
-/
theorem rightMul_dpi_of_schwarzMap {n m : ℕ} (Ψ : HSMap n m)
    {B : Mₙ m}
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hB : MatrixPosDef B) :
    HSLE
      ((hsAdjoint Ψ).comp ((rightMul B).comp Ψ))
      (rightMul (hsAdjoint Ψ B)) := by
  rw [HSLE]
  intro X
  let Z : Mₙ n := Matrix.conjTranspose X * X
  let Q : Mₙ m := Matrix.conjTranspose (Ψ X) * Ψ X
  let P : Mₙ m := Ψ Z - Q
  have hP_nonneg : 0 ≤ P := by
    simpa [P, Q, Z] using (sub_nonneg.mpr (hSch X))
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hQherm : Q.IsHermitian := by
    simpa [Q] using Matrix.isHermitian_conjTranspose_mul_self (Ψ X)
  have hΨZherm : (Ψ Z).IsHermitian := by
    have hsum : (P + Q).IsHermitian := hP.1.add hQherm
    have hsum_eq : P + Q = Ψ Z := by
      simp [P, Q]
    simpa [hsum_eq] using hsum
  have htrace_nonneg : 0 ≤ Matrix.trace (P * B) :=
    matrix_trace_mul_nonneg_of_posSemidef hP (matrixPosDef_posDef hB).posSemidef
  have htrace_re : 0 ≤ Complex.re (Matrix.trace (P * B)) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have hfirst :
      Matrix.trace (Matrix.conjTranspose X * (X * hsAdjoint Ψ B)) =
        Matrix.trace (Ψ (Matrix.conjTranspose X * X) * B) := by
    have hZstar : Matrix.conjTranspose Z = Z := by
      simp [Z, Matrix.conjTranspose_mul]
    have hΨZstar : Matrix.conjTranspose (Ψ Z) = Ψ Z := hΨZherm.eq
    calc
      Matrix.trace (Matrix.conjTranspose X * (X * hsAdjoint Ψ B))
          = Matrix.trace (Z * hsAdjoint Ψ B) := by
              simp [Z, Matrix.mul_assoc]
      _ = Matrix.trace (Matrix.conjTranspose Z * hsAdjoint Ψ B) := by
              rw [hZstar]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ Z) * B) :=
              trace_hsAdjoint_eq Ψ Z B
      _ = Matrix.trace (Ψ Z * B) := by
              rw [hΨZstar]
  have hsecond :
      Matrix.trace
          (Matrix.conjTranspose X * hsAdjoint Ψ (Ψ X * B)) =
        Matrix.trace ((Matrix.conjTranspose (Ψ X) * Ψ X) * B) := by
    calc
      Matrix.trace
          (Matrix.conjTranspose X * hsAdjoint Ψ (Ψ X * B))
          = Matrix.trace (Matrix.conjTranspose (Ψ X) * (Ψ X * B)) := by
              simpa using
                trace_hsAdjoint_eq Ψ X (Ψ X * B)
      _ = Matrix.trace ((Matrix.conjTranspose (Ψ X) * Ψ X) * B) := by
              rw [Matrix.mul_assoc]
  have hgoal :
      Complex.re (Matrix.trace
        (Matrix.conjTranspose X *
          (((rightMul (hsAdjoint Ψ B)) -
              ((hsAdjoint Ψ).comp ((rightMul B).comp Ψ))) X))) =
        Complex.re (Matrix.trace (P * B)) := by
    change Complex.re (Matrix.trace
        (Matrix.conjTranspose X * (X * hsAdjoint Ψ B - hsAdjoint Ψ (Ψ X * B)))) =
      Complex.re (Matrix.trace (P * B))
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.sub_mul, Matrix.trace_sub]
    rw [Complex.sub_re, Complex.sub_re]
    rw [hfirst, hsecond]
  rw [hgoal]
  exact htrace_re

/--
Schwarz plus conjugate-transpose preservation gives the Hilbert--Schmidt
quadratic-form inequality for the left-multiplication endpoint term.
-/
theorem leftMul_dpi_of_schwarzMap_of_map_conjTranspose {n m : ℕ} (Ψ : HSMap n m)
    {A : Mₙ m}
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hstar : ∀ X : Mₙ n, Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X))
    (hA : MatrixPosDef A) :
    HSLE
      ((hsAdjoint Ψ).comp ((leftMul A).comp Ψ))
      (leftMul (hsAdjoint Ψ A)) := by
  rw [HSLE]
  intro X
  let Y : Mₙ n := Matrix.conjTranspose X
  let P : Mₙ m := Ψ (Matrix.conjTranspose Y * Y) - Matrix.conjTranspose (Ψ Y) * Ψ Y
  have hP_nonneg : 0 ≤ P := by
    simpa [P] using (sub_nonneg.mpr (hSch Y))
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hP_eq :
      P = Ψ (X * Matrix.conjTranspose X) - Ψ X * Matrix.conjTranspose (Ψ X) := by
    have hYmap : Ψ Y = Matrix.conjTranspose (Ψ X) := by
      simpa [Y] using hstar X
    simp [P, Y, hYmap, Matrix.conjTranspose_conjTranspose]
  have htrace_nonneg : 0 ≤ Matrix.trace (P * A) :=
    matrix_trace_mul_nonneg_of_posSemidef hP (matrixPosDef_posDef hA).posSemidef
  have htrace_re : 0 ≤ Complex.re (Matrix.trace (P * A)) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have hfirst :
      Matrix.trace (Matrix.conjTranspose X * (hsAdjoint Ψ A * X)) =
        Matrix.trace (Ψ (X * Matrix.conjTranspose X) * A) := by
    let Z : Mₙ n := X * Matrix.conjTranspose X
    have hZstar : Matrix.conjTranspose Z = Z := by
      simp [Z, Matrix.conjTranspose_mul]
    have hΨZstar : Matrix.conjTranspose (Ψ Z) = Ψ Z := by
      have h := hstar Z
      rw [hZstar] at h
      exact h.symm
    calc
      Matrix.trace (Matrix.conjTranspose X * (hsAdjoint Ψ A * X))
          = Matrix.trace ((Matrix.conjTranspose X * hsAdjoint Ψ A) * X) := by
              rw [Matrix.mul_assoc]
      _ = Matrix.trace (X * (Matrix.conjTranspose X * hsAdjoint Ψ A)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((X * Matrix.conjTranspose X) * hsAdjoint Ψ A) := by
              rw [Matrix.mul_assoc]
      _ = Matrix.trace (Z * hsAdjoint Ψ A) := by
              simp [Z, Matrix.mul_assoc]
      _ = Matrix.trace (Matrix.conjTranspose Z * hsAdjoint Ψ A) := by
              rw [hZstar]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ Z) * A) :=
              trace_hsAdjoint_eq Ψ Z A
      _ = Matrix.trace (Ψ Z * A) := by
              rw [hΨZstar]
  have hsecond :
      Matrix.trace
          (Matrix.conjTranspose X * hsAdjoint Ψ (A * Ψ X)) =
        Matrix.trace ((Ψ X * Matrix.conjTranspose (Ψ X)) * A) := by
    calc
      Matrix.trace
          (Matrix.conjTranspose X * hsAdjoint Ψ (A * Ψ X))
          = Matrix.trace (Matrix.conjTranspose (Ψ X) * (A * Ψ X)) := by
              simpa using
                trace_hsAdjoint_eq Ψ X (A * Ψ X)
      _ = Matrix.trace ((Matrix.conjTranspose (Ψ X) * A) * Ψ X) := by
              rw [Matrix.mul_assoc]
      _ = Matrix.trace (Ψ X * (Matrix.conjTranspose (Ψ X) * A)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((Ψ X * Matrix.conjTranspose (Ψ X)) * A) := by
              rw [Matrix.mul_assoc]
  have hgoal :
      Complex.re (Matrix.trace
        (Matrix.conjTranspose X *
          (((leftMul (hsAdjoint Ψ A)) -
              ((hsAdjoint Ψ).comp ((leftMul A).comp Ψ))) X))) =
        Complex.re (Matrix.trace (P * A)) := by
    change Complex.re (Matrix.trace
        (Matrix.conjTranspose X * (hsAdjoint Ψ A * X - hsAdjoint Ψ (A * Ψ X)))) =
      Complex.re (Matrix.trace (P * A))
    rw [Matrix.mul_sub, Matrix.trace_sub]
    rw [hP_eq]
    rw [Matrix.sub_mul, Matrix.trace_sub]
    rw [Complex.sub_re, Complex.sub_re]
    rw [hfirst, hsecond]
  rw [hgoal]
  exact htrace_re

end

end Quantum.TraceInequality.Loewner.HiaiPetz
