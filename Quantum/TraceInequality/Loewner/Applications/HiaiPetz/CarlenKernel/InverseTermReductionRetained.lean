/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.AdjointHelpers
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

/-- A unital Hilbert--Schmidt map has a trace-preserving Hilbert--Schmidt adjoint. -/
theorem hsAdjoint_tracePreserving_of_isUnitalMap {n m : ℕ} {Ψ : HSMap n m}
    (hΨ : IsUnitalMap Ψ) :
    _root_.HiaiPetz.TracePreserving (hsAdjoint Ψ) := by
  intro Z
  have h := trace_hsAdjoint_eq Ψ (1 : Mₙ n) Z
  have hstar : Matrix.conjTranspose (Ψ (1 : Mₙ n)) = (1 : Mₙ m) := by
    rw [hΨ]
    simp
  simpa [hstar] using h

/--
Kadison--Choi Schwarz gives the Hilbert--Schmidt quadratic-form inequality for
the right-multiplication endpoint term.
-/
theorem rightMul_dpi_of_isUnitalTwoPositiveMap {n m : ℕ} (Ψ : HSMap n m)
    {B : Mₙ m} (hΨ : IsUnitalTwoPositiveMap Ψ) (hB : MatrixPosDef B) :
    HSLE
      ((hsAdjoint Ψ).comp ((rightMul B).comp Ψ))
      (rightMul (hsAdjoint Ψ B)) := by
  rw [HSLE]
  intro X
  let P : Mₙ m :=
    Ψ (Matrix.conjTranspose X * X) - Matrix.conjTranspose (Ψ X) * Ψ X
  have hP : P.PosSemidef := by
    simpa [P] using kadisonChoi_schwarz_of_isUnitalTwoPositiveMap hΨ X
  have htrace_nonneg : 0 ≤ Matrix.trace (P * B) :=
    matrix_trace_mul_nonneg_of_posSemidef hP (matrixPosDef_posDef hB).posSemidef
  have htrace_re : 0 ≤ Complex.re (Matrix.trace (P * B)) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have hfirst :
      Matrix.trace (Matrix.conjTranspose X * (X * hsAdjoint Ψ B)) =
        Matrix.trace (Ψ (Matrix.conjTranspose X * X) * B) := by
    let Z : Mₙ n := Matrix.conjTranspose X * X
    have hZstar : Matrix.conjTranspose Z = Z := by
      simp [Z, Matrix.conjTranspose_mul]
    have hΨZstar : Matrix.conjTranspose (Ψ Z) = Ψ Z := by
      rw [← map_conjTranspose_of_isTwoPositiveMap hΨ.2 Z, hZstar]
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
Kadison--Choi Schwarz gives the Hilbert--Schmidt quadratic-form inequality for
the left-multiplication slope term.
-/
theorem leftMul_dpi_of_isUnitalTwoPositiveMap {n m : ℕ} (Ψ : HSMap n m)
    {A : Mₙ m} (hΨ : IsUnitalTwoPositiveMap Ψ) (hA : MatrixPosDef A) :
    HSLE
      ((hsAdjoint Ψ).comp ((leftMul A).comp Ψ))
      (leftMul (hsAdjoint Ψ A)) := by
  rw [HSLE]
  intro X
  let Y : Mₙ n := Matrix.conjTranspose X
  let P : Mₙ m := Ψ (Matrix.conjTranspose Y * Y) - Matrix.conjTranspose (Ψ Y) * Ψ Y
  have hP : P.PosSemidef := by
    simpa [P] using kadisonChoi_schwarz_of_isUnitalTwoPositiveMap hΨ Y
  have hP_eq :
      P = Ψ (X * Matrix.conjTranspose X) - Ψ X * Matrix.conjTranspose (Ψ X) := by
    have hYmap : Ψ Y = Matrix.conjTranspose (Ψ X) := by
      simpa [Y] using map_conjTranspose_of_isTwoPositiveMap hΨ.2 X
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
      rw [← map_conjTranspose_of_isTwoPositiveMap hΨ.2 Z, hZstar]
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

/--
The two linear terms in Carlen's `G_f` decomposition satisfy the
Hilbert--Schmidt quadratic-form DPI under a unital two-positive map.
-/
theorem gOperator_linear_terms_dpi_of_isUnitalTwoPositiveMap {n m : ℕ} (Ψ : HSMap n m)
    {X Y : Mₙ m} (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    HSLE
        ((hsAdjoint Ψ).comp ((leftMul Y).comp Ψ))
        (leftMul (hsAdjoint Ψ Y)) ∧
      HSLE
        ((hsAdjoint Ψ).comp ((rightMul X).comp Ψ))
        (rightMul (hsAdjoint Ψ X)) :=
  ⟨leftMul_dpi_of_isUnitalTwoPositiveMap Ψ hΨ hY,
    rightMul_dpi_of_isUnitalTwoPositiveMap Ψ hΨ hX⟩

end

end Quantum.TraceInequality.Loewner.HiaiPetz
