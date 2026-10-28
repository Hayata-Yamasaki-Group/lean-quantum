/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.MultiplicativeDomain
import Quantum.TraceInequality.HansenPedersen.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetzTheorem.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Basic

/-!
# Output-support corner reduction of the multiplicative domain

Membership in the adjoint multiplicative domain descends to the output-support
corner algebra: `inAdjointMultiplicativeDomain_outputSupportCorner`.
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology Interval
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private theorem hsAdjoint_outputSupport_corner_eq {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ m) :
    (hsAdjoint Φ) (outputSupportProj Φ * Y * outputSupportProj Φ) =
      (hsAdjoint Φ) Y := by
  simpa [matrixCornerProj_apply] using
    hsAdjoint_matrixCornerProj_eq Φ hPos Y

private theorem hsAdjoint_outputSupport_left_eq {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ m) :
    (hsAdjoint Φ) (outputSupportProj Φ * Y) = (hsAdjoint Φ) Y := by
  let P : Mₙ m := outputSupportProj Φ
  have hPidem : P * P = P := by
    simpa [P] using OutputSupportProj.idempotent Φ
  have hcorner :=
    hsAdjoint_matrixCornerProj_eq Φ hPos (P * Y)
  have hproj : matrixCornerProj P (P * Y) = P * Y * P := by
    calc
      matrixCornerProj P (P * Y) = P * (P * (Y * P)) := by
        simp [matrixCornerProj_apply, Matrix.mul_assoc]
      _ = P * (Y * P) := by rw [← Matrix.mul_assoc, hPidem]
      _ = P * Y * P := by simp [Matrix.mul_assoc]
  calc
    (hsAdjoint Φ) (P * Y)
        = (hsAdjoint Φ) (matrixCornerProj P (P * Y)) := hcorner.symm
    _ = (hsAdjoint Φ) (P * Y * P) := by rw [hproj]
    _ = (hsAdjoint Φ) Y := by
          simpa [P] using hsAdjoint_outputSupport_corner_eq Φ hPos Y

private theorem hsAdjoint_outputSupport_right_eq {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ m) :
    (hsAdjoint Φ) (Y * outputSupportProj Φ) = (hsAdjoint Φ) Y := by
  let P : Mₙ m := outputSupportProj Φ
  have hPidem : P * P = P := by
    simpa [P] using OutputSupportProj.idempotent Φ
  have hcorner :=
    hsAdjoint_matrixCornerProj_eq Φ hPos (Y * P)
  have hproj : matrixCornerProj P (Y * P) = P * Y * P := by
    calc
      matrixCornerProj P (Y * P) = P * ((Y * P) * P) := by
        simp [matrixCornerProj_apply, Matrix.mul_assoc]
      _ = P * (Y * P) := by rw [Matrix.mul_assoc, hPidem]
      _ = P * Y * P := by simp [Matrix.mul_assoc]
  calc
    (hsAdjoint Φ) (Y * P)
        = (hsAdjoint Φ) (matrixCornerProj P (Y * P)) := hcorner.symm
    _ = (hsAdjoint Φ) (P * Y * P) := by rw [hproj]
    _ = (hsAdjoint Φ) Y := by
          simpa [P] using hsAdjoint_outputSupport_corner_eq Φ hPos Y

private theorem inAdjointMultiplicativeDomain_outputSupportCorner_raw
    {n m : ℕ} {Φ : HSMap n m} (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ)
    {X : Mₙ m} (hmd : InAdjointMultiplicativeDomain Φ X)
    (Xcorner : matrixCornerSubmodule (outputSupportProj Φ))
    (hXcorner : Xcorner.1 = matrixCornerProj (outputSupportProj Φ) X) :
    InAdjointMultiplicativeDomain Φ Xcorner.1 := by
  let P : Mₙ m := outputSupportProj Φ
  have hPproj : IsMatrixProj P := by
    simpa [P] using OutputSupportProj.isProj Φ
  have hPidem : P * P = P := hPproj.1
  have hPstar : Matrix.conjTranspose P = P := by
    simpa [Matrix.star_eq_conjTranspose] using hPproj.2.star_eq
  have hPP (Z : Mₙ m) : P * (P * Z) = P * Z := by
    rw [← Matrix.mul_assoc, hPidem]
  have hXcorner' : Xcorner.1 = P * X * P := by
    simpa [P, matrixCornerProj_apply] using hXcorner
  have hAdjXcorner : (hsAdjoint Φ) Xcorner.1 = (hsAdjoint Φ) X := by
    rw [hXcorner']
    simpa [P] using hsAdjoint_outputSupport_corner_eq Φ hPos X
  constructor
  · have hprod :
        Xcorner.1 * Matrix.conjTranspose Xcorner.1 =
          P * (X * P * Matrix.conjTranspose X) * P := by
      rw [hXcorner']
      simp [Matrix.conjTranspose_mul, hPstar, hPP, Matrix.mul_assoc]
    calc
      (hsAdjoint Φ) (Xcorner.1 * Matrix.conjTranspose Xcorner.1)
          = (hsAdjoint Φ) (X * P * Matrix.conjTranspose X) := by
              rw [hprod]
              simpa [P] using
                hsAdjoint_outputSupport_corner_eq Φ hPos (X * P * Matrix.conjTranspose X)
      _ = (hsAdjoint Φ) (X * Matrix.conjTranspose (X * P)) := by
            simp [Matrix.conjTranspose_mul, hPstar, Matrix.mul_assoc]
      _ = (hsAdjoint Φ) X *
            Matrix.conjTranspose ((hsAdjoint Φ) (X * P)) :=
            hsAdjoint_mul_conjTranspose_of_inAdjointMultiplicativeDomain
              (Φ := Φ) (X := X) (Y := X * P) hSch hmd
      _ = (hsAdjoint Φ) X * Matrix.conjTranspose ((hsAdjoint Φ) X) := by
            rw [hsAdjoint_outputSupport_right_eq Φ hPos X]
      _ = (hsAdjoint Φ) Xcorner.1 *
            Matrix.conjTranspose ((hsAdjoint Φ) Xcorner.1) := by
            rw [hAdjXcorner]
  · have hprod :
        Matrix.conjTranspose Xcorner.1 * Xcorner.1 =
          P * (Matrix.conjTranspose X * P * X) * P := by
      rw [hXcorner']
      simp [Matrix.conjTranspose_mul, hPstar, hPP, Matrix.mul_assoc]
    calc
      (hsAdjoint Φ) (Matrix.conjTranspose Xcorner.1 * Xcorner.1)
          = (hsAdjoint Φ) (Matrix.conjTranspose X * P * X) := by
              rw [hprod]
              simpa [P] using
                hsAdjoint_outputSupport_corner_eq Φ hPos
                  (Matrix.conjTranspose X * P * X)
      _ = (hsAdjoint Φ) (Matrix.conjTranspose X * (P * X)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.conjTranspose ((hsAdjoint Φ) X) * ((hsAdjoint Φ) (P * X)) :=
            hsAdjoint_conjTranspose_mul_of_inAdjointMultiplicativeDomain
              (Φ := Φ) (X := X) (Y := P * X) hSch hmd
      _ = Matrix.conjTranspose ((hsAdjoint Φ) X) * ((hsAdjoint Φ) X) := by
            rw [hsAdjoint_outputSupport_left_eq Φ hPos X]
      _ = Matrix.conjTranspose ((hsAdjoint Φ) Xcorner.1) * ((hsAdjoint Φ) Xcorner.1) := by
            rw [hAdjXcorner]

/-- Membership in the adjoint multiplicative domain descends to the output-support
corner algebra: if `X` lies in the adjoint multiplicative domain of `Φ` and `Xcorner`
is the output-support corner projection of `X`, then the corner-model image
`(outputSupportMatrixCornerModel Φ).toMat Xcorner` lies in the adjoint multiplicative
domain of the output-support reduced map `outputSupportReducedMap Φ hPos`.
Source: Hiai, Theorem 6.3 (reduction step). -/
theorem inAdjointMultiplicativeDomain_outputSupportCorner
    {n m : ℕ} {Φ : HSMap n m} (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ)
    {X : Mₙ m} (hmd : InAdjointMultiplicativeDomain Φ X)
    (Xcorner : matrixCornerSubmodule (outputSupportProj Φ))
    (hXcorner : Xcorner.1 = matrixCornerProj (outputSupportProj Φ) X) :
    InAdjointMultiplicativeDomain (outputSupportReducedMap Φ hPos)
      ((outputSupportMatrixCornerModel Φ).toMat Xcorner) := by
  let model : MatrixCornerModel (outputSupportProj Φ) := outputSupportMatrixCornerModel Φ
  let Y : Mₙ model.dim := model.toMat Xcorner
  have hraw :=
    inAdjointMultiplicativeDomain_outputSupportCorner_raw
      (Φ := Φ) hPos hSch hmd Xcorner hXcorner
  constructor
  · have hsymm :
        ((model.toMat.symm (Y * Matrix.conjTranspose Y)).1) =
          Xcorner.1 * Matrix.conjTranspose Xcorner.1 := by
      have h :=
        congrArg Subtype.val (model.toMat_symm_mul_star Y)
      simpa [Y, Matrix.star_eq_conjTranspose] using h
    calc
      (hsAdjoint (outputSupportReducedMap Φ hPos)) (Y * Matrix.conjTranspose Y)
          = (hsAdjoint Φ) (Xcorner.1 * Matrix.conjTranspose Xcorner.1) := by
              rw [outputSupportReducedMap_hsAdjoint_apply]
              rw [hsymm]
      _ = (hsAdjoint Φ) Xcorner.1 *
            Matrix.conjTranspose ((hsAdjoint Φ) Xcorner.1) := hraw.1
      _ = (hsAdjoint (outputSupportReducedMap Φ hPos)) Y *
            Matrix.conjTranspose ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y) := by
            simp [Y, model, outputSupportReducedMap_hsAdjoint_apply]
  · have hsymm :
        ((model.toMat.symm (Matrix.conjTranspose Y * Y)).1) =
          Matrix.conjTranspose Xcorner.1 * Xcorner.1 := by
      have h :=
        congrArg Subtype.val (MatrixCornerModel.toMat_symm_star_mul model Y)
      simpa [Y, Matrix.star_eq_conjTranspose] using h
    calc
      (hsAdjoint (outputSupportReducedMap Φ hPos)) (Matrix.conjTranspose Y * Y)
          = (hsAdjoint Φ) (Matrix.conjTranspose Xcorner.1 * Xcorner.1) := by
              rw [outputSupportReducedMap_hsAdjoint_apply]
              rw [hsymm]
      _ = Matrix.conjTranspose ((hsAdjoint Φ) Xcorner.1) *
            ((hsAdjoint Φ) Xcorner.1) := hraw.2
      _ = Matrix.conjTranspose ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y) *
            ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y) := by
            simp [Y, model, outputSupportReducedMap_hsAdjoint_apply]

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
