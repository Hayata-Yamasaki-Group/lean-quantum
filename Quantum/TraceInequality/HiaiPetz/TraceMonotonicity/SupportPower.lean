/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Semidefinite

/-!
# Support-power trace monotonicity surface
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Unified output-support support-power form of Theorem 6.3(1).

This statement packages the open interval and the two support-projection endpoint
theorems using the `supportLiebTracePower` API.
Source: Hiai, Theorem 6.3. -/
def DirectSupportTracePowerOutputSupport : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    0 ≤ A →
    0 ≤ B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      supportLiebTracePower p A B ((hsAdjoint Ψ) X) ≤
        supportLiebTracePower p (Ψ A) (Ψ B) X

/-- Direct output-support support-power theorem.
Source: Hiai, Theorem 6.3. -/
theorem directSupportTracePowerOutputSupport :
    DirectSupportTracePowerOutputSupport := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨA_nonneg : 0 ≤ Ψ A := hΨpos hA
  have hΨB_nonneg : 0 ≤ Ψ B := hΨpos hB
  by_cases hp0 : p = 0
  · subst p
    have hraw :=
      trace_supportProj_le_map_zero Φ
        (A := A) (B := B) hPos hTrace hSch hA hB (X := X)
    have hleft :
        supportLiebTracePower 0 (Ψ A) (Ψ B) X =
          Complex.re
            (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj (Ψ A) * X *
              matrixPower 1 (Ψ B))) :=
      supportLiebTracePower_zero_eq_trace_supportProj hΨA_nonneg hΨB_nonneg
    have hright :
        supportLiebTracePower 0 A B ((hsAdjoint Ψ) X) =
          Complex.re
            (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixSupportProj A *
              ((hsAdjoint Ψ) X) * matrixPower 1 B)) :=
      supportLiebTracePower_zero_eq_trace_supportProj hA hB
    calc
      supportLiebTracePower 0 A B ((hsAdjoint Ψ) X)
          =
        Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixSupportProj A *
            ((hsAdjoint Ψ) X) * matrixPower 1 B)) := hright
      _ ≤
        Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj (Ψ A) * X *
            matrixPower 1 (Ψ B))) := by
          simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
            MatrixCornerModel.transportMap] using hraw
      _ = supportLiebTracePower 0 (Ψ A) (Ψ B) X := hleft.symm
  by_cases hp1 : p = 1
  · subst p
    have hraw :=
      trace_supportProj_le_map_one Φ
        (A := A) (B := B) hPos hTrace hSch hA hB (X := X)
    have hleft :
        supportLiebTracePower 1 (Ψ A) (Ψ B) X =
          Complex.re
            (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 (Ψ A) * X *
              matrixSupportProj (Ψ B))) :=
      supportLiebTracePower_one_eq_trace_supportProj hΨA_nonneg hΨB_nonneg
    have hright :
        supportLiebTracePower 1 A B ((hsAdjoint Ψ) X) =
          Complex.re
            (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixPower 1 A *
              ((hsAdjoint Ψ) X) * matrixSupportProj B)) :=
      supportLiebTracePower_one_eq_trace_supportProj hA hB
    calc
      supportLiebTracePower 1 A B ((hsAdjoint Ψ) X)
          =
        Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixPower 1 A *
            ((hsAdjoint Ψ) X) * matrixSupportProj B)) := hright
      _ ≤
        Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 (Ψ A) * X *
            matrixSupportProj (Ψ B))) := by
          simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
            MatrixCornerModel.transportMap] using hraw
      _ = supportLiebTracePower 1 (Ψ A) (Ψ B) X := hleft.symm
  have hpIoo : p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
  have hraw :=
    liebTracePower_le_map_semidef_Ioo Φ
      (p := p) (A := A) (B := B) hpIoo hPos hTrace hSch hA hB (X := X)
  have hleft :
      supportLiebTracePower p (Ψ A) (Ψ B) X =
        liebTracePower p (Ψ A) (Ψ B) X :=
    supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hpIoo hΨA_nonneg hΨB_nonneg
  have hright :
      supportLiebTracePower p A B ((hsAdjoint Ψ) X) =
        liebTracePower p A B ((hsAdjoint Ψ) X) :=
    supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hpIoo hA hB
  calc
    supportLiebTracePower p A B ((hsAdjoint Ψ) X)
        = liebTracePower p A B ((hsAdjoint Ψ) X) := hright
    _ ≤ liebTracePower p (Ψ A) (Ψ B) X := by
          simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
            MatrixCornerModel.transportMap] using hraw
    _ = supportLiebTracePower p (Ψ A) (Ψ B) X := hleft.symm

/-- Inverse output-support trace-power theorem.
Source: Hiai, Theorem 6.3. -/
theorem inverseTracePowerOutputSupport :
    InverseTracePowerOutputSupport := by
  intro n m Φ p A B X hp
  dsimp
  intro hPos hTrace hSch hA hB
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (inverseTracePowerStrictlyPositive Ψ (p := p) (A := A) (B := B) (X := X)
      hp hΨpos hΨtrace hΨsch hA hB hΨ1)

/-- Aggregate output-support direct/inverse trace-power theorem.
Source: Hiai, Theorem 6.3. -/
theorem directInverseTracePowerOutputSupport :
    DirectTracePowerOutputSupport ∧ InverseTracePowerOutputSupport := by
  exact ⟨directTracePowerOutputSupport, inverseTracePowerOutputSupport⟩

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
