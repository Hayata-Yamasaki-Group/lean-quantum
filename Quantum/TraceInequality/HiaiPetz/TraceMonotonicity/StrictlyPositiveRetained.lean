/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Basic
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.TraceFunctionMonotonicity.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridgeRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive

/-!
# Strict-output trace-power reduction
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Inverse `J`-form inequality under the explicit condition (i) hypothesis.
Source: Hiai, proof of Theorem 6.3. -/
theorem jInversePowerTrace_map_le_of_operatorMonotone :
    ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
      ContinuousOn (powerFn p) (Set.Ioi (0 : ℝ)) →
      (∀ x ∈ Set.Ioi (0 : ℝ), 0 < powerFn p x) →
      QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi (powerFn p) →
      IsPositiveMap Φ →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      Matrix.PosDef (Φ (1 : Mₙ n)) →
      Matrix.PosDef (Φ B) →
      jInversePowerTrace p (Φ A) (Φ B) (Φ X) ≤
        jInversePowerTrace p A B X := by
  intro n m Φ p A B X hf hpos hI hPos hTrace hSch hA hB hΦ1 hΦB
  have hImat : ProofNet.MatrixMonotone (powerFn p) :=
    ProofNet.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi hI
  have hEquivalences := ProofNet.strictDPIEquivalences (f := powerFn p) hf hpos
  have hII : ProofNet.StrictInverseDPI (powerFn p) :=
    hEquivalences.matrixMonotone_iff_strictInverseDPI.mp hImat
  have hIII : ProofNet.StrictDirectDPI (powerFn p) :=
    hEquivalences.strictInverseDPI_iff_strictDirectDPI.mp hII
  have hHS :
      (show HSOp n from
        (hsAdjoint Φ).comp ((jOperatorInv (powerFn p) (Φ A) (Φ B)).comp Φ)) ≤
        (jOperatorInv (powerFn p) A B) :=
    hII Φ (A := A) (B := B) hPos hTrace hSch hA hB hΦ1
  have hq :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint Φ).comp ((jOperatorInv (powerFn p) (Φ A) (Φ B)).comp Φ)) X))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperatorInv (powerFn p) A B) X))) := by
    exact hsQForm_le_of_le hHS X
  have hleft :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint Φ).comp ((jOperatorInv (powerFn p) (Φ A) (Φ B)).comp Φ)) X))) =
        jInversePowerTrace p (Φ A) (Φ B) (Φ X) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint Φ).comp ((jOperatorInv (powerFn p) (Φ A) (Φ B)).comp Φ)) X)))
          =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (Φ X) *
              ((jOperatorInv (powerFn p) (Φ A) (Φ B)) (Φ X)))) := by
            simpa using hsQForm_hsAdjoint_comp Φ (jOperatorInv (powerFn p) (Φ A) (Φ B)) X
      _ = jInversePowerTrace p (Φ A) (Φ B) (Φ X) := by
            simpa [jInversePowerTrace] using
              hsQForm_jOperatorInv_of_posDef (f := powerFn p) (A := Φ A) (B := Φ B)
                hΦB (Φ X) (Φ X)
  have hright :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperatorInv (powerFn p) A B) X))) =
        jInversePowerTrace p A B X := by
    simpa [jInversePowerTrace] using
      hsQForm_jOperatorInv_of_posDef (f := powerFn p) (A := A) (B := B) hB X X
  calc
    jInversePowerTrace p (Φ A) (Φ B) (Φ X)
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                (((hsAdjoint Φ).comp ((jOperatorInv (powerFn p) (Φ A) (Φ B)).comp Φ)) X))) :=
          hleft.symm
    _ ≤ Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperatorInv (powerFn p) A B) X))) := hq
    _ = jInversePowerTrace p A B X := hright

/-- Inverse `J`-form inequality for exponents in `[0,1]`.
Source: Hiai, Theorem 6.3. -/
theorem jInversePowerTrace_map_le :
    ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
      p ∈ Set.Icc (0 : ℝ) 1 →
      IsPositiveMap Φ →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      Matrix.PosDef (Φ (1 : Mₙ n)) →
      Matrix.PosDef (Φ B) →
      jInversePowerTrace p (Φ A) (Φ B) (Φ X) ≤
        jInversePowerTrace p A B X := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hΦB
  exact jInversePowerTrace_map_le_of_operatorMonotone Φ
    (p := p) (A := A) (B := B) (X := X)
    (powerFn_continuousOn_Ioi p) (powerFn_pos_Ioi p)
    (powerFn_operatorMonotone_of_Icc hp) hPos hTrace hSch hA hB hΦ1 hΦB

/-- Strict-output trace-power form of Theorem 6.3(2), in the positive-definite
full-support regime.

The Lean statement holds under weaker assumptions than the source: positive
definiteness of `Φ A` and `Φ B` is derived internally. The source form follows
by specialization.
Source: Hiai, Theorem 6.3. -/
def InverseTracePowerStrictlyPositive : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    inverseTracePower p (Φ A) (Φ B) (Φ X) ≤
      inverseTracePower p A B X

/-- Inverse trace-power inequality in the strict-output positive-definite regime.
Source: Hiai, Theorem 6.3. -/
theorem inverseTracePowerStrictlyPositive :
    InverseTracePowerStrictlyPositive := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1
  have hΦA : Matrix.PosDef (Φ A) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hj :
      jInversePowerTrace p (Φ A) (Φ B) (Φ X) ≤
        jInversePowerTrace p A B X :=
    jInversePowerTrace_map_le Φ (p := p) (A := A) (B := B) (X := X)
      hp hPos hTrace hSch hA hB hΦ1 hΦB
  have hleft :
      jInversePowerTrace p (Φ A) (Φ B) (Φ X) =
        inverseTracePower p (Φ A) (Φ B) (Φ X) :=
    jInversePowerTrace_eq_inverseTracePower_of_posDef (p := p) hΦA hΦB
  have hright :
      jInversePowerTrace p A B X = inverseTracePower p A B X :=
    jInversePowerTrace_eq_inverseTracePower_of_posDef (p := p) hA hB
  calc
    inverseTracePower p (Φ A) (Φ B) (Φ X)
        = jInversePowerTrace p (Φ A) (Φ B) (Φ X) := hleft.symm
    _ ≤ jInversePowerTrace p A B X := hj
    _ = inverseTracePower p A B X := hright

/-- Aggregate strict-output direct/inverse trace-power theorem.
Local API: one-line wrapper; terminology from Hiai, Theorem 6.3. -/
theorem directInverseTracePowerStrictlyPositive :
    DirectTracePowerStrictlyPositive ∧ InverseTracePowerStrictlyPositive := by
  exact ⟨directTracePowerStrictlyPositive, inverseTracePowerStrictlyPositive⟩

/-- Output-support trace-power form of Theorem 6.3(1), stated through the reduced map
built on a fixed orthonormal matrix realization of the support corner. The reduced output
positive-definiteness follows from positivity and the strict reduced unit.
Source: Hiai, Theorem 6.3. -/
def DirectTracePowerOutputSupport : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      liebTracePower p A B ((hsAdjoint Ψ) X) ≤
        liebTracePower p (Ψ A) (Ψ B) X

/-- Output-support trace-power form of Theorem 6.3(2), using the same fixed orthonormal matrix
realization of the support corner as the book-facing Theorem 6.2 layer.
Source: Hiai, Theorem 6.3. -/
def InverseTracePowerOutputSupport : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    inverseTracePower p (Ψ A) (Ψ B) (Ψ X) ≤
      inverseTracePower p A B X

/-- Direct output-support trace-power theorem.
Source: Hiai, Theorem 6.3. -/
theorem directTracePowerOutputSupport :
    DirectTracePowerOutputSupport := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (directTracePowerStrictlyPositive Ψ (p := p) (A := A) (B := B) (X := X)
      hp hΨpos hΨtrace hΨsch hA hB hΨ1)

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
