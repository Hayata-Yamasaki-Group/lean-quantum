/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- This file is long but is not split: its private declarations are specific to the proof
-- routes of Theorems 6.2 and 6.4, and splitting the file or making them public would add API
-- without benefit. The eigenrow/`vecMulVec`/`matrixCfcR` lemmas shared with `MidpointKernel`
-- are public.

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.HiaiPetz.PowerTraceRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridgeRetained
import Quantum.TraceInequality.HansenPedersen.MapVocabulary
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.Surface
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Surface
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus

/-!
# Matrix functional calculus layer for the Hiai–Petz inequalities

Matrix-level functional-calculus machinery connecting the several equivalent
conditions of Hiai–Petz Theorem 6.2 and feeding the trace-power monotonicity and
concavity results.  It packages the operator/matrix monotonicity conditions and
the strictly-positive direct and inverse map inequalities as propositions, and it
identifies the `J`-operator trace-power functionals with the Lieb and inverse
trace-power functionals under the unit and positive-definite regimes.

## Main definitions

* `AllHOperatorMonotoneOnIoi` / `MatrixMonotoneCondition`: the all-Hilbert-space
  and matrix-only forms of Theorem 6.2 condition (i).
* `StrictlyPositiveDirectInequality` / `StrictlyPositiveInverseInequality`: the
  direct and inverse map inequalities in the strictly-positive regime.
* `JointConcavity`: the joint-concavity condition for a scalar function `f`.

## Main results

* `jPowerTrace_unit_eq_liebTracePower` /
  `jInversePowerTrace_unit_eq_inverseTracePower` and their positive-definite
  extensions `..._eq_..._of_posDef`: identification of the `J`-operator
  trace-power functionals with the Lieb / inverse trace-power functionals.
* `matrix_midpoint_concave_Ioi_of_jointConcavity`: joint concavity of `f`
  transfers to matrix midpoint concavity of `matrixCfcR f` in the Loewner order
  on the positive spectrum.

## Implementation notes

The private-declaration dependency graph forms a single indivisible cluster
spanning most of the file (see the NOTE below), so the module is kept unsplit.

## References

* Hiai, Theorem 6.2.
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

private theorem matrixCfcR_powerFn_one {n : ℕ} (p : ℝ) :
    HansenPedersen.matrixCfcR (powerFn p) (1 : Mₙ n) = 1 := by
  ext i j
  simp [powerFn, HansenPedersen.matrixCfcR]

private theorem matrixCfcR_inv_powerFn_eq_matrixPower_neg
    {n : ℕ} (p : ℝ) {A : Mₙ n} (hA : Matrix.PosDef A) :
    HansenPedersen.matrixCfcR (fun x : ℝ => (powerFn p x)⁻¹) A =
      matrixPower (-p) A := by
  classical
  unfold matrixPower HansenPedersen.matrixCfcR
  apply congrArg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
  apply cfc_congr
  intro x hx
  have hxC :
      (x : ℂ) ∈ spectrum ℂ (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)) := by
    rwa [← spectrum.algebraMap_mem_iff ℂ]
  have hxCA : (x : ℂ) ∈ spectrum ℂ A := by
    simpa using
      (show
        (x : ℂ) ∈ spectrum ℂ
            (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)) ↔
          (x : ℂ) ∈ spectrum ℂ A from by
            rw [AlgEquiv.spectrum_eq
              ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) A])
        |>.mp hxC
  have hxA : x ∈ spectrum ℝ A := spectrum.of_algebraMap_mem ℂ hxCA
  let hAh : A.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hA.1
  have hposDef : A.PosDef := hA
  have hxpos : 0 < x := by
    have hxrange : x ∈ Set.range hAh.eigenvalues := by
      simpa [hAh.spectrum_real_eq_range_eigenvalues] using hxA
    rcases hxrange with ⟨i, rfl⟩
    exact (hAh.posDef_iff_eigenvalues_pos.mp hposDef i)
  simpa [powerFn] using (Real.rpow_neg (le_of_lt hxpos) p).symm

/-- Closed trace-power bridge for the unit right input.  This is the first
functional-calculus closed-form step in the proof of Theorem 6.3. -/
theorem jPowerTrace_unit_eq_liebTracePower
    {n : ℕ} (p : ℝ) {A X : Mₙ n} (hA : IsSelfAdjoint A) :
    jPowerTrace p A (1 : Mₙ n) X = liebTracePower p A (1 : Mₙ n) X := by
  rw [jPowerTrace_eq_quasiEntropy_powerFn (p := p) (A := A) (B := (1 : Mₙ n))
    (X := X) (Matrix.PosDef.one (R := ℂ) (n := Fin n))]
  rw [quasiEntropy_one_right (powerFn p) hA]
  simp [liebTracePower, powerTrace, matrixPower, matrixCfcR_powerFn_one,
    Matrix.mul_assoc]

private theorem jOperatorInv_one_eq_leftMul_matrixCfcR_inv
    {n : ℕ} (p : ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) :
    jOperatorInv (powerFn p) A (1 : Mₙ n) =
      leftMul (HansenPedersen.matrixCfcR (fun x : ℝ => (powerFn p x)⁻¹) A) := by
  calc
    jOperatorInv (powerFn p) A (1 : Mₙ n)
        = hsCfcR (fun x : ℝ => (powerFn p x)⁻¹) (leftMul A) *
            rightMul (((1 : Mₙ n)⁻¹)) := by
            simp [jOperatorInv, jArg_one_eq_leftMul]
    _ = leftMul (HansenPedersen.matrixCfcR (fun x : ℝ => (powerFn p x)⁻¹) A) *
          rightMul (1 : Mₙ n) := by
          rw [cfc_leftMul_eq_leftMul_matrixCfcR (fun x : ℝ => (powerFn p x)⁻¹) hA]
          simp
    _ = leftMul (HansenPedersen.matrixCfcR (fun x : ℝ => (powerFn p x)⁻¹) A) := by
          rw [rightMul_one]
          simp

/-- Closed inverse trace-power bridge for the unit right input.  This is the inverse
counterpart of `jPowerTrace_unit_eq_liebTracePower` in Theorem 6.3. -/
theorem jInversePowerTrace_unit_eq_inverseTracePower
    {n : ℕ} (p : ℝ) {A X : Mₙ n} (hA : Matrix.PosDef A) :
    jInversePowerTrace p A (1 : Mₙ n) X =
      inverseTracePower p A (1 : Mₙ n) X := by
  rw [jInversePowerTrace_eq_jOperatorInv_powerFn_qform (p := p) (A := A) (B := (1 : Mₙ n))
    (X := X) (Matrix.PosDef.one (R := ℂ) (n := Fin n))]
  rw [jOperatorInv_one_eq_leftMul_matrixCfcR_inv (p := p) (A := A) hA.1]
  rw [matrixCfcR_inv_powerFn_eq_matrixPower_neg (p := p) hA]
  simp [inverseTracePower, powerTrace, matrixPower, matrixCfcR_powerFn_one, Matrix.mul_assoc]

end HiaiPetz
