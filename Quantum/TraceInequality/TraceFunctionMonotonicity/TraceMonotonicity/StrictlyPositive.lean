/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.TraceFunctionMonotonicity.BasicTheorems
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HiaiPetz.Interface.Strict
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.SelectedProvider
import Quantum.TraceInequality.TraceFunctionMonotonicity.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.SharedVocabulary

/-!
# Strict-output trace-power reduction
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- The power function is continuous on `(0,∞)` for every real exponent. -/
@[fun_prop] theorem powerFn_continuousOn_Ioi (p : ℝ) :
    ContinuousOn (powerFn p) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- The power function is strictly positive on `(0,∞)` for every real exponent. -/
theorem powerFn_pos_Ioi (p : ℝ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < powerFn p x := by
  intro x hx
  exact Real.rpow_pos_of_pos hx p

/-- Löwner--Heinz gives all-Hilbert-space operator monotonicity of `x ↦ x^p` on `(0,∞)`. -/
theorem powerFn_allHOperatorMonotone_Ioi {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ)) (powerFn p) := by
  intro K _ _ _ _ _
  have hmonoIci :
      HansenPedersen.HOperatorMonotoneOnInterval K (Set.Ici (0 : ℝ)) (powerFn p) := by
    simpa [powerFn] using
      (HansenPedersen.operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici
        (ℋ := K)
        (LownerHeinzTheorem.power_Icc_zero_one_operatorMonotoneOn_Ici
          (ℋ := K) p hp))
  intro A B hA hB hσA hσB hAB
  apply hmonoIci hA hB
  · intro x hx
    exact le_of_lt (show (0 : ℝ) < x from hσA hx)
  · intro x hx
    exact le_of_lt (show (0 : ℝ) < x from hσB hx)
  · exact hAB

/-- Power functions with exponent in `[0,1]` satisfy Hiai--Petz condition (i). -/
theorem powerFn_operatorMonotone_of_Icc {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi (powerFn p) :=
  powerFn_allHOperatorMonotone_Ioi hp

/-- Direct `J`-form inequality under the explicit condition (i) hypothesis.
Source: Hiai, proof of Theorem 6.3. -/
theorem jPowerTrace_le_map_of_operatorMonotone :
    ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
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
      jPowerTrace p A B ((hsAdjoint Φ) X) ≤
        jPowerTrace p (Φ A) (Φ B) X := by
  intro n m Φ p A B X hf hpos hI hPos hTrace hSch hA hB hΦ1 hΦB
  have hImat : ProofNet.MatrixMonotone (powerFn p) :=
    ProofNet.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi hI
  have hEquivalences := ProofNet.strictDPIEquivalences (f := powerFn p) hf hpos
  have hIII : ProofNet.StrictDirectDPI (powerFn p) :=
    hEquivalences.strictInverseDPI_iff_strictDirectDPI.mp
      (hEquivalences.matrixMonotone_iff_strictInverseDPI.mp hImat)
  have hHS :
      (show HSOp m from
        Φ.comp ((jOperator (powerFn p) A B).comp (hsAdjoint Φ))) ≤
        (jOperator (powerFn p) (Φ A) (Φ B)) :=
    hIII Φ (A := A) (B := B) hPos hTrace hSch hA hB hΦ1
  have hq :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator (powerFn p) A B).comp (hsAdjoint Φ))) X))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperator (powerFn p) (Φ A) (Φ B)) X))) := by
    exact hsQForm_le_of_le hHS X
  have hsource :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator (powerFn p) A B).comp (hsAdjoint Φ))) X))) =
        jPowerTrace p A B ((hsAdjoint Φ) X) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator (powerFn p) A B).comp (hsAdjoint Φ))) X)))
          =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) *
              ((jOperator (powerFn p) A B) ((hsAdjoint Φ) X)))) := by
            simpa using hsQForm_comp_hsAdjoint Φ (jOperator (powerFn p) A B) X
      _ = jPowerTrace p A B ((hsAdjoint Φ) X) := by
            simpa [jPowerTrace] using
              hsQForm_jOperator_of_posDef (f := powerFn p) (A := A) (B := B)
                hB ((hsAdjoint Φ) X) ((hsAdjoint Φ) X)
  have htarget :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperator (powerFn p) (Φ A) (Φ B)) X))) =
        jPowerTrace p (Φ A) (Φ B) X := by
    simpa [jPowerTrace] using
      hsQForm_jOperator_of_posDef (f := powerFn p) (A := Φ A) (B := Φ B) hΦB X X
  calc
    jPowerTrace p A B ((hsAdjoint Φ) X)
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((Φ.comp ((jOperator (powerFn p) A B).comp (hsAdjoint Φ))) X))) := hsource.symm
    _ ≤ Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperator (powerFn p) (Φ A) (Φ B)) X))) := hq
    _ = jPowerTrace p (Φ A) (Φ B) X := htarget

/-- Direct `J`-form inequality for exponents in `[0,1]`.
Source: Hiai, Theorem 6.3. -/
theorem jPowerTrace_le_map :
    ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
      p ∈ Set.Icc (0 : ℝ) 1 →
      IsPositiveMap Φ →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      Matrix.PosDef (Φ (1 : Mₙ n)) →
      Matrix.PosDef (Φ B) →
      jPowerTrace p A B ((hsAdjoint Φ) X) ≤
        jPowerTrace p (Φ A) (Φ B) X := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hΦB
  exact jPowerTrace_le_map_of_operatorMonotone Φ
    (p := p) (A := A) (B := B) (X := X)
    (powerFn_continuousOn_Ioi p) (powerFn_pos_Ioi p)
    (powerFn_operatorMonotone_of_Icc hp) hPos hTrace hSch hA hB hΦ1 hΦB

/-- Strict-output trace-power form of Theorem 6.3(1), in the positive-definite
full-support regime.

The Lean statement holds under weaker assumptions than the source: positive
definiteness of `Φ A` and `Φ B` is derived internally. The source form follows
by specialization.
Source: Hiai, Theorem 6.3. -/
def DirectTracePowerStrictlyPositive : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    liebTracePower p A B ((hsAdjoint Φ) X) ≤
      liebTracePower p (Φ A) (Φ B) X

/-- Direct trace-power inequality in the strict-output positive-definite regime.
Source: Hiai, Theorem 6.3. -/
theorem directTracePowerStrictlyPositive :
    DirectTracePowerStrictlyPositive := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1
  have hΦA : Matrix.PosDef (Φ A) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hj :
      jPowerTrace p A B ((hsAdjoint Φ) X) ≤
        jPowerTrace p (Φ A) (Φ B) X :=
    jPowerTrace_le_map Φ (p := p) (A := A) (B := B) (X := X)
      hp hPos hTrace hSch hA hB hΦ1 hΦB
  have hsource :
      jPowerTrace p A B ((hsAdjoint Φ) X) =
        liebTracePower p A B ((hsAdjoint Φ) X) :=
    jPowerTrace_eq_liebTracePower_of_posDef (p := p) hA hB
  have htarget :
      jPowerTrace p (Φ A) (Φ B) X =
        liebTracePower p (Φ A) (Φ B) X :=
    jPowerTrace_eq_liebTracePower_of_posDef (p := p) hΦA hΦB
  change liebTracePower p A B ((hsAdjoint Φ) X) ≤
    liebTracePower p (Φ A) (Φ B) X
  calc
    liebTracePower p A B ((hsAdjoint Φ) X)
        = jPowerTrace p A B ((hsAdjoint Φ) X) := hsource.symm
    _ ≤ jPowerTrace p (Φ A) (Φ B) X := hj
    _ = liebTracePower p (Φ A) (Φ B) X := htarget

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
