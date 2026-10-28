/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
-- Supplies the genuine all-Hilbert-space-to-matrix bridge used by the public wrapper.
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Conditions
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.InverseDirectEquiv

/-!
# From operator monotonicity to the strict-output direct inequality

Packages the core lemma `strictlyPositiveDirect_of_matrixMonotoneCondition` as the
matrix-side implication, then composes it with the genuine all-Hilbert-space-to-matrix
bridge to obtain the public operator-monotone implication for Theorem 6.2 in the
output-nondegenerate case.
-/

namespace HiaiPetz

open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Strict-output data processing from the matrix-monotone condition to the direct inequality.
Source: Hiai, Theorem 6.2, condition (i) implies condition (iii),
output-nondegenerate case. -/
theorem QuasiEntropyDataProcessing.strictlyPositiveDirectInequality_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f →
      QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality f := by
  intro hI n m Φ A B hPos hTr hSch hA hB hΦ1
  exact strictlyPositiveDirect_of_matrixMonotoneCondition (f := f)
    (n := n) (m := m) Φ (A := A) (B := B) hf hpos hI hPos hSch hA hB hΦ1

/-- Strict-output data processing from genuine operator monotonicity to the direct inequality.
Source: Hiai, Theorem 6.2, condition (i) implies condition (iii),
output-nondegenerate case. -/
theorem QuasiEntropyDataProcessing.strictlyPositiveDirectInequality_of_operatorMonotone
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi f →
      QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality f := by
  intro hI
  exact QuasiEntropyDataProcessing.strictlyPositiveDirectInequality_of_matrixMonotoneCondition
    f hf hpos
      (HiaiPetz.MatrixFunctionalCalculus.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi hI)

end MatrixScopedInstances

end HiaiPetz
