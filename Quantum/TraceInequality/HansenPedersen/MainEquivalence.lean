/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
-- Provides `List.TFAE`, `tfae_have`, and `tfae_finish` for the public equivalence surfaces.
import Mathlib.Tactic.TFAE
import Quantum.TraceInequality.HansenPedersen.MatrixFunctionalCalculus
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ResidualEquivalence
import
Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StrictlyPositive.MonotoneToDirect
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.DirectToConcavity
import Quantum.TraceInequality.HiaiPetzTheorem.QuasiEntropyDataProcessing.JointToMonotone

/-!
# Main equivalence of the strictly-positive characterizations

Top-level assembly of Hiai–Petz Theorem 6.2 in the output-nondegenerate case. For a
function `f` that is continuous and strictly positive on `(0, ∞)`, the genuine
all-Hilbert-space operator monotonicity, the output-nondegenerate inverse and direct inequalities,
and joint concavity are equivalent. An extended theorem also includes the matrix-monotone
condition used by the finite-dimensional bridge.

## Main results

* `QuasiEntropyDataProcessing.allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition`:
  the matrix-monotone condition yields operator monotonicity on every complex Hilbert space.
* `QuasiEntropyDataProcessing.strictlyPositive_characterizations`: the full cycle of
  equivalences among the strictly-positive characterizations.
* `QuasiEntropyDataProcessing.strictlyPositive_characterizations_tfae`: the four
  book-facing conditions as a genuine `List.TFAE`.
* `QuasiEntropyDataProcessing.strictlyPositive_characterizations_tfae_with_matrix`:
  the extended five-condition `List.TFAE`.

## References

* Hiai, Theorem 6.2, output-nondegenerate case.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

namespace QuasiEntropyDataProcessing


/-- Strictly positive output characterizations in Hiai–Petz Theorem 6.2,
output-nondegenerate case. The public entry points are the `ProofNet.*` declarations;
`strictlyPositive_characterizations_tfae` is an auxiliary TFAE form of this statement. -/
theorem strictlyPositive_characterizations {f : ℝ → ℝ} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
      (AllHOperatorMonotoneOnIoi f ↔ StrictlyPositiveInverseInequality f) ∧
      (StrictlyPositiveInverseInequality f ↔ StrictlyPositiveDirectInequality f) ∧
      (StrictlyPositiveDirectInequality f ↔ JointConcavity f) ∧
      (JointConcavity f → MatrixMonotoneCondition f) ∧
      (MatrixMonotoneCondition f → AllHOperatorMonotoneOnIoi f) := by
  intro hf hpos
  have hIIiffIII : StrictlyPositiveInverseInequality f ↔ StrictlyPositiveDirectInequality f :=
    strictlyPositiveInverseInequality_iff_directInequality f hf hpos
  have hItoIII : AllHOperatorMonotoneOnIoi f → StrictlyPositiveDirectInequality f :=
    strictlyPositiveDirectInequality_of_operatorMonotone f hf hpos
  have hIIItoIV : StrictlyPositiveDirectInequality f → JointConcavity f :=
    jointConcavity_of_strictDirectDPI f hf
  have hIVtoImat : JointConcavity f → MatrixMonotoneCondition f :=
    matrixMonotone_of_jointConcavity f hf hpos
  have hImatToI : MatrixMonotoneCondition f → AllHOperatorMonotoneOnIoi f :=
    HiaiPetz.MatrixFunctionalCalculus.allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hI
      exact hIIiffIII.mpr (hItoIII hI)
    · intro hII
      exact hImatToI (hIVtoImat (hIIItoIV (hIIiffIII.mp hII)))
  · exact hIIiffIII
  · constructor
    · exact hIIItoIV
    · intro hIV
      exact hItoIII (hImatToI (hIVtoImat hIV))
  · exact hIVtoImat
  · exact hImatToI

/-- The four book-facing conditions of Theorem 6.2 are equivalent in the
output-nondegenerate case.

The source theorem does not assume continuity; this implementation through the continuous
functional calculus assumes `hf`. In the source, the primed labels `(ii')` and `(iii')`
denote the conditions restricted to trace-preserving completely positive maps; the second and
third conditions here use the same map class as conditions `(ii)` and `(iii)`, with
positive-definite `Φ(1)`. -/
theorem strictlyPositive_characterizations_tfae {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    List.TFAE [
      AllHOperatorMonotoneOnIoi f,
      StrictlyPositiveInverseInequality f,
      StrictlyPositiveDirectInequality f,
      JointConcavity f
    ] := by
  rcases strictlyPositive_characterizations (f := f) hf hpos with
    ⟨hIiffII, hIIiffIII, hIIIiffIV, _, _⟩
  tfae_have 1 ↔ 2 := hIiffII
  tfae_have 2 ↔ 3 := hIIiffIII
  tfae_have 3 ↔ 4 := hIIIiffIV
  tfae_finish

/-- Extended output-nondegenerate characterization adding the matrix-monotone bridge
condition to the four book-facing conditions.

The source theorem does not assume continuity; this implementation through the continuous
functional calculus assumes `hf`. -/
theorem strictlyPositive_characterizations_tfae_with_matrix {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    List.TFAE [
      AllHOperatorMonotoneOnIoi f,
      StrictlyPositiveInverseInequality f,
      StrictlyPositiveDirectInequality f,
      JointConcavity f,
      MatrixMonotoneCondition f
    ] := by
  rcases strictlyPositive_characterizations (f := f) hf hpos with
    ⟨hIiffII, hIIiffIII, hIIIiffIV, hIVtoImat, hImatToI⟩
  tfae_have 1 ↔ 2 := hIiffII
  tfae_have 2 ↔ 3 := hIIiffIII
  tfae_have 3 ↔ 4 := hIIIiffIV
  tfae_have 4 → 5 := hIVtoImat
  tfae_have 5 → 1 := hImatToI
  tfae_finish

end QuasiEntropyDataProcessing

end MatrixScopedInstances

end HiaiPetz
