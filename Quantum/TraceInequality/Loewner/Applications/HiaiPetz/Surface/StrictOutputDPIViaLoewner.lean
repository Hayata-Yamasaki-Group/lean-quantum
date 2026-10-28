/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.StrictOutput
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.ConvexityUpgrade
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.SharedStageCompatibility
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Strict-output Hiai--Petz 6.2 aggregate wrapper

This file packages the Carlen--Loewner route into the theorem-facing strict-output
Hiai--Petz 6.2 family exposed by the `QuasiEntropyDPI` bridge.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

noncomputable section

/--
Strict-output Hiai--Petz 6.2 theorem family on the bridge surface.

On the route through Löwner's theorem (H2), under
continuity and positivity of `f` on `(0,∞)`, the strict-output direct and inverse
data-processing predicates, quasi-entropy joint concavity, and finite-dimensional
matrix monotonicity condition fit into the usual five theorem-facing pieces.

Theorem 6.2 of [hiai2025].
-/
def strictOutputQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (QuasiEntropyDPI.matrixMonotoneCondition f ↔ QuasiEntropyDPI.strictInverseDPICondition f) ∧
    (QuasiEntropyDPI.strictInverseDPICondition f ↔ QuasiEntropyDPI.strictDirectDPICondition f) ∧
    (QuasiEntropyDPI.strictDirectDPICondition f ↔
      QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → QuasiEntropyDPI.matrixMonotoneCondition f)

/--
Carlen--Loewner route proof of the strict-output Hiai--Petz 6.2 aggregate
family.
-/
theorem strict_output_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    strictOutputQuasiEntropyDpiPackageStmt f := by
  intro hf hpos
  have hfCarlen : CarlenOpMontIFunctionHypothesis f := by
    exact ⟨hf, fun {x} hx => hpos x hx⟩
  have hIIiffIII :
      QuasiEntropyDPI.strictInverseDPICondition f ↔
        QuasiEntropyDPI.strictDirectDPICondition f := by
    simpa using
      (conditionII_strict_iff_conditionIII_strict_of_carlenFunctionHypothesis
        (f := f) hfCarlen)
  have hItoPair :
      QuasiEntropyDPI.matrixMonotoneCondition f →
        QuasiEntropyDPI.strictDirectDPICondition f ∧
          QuasiEntropyDPI.strictInverseDPICondition f := by
    intro hI
    simpa using
      (matrix_monotone_to_strict_direct_and_inverse_dpi
        (f := f) hfCarlen hI)
  have hItoIII :
      QuasiEntropyDPI.matrixMonotoneCondition f →
        QuasiEntropyDPI.strictDirectDPICondition f :=
    fun hI => (hItoPair hI).1
  have hItoII :
      QuasiEntropyDPI.matrixMonotoneCondition f →
        QuasiEntropyDPI.strictInverseDPICondition f :=
    fun hI => (hItoPair hI).2
  have hIIItoIV :
      QuasiEntropyDPI.strictDirectDPICondition f →
        QuasiEntropyDPI.quasiEntropyJointConcavityCondition f :=
    jointConcavity_of_strictDirectDPI f hf
  have hIVtoImat :
      QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
        QuasiEntropyDPI.matrixMonotoneConditionMatrix f :=
    quasiEntropy_conditionIV_to_conditionI_matrix f hf hpos
  have hIVtoI :
      QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
        QuasiEntropyDPI.matrixMonotoneCondition f :=
    matrixMonotone_of_jointConcavity f hf hpos
  have hImatToI :
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f →
        QuasiEntropyDPI.matrixMonotoneCondition f :=
    matrix_surface_condition_to_conditionI f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact hItoII
    · intro hII
      exact hIVtoI (hIIItoIV (hIIiffIII.mp hII))
  · exact hIIiffIII
  · constructor
    · exact hIIItoIV
    · intro hIV
      exact hItoIII (hIVtoI hIV)
  · exact hIVtoImat
  · exact hImatToI

/-- Alias name emphasizing the Carlen operator-monotonicity route.
Theorem 6.2 of [hiai2025]. -/
theorem strict_output_quasiEntropy_dpi_package_via_carlen_opmontI {f : ℝ → ℝ} :
    strictOutputQuasiEntropyDpiPackageStmt f :=
  strict_output_quasiEntropy_dpi_package_via_loewner

end

end Quantum.TraceInequality.Loewner.HiaiPetz
