/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Interface.Strict
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map
import Mathlib.LinearAlgebra.Lagrange

/-!
# Provider-neutral output-support Hiai--Petz 6.2 interface

This module owns the general-output statements, their named equivalence package,
and the provider value shape.  It depends only on the reduced-map definition;
readiness proofs remain below the adapters.
-/

namespace ProofNet

open HiaiPetz
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section

/-- General-output inverse DPI through the canonical output-support matrix model. -/
def OutputSupportInverseDPI (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      (show HSOp n from
        (hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ)) ≤
        jOperatorInv f A B

/-- General-output direct DPI through the canonical output-support matrix model. -/
def OutputSupportDirectDPI (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      (show HSOp (outputSupportMatrixCornerModel Φ).dim from
        Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ))) ≤
        jOperator f (Ψ A) (Ψ B)
/-- The four general-output Hiai--Petz 6.2 equivalences, with stable named fields. -/
structure OutputSupportDPIEquivalenceFields (f : ℝ → ℝ) : Prop where
  outputSupportDirectDPI_of_matrixMonotone : MatrixMonotone f → OutputSupportDirectDPI f
  outputSupportInverseDPI_iff_outputSupportDirectDPI :
    OutputSupportInverseDPI f ↔ OutputSupportDirectDPI f
  jointConcavity_of_outputSupportDirectDPI : OutputSupportDirectDPI f → JointConcavity f
  matrixMonotone_of_jointConcavity : JointConcavity f → MatrixMonotone f

/-- Common general-output Hiai--Petz 6.2 package. -/
def OutputSupportDPIEquivalences (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    OutputSupportDPIEquivalenceFields f

/-- Available proof routes for the Hiai--Petz 6.2 equivalence packages. -/
inductive ProviderRoute
  | hansenPedersen
  | loewner

/-- An explicit provider of both Hiai--Petz 6.2 equivalence packages.

The route is metadata for display and probes; proof selection is ordinary value selection. -/
structure Provider where
  route : ProviderRoute
  strictDPIEquivalences : ∀ {f : ℝ → ℝ}, StrictDPIEquivalences f
  outputSupportDPIEquivalences : ∀ {f : ℝ → ℝ}, OutputSupportDPIEquivalences f

/-- Convert the named general-output fields to the legacy nested conjunction. -/
def OutputSupportDPIEquivalenceFields.toLegacyAnd {f : ℝ → ℝ}
    (h : OutputSupportDPIEquivalenceFields f) :
    (MatrixMonotone f → OutputSupportDirectDPI f) ∧
    (OutputSupportInverseDPI f ↔ OutputSupportDirectDPI f) ∧
    (OutputSupportDirectDPI f → JointConcavity f) ∧
    (JointConcavity f → MatrixMonotone f) :=
  ⟨h.outputSupportDirectDPI_of_matrixMonotone,
    h.outputSupportInverseDPI_iff_outputSupportDirectDPI,
    h.jointConcavity_of_outputSupportDirectDPI,
    h.matrixMonotone_of_jointConcavity⟩

/-- Convert the legacy general-output conjunction to the named fields. -/
def OutputSupportDPIEquivalenceFields.ofLegacyAnd {f : ℝ → ℝ}
    (h :
      (MatrixMonotone f → OutputSupportDirectDPI f) ∧
      (OutputSupportInverseDPI f ↔ OutputSupportDirectDPI f) ∧
      (OutputSupportDirectDPI f → JointConcavity f) ∧
      (JointConcavity f → MatrixMonotone f)) :
    OutputSupportDPIEquivalenceFields f :=
  { outputSupportDirectDPI_of_matrixMonotone := h.1
    outputSupportInverseDPI_iff_outputSupportDirectDPI := h.2.1
    jointConcavity_of_outputSupportDirectDPI := h.2.2.1
    matrixMonotone_of_jointConcavity := h.2.2.2 }

/-- Round-trip from named general-output fields through the legacy conjunction. -/
theorem OutputSupportDPIEquivalenceFields.ofLegacyAnd_toLegacyAnd {f : ℝ → ℝ}
    (h : OutputSupportDPIEquivalenceFields f) : ofLegacyAnd h.toLegacyAnd = h :=
  Subsingleton.elim _ _

/-- Round-trip from the legacy general-output conjunction through the named fields. -/
theorem OutputSupportDPIEquivalenceFields.toLegacyAnd_ofLegacyAnd {f : ℝ → ℝ}
    (h :
      (MatrixMonotone f → OutputSupportDirectDPI f) ∧
      (OutputSupportInverseDPI f ↔ OutputSupportDirectDPI f) ∧
      (OutputSupportDirectDPI f → JointConcavity f) ∧
      (JointConcavity f → MatrixMonotone f)) :
    (ofLegacyAnd h).toLegacyAnd = h :=
  Subsingleton.elim _ _

end

end ProofNet
