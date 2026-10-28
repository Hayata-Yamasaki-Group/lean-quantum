/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.HiaiPetz.Basic
import Mathlib.LinearAlgebra.Lagrange


/-!
# Provider-neutral strict-output Hiai--Petz 6.2 interface

This module owns the strict-output statement vocabulary and equivalence package.
It does not import the output-support reduction proof payload.
-/

namespace ProofNet

open HiaiPetz
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section

/-- Finite-dimensional matrix operator monotonicity on `(0, ∞)`. -/
def MatrixMonotone (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval (Set.Ioi (0 : ℝ)) f

/-- Strict-output inverse data-processing inequality in the standard operator order. -/
def StrictInverseDPI (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      jOperatorInv f A B

/-- Strict-output direct data-processing inequality in the standard operator order. -/
def StrictDirectDPI (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      jOperator f (Φ A) (Φ B)

/-- Joint concavity of the common quasi-entropy surface. -/
def JointConcavity (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A₁ A₂ B₁ B₂ X : Mₙ n} {t : ℝ},
    0 ≤ t →
    t ≤ 1 →
    Matrix.PosDef A₁ →
    Matrix.PosDef A₂ →
    Matrix.PosDef B₁ →
    Matrix.PosDef B₂ →
    t * quasiEntropy f A₁ B₁ X + (1 - t) * quasiEntropy f A₂ B₂ X ≤
      quasiEntropy f (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X
/-- The four strict-output Hiai--Petz 6.2 equivalences, with stable named fields. -/
structure StrictDPIEquivalenceFields (f : ℝ → ℝ) : Prop where
  matrixMonotone_iff_strictInverseDPI : MatrixMonotone f ↔ StrictInverseDPI f
  strictInverseDPI_iff_strictDirectDPI : StrictInverseDPI f ↔ StrictDirectDPI f
  strictDirectDPI_iff_jointConcavity : StrictDirectDPI f ↔ JointConcavity f
  matrixMonotone_of_jointConcavity : JointConcavity f → MatrixMonotone f

/-- Common strict-output Hiai--Petz 6.2 package. -/
def StrictDPIEquivalences (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    StrictDPIEquivalenceFields f

/-- Convert the named strict-output fields to the legacy nested conjunction. -/
def StrictDPIEquivalenceFields.toLegacyAnd {f : ℝ → ℝ}
    (h : StrictDPIEquivalenceFields f) :
    (MatrixMonotone f ↔ StrictInverseDPI f) ∧
    (StrictInverseDPI f ↔ StrictDirectDPI f) ∧
    (StrictDirectDPI f ↔ JointConcavity f) ∧
    (JointConcavity f → MatrixMonotone f) :=
  ⟨h.matrixMonotone_iff_strictInverseDPI,
    h.strictInverseDPI_iff_strictDirectDPI,
    h.strictDirectDPI_iff_jointConcavity,
    h.matrixMonotone_of_jointConcavity⟩

/-- Convert the legacy strict-output conjunction to the named fields. -/
def StrictDPIEquivalenceFields.ofLegacyAnd {f : ℝ → ℝ}
    (h :
      (MatrixMonotone f ↔ StrictInverseDPI f) ∧
      (StrictInverseDPI f ↔ StrictDirectDPI f) ∧
      (StrictDirectDPI f ↔ JointConcavity f) ∧
      (JointConcavity f → MatrixMonotone f)) :
    StrictDPIEquivalenceFields f :=
  { matrixMonotone_iff_strictInverseDPI := h.1
    strictInverseDPI_iff_strictDirectDPI := h.2.1
    strictDirectDPI_iff_jointConcavity := h.2.2.1
    matrixMonotone_of_jointConcavity := h.2.2.2 }

/-- Round-trip from named strict-output fields through the legacy conjunction. -/
theorem StrictDPIEquivalenceFields.ofLegacyAnd_toLegacyAnd {f : ℝ → ℝ}
    (h : StrictDPIEquivalenceFields f) : ofLegacyAnd h.toLegacyAnd = h :=
  Subsingleton.elim _ _

/-- Round-trip from the legacy strict-output conjunction through the named fields. -/
theorem StrictDPIEquivalenceFields.toLegacyAnd_ofLegacyAnd {f : ℝ → ℝ}
    (h :
      (MatrixMonotone f ↔ StrictInverseDPI f) ∧
      (StrictInverseDPI f ↔ StrictDirectDPI f) ∧
      (StrictDirectDPI f ↔ JointConcavity f) ∧
      (JointConcavity f → MatrixMonotone f)) :
    (ofLegacyAnd h).toLegacyAnd = h :=
  Subsingleton.elim _ _

end

end ProofNet
