/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.ConditionICompat

/-!
# Alignment with the legacy HP62 theorem-facing surface

This file exposes theorem-facing names for the Hiai--Petz 6.2 surface used by
the Hiai--Petz formulation.  The strict-output names below are definitional
aliases for the Loewner-route surface in this namespace.  The quasi-entropy
condition is restated with the same local `J_f` surface.  This file does not
import the old proof route or the output-support layer.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

namespace QuasiEntropyDPI

/-- Legacy HP62 condition (i), aligned with the Loewner-route `ConditionI`. -/
abbrev matrixMonotoneCondition (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.Loewner.HiaiPetz.ConditionI f

open scoped MatrixOrder in
/--
gcongr form of the aligned HP62 matrix-monotonicity condition.
It delegates to `QuasiEntropyDPI.matrixMonotoneCondition`.
-/
@[gcongr]
theorem matrixCfcR_le_matrixCfcR_of_le_of_matrixMonotoneCondition
    {f : ℝ → ℝ} (hf : matrixMonotoneCondition f)
    {n : ℕ} {A B : HansenPedersen.Mₙ n} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    HansenPedersen.matrixCfcR f A ≤ HansenPedersen.matrixCfcR f B :=
  hf hA hB hσA hσB hAB

/-- Legacy HP62 matrix condition (i), aligned with the same matrix surface.
Theorem 6.2 of [hiai2025]. -/
abbrev matrixMonotoneConditionMatrix (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.Loewner.HiaiPetz.ConditionI f

open scoped MatrixOrder in
/--
gcongr form of the aligned HP62 matrix condition (i).
It delegates to `QuasiEntropyDPI.matrixMonotoneConditionMatrix`.
-/
@[gcongr]
theorem matrixCfcR_le_matrixCfcR_of_le_of_matrixMonotoneConditionMatrix
    {f : ℝ → ℝ} (hf : matrixMonotoneConditionMatrix f)
    {n : ℕ} {A B : HansenPedersen.Mₙ n} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    HansenPedersen.matrixCfcR f A ≤ HansenPedersen.matrixCfcR f B :=
  hf hA hB hσA hσB hAB

/-- Legacy HP62 strict-output inverse predicate.
Theorem 6.2 of [hiai2025]. -/
abbrev strictInverseDPICondition (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.Loewner.HiaiPetz.ConditionII_strict f

/-- Legacy HP62 strict-output direct predicate.
Theorem 6.2 of [hiai2025]. -/
abbrev strictDirectDPICondition (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.Loewner.HiaiPetz.ConditionIII_strict f

/-- Legacy HP62 quasi-entropy, written with the Loewner-route `J_f` surface.
Theorem 6.2 of [hiai2025]. -/
noncomputable abbrev quasiEntropy {n : ℕ} (f : ℝ → ℝ) (A B X : Mₙ n) : ℝ :=
  _root_.HiaiPetz.quasiEntropy f A B X

/-- Legacy HP62 condition (iv): joint concavity of the quasi-entropy.
Theorem 6.2 of [hiai2025]. -/
def quasiEntropyJointConcavityCondition (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A₁ A₂ B₁ B₂ X : Mₙ n} {t : ℝ},
    0 ≤ t →
    t ≤ 1 →
    MatrixPosDef A₁ →
    MatrixPosDef A₂ →
    MatrixPosDef B₁ →
    MatrixPosDef B₂ →
    t * quasiEntropy f A₁ B₁ X + (1 - t) * quasiEntropy f A₂ B₂ X ≤
      quasiEntropy f (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X

end QuasiEntropyDPI

/--
The Loewner-route condition (i) is definitionally the theorem-facing HP62
condition (i) exposed in this bridge surface.

Theorem 6.2 of [hiai2025].
-/
theorem conditionI_iff_quasiEntropyDPI_matrixMonotone {f : ℝ → ℝ} :
    ConditionI f ↔ QuasiEntropyDPI.matrixMonotoneCondition f :=
  Iff.rfl

/--
The Loewner-route condition (i) is also definitionally the theorem-facing HP62
matrix condition (i) exposed in this bridge surface.

Theorem 6.2 of [hiai2025].
-/
theorem conditionI_iff_quasiEntropyDPI_matrixCondition {f : ℝ → ℝ} :
    ConditionI f ↔ QuasiEntropyDPI.matrixMonotoneConditionMatrix f :=
  Iff.rfl

/--
The Loewner-route strict-output inverse predicate is definitionally the HP62
strict-output inverse predicate exposed in this bridge surface.

Theorem 6.2 of [hiai2025].
-/
theorem strict_inverse_dpi_iff_quasiEntropyDPI_strict_inverse {f : ℝ → ℝ} :
    ConditionII_strict f ↔ QuasiEntropyDPI.strictInverseDPICondition f :=
  Iff.rfl

/--
The Loewner-route strict-output direct predicate is definitionally the HP62
strict-output direct predicate exposed in this bridge surface.

Theorem 6.2 of [hiai2025].
-/
theorem strict_direct_dpi_iff_quasiEntropyDPI_strict_direct {f : ℝ → ℝ} :
    ConditionIII_strict f ↔ QuasiEntropyDPI.strictDirectDPICondition f :=
  Iff.rfl

end Quantum.TraceInequality.Loewner.HiaiPetz
