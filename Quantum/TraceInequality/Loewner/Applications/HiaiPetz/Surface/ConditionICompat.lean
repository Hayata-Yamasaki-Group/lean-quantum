/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Basic

/-!
# Hiai--Petz condition (i) compatibility name

This file keeps the Hiai--Petz condition (i) name separate from the strict-output
statement surface.  The Carlen--Loewner proof route should not import proof
plumbing through this file; it only exposes the provider-independent
`Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval` predicate on `(0,∞)`
under the local Hiai--Petz condition name.
Source: Hiai--Petz Theorem 6.2(i) for the condition name; the Hansen--Pedersen
chapter for the original matrix-monotonicity implementation.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

/-- Condition (i): matrix operator monotonicity on `(0,∞)`. -/
abbrev ConditionI (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval (Set.Ioi (0 : ℝ)) f

open scoped MatrixOrder in
/--
gcongr form of Hiai--Petz condition (i): matrix CFC monotonicity on `(0,∞)`.
It delegates to `ConditionI`.
-/
@[gcongr]
theorem matrixCfcR_le_matrixCfcR_of_le_of_conditionI
    {f : ℝ → ℝ} (hf : ConditionI f)
    {n : ℕ} {A B : HansenPedersen.Mₙ n} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    HansenPedersen.matrixCfcR f A ≤ HansenPedersen.matrixCfcR f B :=
  hf hA hB hσA hσB hAB

end Quantum.TraceInequality.Loewner.HiaiPetz
