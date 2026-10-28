/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Basic

/-!
# Shared operator-monotonicity vocabulary for Hiai--Petz consumers

This module contains only the condition names used by the Hiai--Petz statements.
It deliberately has no dependency on either proof of Theorem 6.2.
-/

namespace HiaiPetz.QuasiEntropyDataProcessing

/-- Operator monotonicity on `(0, ∞)` on every universe-0 complex Hilbert space. -/
def AllHOperatorMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ)) f

/-- Finite-dimensional matrix operator monotonicity on `(0, ∞)`. -/
def MatrixMonotoneCondition (f : ℝ → ℝ) : Prop :=
  _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval (Set.Ioi (0 : ℝ)) f

end HiaiPetz.QuasiEntropyDataProcessing
