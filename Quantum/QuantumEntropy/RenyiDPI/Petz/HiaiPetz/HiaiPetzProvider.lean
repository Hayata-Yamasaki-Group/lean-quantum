/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.HiaiPetz.TracePowerTransfer
import Quantum.QuantumEntropy.RenyiDPI.Petz.NonNegLift
import Quantum.QuantumEntropy.RenyiDPI.Petz.AlphaOne
import Quantum.QuantumEntropy.RenyiDPI.Petz.Tensor

/-! # Initial Petz provider via Hiai–Petz

The positive-definite Hiai–Petz core is passed to the provider-neutral lift.
Tensor additivity and the logarithmic left limit are supplied independently.
-/

namespace RenyiDPI

universe u v

/-- The Hiai–Petz theorem expressed in the reusable positive-definite contract. -/
theorem petzTracePowerMonotoneOnPosDef_hiaiPetz : PetzTracePowerMonotoneOnPosDef.{u} := by
  intro H K _ _ _ _ E ρ σ hρ hσ hEρ hEσ α hα
  exact UmegakiDPI.tracePower_le_of_cptp E hρ hσ hEρ hEσ hα

/-- Initial Petz proof supply, with the fixed natural-log quantities of `Defs`. -/
def petzHiaiPetzProvider : PetzSide.{u, v} where
  route := `hiaiPetz
  monotoneOnNonNeg := petzMonotoneOnNonNeg_of_posDef
    petzTracePowerMonotoneOnPosDef_hiaiPetz
  tensorAdditivity := petzTensorAdditiveOnDensity
  limitAtOne := petzLimitAtOneOnPosDef

end RenyiDPI
