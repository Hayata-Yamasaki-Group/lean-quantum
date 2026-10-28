/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.SelectedProvider
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumMechanics.QuantumState

/-! # Public Petz-side proof interface

Each theorem projects only the corresponding field of the selected Petz value.
These are internal interface nodes.
-/

namespace RenyiDPI

universe u v

/-- Nonnegative Petz data processing supplied by the selected provider. -/
theorem petzMonotoneOnNonNeg : PetzMonotoneOnNonNeg.{u} :=
  selectedPetzProvider.{u, u}.monotoneOnNonNeg

/-- Density-pair tensor additivity supplied by the selected provider. -/
theorem petzTensorAdditivity : PetzTensorAdditiveOnDensity.{u, v} :=
  selectedPetzProvider.{u, v}.tensorAdditivity

/-- The left limit of the real divergence supplied by the selected provider. -/
theorem petzLimitAtOne : PetzLimitAtOneOnPosDef.{u} :=
  selectedPetzProvider.{u, u}.limitAtOne

end RenyiDPI
