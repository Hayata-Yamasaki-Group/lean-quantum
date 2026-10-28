/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.SelectedProvider
import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumMechanics.QuantumState

/-- **Umegaki data processing for positive-definite inputs.** -/
theorem UmegakiDPI.monotoneOnPosDef : UmegakiDPI.MonotoneOnPosDef :=
  UmegakiDPI.selectedProvider.monotoneOnPosDef
