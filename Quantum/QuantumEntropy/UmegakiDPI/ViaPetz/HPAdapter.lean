/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.UmegakiLimit

/-- The selected Petz contract supplies Umegaki DPI through its Hiai--Petz wrapper. -/
theorem UmegakiDPI.monotoneOnPosDef_via_hiaiPetz : UmegakiDPI.MonotoneOnPosDef :=
  UmegakiDPI.umegakiNorm_monotone_via_hiaiPetz

/-- The Petz-derived proof packaged with the compatible Hiai--Petz branch tag. -/
def UmegakiDPI.hiaiPetzProvider : UmegakiDPI.Provider where
  route := .hiaiPetz
  monotoneOnPosDef := UmegakiDPI.monotoneOnPosDef_via_hiaiPetz
