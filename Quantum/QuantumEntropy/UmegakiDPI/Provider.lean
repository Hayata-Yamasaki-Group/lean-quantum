/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.SelectedProvider

/-- **Provider-neutral data processing for the Umegaki relative entropy,
    positive-definite case.** -/
theorem UmegakiDPI.monotoneOnPosDef : UmegakiDPI.MonotoneOnPosDef :=
  UmegakiDPI.selectedProvider.monotoneOnPosDef

@[deprecated (since := "2026-09-02")]
alias UmegakiDPI.monotone_pd_selected := UmegakiDPI.monotoneOnPosDef
