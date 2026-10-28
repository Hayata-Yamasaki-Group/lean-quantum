/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.FromRenyi.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider


/-- The sandwiched-Rényi construction supplies positive-definite Umegaki DPI. -/
theorem UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi : UmegakiDPI.MonotoneOnPosDef :=
  UmegakiDPI.monotoneOnPosDef_of_sandwiched RenyiDPI.selectedSandwichedProvider

/-- The Umegaki provider via the sandwiched route (via1): positive-definite Umegaki data
processing obtained from the selected sandwiched Rényi provider. -/
def UmegakiDPI.sandwichedRenyiProvider : UmegakiDPI.Provider where
  route := .sandwichedRenyi
  monotoneOnPosDef := UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi
