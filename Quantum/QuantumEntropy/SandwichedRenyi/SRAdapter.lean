/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumEntropy.SandwichedRenyi.Umegaki.AlphaOneLinear

/-- The sandwiched-Rényi construction supplies positive-definite Umegaki DPI. -/
theorem UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi : UmegakiDPI.MonotoneOnPosDef :=
  SandwichedRenyiRelativeEntropy.umegakiNorm_monotone_pd

/-- The sandwiched-Rényi proof packaged as an explicit provider value. -/
def UmegakiDPI.sandwichedRenyiProvider : UmegakiDPI.Provider where
  route := .sandwichedRenyi
  monotoneOnPosDef := UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi
