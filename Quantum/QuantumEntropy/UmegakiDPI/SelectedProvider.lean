/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.SRAdapter

/-!
# Selected Umegaki DPI provider

This module defines `selectedProvider` using
`sandwichedRenyiProvider`.
-/

namespace UmegakiDPI

/-- The Umegaki DPI provider supplied by `sandwichedRenyiProvider`. -/
def selectedProvider : Provider := sandwichedRenyiProvider

@[deprecated (since := "2026-09-02")]
alias monotone_pd := monotoneOnPosDef_via_sandwichedRenyi

end UmegakiDPI
