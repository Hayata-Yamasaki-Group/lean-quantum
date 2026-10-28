/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.SRAdapter

/-!
# The selected Umegaki DPI provider

The current provider derives Umegaki data processing from sandwiched Rényi data processing
and the limit as the order decreases to one.
-/

namespace UmegakiDPI

/-- The unique entry point that selects the Umegaki DPI provider. It currently selects the provider
via the α→1 limit of the sandwiched Rényi divergence (`sandwichedRenyiProvider`).
In the configuration names `xyz-Hk` of the replacement checks, `x` selects the sandwiched provider,
`y` selects the Petz provider, and `Hk` selects the Hiai--Petz provider (`H1` = Hansen--Pedersen,
`H2` = Loewner). The third letter `z` records the Umegaki selection:
`A` = `sandwichedRenyiProvider` (`via1`, through interface 1, the sandwiched Rényi side) and
`B` = `hiaiPetzProvider` (`via2`, through interface 2, the Petz side). Thus `z` names the interface
used for the limit; the mathematical route A/B for that interface is selected by `x` or `y`. -/
def selectedProvider : Provider := sandwichedRenyiProvider

end UmegakiDPI
