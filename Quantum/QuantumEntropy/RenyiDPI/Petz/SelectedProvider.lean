/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.HiaiPetz.HiaiPetzProvider

/-! # The independently selected Petz provider -/

namespace RenyiDPI

universe u v

/-- The unique entry point that selects the Petz Rényi provider; independent of the sandwiched
selection. It currently selects the Hiai–Petz provider (`petzHiaiPetzProvider`). -/
def selectedPetzProvider : PetzSide.{u, v} := petzHiaiPetzProvider

end RenyiDPI
