/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.AlphaOne

/-! # The positive-definite order-one right limit of sandwiched Rényi divergence -/

namespace RenyiDPI

open QuantumState SandwichedRenyiRelativeEntropy

universe u

/-- The existing natural-log, trace-normalized right limit; no DPI is used here. -/
theorem sandwichedLimitAtOneOnPosDef : SandwichedLimitAtOneOnPosDef.{u} := by
  intro H _ _ ρ σ hρ hσ
  exact sandwichedRenyiDiv_tendsto_umegaki hρ hσ

end RenyiDPI
