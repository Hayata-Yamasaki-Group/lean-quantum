/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.NonNeg.Monotonicity

/-! # Sandwiched Rényi data processing from the Lieb–Ando inequality -/

namespace RenyiDPI

universe u

/-- The nonnegative CPTP theorem, restricted to orders greater than one. -/
theorem sandwichedMonotoneOnNonNeg_liebAndo : SandwichedMonotoneOnNonNeg.{u} := by
  intro H K _ _ _ _ E α ρ σ hα hρ hσ
  exact SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_monotone E
    (by linarith) (ne_of_gt hα) hρ hσ

end RenyiDPI
