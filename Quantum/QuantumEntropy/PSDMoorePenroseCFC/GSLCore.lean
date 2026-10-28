/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourShortedOperator.GSLCore
import Quantum.QuantumEntropy.PetzSupportRpowContinuity.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider

/-!
# CFC identities for positive semidefinite Moore--Penrose inverses

Reusable support-projection and real-power identities for positive
finite-dimensional operators.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

universe u

variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Multiplying the positive square root by the inverse square root gives
the support projection. -/
theorem rpow_half_mul_invHalf
    {A : L H} (hA : 0 ≤ A) :
    CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A (-(1 / 2 : ℝ)) =
      (LinearMap.range A).starProjection.toLinearMap := by
  rw [← petzSupportRpow_of_ne_zero A (by norm_num : (1 / 2 : ℝ) ≠ 0),
    ← petzSupportRpow_of_ne_zero A (by norm_num : (-(1 / 2 : ℝ)) ≠ 0),
    petzSupportRpow_add hA]
  norm_num

end OPT
