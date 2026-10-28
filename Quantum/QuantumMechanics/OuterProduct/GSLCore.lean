/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.QuantumState

/-!
# Outer-product identities

Pointwise identities for the finite-dimensional outer product.
-/

namespace QuantumChannel

open QuantumState

universe u v

/-- Application of an outer product: `(|v⟩⟨u|) x = ⟪u, x⟫ • v`. -/
theorem outer_product_apply_univ
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (u : H) (v : K) (x : H) :
    outer_product u v x = inner ℂ u x • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

end QuantumChannel
