/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourBipartiteChoi.GSLCore
import Mathlib.LinearAlgebra.Complex.Module
import Quantum.QuantumMechanics.Channel.Representations

/-!
# Trace and partial trace of tensor-product operators

`tensor_trace`: the partial traces of `X ⊗ Y` are `Tr₂ (X ⊗ Y) = (Tr X) • Y` and
`TrRight (X ⊗ Y) = (Tr Y) • X`, and the full trace is `Tr X * Tr Y`.
This module contains only those declarations of the original module that the public part uses.
-/

namespace GourChoi

open QuantumState QuantumChannel
open scoped TensorProduct BigOperators ComplexOrder

universe u

set_option autoImplicit false


theorem tensor_trace :
    ∀ {E : Type u} {F : Type u} [Qudit E] [Qudit F] (X : L E) (Y : L F),
      Tr₂ (TensorProduct.map X Y) = (Tr X) • Y ∧
      TrRight (TensorProduct.map X Y) = (Tr Y) • X ∧
      Tr (TensorProduct.map X Y) = Tr X * Tr Y := by
  intro E F _ _ X Y
  refine ⟨?_, ?_, LinearMap.trace_tensorProduct' X Y⟩
  · rw [← endomorphismTensorEquiv_symm_tmul, Tr₂_l_tensor_equiv_symm_tmul]
  · have hswap :
        conjugateEnd (TensorProduct.comm ℂ E F) (TensorProduct.map X Y) =
          TensorProduct.map Y X := by
      apply TensorProduct.ext'
      intro y x
      change (TensorProduct.comm ℂ E F).toLinearMap
          ((TensorProduct.map X Y)
            ((TensorProduct.comm ℂ E F).symm.toLinearMap (y ⊗ₜ[ℂ] x))) =
        (TensorProduct.map Y X) (y ⊗ₜ[ℂ] x)
      simp [TensorProduct.map_tmul]
    change Tr₂ (conjugateEnd (TensorProduct.comm ℂ E F) (TensorProduct.map X Y)) =
      (Tr Y) • X
    rw [hswap, ← endomorphismTensorEquiv_symm_tmul, Tr₂_l_tensor_equiv_symm_tmul]

end GourChoi

open Lean
