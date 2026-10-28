/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.Channel.Stinespring

/-!
# Quantum channels as linear maps

Linear-map representations of channels and their spectral and norm identities.
-/

namespace QuantumChannel

open QuantumState TensorProduct
universe u v w
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

noncomputable instance linear_isometry_equiv {ℋ : Type u} [Qudit ℋ] : (L ℋ) ≃ᵢ (ℋ →L[ℂ] ℋ) where
  toFun := fun X => X.toContinuousLinearMap
  invFun := fun X => X.toLinearMap
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  isometry_toFun := fun _ _ => rfl

@[reducible]
noncomputable instance l_tensor_equiv {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂] :
  (L (ℋ₁ ⊗[ℂ] ℋ₂)) ≃ₗ[ℂ] (L ℋ₁ ⊗[ℂ] L ℋ₂) :=
  endomorphismTensorEquiv

noncomputable def Tr₂ : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ :=
  (TensorProduct.lid ℂ (L ℋ₂)).toLinearMap
  ∘ₗ (TensorProduct.map Tr LinearMap.id)
  ∘ₗ l_tensor_equiv.toLinearMap

noncomputable def TrRight {ℋ₃ : Type u} [Qudit ℋ₃] : T (ℋ₂ ⊗[ℂ] ℋ₃) ℋ₂ :=
  (Tr₂ (ℋ₁ := ℋ₃) (ℋ₂ := ℋ₂)).comp
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ ℋ₃))

end QuantumChannel
