import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.Channel.Basic

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Monotonicity

open MeasureTheory QuantumChannel TensorProduct GeneralizedPerspectiveFunction

universe u₅

variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

/-- `TensorProduct.map` preserves `pdSetLM`: the tensor of two positive-definite
    operators is positive-definite. -/
lemma pdSetLM_tensorMap {ℋ₁ ℋ₂ : Type u₅} [Qudit ℋ₁] [Qudit ℋ₂]
    [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    {A : L ℋ₁} {B : L ℋ₂} (hA : A ∈ pdSetLM (ℋ := ℋ₁)) (hB : B ∈ pdSetLM (ℋ
      := ℋ₂)) :
    (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) ∈ pdSetLM (ℋ := ℋ₁ ⊗[ℂ]
      ℋ₂) := by
  have hA_strict := (pdSetLM_strictPositivity_certificate A).1 hA
  have hB_strict := (pdSetLM_strictPositivity_certificate B).1 hB
  let r : L ℋ₁ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) :=
    TensorCFC.rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)
  let l : L ℋ₂ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) :=
    TensorCFC.lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)
  have hT_rl : (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) = r A * l B := by
    exact TensorCFC.map_eq_rTensor_mul_lTensor A B
  have hT_lr : (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) = l B * r A := by
    exact TensorCFC.map_eq_lTensor_mul_rTensor A B
  have hcomm : Commute (r A) (l B) := by
    change r A * l B = l B * r A
    rw [← hT_rl, ← hT_lr]
  have hT_nn : (0 : L (ℋ₁ ⊗[ℂ] ℋ₂)) ≤ TensorProduct.map A B := by
    rw [hT_rl]
    exact Commute.mul_nonneg (map_nonneg r hA_strict.nonneg)
      (map_nonneg l hB_strict.nonneg) hcomm
  have hT_unit : IsUnit (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
    rw [hT_rl]
    exact (IsUnit.map r hA_strict.isUnit).mul (IsUnit.map l hB_strict.isUnit)
  apply (pdSetLM_strictPositivity_certificate _).2
  exact hT_unit.isStrictlyPositive hT_nn

end Monotonicity

end SandwichedRenyiRelativeEntropy
