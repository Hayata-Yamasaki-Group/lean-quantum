/-
Tensor coherence: a state-independent Uₙ is chosen first, and both ρ/σ are carried in the same coordinates.
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCoreRetained
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge
import Quantum.QuantumEntropy.GourResource.TensorTransport
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem b05_zero_coordinates {A : Type u} [Qudit.{u} A] [Nontrivial A] :
    Nonempty (Copy.{u} A 0 ≃ₗᵢ[ℂ]
      QuantumModel.Space
        QuantumModel.tensorUnitSystem) := by
  obtain ⟨T, hT, ⟨V⟩⟩ := GourResource.gsl_b01.1 (A := Copy.{u} A 0)
  have hdim : Module.finrank ℂ (Copy.{u} A 0) = 1 := by
    calc
      _ = Module.finrank ℂ ℂ :=
        (LinearIsometryEquiv.ulift.{0, 0, u} ℂ ℂ).toLinearEquiv.finrank_eq
      _ = 1 := Module.finrank_self ℂ
  have hunit : T = QuantumModel.tensorUnitSystem := by
    cases T with
    | mk d hd =>
      have hd1 : d = 1 := hT.trans hdim
      subst d
      rfl
  rw [hunit] at V
  exact ⟨V⟩

private theorem b05_push_trans {A : Type u} [Qudit.{u} A]
    {B C : Type} [Qudit B] [Qudit C]
    (U : A ≃ₗᵢ[ℂ] B) (V : B ≃ₗᵢ[ℂ] C) (X : L.{u} A) :
    push0 (U.trans V) X = push0 V (push0 U X) := by
  ext x
  rfl

private theorem b05_push_tensor {A B : Type u} [Qudit.{u} A] [Qudit.{u} B]
    {C D : Type} [Qudit C] [Qudit D]
    (U : A ≃ₗᵢ[ℂ] C) (V : B ≃ₗᵢ[ℂ] D) (X : L.{u} A) (Y : L.{u} B) :
    push0 (TensorProduct.congrIsometry U V) (TensorProduct.map X Y) =
      TensorProduct.map (push0 U X) (push0 V Y) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [push0, TensorProduct.congrIsometry_symm]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem b05_push_native
    {S T : QuantumModel.Sys}
    (r : QuantumModel.DensityMatrix S)
    (s : QuantumModel.DensityMatrix T) :
    push0 (QuantumModel.nativeTensorEquiv S T).symm
        (TensorProduct.map r.operator s.operator) =
      (QuantumModel.densityTensor r s).operator := by
  let V := QuantumModel.nativeTensorEquiv S T
  have h :=
    QuantumModel.nativeTensorOperatorTransport_densityTensor_operator r s
  change push0 V (QuantumModel.densityTensor r s).operator =
    TensorProduct.map r.operator s.operator at h
  rw [← h]
  apply LinearMap.ext
  intro x
  simp [push0, V]

/-- Isometric transport of tensor powers (a foundation): for a linear isometric isomorphism
`U` from `A` to the model space, for each `n` there is an isomorphism `Uₙ` from the `n`-copy
space to the `n`-fold tensor product of the model space, and the same `Uₙ` transports the
tensor powers of all states corresponding under `U`. -/
theorem gsl_b05 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S : QuantumModel.Sys) (U : A
  ≃ₗᵢ[ℂ] QuantumModel.Space S) (n : ℕ),
  ∃ Uₙ : Copy.{u} A n ≃ₗᵢ[ℂ] QuantumModel.Space
    (QuantumModel.systemPow S n),
    ∀ (ρ : State.{u} A) (r : QuantumModel.DensityMatrix S),
      r.operator = push0.{u} U ρ.1 →
      push0.{u} Uₙ (pow.{u} ρ n) = (QuantumModel.densityTensorPow r
        n).operator
:= by
  intro A instA instN S U n
  induction n with
  | zero =>
      obtain ⟨V⟩ := b05_zero_coordinates (A := A)
      refine ⟨V, ?_⟩
      intro ρ r hr
      change push0 V 1 = LinearMap.id
      ext x
      simp [push0]
  | succ n ih =>
      obtain ⟨V, hV⟩ := ih
      refine ⟨(TensorProduct.congrIsometry U V).trans
        (QuantumModel.nativeTensorEquiv S
          (QuantumModel.systemPow S n)).symm, ?_⟩
      intro ρ r hr
      change push0 _ (TensorProduct.map ρ.1 (pow ρ n)) =
        (QuantumModel.densityTensor r
          (QuantumModel.densityTensorPow r n)).operator
      refine (b05_push_trans (TensorProduct.congrIsometry U V)
        (QuantumModel.nativeTensorEquiv S
          (QuantumModel.systemPow S n)).symm
        (TensorProduct.map ρ.1 (pow ρ n))).trans ?_
      rw [b05_push_tensor, ← hr, hV ρ r hr]
      exact b05_push_native r _

end GourResource

