import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore

open QuantumState QuantumChannel GourChoi GourSemiCausal
open scoped TensorProduct ComplexOrder BigOperators ENNReal

universe u

namespace GourConditionalEntropy

def minPrimalSet {A B : Type u} [Qudit A] [Qudit B]
    (ρ : {X : L (A ⊗[ℂ] B) // IsDensity X}) : Set (L B) :=
  {Λ | Λ.IsPositive ∧ ρ.1 ≤ TensorProduct.map (I A) Λ}

def minPrimalValues {A B : Type u} [Qudit A] [Qudit B]
    (ρ : {X : L (A ⊗[ℂ] B) // IsDensity X}) : Set ℝ :=
  (fun Λ : L B => (Tr Λ).re) '' minPrimalSet ρ

noncomputable def rootFidelity {A : Type u} [Qudit A] (ρ σ : L A) : ℝ :=
  (Tr (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ))).re

end GourConditionalEntropy
