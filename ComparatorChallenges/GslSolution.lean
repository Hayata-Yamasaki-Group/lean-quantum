import Quantum.QuantumEntropy.GourResource.GeneralizedStein

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

namespace ComparatorChallenges.Gsl

theorem y54 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), valid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (hRate.{u} ρ F ε) atTop (𝓝 (reg.{u} ρ F))
:= GourResource.gsl_y54.{u}

theorem y53 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (rate (fun n => dSet.{u} (pow.{u} ρ n) (F n) ε)) atTop (𝓝 (reg.{u} ρ F))
:= GourResource.gsl_y53.{u}

end ComparatorChallenges.Gsl
