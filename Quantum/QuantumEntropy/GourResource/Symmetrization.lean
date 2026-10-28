/-
Passes the CPTP evidence of gsl_c28 directly to the data-processing inequality of gsl_b02. Symmetrized inf of the testing divergence.
-/
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.Permutation
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c31 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), valid.{u} ρ F →
  ∀ n : ℕ, 0 < n →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
  res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (F n) =
    res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (symFamily.{u} ρ F n))
:= by
  intro A _ _ ρ F hF n hn ε hε
  obtain ⟨hfix, hfree⟩ := GourResource.gsl_c29.{u} ρ F hF n hn
  obtain ⟨E, hE⟩ := (GourResource.gsl_c28.{u} ρ n).2
  have hpow : IsDensity (pow ρ n) :=
    (w42_tensor_spectral_dictionary.1 ρ n).2.1
  unfold res
  apply le_antisymm
  · refine le_iInf fun X => le_iInf fun hX => ?_
    exact iInf_le_of_le X (iInf_le_of_le hX.1 le_rfl)
  · refine le_iInf fun X => le_iInf fun hX => ?_
    have htwirl : twirl ρ n X ∈ symFamily ρ F n := hfree X hX
    have hDPI := GourResource.gsl_b02.{u}.2.2.2.2.2.2
      (⟨pow ρ n, hpow⟩ : State (Copy A n))
      (⟨X, hF.1 n hn hX⟩ : State (Copy A n)) E ε ⟨hε.1.le, hε.2⟩
    change dh (E.toFun (pow ρ n)) (E.toFun X) ε ≤ dh (pow ρ n) X ε at hDPI
    rw [hE, hE, hfix] at hDPI
    exact iInf_le_of_le (twirl ρ n X) (iInf_le_of_le htwirl hDPI)

end GourResource

