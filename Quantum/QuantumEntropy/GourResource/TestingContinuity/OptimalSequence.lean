/-
Composition of choices that picks an optimal free state for each n and fills an arbitrary OpSeq down to index 0.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.ResourceTesting
import Quantum.QuantumEntropy.GourResource.TensorSeed

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y11 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 → ∃ z : OpSeq.{u} A, optSeq.{u} ρ F ε z
:= by
  classical
  intro A _ _ ρ F hF ε hε
  obtain ⟨γ, lam, _, _, hseed⟩ := GourResource.gsl_y06.{u} ρ F hF
  have hx : ∀ n : ℕ, ∃ σ : L (Copy A n), 0 < n →
      σ ∈ F n ∧ IsDensity σ ∧
      dh (pow ρ n) σ ε = res (fun X Y => dh X Y ε) (pow ρ n) (F n) := by
    intro n
    by_cases hn : 0 < n
    · have hd : IsDensity (pow ρ n) := (w42_tensor_spectral_dictionary.1 ρ n).2.1
      obtain ⟨σ, hσ, heq⟩ := GourResource.gsl_c20 ⟨pow ρ n, hd⟩ (F n) ε
        ⟨pow γ n, (hseed n hn).1⟩ (hF.2.1 n hn).1 (hF.1 n hn) hε
      exact ⟨σ, fun _ => ⟨hσ, hF.1 n hn hσ, heq⟩⟩
    · exact ⟨0, fun h => (hn h).elim⟩
  choose z hz using hx
  exact ⟨z, (fun n hn => ⟨(hz n hn).1, (hz n hn).2.1⟩),
    fun n hn => (hz n hn).2.2⟩

end GourResource

