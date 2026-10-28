/-
Upper estimate of the GSL.
Source context: Gour, Theorem 11.4.
-/
/-
Making the lower testing limit s a finite real number.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4; Hayashi–Yamasaki, Lemma 5.
-/

import Quantum.OperationalProbabilistic.Framework.FiniteIIDPMF.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesClassicalProbabilityDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityFoundationDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityTensorFoundation.GSLCore
import Quantum.QuantumEntropy.GourResource.BlockConverse
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.Regularization
import Quantum.QuantumEntropy.QuantumFDivergence.GSLCore
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein
import Quantum.QuantumModel.KW.Distances.HypothesisTestingCore.Basic
import Quantum.QuantumModel.NativeFacade.GSLCore
import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.QuantumModel.Skeleton.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c65_dh_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) (ε : ℝ) (hε : ε ∈ Set.Ico 0 1) :
    0 ≤ dh ρ.1 σ.1 ε := by
  have h := GourResource.gsl_b02.{u}.2.2.2.2.2.1 ρ σ 0 ε
    (by norm_num) hε hε.1
  have hzero : 0 ≤ dh ρ.1 σ.1 0 := by simpa using h.2.1
  exact hzero.trans h.1

private theorem c65_hRate_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid ρ F)
    (ε : ℝ) (hε : ε ∈ Set.Ico 0 1) (n : ℕ) : 0 ≤ hRate ρ F ε n := by
  rcases n.eq_zero_or_pos with hn | hn
  · simp [hn, hRate, rate]
  · rw [hRate, rate, if_neg (Nat.ne_of_gt hn)]
    apply mul_nonneg
    · exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg n))
    · apply le_iInf
      intro σ
      apply le_iInf
      intro hσ
      exact c65_dh_nonneg ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
        ⟨σ, hF.1 n hn hσ⟩ ε hε

/-- Under `hyValid ρ F`, for every `ε ∈ (0, 1)` the lower limit of `hRate ρ F ε` is a finite
nonnegative real number (an auxiliary result in the proof of Hayashi–Yamasaki, Theorem 4). -/
theorem gsl_c65 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 → ∃ s : ℝ, 0 ≤ s ∧
    Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal))
:= by
  intro A _ _ ρ F hF ε hε
  have hε' : ε ∈ Set.Ico 0 1 := ⟨hε.1.le, hε.2⟩
  have hnonneg : 0 ≤ Filter.liminf (hRate ρ F ε) atTop :=
    Filter.le_liminf_of_le
      (h := Filter.Eventually.of_forall (c65_hRate_nonneg ρ F hF ε hε'))
  obtain ⟨r, hr⟩ := (GourResource.gsl_c23.{u} ρ F hF).2
  have hupper : Filter.liminf (hRate ρ F ε) atTop ≤ (r : EReal) := by
    calc
      Filter.liminf (hRate ρ F ε) atTop ≤ Filter.limsup (hRate ρ F ε) atTop :=
        Filter.liminf_le_limsup
      _ ≤ reg ρ F := GourResource.gsl_y10.{u} ρ F hF ε hε'
      _ = (r : EReal) := hr
  have htop : Filter.liminf (hRate ρ F ε) atTop ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hupper (EReal.coe_lt_top r))
  have hbot : Filter.liminf (hRate ρ F ε) atTop ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le (by simp) hnonneg)
  exact ⟨(Filter.liminf (hRate ρ F ε) atTop).toReal, EReal.toReal_nonneg hnonneg,
    (EReal.coe_toReal htop hbot).symm⟩

end GourResource
