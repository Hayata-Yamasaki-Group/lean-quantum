import ComparatorChallenges.Paper2Headline
import Quantum.QuantumEntropy.GourResource.GeneralizedStein
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.SRAdapter
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.FromRenyi.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.HPAdapter
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.UmegakiDPI.Provider
import Quantum.QuantumEntropy.VonNeumann.SSA
import Quantum.TraceInequality.HansenPedersen.HansenPedersenAdapter
import Quantum.TraceInequality.HiaiPetz.SelectedProvider
import Quantum.TraceInequality.Loewner.LoewnerAdapter
import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.PublicCorrespondence

/-! Paper 2 axiom comparator fixture. Each proof delegates to its public declaration.
The weak and axiom fixtures intentionally corrupt only the GSL y54 entry. -/
namespace ComparatorChallenges.Paper2

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open GeneralizedPerspectiveFunction SandwichedRenyiRelativeEntropy VonNeumann
open ProofNet UmegakiDPI Quantum.TraceInequality.Loewner
open scoped TensorProduct BigOperators ComplexOrder
universe u

theorem gsl_y54 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), valid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (hRate.{u} ρ F ε) atTop (𝓝 (reg.{u} ρ F)) := by
  sorry

theorem gsl_y53 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (rate (fun n => dSet.{u} (pow.{u} ρ n) (F n) ε)) atTop (𝓝 (reg.{u} ρ F)) := by
  exact GourResource.gsl_y53

theorem gsl_y55 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
  ∃ r : ℝ, 0 ≤ r ∧ reg.{u} ρ F = (r : EReal) ∧
    Tendsto (rate (fun n => dSet.{u} (pow.{u} ρ n) (F n) ε)) atTop (𝓝 (r : EReal)) ∧
    Tendsto (uRate.{u} ρ F) atTop (𝓝 (r : EReal)) := by
  exact GourResource.gsl_y55

section
variable {ℋA ℋB ℋC : Type u} [Qudit ℋA] [Qudit ℋB] [Qudit ℋC]
variable [Nontrivial ℋA] [Nontrivial ℋB] [Nontrivial ℋC]

theorem strongSubadditivity_of_state
    (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    VonNeumann.vonNeumannEntropy ρ +
        VonNeumann.vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) ≤
      VonNeumann.vonNeumannEntropy (QuantumChannel.traceOutThird ρ) +
        VonNeumann.vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  exact VonNeumann.strongSubadditivity_of_state ρ hρ hTr

end

theorem strictDPIEquivalences {f : ℝ → ℝ} : StrictDPIEquivalences f := by
  exact ProofNet.strictDPIEquivalences

theorem outputSupportDPIEquivalences {f : ℝ → ℝ} : OutputSupportDPIEquivalences f := by
  exact ProofNet.outputSupportDPIEquivalences

theorem monotoneOnPosDef_of_sandwiched (p : RenyiDPI.SandwichedSide.{u, u}) :
    MonotoneOnPosDef.{u} := by
  exact UmegakiDPI.monotoneOnPosDef_of_sandwiched p

theorem monotoneOnPosDef_of_petz (p : RenyiDPI.PetzSide.{u, u}) :
    MonotoneOnPosDef.{u} := by
  exact UmegakiDPI.monotoneOnPosDef_of_petz p

theorem monotoneOnPosDef : UmegakiDPI.MonotoneOnPosDef := by
  exact UmegakiDPI.monotoneOnPosDef

section
variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

theorem monotoneOnNonNeg
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    umegakiRelEntropyNN (E.toFun ρ)
      (E.toFun σ) ≤ umegakiRelEntropyNN ρ σ := by
  exact UmegakiDPI.monotoneOnNonNeg E hρ hσ

end

theorem loewnerUnitIntervalFourConditions {f : ℝ → ℝ} :
    (LoewnerPosOnUnitInterval f ↔ Nonempty (PickExtensionOnUnitInterval f)) ∧
    (Nonempty (PickExtensionOnUnitInterval f) ↔ Nonempty (IntegralRepOnUnitInterval f)) ∧
    (Nonempty (IntegralRepOnUnitInterval f) ↔ OperatorMonotoneOnUnitInterval.{u} f) := by
  exact ComparatorChallenges.loewnerUnitIntervalFourConditions

theorem unitIntervalPickExtension_iff_integralRep (f : ℝ → ℝ) :
    Nonempty (PickExtensionOnUnitInterval f) ↔
      Nonempty (IntegralRepOnUnitInterval f) := by
  exact Quantum.TraceInequality.Loewner.unitIntervalPickExtension_iff_integralRep f

theorem operatorMonotoneOnUnitInterval_of_integralRep {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) :
    OperatorMonotoneOnUnitInterval.{u} f := by
  exact Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_of_integralRep rep

theorem strictDPIEquivalences_via_hansenPedersen
    {f : ℝ → ℝ} : StrictDPIEquivalences f := by
  exact ProofNet.strictDPIEquivalences_via_hansenPedersen

theorem outputSupportDPIEquivalences_via_hansenPedersen
    {f : ℝ → ℝ} : OutputSupportDPIEquivalences f := by
  exact ProofNet.outputSupportDPIEquivalences_via_hansenPedersen

theorem strictDPIEquivalences_via_loewner {f : ℝ → ℝ} : StrictDPIEquivalences f := by
  exact ProofNet.strictDPIEquivalences_via_loewner

theorem outputSupportDPIEquivalences_via_loewner
    {f : ℝ → ℝ} : OutputSupportDPIEquivalences f := by
  exact ProofNet.outputSupportDPIEquivalences_via_loewner

theorem monotoneOnPosDef_via_sandwichedRenyi : UmegakiDPI.MonotoneOnPosDef := by
  exact UmegakiDPI.monotoneOnPosDef_via_sandwichedRenyi

theorem monotoneOnPosDef_via_hiaiPetz : UmegakiDPI.MonotoneOnPosDef := by
  exact UmegakiDPI.monotoneOnPosDef_via_hiaiPetz

end ComparatorChallenges.Paper2
