import Quantum.TraceInequality.Loewner.HalfLine.Uniqueness
import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFCReverse
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.Main
import Quantum.TraceInequality.HiaiPetz.SelectedProvider
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity
import Quantum.TraceInequality.HiaiPetz.TraceConvexity
import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Main
import Quantum.QuantumEntropy.UmegakiDPI.Provider
import Quantum.QuantumEntropy.UmegakiDPI.SandwichedRenyi.Reduction
import Quantum.QuantumEntropy.VonNeumann.SSA

namespace ComparatorChallenges

open QuantumState
open HiaiPetz
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

universe u

theorem strictDPIEquivalences {f : ℝ → ℝ} :
    ProofNet.StrictDPIEquivalences f :=
  ProofNet.strictDPIEquivalences

theorem outputSupportDPIEquivalences {f : ℝ → ℝ} :
    ProofNet.OutputSupportDPIEquivalences f :=
  ProofNet.outputSupportDPIEquivalences

theorem loewnerHalfLineIntegralRepUnique {h : ℝ → ℝ} :
    Quantum.TraceInequality.Loewner.OperatorMonotoneOnPositive.{u} h ↔
      ∃ rep : Quantum.TraceInequality.Loewner.HalfLineIntegralRep h,
        Filter.Tendsto (fun x : ℝ => h x / x) Filter.atTop (nhds (rep.b : ℝ)) ∧
        (∀ rep' : Quantum.TraceInequality.Loewner.HalfLineIntegralRep h,
          rep'.b = rep.b) ∧
        (∀ rep' : Quantum.TraceInequality.Loewner.HalfLineIntegralRep h,
          rep'.μ = rep.μ) :=
  Quantum.TraceInequality.Loewner.operatorMonotoneOnPositive_iff_exists_halfLineIntegralRep_unique

theorem loewnerClosedPositiveOfCFCWithEndpoint {h : ℝ → ℝ}
    (hh :
      Quantum.TraceInequality.Loewner.OperatorMonotoneOnClosedPositiveCFCWithEndpoint.{0} h) :
    Quantum.TraceInequality.Loewner.OperatorMonotoneOnClosedPositive.{u} h :=
  Quantum.TraceInequality.Loewner.operatorMonotoneOnClosedPositive_of_closedPositiveCFCWithEndpoint
    hh

theorem hansenPedersenOperatorConvexityCharacterizations
    (α : WithTop ℝ) (f : ℝ → ℝ) :
    (0 : WithTop ℝ) < α →
      ContinuousOn f (HansenPedersen.halfOpenRay α) →
        ((HansenPedersen.ConvexityCharacterization.ConditionI.{u} α f ↔
            HansenPedersen.ConvexityCharacterization.ConditionII.{u} α f) ∧
          (HansenPedersen.ConvexityCharacterization.ConditionI.{u} α f ↔
            HansenPedersen.ConvexityCharacterization.ConditionIII.{u} α f) ∧
          (HansenPedersen.ConvexityCharacterization.ConditionI.{u} α f ↔
            HansenPedersen.ConvexityCharacterization.ConditionIV.{u} α f) ∧
          (HansenPedersen.ConvexityCharacterization.ConditionI.{u} α f ↔
            HansenPedersen.ConvexityCharacterization.ConditionV.{u} α f)) :=
  HansenPedersen.operatorConvexity_characterizations α f

theorem hiaiPetzSupportTracePowerMonotonicity :
    (∀ {n m : ℕ} (Φ : HiaiPetz.HSMap n m) {p : ℝ}
        {A B : Mₙ n} {X : Mₙ m},
      p ∈ Set.Icc (0 : ℝ) 1 →
      HiaiPetz.IsPositiveMap Φ →
      HiaiPetz.TracePreserving Φ →
      HiaiPetz.HSAdjointSchwarz Φ →
      0 ≤ A →
      0 ≤ B →
      HiaiPetz.supportLiebTracePower p A B ((HiaiPetz.hsAdjoint Φ) X) ≤
        HiaiPetz.supportLiebTracePower p (Φ A) (Φ B) X) ∧
    (∀ {n m : ℕ} (Φ : HiaiPetz.HSMap n m) {p : ℝ} {A B X : Mₙ n},
      p ∈ Set.Icc (0 : ℝ) 1 →
      HiaiPetz.IsPositiveMap Φ →
      HiaiPetz.TracePreserving Φ →
      HiaiPetz.HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      HiaiPetz.supportPowerTrace (-p) (p - 1) (Φ A) (Φ B) (Φ X) ≤
        HiaiPetz.supportPowerTrace (-p) (p - 1) A B X) ∧
    (∀ {n m : ℕ} (Φ : HiaiPetz.HSMap n m) {p : ℝ}
        {A B : Mₙ n} {X : Mₙ m},
      (p ∈ Set.Icc (-1 : ℝ) 0 ∨ p ∈ Set.Icc (1 : ℝ) 2) →
      HiaiPetz.IsPositiveMap Φ →
      HiaiPetz.TracePreserving Φ →
      HiaiPetz.HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      (HiaiPetz.hsAdjoint Φ (X * Matrix.conjTranspose X) =
          (HiaiPetz.hsAdjoint Φ X) *
            Matrix.conjTranspose (HiaiPetz.hsAdjoint Φ X) ∧
        HiaiPetz.hsAdjoint Φ (Matrix.conjTranspose X * X) =
          Matrix.conjTranspose (HiaiPetz.hsAdjoint Φ X) *
            (HiaiPetz.hsAdjoint Φ X)) →
      HiaiPetz.supportLiebTracePower p (Φ A) (Φ B) X ≤
        HiaiPetz.supportLiebTracePower p A B ((HiaiPetz.hsAdjoint Φ) X)) := by
  simpa only [HiaiPetz.TraceMonotonicity.DirectSupportTracePower,
    HiaiPetz.TraceMonotonicity.InverseSupportTracePower,
    HiaiPetz.TraceMonotonicity.MultiplicativeDomainSupportTracePower,
    HiaiPetz.TraceMonotonicity.supportInverseTracePower,
    HiaiPetz.TraceMonotonicity.InAdjointMultiplicativeDomain] using
    HiaiPetz.TraceMonotonicity.supportTracePowerMonotonicity

theorem hiaiPetzLiebAndoConvexity :
    (∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      0 ≤ p →
      0 ≤ q →
      p + q ≤ 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * HiaiPetz.supportPowerTrace p q A1 B1 X +
            (1 - t) * HiaiPetz.supportPowerTrace p q A2 B2 X ≤
          HiaiPetz.supportPowerTrace p q (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X) ∧
    (∀ {n : ℕ} {p q : ℝ},
      0 ≤ p →
      0 ≤ q →
      p + q ≤ 1 →
      ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        HiaiPetz.powerTrace (-p) (-q) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
          t * HiaiPetz.powerTrace (-p) (-q) A1 B1 X1 +
            (1 - t) * HiaiPetz.powerTrace (-p) (-q) A2 B2 X2) ∧
    (∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      ((p ∈ Set.Icc (-1 : ℝ) 0 ∧ q ∈ Set.Icc (-1 : ℝ) 0) ∨
        (p ∈ Set.Icc (-1 : ℝ) 0 ∧ q ∈ Set.Icc (1 - p) 2) ∨
        (q ∈ Set.Icc (-1 : ℝ) 0 ∧ p ∈ Set.Icc (1 - q) 2)) →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        HiaiPetz.powerTrace p q (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X ≤
          t * HiaiPetz.powerTrace p q A1 B1 X +
            (1 - t) * HiaiPetz.powerTrace p q A2 B2 X) := by
  simpa only [HiaiPetz.TraceConvexity.LiebConcavity,
    HiaiPetz.TraceConvexity.LiebThreeVariableConvexity,
    HiaiPetz.TraceConvexity.AndoConvexity,
    HiaiPetz.TraceConvexity.AndoConvexityRange] using
    HiaiPetz.TraceConvexity.liebAndoConvexity

theorem liebConcavity :
    ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      0 ≤ p →
      0 ≤ q →
      p + q ≤ 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * HiaiPetz.supportPowerTrace p q A1 B1 X +
            (1 - t) * HiaiPetz.supportPowerTrace p q A2 B2 X ≤
          HiaiPetz.supportPowerTrace p q (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  exact HiaiPetz.TraceConvexity.liebConcavity

theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : QuantumChannel.CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hσ : σ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := 𝒦)) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv α ρ σ :=
  SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_monotone
    E hα_ge hα_ne1 hρ hσ hEρ hEσ

theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ]
    [Qudit 𝒦] [Nontrivial 𝒦]
    (E : QuantumChannel.CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α ρ σ :=
  SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_monotone
    E hα_ge hα_ne1 hρ hσ

theorem umegakiMonotoneOnPosDef : UmegakiDPI.MonotoneOnPosDef :=
  UmegakiDPI.monotoneOnPosDef

theorem monotoneOnNonNeg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : QuantumChannel.CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ σ := by
  exact UmegakiDPI.monotoneOnNonNeg E hρ hσ

theorem strongSubadditivity_of_state
    {ℋA ℋB ℋC : Type u}
    [Qudit ℋA] [Qudit ℋB] [Qudit ℋC]
    [Nontrivial ℋA] [Nontrivial ℋB] [Nontrivial ℋC]
    (ρ : L (TensorProduct ℂ ℋA (TensorProduct ℂ ℋB ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    VonNeumann.vonNeumannEntropy ρ +
        VonNeumann.vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) ≤
      VonNeumann.vonNeumannEntropy (QuantumChannel.traceOutThird ρ) +
        VonNeumann.vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) :=
  VonNeumann.strongSubadditivity_of_state ρ hρ hTr

theorem loewnerUnitIntervalCharacterizations {f : ℝ → ℝ} :
    (Quantum.TraceInequality.Loewner.OperatorMonotoneOnUnitInterval.{u} f ↔
      Nonempty (Quantum.TraceInequality.Loewner.IntegralRepOnUnitInterval f)) ∧
    (Nonempty (Quantum.TraceInequality.Loewner.PickExtensionOnUnitInterval f) ↔
      Nonempty (Quantum.TraceInequality.Loewner.IntegralRepOnUnitInterval f)) ∧
    (Quantum.TraceInequality.Loewner.LoewnerPosOnUnitInterval f →
      Quantum.TraceInequality.Loewner.OperatorMonotoneOnUnitInterval.{u} f) := by
  refine ⟨⟨?_, ?_⟩,
    Quantum.TraceInequality.Loewner.unitIntervalPickExtension_iff_integralRep f, ?_⟩
  · intro hmono
    exact (Quantum.TraceInequality.Loewner.unitInterval_loewnerPos_has_all_three.{u}
      (Quantum.TraceInequality.Loewner.loewnerPosOnUnitInterval_of_operatorMonotone
        (Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_toZero hmono))).2.1
  · rintro ⟨rep⟩
    exact Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_of_integralRep rep
  · intro hpos
    exact (Quantum.TraceInequality.Loewner.unitInterval_loewnerPos_has_all_three.{u} hpos).2.2

end ComparatorChallenges
