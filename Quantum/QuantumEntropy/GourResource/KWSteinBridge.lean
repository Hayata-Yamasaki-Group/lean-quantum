/-
Composition connecting the quantification over arbitrary δ and all tails in the operational predicate to the liminf/limsup at fixed ε.
-/
import Quantum.QuantumModel.KW.Entropies.SteinTheorem.GSLCore
import Quantum.QuantumEntropy.GourResource.KWEntropyBridge
import Quantum.QuantumEntropy.GourResource.KWTensorBridge
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem b06_scale (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    ((1 / (n : ℝ) : ℝ) : EReal) * (((n : ℝ) * r : ℝ) : EReal) =
      (r : EReal) := by
  rw [← EReal.coe_mul]
  congr 1
  field_simp

private theorem b06_protocol_lower
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (ε : OPT.ProbabilityLevel) (n : ℕ) (r : ℝ)
    (P : QuantumModel.NativeStein.HypothesisTestingProtocol n ρ σ
      (OPT.binaryExponentProbability r) ⟨ε.1, ε.2.1⟩) :
    (r : EReal) ≤
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
        (QuantumModel.densityTensorPow σ n).operator := by
  have herror : 1 -
      QuantumModel.NativeHypothesisTesting.testValue P.test
        (QuantumModel.densityTensorPow ρ n).operator ≤ ε.1 := by
    exact (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr P.typeI_le)
  have hb := QuantumModel.NativeHypothesisTesting.Internal.betaEpsilon_le_objective
    ε (QuantumModel.densityTensorPow ρ n)
    (QuantumModel.densityTensorPow σ n).operator
    ⟨P.test, by linarith⟩
  have hl := QuantumModel.NativeHypothesisTesting.Internal.binaryNegLog2_antitone
    (hb.trans P.typeII_le)
  rw [OPT.binaryNegLog2_binaryExponentProbability] at hl
  exact hl

private theorem b06_no_protocol_upper
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (ε : OPT.ProbabilityLevel) (n : ℕ) (r : ℝ)
    (h : ¬ Nonempty
      (QuantumModel.NativeStein.HypothesisTestingProtocol n ρ σ
        (OPT.binaryExponentProbability r) ⟨ε.1, ε.2.1⟩)) :
    QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
      (QuantumModel.densityTensorPow ρ n)
      (QuantumModel.densityTensorPow σ n).operator ≤ (r : EReal) := by
  obtain ⟨Q, hQ⟩ := QuantumModel.NativeHypothesisTesting.exists_betaOptimal
    ε (QuantumModel.densityTensorPow ρ n)
    (QuantumModel.densityTensorPow σ n).operator
    (QuantumModel.densityTensorPow σ n).nonneg
  have hb : OPT.binaryExponentProbability r ≤
      QuantumModel.NativeHypothesisTesting.betaEpsilon ε
        (QuantumModel.densityTensorPow ρ n)
        (QuantumModel.densityTensorPow σ n).operator := by
    by_contra hn
    apply h
    refine ⟨⟨Q, ?_, ?_⟩⟩
    · exact hQ.2.trans_le (le_of_not_ge hn)
    · apply Real.toNNReal_le_iff_le_coe.mpr
      change 1 - _ ≤ ε.1
      linarith [hQ.1]
  have hl := QuantumModel.NativeHypothesisTesting.Internal.binaryNegLog2_antitone hb
  rw [OPT.binaryNegLog2_binaryExponentProbability] at hl
  exact hl

private theorem b06_achievable
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (R : ℝ) (ε : OPT.ProbabilityLevel) (hε : 0 < ε.1)
    (hR : QuantumModel.NativeStein.IsAchievableRate ρ σ R) :
    (R : EReal) ≤ Filter.liminf (rate (fun n =>
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
        (QuantumModel.densityTensorPow σ n).operator)) atTop := by
  apply (le_liminf_iff').mpr
  intro y hy
  obtain ⟨r, hyr, hrR⟩ := EReal.exists_between_coe_real hy
  have hd : 0 < R - r := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hrR)
  filter_upwards [hR.2 ε hε (R - r) hd, eventually_ne_atTop 0] with n hn hn0
  obtain ⟨P⟩ := hn
  have hl := b06_protocol_lower S ρ σ ε n ((n : ℝ) * (R - (R - r))) P
  have hs := mul_le_mul_of_nonneg_left hl
    (EReal.coe_nonneg.mpr (by positivity : 0 ≤ 1 / (n : ℝ)))
  rw [b06_scale n hn0, sub_sub_cancel] at hs
  exact hyr.le.trans (by simpa only [rate, if_neg hn0] using hs)

private theorem b06_converse
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (R : ℝ) (ε : OPT.ProbabilityLevel) (hε : ε.1 < 1)
    (hR : QuantumModel.NativeStein.IsStrongConverseRate ρ σ R) :
    Filter.limsup (rate (fun n =>
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
        (QuantumModel.densityTensorPow σ n).operator)) atTop ≤ (R : EReal) := by
  apply (limsup_le_iff').mpr
  intro y hy
  obtain ⟨r, hRr, hry⟩ := EReal.exists_between_coe_real hy
  have hd : 0 < r - R := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hRr)
  filter_upwards [hR.2 ε hε (r - R) hd, eventually_ne_atTop 0] with n hn hn0
  have hl := b06_no_protocol_upper S ρ σ ε n ((n : ℝ) * (R + (r - R))) hn
  have hs := mul_le_mul_of_nonneg_left hl
    (EReal.coe_nonneg.mpr (by positivity : 0 ≤ 1 / (n : ℝ)))
  rw [b06_scale n hn0, add_sub_cancel] at hs
  apply le_trans _ hry.le
  simpa only [rate, if_neg hn0] using hs

private theorem b06_native_bounds
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (ε : OPT.ProbabilityLevel) (hε0 : 0 < ε.1) (hε1 : ε.1 < 1)
    (hsupp : QuantumModel.DensityMatrix.SupportLE ρ σ) :
    let a := rate (fun n =>
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
        (QuantumModel.densityTensorPow σ n).operator)
    let D := QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits
      ρ σ.operator
    Filter.limsup a atTop ≤ D ∧ D ≤ Filter.liminf a atTop := by
  dsimp only
  have hfinite :
      QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits ρ σ.operator =
        ((SandwichedRenyiRelativeEntropy.umegakiNorm ρ.operator σ.operator /
          Real.log 2 : ℝ) : EReal) := by
    change SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ.operator σ.operator /
      ((Real.log 2 : ℝ) : EReal) = _
    have hs : SandwichedRenyiRelativeEntropy.suppLE ρ.operator σ.operator :=
      (QuantumModel.DensityMatrix.supportLE_iff_suppLE ρ σ).mp hsupp
    rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_pos hs, ← EReal.coe_div]
  have hcoe :
      (((QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits
        ρ σ.operator).toReal : ℝ) : EReal) =
      QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits ρ σ.operator := by
    rw [hfinite, EReal.toReal_coe]
  constructor
  · rw [← hcoe]
    exact b06_converse S ρ σ _ ε hε1
      (QuantumModel.NativeStein.isStrongConverseRate_umegaki_of_supportLE ρ σ hsupp)
  · rw [← hcoe]
    exact b06_achievable S ρ σ _ ε hε0
      (QuantumModel.NativeStein.isAchievableRate_umegaki_of_supportLE ρ σ hsupp)

private theorem b06_tensor_dh
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (S : QuantumModel.Sys) (ρ σ : State.{u} A)
    (r s : QuantumModel.DensityMatrix S) (ε : ℝ)
    (hε : ε ∈ Set.Ioo 0 1) (n : ℕ)
    (U : Copy.{u} A n ≃ₗᵢ[ℂ]
      QuantumModel.Space (QuantumModel.systemPow S n))
    (hr : push0 U (pow ρ n) = (QuantumModel.densityTensorPow r n).operator)
    (hs : push0 U (pow σ n) = (QuantumModel.densityTensorPow s n).operator) :
    dh (pow ρ n) (pow σ n) ε =
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv
        ⟨ε, hε.1.le, hε.2.le⟩ (QuantumModel.densityTensorPow r n)
        (QuantumModel.densityTensorPow s n).operator := by
  let ρn : State (Copy A n) := ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
  let σn : State (Copy A n) := ⟨pow σ n, (w42_tensor_spectral_dictionary.1 σ n).2.1⟩
  rw [← (GourResource.gsl_b02.{u}.1 _
    (QuantumModel.densityTensorPow r n)
    (QuantumModel.densityTensorPow s n) ⟨ε, hε.1.le, hε.2.le⟩).2.1,
    ← hr, ← hs]
  exact congrArg (fun b => OPT.binaryNegLog2 (Real.toNNReal b))
    (GourResource.gsl_b02.2.1 _ U ρn σn ε ⟨hε.1.le, hε.2⟩).symm

/-- Simple hypothesis testing in the finite-dimensional model (a foundation): estimates of the
lower and upper limits of the testing rate at a fixed `ε ∈ (0, 1)`; if `ρ` and `σ` satisfy
the support inclusion, the rate converges to the Umegaki relative entropy. -/
theorem gsl_b06 :
(∀ (S : QuantumModel.Sys) (ρ σ :
  QuantumModel.DensityMatrix S) (R : ℝ) (ε : OPT.ProbabilityLevel),
  0 < ε.1 → ε.1 < 1 →
  (QuantumModel.NativeStein.IsAchievableRate ρ σ R →
    (R : EReal) ≤ Filter.liminf (rate (fun n =>
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
          (QuantumModel.densityTensorPow σ n).operator)) atTop) ∧
  (QuantumModel.NativeStein.IsStrongConverseRate ρ σ R →
    Filter.limsup (rate (fun n =>
      QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε
        (QuantumModel.densityTensorPow ρ n)
          (QuantumModel.densityTensorPow σ n).operator)) atTop ≤ (R :
          EReal))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  SandwichedRenyiRelativeEntropy.suppLE.{u} ρ.1 σ.1 →
  Filter.limsup (rate (fun n => dh.{u} (pow.{u} ρ n) (pow.{u} σ n) ε)) atTop ≤ du.{u} ρ.1 σ.1)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  SandwichedRenyiRelativeEntropy.suppLE.{u} ρ.1 σ.1 →
  du.{u} ρ.1 σ.1 ≤ Filter.liminf (rate (fun n => dh.{u} (pow.{u} ρ n) (pow.{u} σ n) ε)) atTop)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  SandwichedRenyiRelativeEntropy.suppLE.{u} ρ.1 σ.1 →
  Tendsto (rate (fun n => dh.{u} (pow.{u} ρ n) (pow.{u} σ n) ε)) atTop (𝓝 (du.{u} ρ.1 σ.1))))
:= by
  have hbounds : ∀ {A : Type u} [Qudit.{u} A] [Nontrivial A]
      (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
      SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1 →
      Filter.limsup (rate (fun n => dh (pow ρ n) (pow σ n) ε)) atTop ≤ du ρ.1 σ.1 ∧
      du ρ.1 σ.1 ≤ Filter.liminf (rate (fun n => dh (pow ρ n) (pow σ n) ε)) atTop := by
    intro A _ _ ρ σ ε hε hsupp
    obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
    obtain ⟨e, he⟩ := (GourResource.gsl_b01.2.1 S U).1
    have hs : QuantumModel.DensityMatrix.SupportLE (e ρ) (e σ) := by
      apply (QuantumModel.DensityMatrix.supportLE_iff_suppLE (e ρ) (e σ)).mpr
      rw [he ρ, he σ]
      exact ((GourResource.gsl_b01.2.1 S U).2 ρ.1 σ.1).2.2.2.mp hsupp
    have hD : du ρ.1 σ.1 =
        QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits
          (e ρ) (e σ).operator := by
      rw [← (GourResource.gsl_b03.{u}.1 S (e ρ) (e σ)).1, he ρ, he σ]
      exact (GourResource.gsl_b03.2.1 S U ρ σ).1.symm
    have hseq : (fun n => dh (pow ρ n) (pow σ n) ε) = (fun n =>
        QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv
          ⟨ε, hε.1.le, hε.2.le⟩ (QuantumModel.densityTensorPow (e ρ) n)
          (QuantumModel.densityTensorPow (e σ) n).operator) := by
      funext n
      obtain ⟨Un, hn⟩ := GourResource.gsl_b05.{u} S U n
      exact b06_tensor_dh S ρ σ (e ρ) (e σ) ε hε n Un
        (hn ρ (e ρ) (he ρ)) (hn σ (e σ) (he σ))
    rw [hseq, hD]
    exact b06_native_bounds S (e ρ) (e σ) ⟨ε, hε.1.le, hε.2.le⟩ hε.1 hε.2 hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S ρ σ R ε hε0 hε1
    exact ⟨b06_achievable S ρ σ R ε hε0, b06_converse S ρ σ R ε hε1⟩
  · intro A _ _ ρ σ ε hε hsupp
    exact (hbounds ρ σ ε hε hsupp).1
  · intro A _ _ ρ σ ε hε hsupp
    exact (hbounds ρ σ ε hε hsupp).2
  · intro A _ _ ρ σ ε hε hsupp
    exact tendsto_of_le_liminf_of_limsup_le
      (hbounds ρ σ ε hε hsupp).2 (hbounds ρ σ ε hε hsupp).1

end GourResource

