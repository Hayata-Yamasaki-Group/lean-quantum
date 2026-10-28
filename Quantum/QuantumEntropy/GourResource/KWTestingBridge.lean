/-
In finite dimensions, transports effect operators and trace pairings by an isometry and identifies the hypothesis-testing quantities.
Uses optimal tests, monotonicity in the error, and the data-processing inequality.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.QuantumModel.KW.Distances.HypothesisTestingCore.Basic
import Quantum.QuantumModel.MatrixHockeyStick.GSLCore


open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

open QuantumModel in
private theorem b02_effect_iff (S : Sys) (M : L (Space S)) :
    effect M ↔ NativeNoCloning.POVMElement M := by
  simp only [effect, NativeNoCloning.POVMElement,
    ← LinearMap.nonneg_iff_isPositive, sub_nonneg]
  rfl

open QuantumModel in
private noncomputable def b02_effectEquiv (S : Sys) :
    {M : L (Space S) // effect M} ≃ NativeHypothesisTesting.Effect S where
  toFun M := NativeHypothesisTesting.Internal.matrixEffectOfPOVMElement
    M.1 ((b02_effect_iff S M.1).mp M.2)
  invFun Q := ⟨(operatorEquivMatrix S).symm Q.1,
    (b02_effect_iff S _).mpr
      (NativeHypothesisTesting.Internal.matrixEffect_to_povmElement Q)⟩
  left_inv M := by
    apply Subtype.ext
    exact (operatorEquivMatrix S).symm_apply_apply M.1
  right_inv Q := by
    apply Subtype.ext
    exact (operatorEquivMatrix S).apply_symm_apply Q.1

open QuantumModel in
private theorem b02_pairing_native (S : Sys)
    (M : {M : L (Space S) // effect M}) (X : L (Space S)) :
    pairing X M.1 = NativeHypothesisTesting.testValue (b02_effectEquiv S M) X := by
  change pairing X M.1 = NativeHypothesisTesting.testValue
    (NativeHypothesisTesting.Internal.matrixEffectOfPOVMElement M.1
      ((b02_effect_iff S M.1).mp M.2)) X
  rw [NativeHypothesisTesting.Internal.testValue_matrixEffectOfPOVMElement_operator]
  exact congrArg Complex.re (LinearMap.trace_mul_comm ℂ X M.1)

open QuantumModel in
private theorem b02_pairing_nonneg (S : Sys) (σ : DensityMatrix S)
    (M : {M : L (Space S) // effect M}) : 0 ≤ pairing σ.operator M.1 := by
  rw [b02_pairing_native]
  exact NativeHypothesisTesting.Internal.testValue_nonneg _ _ σ.nonneg

open QuantumModel in
private theorem b02_beta_native (S : Sys) (ρ σ : DensityMatrix S)
    (ε : OPT.ProbabilityLevel) :
    beta ρ.operator σ.operator ε.1 =
      (NativeHypothesisTesting.betaEpsilon ε ρ σ.operator : ℝ) := by
  let f := b02_effectEquiv S
  obtain ⟨Q, hQ⟩ := NativeHypothesisTesting.exists_betaOptimal ε ρ σ.operator σ.nonneg
  have hpair (R : NativeHypothesisTesting.Effect S) (X : L (Space S)) :
      pairing X (f.symm R).1 = NativeHypothesisTesting.testValue R X := by
    calc
      _ = NativeHypothesisTesting.testValue (f (f.symm R)) X :=
        b02_pairing_native S (f.symm R) X
      _ = _ := congrArg (fun Q => NativeHypothesisTesting.testValue Q X)
        (f.apply_symm_apply R)
  have hnonneg := NativeHypothesisTesting.Internal.testValue_nonneg Q σ.operator σ.nonneg
  have hvalue : pairing σ.operator (f.symm Q).1 =
      (NativeHypothesisTesting.betaEpsilon ε ρ σ.operator : ℝ) := by
    rw [hpair, ← hQ.2, Real.coe_toNNReal _ hnonneg]
  have hbdd : BddBelow {b : ℝ | ∃ M : L (Space S),
      effect M ∧ 1 - ε.1 ≤ pairing ρ.operator M ∧ b = pairing σ.operator M} := by
    refine ⟨0, ?_⟩
    rintro b ⟨M, hM, _, rfl⟩
    exact b02_pairing_nonneg S σ ⟨M, hM⟩
  have hmem : (NativeHypothesisTesting.betaEpsilon ε ρ σ.operator : ℝ) ∈
      {b : ℝ | ∃ M : L (Space S),
        effect M ∧ 1 - ε.1 ≤ pairing ρ.operator M ∧ b = pairing σ.operator M} :=
    ⟨(f.symm Q).1, (f.symm Q).2, (hpair Q ρ.operator).symm ▸ hQ.1, hvalue.symm⟩
  apply le_antisymm (csInf_le hbdd hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro b ⟨M, hM, hacc, rfl⟩
  have hm := NativeHypothesisTesting.Internal.betaEpsilon_le_objective ε ρ σ.operator
    ⟨f ⟨M, hM⟩, (b02_pairing_native S ⟨M, hM⟩ ρ.operator) ▸ hacc⟩
  have hm' := NNReal.coe_le_coe.mpr hm
  rwa [← b02_pairing_native S ⟨M, hM⟩ σ.operator,
    Real.coe_toNNReal _ (b02_pairing_nonneg S σ ⟨M, hM⟩)] at hm'

private noncomputable def b02_conj {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) : L A ≃⋆ₐ[ℂ] L B :=
  (linearToContinuousEndStarAlgEquiv A).trans
    (U.conjStarAlgEquiv.trans (linearToContinuousEndStarAlgEquiv B).symm)

private theorem b02_conj_apply {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) : b02_conj U X = push0 U X := rfl

private theorem b02_conj_trace {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) : Tr (b02_conj U X) = Tr X :=
  LinearMap.trace_conj' X U.toLinearEquiv

private theorem b02_conj_pairing {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X M : L A) :
    pairing (b02_conj U X) (b02_conj U M) = pairing X M := by
  unfold pairing
  rw [← map_mul, b02_conj_trace]

private theorem b02_conj_effect {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (M : L A) : effect (b02_conj U M) ↔ effect M := by
  simp only [effect, ← LinearMap.nonneg_iff_isPositive]
  rw [← map_one (b02_conj U), ← map_sub]
  exact and_congr (starAlgEquiv_nonneg_iff (b02_conj U))
    (starAlgEquiv_nonneg_iff (b02_conj U))

private theorem b02_beta_push {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (ρ σ : L A) (ε : ℝ) :
    beta (push0 U ρ) (push0 U σ) ε = beta ρ σ ε := by
  unfold beta
  congr 1
  ext b
  constructor
  · rintro ⟨M, hM, hacc, hb⟩
    obtain ⟨N, rfl⟩ := (b02_conj U).surjective M
    refine ⟨N, (b02_conj_effect U N).mp hM, ?_, ?_⟩
    · exact (b02_conj_pairing U ρ N) ▸ hacc
    · exact hb.trans (b02_conj_pairing U σ N)
  · rintro ⟨M, hM, hacc, hb⟩
    refine ⟨b02_conj U M, (b02_conj_effect U M).mpr hM, ?_, ?_⟩
    · exact (b02_conj_pairing U ρ M).symm ▸ hacc
    · exact hb.trans (b02_conj_pairing U σ M).symm

private noncomputable def b02_channel {A B : Type u} [Qudit A] [Qudit B]
    {H K : Type} [Qudit H] [Qudit K] (U : A ≃ₗᵢ[ℂ] H) (V : B ≃ₗᵢ[ℂ] K)
    (E : CPTP A B) : CompletelyPositiveMap (L H) (L K) where
  toLinearMap := (b02_conj V).toAlgEquiv.toLinearMap.comp
    (E.toCompletelyPositiveMap.toLinearMap.comp (b02_conj U).symm.toAlgEquiv.toLinearMap)
  map_cstarMatrix_nonneg' k M hM := by
    have h₁ : 0 ≤ M.map (b02_conj U).symm :=
      CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
      (b02_conj U).symm k M hM
    have h₂ := E.toCompletelyPositiveMap.map_cstarMatrix_nonneg' k _ h₁
    have h₃ : 0 ≤ ((M.map (b02_conj U).symm).map
        E.toCompletelyPositiveMap.toLinearMap).map (b02_conj V) :=
      CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
      (b02_conj V) k _ h₂
    exact h₃

private theorem b02_channel_trace {A B : Type u} [Qudit A] [Qudit B]
    {H K : Type} [Qudit H] [Qudit K] (U : A ≃ₗᵢ[ℂ] H) (V : B ≃ₗᵢ[ℂ] K)
    (E : CPTP A B) (X : L H) : Tr (b02_channel U V E X) = Tr X := by
  change Tr (b02_conj V (E.toFun ((b02_conj U).symm X))) = Tr X
  rw [b02_conj_trace, ← E.trace_map]
  exact (b02_conj_trace U ((b02_conj U).symm X)).symm.trans
    (congrArg Tr ((b02_conj U).apply_symm_apply X))

open QuantumModel in
private theorem b02_channel_native {A B : Type u} [Qudit A] [Qudit B]
    (S T : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (V : B ≃ₗᵢ[ℂ] Space T) (E : CPTP A B) :
    ∃ Φ : NativeNoCloning.Superoperator S T, IsCPTP Φ ∧
      ∀ X : L A, HPHom.toRawSuperoperator Φ (push0 U X) = push0 V (E.toFun X) := by
  let F := b02_channel U V E
  let Φ : NativeNoCloning.Superoperator S T :=
    ⟨WithConv.toConv F.toLinearMap,
      (LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _).mpr (map_star F)⟩
  refine ⟨Φ, ⟨⟨F, rfl⟩, b02_channel_trace U V E⟩, ?_⟩
  intro X
  change b02_conj V (E.toFun ((b02_conj U).symm (b02_conj U X))) = _
  rw [(b02_conj U).symm_apply_apply]
  rfl

open QuantumModel in
private theorem b02_dh_native (S : Sys) (ρ σ : DensityMatrix S)
    (ε : OPT.ProbabilityLevel) :
    dh ρ.operator σ.operator ε.1 =
      NativeHypothesisTesting.hypothesisTestingDiv ε ρ σ.operator := by
  simp only [dh, b02_beta_native, Real.toNNReal_coe,
    NativeHypothesisTesting.hypothesisTestingDiv]

open QuantumModel in
private theorem b02_dh_coords {A : Type u} [Qudit A]
    (S : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (ρ σ : L A) (r s : DensityMatrix S)
    (hr : r.operator = push0 U ρ) (hs : s.operator = push0 U σ)
    (ε : OPT.ProbabilityLevel) :
    dh ρ σ ε.1 = NativeHypothesisTesting.hypothesisTestingDiv ε r s.operator := by
  rw [← b02_dh_native]
  simp only [dh, hr, hs, b02_beta_push]

open QuantumModel in
private theorem b02_pull_effect {A : Type u} [Qudit A]
    (S : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (Q : NativeHypothesisTesting.Effect S) :
    ∃ M : L A, effect M ∧ ∀ X : L A,
      pairing X M = NativeHypothesisTesting.testValue Q (push0 U X) := by
  let N := (b02_effectEquiv S).symm Q
  let M := (b02_conj U).symm N.1
  have hMN : b02_conj U M = N.1 := (b02_conj U).apply_symm_apply N.1
  refine ⟨M, (b02_conj_effect U M).mp (hMN.symm ▸ N.2), ?_⟩
  intro X
  calc
    pairing X M = pairing (b02_conj U X) N.1 := by
      rw [← hMN, b02_conj_pairing]
    _ = NativeHypothesisTesting.testValue ((b02_effectEquiv S) N) (push0 U X) :=
      b02_pairing_native S N (push0 U X)
    _ = _ := congrArg (fun R => NativeHypothesisTesting.testValue R (push0 U X))
      ((b02_effectEquiv S).apply_symm_apply Q)

open QuantumModel in
private theorem b02_optimal_coords {A : Type u} [Qudit A]
    (S : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (ρ σ : L A) (r s : DensityMatrix S)
    (hr : r.operator = push0 U ρ) (hs : s.operator = push0 U σ)
    (ε : OPT.ProbabilityLevel) :
    ∃ M : L A, effect M ∧ pairing ρ M = 1 - ε.1 ∧
      pairing σ M = beta ρ σ ε.1 := by
  obtain ⟨Q, hQ, hacc⟩ :=
    NativeHypothesisTesting.exists_betaOptimal_acceptance_eq ε r s.operator s.nonneg
  obtain ⟨M, hM, hpair⟩ := b02_pull_effect S U Q
  refine ⟨M, hM, ?_, ?_⟩
  · rw [hpair, ← hr, hacc]
  · rw [hpair, ← hs, ← b02_beta_push U ρ σ, ← hr, ← hs, b02_beta_native, ← hQ.2]
    exact (Real.coe_toNNReal _
      (NativeHypothesisTesting.Internal.testValue_nonneg Q s.operator s.nonneg)).symm

private theorem b02_scalar_effect {A : Type u} [Qudit A]
    (ε : ℝ) (hε : ε ∈ Set.Icc 0 1) : effect ((1 - ε) • (1 : L A)) := by
  refine ⟨LinearMap.isPositive_one.smul_of_nonneg ?_, ?_⟩
  · exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hε.2)
  · have h : (1 : L A) - (1 - ε) • (1 : L A) = ε • (1 : L A) := by module
    rw [h]
    exact LinearMap.isPositive_one.smul_of_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).mpr hε.1)

private theorem b02_pairing_scalar {A : Type u} [Qudit A]
    (X : L A) (hX : Tr X = 1) (t : ℝ) : pairing X (t • (1 : L A)) = t := by
  simp [pairing, hX]

private theorem b02_log (ε : ℝ) (hε : ε < 1) :
    OPT.binaryNegLog2 (Real.toNNReal (1 - ε)) = ((-Real.logb 2 (1 - ε) : ℝ) : EReal) := by
  have hpos : 0 < 1 - ε := sub_pos.mpr hε
  rw [OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hpos)),
    Real.coe_toNNReal _ hpos.le]

open QuantumModel in
private theorem b02_native_lower (S : Sys) (ρ σ : DensityMatrix S)
    (ε : OPT.ProbabilityLevel) (hε : ε.1 < 1) :
    ((-Real.logb 2 (1 - ε.1) : ℝ) : EReal) ≤
      NativeHypothesisTesting.hypothesisTestingDiv ε ρ σ.operator := by
  let M : {M : L (Space S) // effect M} :=
    ⟨(1 - ε.1) • (1 : L (Space S)), b02_scalar_effect ε.1 ε.2⟩
  have hpair (X : L (Space S)) (hX : Tr X = 1) :
      NativeHypothesisTesting.testValue (b02_effectEquiv S M) X = 1 - ε.1 := by
    rw [← b02_pairing_native]
    exact b02_pairing_scalar X hX _
  have hβ := NativeHypothesisTesting.Internal.betaEpsilon_le_objective ε ρ σ.operator
    ⟨b02_effectEquiv S M, (hpair ρ.operator ρ.trace_one).symm.le⟩
  rw [hpair σ.operator σ.trace_one] at hβ
  rw [← b02_log ε.1 hε]
  exact NativeHypothesisTesting.Internal.binaryNegLog2_antitone hβ

open QuantumModel in
private theorem b02_laws_coords {A : Type u} [Qudit A]
    (S : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (ρ σ : L A) (r s : DensityMatrix S)
    (hr : r.operator = push0 U ρ) (hs : s.operator = push0 U σ)
    (ε δ : ℝ) (hε : ε ∈ Set.Ico 0 1) (hδ : δ ∈ Set.Ico 0 1) (hεδ : ε ≤ δ) :
    dh ρ σ ε ≤ dh ρ σ δ ∧
      ((-Real.logb 2 (1 - ε) : ℝ) : EReal) ≤ dh ρ σ ε ∧
      dh ρ ρ ε = ((-Real.logb 2 (1 - ε) : ℝ) : EReal) := by
  let e : OPT.ProbabilityLevel := ⟨ε, hε.1, hε.2.le⟩
  let d : OPT.ProbabilityLevel := ⟨δ, hδ.1, hδ.2.le⟩
  rw [b02_dh_coords S U ρ σ r s hr hs e, b02_dh_coords S U ρ σ r s hr hs d,
    b02_dh_coords S U ρ ρ r r hr hr e]
  refine ⟨NativeHypothesisTesting.hypothesisTestingDiv_mono_epsilon hεδ r s.operator,
    b02_native_lower S r s e hε.2, ?_⟩
  rw [NativeHypothesisTesting.hypothesisTestingDiv_self]
  exact b02_log ε hε.2

open QuantumModel in
private theorem b02_dpi_coords {A B : Type u} [Qudit A] [Qudit B]
    (S T : Sys) (U : A ≃ₗᵢ[ℂ] Space S) (V : B ≃ₗᵢ[ℂ] Space T)
    (ρ σ : L A) (r s : DensityMatrix S)
    (hr : r.operator = push0 U ρ) (hs : s.operator = push0 U σ)
    (E : CPTP A B) (ε : OPT.ProbabilityLevel) :
    dh (E.toFun ρ) (E.toFun σ) ε.1 ≤ dh ρ σ ε.1 := by
  obtain ⟨Φ, hΦ, hmap⟩ := b02_channel_native S T U V E
  let r' := NativeFidelity.channelApply r Φ hΦ
  let s' := NativeFidelity.channelApply s Φ hΦ
  have hr' : r'.operator = push0 V (E.toFun ρ) := by
    rw [NativeFidelity.channelApply_operator, hr, hmap]
  have hs' : s'.operator = push0 V (E.toFun σ) := by
    rw [NativeFidelity.channelApply_operator, hs, hmap]
  rw [b02_dh_coords T V _ _ r' s' hr' hs' ε, b02_dh_coords S U ρ σ r s hr hs ε]
  simpa only [r', s', NativeFidelity.channelApply_operator] using
    NativeHypothesisTesting.hypothesisTestingDiv_mono_of_isCPTP ε r s.operator s.nonneg Φ hΦ

/-- Correspondence with the finite-dimensional model for hypothesis testing (a foundation):
`beta`, `dh` and effect operators agree with the model's quantities and are transported by
isometric isomorphisms and quantum channels. Optimal tests and tests accepting with equality
exist for `ε ∈ [0, 1)`; `dh` is monotone in the error, equals `-log₂ (1 - ε)` on equal pairs,
and satisfies the data-processing inequality for quantum channels. -/
theorem gsl_b02 :
(∀ (S : QuantumModel.Sys) (ρ σ :
  QuantumModel.DensityMatrix S) (ε : OPT.ProbabilityLevel),
  beta ρ.operator σ.operator ε.1 =
    (QuantumModel.NativeHypothesisTesting.betaEpsilon ε ρ σ.operator : ℝ) ∧
  dh ρ.operator σ.operator ε.1 =
    QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv ε ρ
      σ.operator ∧
  (∃ e : {M : L (QuantumModel.Space S) // effect M} ≃
    QuantumModel.NativeHypothesisTesting.Effect S,
    ∀ M : {M : L (QuantumModel.Space S) // effect M}, ∀ X : L
      (QuantumModel.Space S),
      pairing X M.1 = QuantumModel.NativeHypothesisTesting.testValue (e M)
        X)) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S : QuantumModel.Sys) (U : A
  ≃ₗᵢ[ℂ] QuantumModel.Space S) (ρ σ : State.{u} A) (ε : ℝ),
  ε ∈ Set.Ico 0 1 →
  beta (push0.{u} U ρ.1) (push0.{u} U σ.1) ε = beta ρ.1 σ.1 ε) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] {B : Type u} [Qudit.{u} B] [Nontrivial B]
  (S T : QuantumModel.Sys) (U : A ≃ₗᵢ[ℂ]
    QuantumModel.Space S)
  (V : B ≃ₗᵢ[ℂ] QuantumModel.Space T) (E : CPTP.{u,u} A B),
  ∃ Φ : QuantumModel.NativeNoCloning.Superoperator S T,
    QuantumModel.IsCPTP Φ ∧
    ∀ X : L.{u} A, QuantumModel.HPHom.toRawSuperoperator Φ (push0.{u} U X)
      = push0.{u} V (E.toFun X)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ico 0 1 →
  ∃ M : L.{u} A, effect.{u} M ∧ 1 - ε ≤ pairing.{u} ρ.1 M ∧ pairing.{u} σ.1 M = beta.{u} ρ.1 σ.1
    ε)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ico 0 1 →
  ∃ M : L.{u} A, effect.{u} M ∧ pairing.{u} ρ.1 M = 1 - ε ∧ pairing.{u} σ.1 M = beta.{u} ρ.1 σ.1
    ε)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε δ : ℝ), ε ∈ Set.Ico 0 1 → δ ∈
  Set.Ico 0 1 → ε ≤ δ →
  dh.{u} ρ.1 σ.1 ε ≤ dh.{u} ρ.1 σ.1 δ ∧
  ((-Real.logb 2 (1 - ε) : ℝ) : EReal) ≤ dh.{u} ρ.1 σ.1 ε ∧
  dh.{u} ρ.1 ρ.1 ε = ((-Real.logb 2 (1 - ε) : ℝ) : EReal))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] {B : Type u} [Qudit.{u} B] [Nontrivial B]
  (ρ σ : State.{u} A) (E : CPTP.{u,u} A B) (ε : ℝ), ε ∈ Set.Ico 0 1 →
  dh.{u} (E.toFun ρ.1) (E.toFun σ.1) ε ≤ dh.{u} ρ.1 σ.1 ε))
:= by
  classical
  have hopt : ∀ {A : Type u} [Qudit A] [Nontrivial A] (ρ σ : State A)
      (ε : ℝ), ε ∈ Set.Ico 0 1 →
      ∃ M : L A, effect M ∧ pairing ρ.1 M = 1 - ε ∧
        pairing σ.1 M = beta ρ.1 σ.1 ε := by
    intro A _ _ ρ σ ε hε
    obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.{u}.1 (A := A)
    obtain ⟨e, he⟩ := (GourResource.gsl_b01.{u}.2.1 S U).1
    exact b02_optimal_coords S U ρ.1 σ.1 (e ρ) (e σ) (he ρ) (he σ)
      ⟨ε, hε.1, hε.2.le⟩
  refine ⟨?_, ?_, ?_, ?_, hopt, ?_, ?_⟩
  · intro S ρ σ ε
    exact ⟨b02_beta_native S ρ σ ε, b02_dh_native S ρ σ ε,
      b02_effectEquiv S, b02_pairing_native S⟩
  · intro A _ _ S U ρ σ ε _
    exact b02_beta_push U ρ.1 σ.1 ε
  · intro A _ _ B _ _ S T U V E
    exact b02_channel_native S T U V E
  · intro A _ _ ρ σ ε hε
    obtain ⟨M, hM, hacc, hβ⟩ := hopt ρ σ ε hε
    exact ⟨M, hM, hacc.symm.le, hβ⟩
  · intro A _ _ ρ σ ε δ hε hδ hεδ
    obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.{u}.1 (A := A)
    obtain ⟨e, he⟩ := (GourResource.gsl_b01.{u}.2.1 S U).1
    exact b02_laws_coords S U ρ.1 σ.1 (e ρ) (e σ) (he ρ) (he σ) ε δ hε hδ hεδ
  · intro A _ _ B _ _ ρ σ E ε hε
    obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.{u}.1 (A := A)
    obtain ⟨T, _, ⟨V⟩⟩ := GourResource.gsl_b01.{u}.1 (A := B)
    obtain ⟨e, he⟩ := (GourResource.gsl_b01.{u}.2.1 S U).1
    exact b02_dpi_coords S T U V ρ.1 σ.1 (e ρ) (e σ) (he ρ) (he σ) E
      ⟨ε, hε.1, hε.2.le⟩

end GourResource

