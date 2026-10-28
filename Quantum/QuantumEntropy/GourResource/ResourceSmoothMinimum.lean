/-
Double optimization and min dictionary for the resource smooth Dmax.
-/
import Quantum.QuantumEntropy.GourQuantumFirstArgumentModulus.GSLCore
import Quantum.QuantumEntropy.GourResource.SmoothMax
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem joint_lowerSemicontinuous
    {A : Type u} [Qudit.{u} A] [Nontrivial A] :
    LowerSemicontinuous (fun p : State.{u} A × State.{u} A => dm p.1.1 p.2.1) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro b
  induction b using EReal.rec with
  | bot =>
      have hempty : (fun p : State A × State A => dm p.1.1 p.2.1) ⁻¹' Set.Iic ⊥ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hnonneg : 0 ≤ dm p.1.1 p.2.1 :=
          OPT.quantumMaxRelativeEntropyBits_nonnegative p.1.1 p.2.1 p.1.2 p.2.2
        exact (not_le_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) hnonneg)) hp
      rw [hempty]
      exact isClosed_empty
  | coe r =>
      have hset : (fun p : State A × State A => dm p.1.1 p.2.1) ⁻¹' Set.Iic (r : EReal) =
          {p : State A × State A | p.1.1 ≤ (((2 : ℝ) ^ r : ℝ) : ℂ) • p.2.1} := by
        ext p
        exact OPT.quantumMaxRelativeEntropyBits_le_coe_iff_domination
          p.1.1 p.2.1 p.1.2 p.2.2 r
      rw [hset]
      exact isClosed_le continuous_fst.subtype_val
        (continuous_const.smul continuous_snd.subtype_val)
  | top =>
      convert (isClosed_univ : IsClosed (Set.univ : Set (State A × State A))) using 1
      ext p
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
      exact le_top

private theorem continuous_trace_distance
    {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) :
    Continuous (fun τ : State.{u} A => td ρ.1 τ.1) := by
  have hsub : Continuous (fun τ : State A =>
      (⟨ρ.1 - τ.1, ρ.2.1.isSelfAdjoint.sub τ.2.1.isSelfAdjoint⟩ :
        {X : L A // IsSelfAdjoint X})) :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  exact ((w40_trace_norm_continuity.{u} (H := A)).1.comp hsub).div_const 2

private theorem joint_minimum
    {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A)
    (S : Set (L.{u} A)) (ε : ℝ) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hS : S ⊆ {X | IsDensity.{u} X}) (hε : 0 ≤ ε) :
    ∃ (σ : L A) (τ : State A), σ ∈ S ∧ td ρ.1 τ.1 ≤ ε ∧
      ∀ (s : L A) (t : State A), s ∈ S → td ρ.1 t.1 ≤ ε → dm τ.1 σ ≤ dm t.1 s := by
  letI : CompactSpace (State A) :=
    isCompact_iff_compactSpace.mp (GourResource.gsl_b01.{u}.2.2 (A := A)).1
  let B : Set (State A) := {τ | td ρ.1 τ.1 ≤ ε}
  let T : Set (State A) := {σ | σ.1 ∈ S}
  have hB : IsClosed B := isClosed_le (continuous_trace_distance ρ) continuous_const
  have hT : IsClosed T := hclosed.preimage continuous_subtype_val
  have hneBT : (B ×ˢ T).Nonempty := by
    obtain ⟨σ, hσ⟩ := hne
    refine ⟨(ρ, ⟨σ, hS hσ⟩), ?_, hσ⟩
    change td ρ.1 ρ.1 ≤ ε
    simpa [td, w40T₁] using hε
  obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hneBT
    (hB.isCompact.prod hT.isCompact) (joint_lowerSemicontinuous.lowerSemicontinuousOn (B ×ˢ T))
  refine ⟨p.2.1, p.1, hp.2, hp.1, ?_⟩
  intro s t hs ht
  -- Read `IsMinOn` through `isMinOn_iff`; applying `hmin` directly makes the elaborator unfold
  -- the principal-filter `∀ᶠ` by `whnf`, which is very slow here.
  exact isMinOn_iff.mp hmin (t, (⟨s, hS hs⟩ : State A)) ⟨ht, hs⟩

theorem gsl_y59 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A),
  LowerSemicontinuous (fun p : State.{u} A × State.{u} A => dm.{u} p.1.1 p.2.1) ∧
  ∀ (S : Set (L.{u} A)) (ε : ℝ), S.Nonempty → IsClosed S →
    S ⊆ {X | IsDensity.{u} X} → ε ∈ Set.Icc 0 1 →
    res.{u} (fun X Y => smoothMax.{u} X Y ε) ρ.1 S =
      (⨅ (τ : L.{u} A) (_ : IsDensity.{u} τ ∧ td.{u} ρ.1 τ ≤ ε), res.{u} dm.{u} τ S) ∧
    ∃ (σ : L.{u} A) (τ : State.{u} A), σ ∈ S ∧ td.{u} ρ.1 τ.1 ≤ ε ∧
      dm.{u} τ.1 σ = res.{u} (fun X Y => smoothMax.{u} X Y ε) ρ.1 S ∧
      IsLeast {d : EReal | ∃ (s : L.{u} A) (t : State.{u} A),
        s ∈ S ∧ td.{u} ρ.1 t.1 ≤ ε ∧ d = dm.{u} t.1 s} (dm.{u} τ.1 σ)
:= by
  intro A _ _ ρ
  refine ⟨joint_lowerSemicontinuous, ?_⟩
  intro S ε hne hclosed hS hε
  constructor
  · unfold res smoothMax
    refine le_antisymm ?_ ?_
    · refine le_iInf fun τ => le_iInf fun hτ => le_iInf fun σ => le_iInf fun hσ => ?_
      exact iInf_le_of_le σ (iInf_le_of_le hσ
        (iInf_le_of_le τ (iInf_le_of_le hτ le_rfl)))
    · refine le_iInf fun σ => le_iInf fun hσ => le_iInf fun τ => le_iInf fun hτ => ?_
      exact iInf_le_of_le τ (iInf_le_of_le hτ
        (iInf_le_of_le σ (iInf_le_of_le hσ le_rfl)))
  · obtain ⟨σ, τ₀, hσ, hτ₀, hmin₀⟩ := joint_minimum ρ S ε hne hclosed hS hε.1
    have hchoice : ∃ τ : State A, td ρ.1 τ.1 ≤ ε ∧ dm τ.1 σ ≤ dm τ₀.1 σ := by
      by_cases hint : ε ∈ Set.Ioo 0 1
      · obtain ⟨τ, hτ, heq⟩ := GourResource.gsl_c15.{u} ρ ⟨σ, hS hσ⟩ ε hint
        refine ⟨τ, hτ, ?_⟩
        rw [heq]
        exact iInf_le_of_le τ₀.1 (iInf_le_of_le ⟨τ₀.2, hτ₀⟩ le_rfl)
      · exact ⟨τ₀, hτ₀, le_rfl⟩
    obtain ⟨τ, hτ, hle⟩ := hchoice
    have hmin (s : L A) (t : State A) (hs : s ∈ S) (ht : td ρ.1 t.1 ≤ ε) :
        dm τ.1 σ ≤ dm t.1 s := hle.trans (hmin₀ s t hs ht)
    refine ⟨σ, τ, hσ, hτ, ?_, ?_⟩
    · apply le_antisymm
      · exact le_iInf fun s => le_iInf fun hs => le_iInf fun t => le_iInf fun ht =>
          hmin s ⟨t, ht.1⟩ hs ht.2
      · exact iInf_le_of_le σ (iInf_le_of_le hσ
          (iInf_le_of_le τ.1 (iInf_le_of_le ⟨τ.2, hτ⟩ le_rfl)))
    · refine ⟨⟨σ, τ, hσ, hτ, rfl⟩, ?_⟩
      rintro d ⟨s, t, hs, ht, rfl⟩
      exact hmin s t hs ht

end GourResource

