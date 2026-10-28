/-
Lower semicontinuity and attainment of the EReal-valued Dmax on the closed trace ball. Without support inclusion the value can be ⊤.
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropyDensity.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_c15_dm_le_iff {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (τ σ : State.{u} A) (r : ℝ) :
    dm τ.1 σ.1 ≤ (r : EReal) ↔ τ.1 ≤ ((2 : ℝ) ^ r) • σ.1 := by
  constructor
  · intro h
    have hfinite : OPT.OrderedCone.maxRelEntropy τ.1 σ.1 ≠ ⊤ :=
      (lt_of_le_of_lt h (EReal.coe_lt_top r)).ne
    obtain ⟨s, hs, hdom⟩ :=
      OPT.OrderedCone.maxRelEntropy_attained_of_isDensity τ.1 σ.1 τ.2 σ.2 hfinite
    have hsr : s ≤ r := EReal.coe_le_coe_iff.mp (hs ▸ h)
    have hdom' : τ.1 ≤ ((2 : ℝ) ^ s) • σ.1 := by
      simpa only [Complex.coe_smul] using hdom
    exact hdom'.trans (smul_le_smul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsr)
      ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1))
  · exact OPT.OrderedCone.maxRelEntropy_le_of_domination

private theorem gsl_c15_dm_ne_bot {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (τ σ : State.{u} A) : dm τ.1 σ.1 ≠ ⊥ := by
  intro hbot
  have hfinite : OPT.OrderedCone.maxRelEntropy τ.1 σ.1 ≠ ⊤ := by
    change dm τ.1 σ.1 ≠ ⊤
    rw [hbot]
    exact bot_ne_top
  obtain ⟨r, hr, _⟩ :=
    OPT.OrderedCone.maxRelEntropy_attained_of_isDensity τ.1 σ.1 τ.2 σ.2 hfinite
  exact EReal.coe_ne_bot r (hr.symm.trans hbot)

private theorem gsl_c15_dm_lowerSemicontinuous {A : Type u} [Qudit.{u} A]
    [Nontrivial A] (σ : State.{u} A) :
    LowerSemicontinuous (fun τ : State.{u} A => dm τ.1 σ.1) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro z
  induction z using EReal.rec with
  | bot =>
      have hempty : {τ : State A | dm τ.1 σ.1 ≤ ⊥} = ∅ := by
        ext τ
        simp only [Set.mem_setOf_eq, le_bot_iff, Set.mem_empty_iff_false, iff_false]
        exact gsl_c15_dm_ne_bot τ σ
      change IsClosed {τ : State A | dm τ.1 σ.1 ≤ ⊥}
      rw [hempty]
      exact isClosed_empty
  | coe r =>
      have hclosed : IsClosed {τ : State A | τ.1 ≤ ((2 : ℝ) ^ r) • σ.1} :=
        isClosed_le continuous_subtype_val continuous_const
      convert hclosed using 1
      ext τ
      exact gsl_c15_dm_le_iff τ σ r
  | top =>
      change IsClosed {τ : State A | dm τ.1 σ.1 ≤ (⊤ : EReal)}
      have huniv : {τ : State A | dm τ.1 σ.1 ≤ (⊤ : EReal)} = Set.univ := by
        ext τ
        exact iff_of_true (show dm τ.1 σ.1 ≤ (⊤ : EReal) from le_top)
          (Set.mem_univ τ)
      rw [huniv]
      exact isClosed_univ

private theorem gsl_c15_td_continuous {A : Type u} [Qudit.{u} A]
    [Nontrivial A] (ρ : State.{u} A) :
    Continuous (fun τ : State.{u} A => td ρ.1 τ.1) := by
  let f : State A → {X : L A // IsSelfAdjoint X} := fun τ =>
    ⟨ρ.1 - τ.1, ρ.2.1.isSelfAdjoint.sub τ.2.1.isSelfAdjoint⟩
  have hf : Continuous f :=
    (continuous_const.sub continuous_subtype_val).subtype_mk _
  exact ((w40_trace_norm_continuity (H := A)).1.comp hf).div_const 2

theorem gsl_c15 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  ∃ τ : State.{u} A, td.{u} ρ.1 τ.1 ≤ ε ∧ dm.{u} τ.1 σ.1 = smoothMax.{u} ρ.1 σ.1 ε)
:= by
  intro A _ _ ρ σ ε hε
  letI : CompactSpace (State A) :=
    isCompact_iff_compactSpace.mp (GourResource.gsl_b01.2.2 (A := A)).1
  let K : Set (State A) := {τ | td ρ.1 τ.1 ≤ ε}
  have hne : K.Nonempty := by
    refine ⟨ρ, ?_⟩
    change td ρ.1 ρ.1 ≤ ε
    simpa only [td, sub_self, w40T₁, star_zero, zero_mul, CFC.sqrt_zero,
      map_zero, Complex.zero_re, zero_div] using hε.1.le
  have hcompact : IsCompact K :=
    (isClosed_le (gsl_c15_td_continuous ρ) continuous_const).isCompact
  obtain ⟨τ, hτ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hcompact
    ((gsl_c15_dm_lowerSemicontinuous σ).lowerSemicontinuousOn K)
  refine ⟨τ, hτ, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro X
    apply le_iInf
    intro hX
    exact (isMinOn_iff.mp hmin) ⟨X, hX.1⟩ hX.2
  · exact iInf_le_of_le τ.1 (iInf_le_of_le ⟨τ.2, hτ⟩ le_rfl)

end GourResource

