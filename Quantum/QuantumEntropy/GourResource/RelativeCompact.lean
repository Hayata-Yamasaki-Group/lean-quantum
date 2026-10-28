/-
Right lower semicontinuity of DU for every ρ.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5.
-/
/-
Minimum of DU on a closed free set.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5.
-/
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

-- Positive Petz powers give continuous approximants, including orthogonal states.
-- Their spectral classical values increase to the support-aware Umegaki value.
private noncomputable def approximation {A : Type u} [Qudit.{u} A]
    (a : ℝ) (ρ σ : L.{u} A) : EReal :=
  (((a - 1)⁻¹ / Real.log 2 : ℝ) : EReal) *
    ENNReal.log (ENNReal.ofReal (OPT.petzTracePowerRaw a ρ σ))

private theorem continuous_power {A : Type u} [Qudit.{u} A] [Nontrivial A]
    {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun X : L.{u} A => CFC.rpow X p) {X : L.{u} A | 0 ≤ X} := by
  exact continuousOn_id.cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem
    (ha' := fun _ hX => hX)
    (hf := NNReal.continuousOn_rpow_const (.inr hp))

private theorem approximation_continuous {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (a : OPT.RenyiOrderBelowOne) (ρ : State.{u} A) :
    Continuous (fun σ : State.{u} A => approximation (a.1 : ℝ) ρ.1 σ.1) := by
  have hp : Continuous (fun σ : State.{u} A => CFC.rpow σ.1 (1 - (a.1 : ℝ))) :=
    (continuous_power (sub_nonneg.mpr a.2.le)).comp_continuous continuous_subtype_val
      (fun σ => (LinearMap.nonneg_iff_isPositive σ.1).mpr σ.2.1)
  have hq : Continuous (fun σ : State.{u} A =>
      OPT.petzTracePowerRaw (a.1 : ℝ) ρ.1 σ.1) :=
    QuantumState.continuous_re_trace_lm.comp (continuous_const.mul hp)
  have hl := ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp hq)
  rw [continuous_iff_continuousAt]
  intro σ
  exact EReal.Tendsto.const_mul (hl.tendsto σ)
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))

private theorem approximation_spectral {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (a : OPT.RenyiOrderBelowOne) (ρ σ : State.{u} A) :
    approximation (a.1 : ℝ) ρ.1 σ.1 =
      ((OPT.classicalRenyiDivBitsFinitePMF a.1
        (OPT.petzSpectralP ρ.1 σ.1 ρ.2 σ.2)
        (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2) : ENNReal) : EReal) := by
  classical
  let b : OPT.PetzRenyiOrder := ⟨(a.1 : ℝ), a.1.2.le, a.2.le.trans (by norm_num)⟩
  have hb0 : (b : ℝ) ≠ 0 := a.1.2.ne'
  have hb1 : (b : ℝ) ≠ 1 := a.2.ne
  rw [← OPT.petzRenyiPunctured_eq_classicalSpectral b ρ.1 σ.1 ρ.2 σ.2 hb0 hb1]
  unfold OPT.petzRenyiPunctured
  split_ifs with h
  · have hq := (OPT.petzTracePower_real_and_pos_of_admissible
      b ρ.1 σ.1 ρ.2 σ.2 hb0 hb1 h).2
    change 0 < OPT.petzTracePowerRaw (a.1 : ℝ) ρ.1 σ.1 at hq
    rw [approximation, ENNReal.log_ofReal_of_pos hq, ← EReal.coe_mul]
    apply congrArg (fun x : ℝ => (x : EReal))
    change ((a.1 : ℝ) - 1)⁻¹ / Real.log 2 *
      Real.log (OPT.petzTracePowerRaw (a.1 : ℝ) ρ.1 σ.1) =
      ((a.1 : ℝ) - 1)⁻¹ * Real.logb 2 (OPT.petzTracePowerRaw (a.1 : ℝ) ρ.1 σ.1)
    rw [Real.logb]
    ring
  · have hmul : ρ.1 * σ.1 = 0 := by
      by_contra hne
      exact h (.inr ⟨a.2, hne⟩)
    have hq := (OPT.petzTraceExpression_eq_some_zero_of_lt_one_of_mul_eq_zero
      (a.1 : ℝ) ρ.1 σ.1 a.1.2.le ρ.2 σ.2 a.2 hmul).2.1
    rw [OPT.petzSupportTracePower_eq_raw _ _ _ a.1.2.ne' a.2.ne] at hq
    rw [approximation, hq, ENNReal.ofReal_zero, ENNReal.log_zero]
    exact EReal.coe_mul_bot_of_neg
      (div_neg_of_neg_of_pos (inv_lt_zero.mpr (sub_neg.mpr a.2))
        (Real.log_pos (by norm_num)))

private theorem du_spectral {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) :
    du.{u} ρ.1 σ.1 =
      ((OPT.classicalKLDivergenceBitsPMF
        (OPT.petzSpectralP ρ.1 σ.1 ρ.2 σ.2)
        (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2) : ENNReal) : EReal) := by
  rw [du, ← OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN]
  simpa only [OPT.petzQuantumRenyiDivergence, OPT.petzRenyiOrderOne,
    Subtype.coe_mk, one_ne_zero, ↓reduceDIte] using
    (OPT.petzRenyiEndpointValues_eq_classicalSpectral ρ.1 σ.1 ρ.2 σ.2).2

private theorem approximation_le_du {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (a : OPT.RenyiOrderBelowOne) (ρ σ : State.{u} A) :
    approximation (a.1 : ℝ) ρ.1 σ.1 ≤ du.{u} ρ.1 σ.1 := by
  rw [approximation_spectral, du_spectral]
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  unfold OPT.classicalRenyiDivBitsFinitePMF OPT.classicalKLDivergenceBitsPMF
  apply ENNReal.div_le_div_right
  simpa only [OPT.classicalRenyiDivPMF_one] using
    OPT.classicalRenyiDivPMF_monotone_order
      (show a.1 ≤ OPT.RenyiOrder.one from a.2.le)
      (OPT.petzSpectralP ρ.1 σ.1 ρ.2 σ.2) (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2)

private theorem approximation_tendsto {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) :
    Tendsto (fun a : OPT.RenyiOrderBelowOne => approximation (a.1 : ℝ) ρ.1 σ.1)
      atTop (𝓝 (du.{u} ρ.1 σ.1)) := by
  simp_rw [approximation_spectral, du_spectral]
  apply continuous_coe_ennreal_ereal.continuousAt.tendsto.comp
  exact (ENNReal.continuous_div_const _
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.log_pos (by norm_num)))).continuousAt.tendsto.comp
    (OPT.classicalRenyiDivPMF_tendsto_kl_fromBelow
      (OPT.petzSpectralP ρ.1 σ.1 ρ.2 σ.2) (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2))

theorem gsl_y56 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A),
  LowerSemicontinuous (fun σ : State.{u} A => du.{u} ρ.1 σ.1)
:= by
  intro A _ _ ρ σ y hy
  letI : Nonempty OPT.RenyiOrderBelowOne := ⟨⟨⟨1 / 2, by norm_num⟩, by norm_num⟩⟩
  obtain ⟨a, ha⟩ := ((approximation_tendsto ρ σ).eventually (Ioi_mem_nhds hy)).exists
  filter_upwards [(approximation_continuous a ρ).lowerSemicontinuous σ y ha] with τ hτ
  exact hτ.trans_le (approximation_le_du a ρ τ)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y57 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (S : Set (L.{u} A)),
  S.Nonempty → IsClosed S → S ⊆ {X | IsDensity.{u} X} →
  ∃ σ ∈ S, du.{u} ρ.1 σ = res.{u} du.{u} ρ.1 S
:= by
  intro A _ _ ρ S hne hclosed hdensity
  let T : Set (State.{u} A) := {σ | σ.1 ∈ S}
  have hTne : T.Nonempty := by
    obtain ⟨σ, hσ⟩ := hne
    exact ⟨⟨σ, hdensity hσ⟩, hσ⟩
  have himage : Subtype.val '' T = S := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hσ
      exact ⟨⟨σ, hdensity hσ⟩, hσ, rfl⟩
  have hTcompact : IsCompact T := by
    apply Subtype.isCompact_iff.mpr
    rw [himage]
    exact (GourResource.gsl_b01.2.2 (A := A)).1.of_isClosed_subset hclosed hdensity
  obtain ⟨σ, hσ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hTne hTcompact
    ((GourResource.gsl_y56.{u} ρ).lowerSemicontinuousOn T)
  refine ⟨σ.1, hσ, le_antisymm ?_ ?_⟩
  · unfold res
    refine le_iInf fun τ => le_iInf fun hτ => ?_
    exact hmin (show (⟨τ, hdensity hτ⟩ : State.{u} A) ∈ T from hτ)
  · exact iInf_le_of_le σ.1 (iInf_le_of_le hσ le_rfl)

end GourResource

