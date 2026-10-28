/-
Right continuity of the resource Petz quantity.
-/
/-
Two-sided estimates of the resource Petz quantity.
-/
import Quantum.QuantumEntropy.GourResource.ResourceSubadditivity
import Quantum.QuantumEntropy.GourResource.ResourcePetzMinimum
import Quantum.QuantumEntropy.GourResource.TestingRenyiLower
import Quantum.QuantumEntropy.GourResource.TestingRenyiUpper
import Quantum.QuantumEntropy.GourQuantumRelativeEntropySemicontinuity.GSLCore
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem petz_spectral_above_one
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (α : OPT.RenyiOrder) (hα : 1 < (α : ℝ)) :
    petz α ρ σ =
      (OPT.classicalRenyiDivBitsFinitePMF α
        (OPT.petzSpectralP ρ σ hρ hσ) (OPT.petzSpectralQ ρ σ hρ hσ) : EReal) := by
  classical
  have hpos : 0 ≤ (α : ℝ) := α.property.le
  have hz : (α : ℝ) ≠ 0 := ne_of_gt α.property
  have ho : (α : ℝ) ≠ 1 := ne_of_gt hα
  simp only [petz, dif_pos hpos, dif_pos hρ, dif_pos hσ,
    OPT.petzQuantumRenyiDivergenceFinite,
    OPT.w26PetzQuantumRenyiDivergenceFinite, dif_neg hz, dif_neg ho]
  by_cases hs : SandwichedRenyiRelativeEntropy.suppLE ρ σ
  · rw [dif_pos (Or.inl hs)]
    simpa only [if_pos hs] using
      OPT.petzFiniteLogFormula_eq_classicalSpectral_of_one_lt α hα ρ σ hρ hσ
  · have ha : ¬ (SandwichedRenyiRelativeEntropy.suppLE ρ σ ∨
        (α : ℝ) < 1 ∧ ρ * σ ≠ 0) := by
      simp only [hs, false_or, not_lt_of_ge hα.le, false_and, not_false_eq_true]
    rw [dif_neg ha]
    simpa only [if_neg hs] using
      OPT.petzFiniteLogFormula_eq_classicalSpectral_of_one_lt α hα ρ σ hρ hσ

private theorem du_spectral
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    du ρ σ = (OPT.classicalKLDivergenceBitsPMF
      (OPT.petzSpectralP ρ σ hρ hσ) (OPT.petzSpectralQ ρ σ hρ hσ) : EReal) := by
  rw [du, ← OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN ρ σ hρ hσ]
  simpa only [OPT.petzQuantumRenyiDivergence, OPT.petzRenyiOrderOne,
    Subtype.coe_mk, one_ne_zero, ↓reduceDIte] using
      (OPT.petzRenyiEndpointValues_eq_classicalSpectral ρ σ hρ hσ).2

private theorem du_le_petz
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (α : ℝ) (hα : 1 < α) : du ρ σ ≤ petz α ρ σ := by
  let a : OPT.RenyiOrder := ⟨α, lt_trans zero_lt_one hα⟩
  rw [du_spectral ρ σ hρ hσ, petz_spectral_above_one ρ σ hρ hσ a hα]
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  unfold OPT.classicalKLDivergenceBitsPMF OPT.classicalRenyiDivBitsFinitePMF
  apply ENNReal.div_le_div_right
  rw [← OPT.classicalRenyiDivPMF_one]
  exact OPT.classicalRenyiDivPMF_monotone_order (show OPT.RenyiOrder.one ≤ a from hα.le) _ _

private theorem petz_tendsto_du
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    Tendsto (fun α : ℝ => petz α ρ σ) (𝓝[Set.Ioi 1] 1) (𝓝 (du ρ σ)) := by
  let a : ℝ → OPT.RenyiOrder := fun α =>
    ⟨max α (1 / 2), lt_of_lt_of_le (by norm_num) (le_max_right _ _)⟩
  have ha : Tendsto a (𝓝[Set.Ioi 1] 1) (𝓝 OPT.RenyiOrder.one) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun α : ℝ => max α (1 / 2)) _ (𝓝 (1 : ℝ))
    have hm : Tendsto (fun α : ℝ => max α (1 / 2))
        (𝓝 1) (𝓝 (max 1 (1 / 2))) :=
      (continuous_id.max continuous_const).continuousAt.tendsto
    simpa only [max_eq_left (show (1 / 2 : ℝ) ≤ 1 by norm_num)] using
      hm.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
  have hc := (OPT.classicalRenyiDivBitsFinite_tendsto_one
    (OPT.petzSpectralP ρ σ hρ hσ) (OPT.petzSpectralQ ρ σ hρ hσ)).comp ha
  rw [du_spectral ρ σ hρ hσ]
  apply (EReal.tendsto_coe_ennreal.mpr hc).congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  have he : (a α : ℝ) = α := max_eq_left (by change 1 < α at hα; linarith)
  have hp := petz_spectral_above_one ρ σ hρ hσ (a α) (by rw [he]; exact hα)
  rw [he] at hp
  exact hp.symm

private theorem res_petz_tendsto_du
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : L A) (hρ : IsDensity ρ) (S : Set (L A))
    (hS : S ⊆ {X | IsDensity X}) :
    Tendsto (fun α : ℝ => res (petz α) ρ S)
      (𝓝[Set.Ioi 1] 1) (𝓝 (res du ρ S)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with α hα
    apply lt_of_lt_of_le hb
    exact iInf_mono fun σ => iInf_mono fun hσ => du_le_petz ρ σ hρ (hS hσ) α hα
  · intro b hb
    obtain ⟨σ, hσ⟩ := iInf_lt_iff.mp hb
    obtain ⟨hmem, hlt⟩ := iInf_lt_iff.mp hσ
    have ht := (petz_tendsto_du ρ σ hρ (hS hmem)).eventually (gt_mem_nhds hlt)
    filter_upwards [ht] with α hα
    exact lt_of_le_of_lt (iInf_le_of_le σ (iInf_le_of_le hmem le_rfl)) hα

theorem gsl_c24 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F
  → ∀ n : ℕ, 0 < n →
  Tendsto (fun α : ℝ => res.{u} (petz.{u} α) (pow.{u} ρ n) (F n))
    (𝓝[Set.Ioi 1] 1) (𝓝 (res.{u} du.{u} (pow.{u} ρ n) (F n))))
:= by
  intro A _ _ ρ F hF n hn
  exact res_petz_tendsto_du (pow ρ n)
    (w42_tensor_spectral_dictionary.1 ρ n).2.1 (F n) (hF.1 n hn)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c60_nonempty {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid.{u} ρ F)
    (n : ℕ) (hn : 0 < n) : (F n).Nonempty := by
  obtain ⟨γ, _, hγ⟩ := hF.2.2.2
  induction n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n ih =>
    cases n with
    | zero => exact ⟨pow γ 1, hγ⟩
    | succ k =>
      obtain ⟨X, hX⟩ := ih (Nat.succ_pos k)
      exact ⟨join ρ (k + 1) 1 X (pow γ 1),
        hF.2.2.1 (k + 1) 1 (Nat.succ_pos k) Nat.one_pos X hX (pow γ 1) hγ⟩

theorem gsl_c60 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 → ∀ n : ℕ, 0 < n →
  (∀ α : ℝ, α ∈ Set.Ioc 1 2 →
    res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (F n) ≤
      res.{u} (petz.{u} α) (pow.{u} ρ n) (F n) + ((α/(α-1)*Real.logb 2 (1/(1-ε)) : ℝ) : EReal)) ∧
  (∀ α : ℝ, α ∈ Set.Ioo 0 1 →
    res.{u} (petz.{u} α) (pow.{u} ρ n) (F n) +
      ((α/(1-α)*(hb α/α-Real.logb 2 (1/ε)) : ℝ) : EReal) ≤
      res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (F n)))
:= by
  intro A _ _ ρ F hF ε hε n hn
  let ρn : State.{u} (Copy.{u} A n) :=
    ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
  have hFn := c60_nonempty ρ F hF n hn
  have hFd := hF.1 n hn
  constructor
  · intro α hα
    obtain ⟨σ, hσ, hmin, _⟩ :=
      (GourResource.gsl_y58.{u} ρn α (lt_trans zero_lt_one hα.1) (ne_of_gt hα.1)).2
        (F n) hFn (hF.2.1 n hn).1 hFd
    have hupper := (GourResource.gsl_h01 ρn ⟨σ, hFd hσ⟩ ε hε).1 α hα.1
    have hcompare := GourResource.gsl_c59.{u} ρn ⟨σ, hFd hσ⟩ α hα
    calc
      res (fun X Y => dh X Y ε) (pow ρ n) (F n) ≤ dh ρn.1 σ ε :=
        iInf_le_of_le σ (iInf_le_of_le hσ le_rfl)
      _ ≤ sand α ρn.1 σ +
          ((α/(α-1)*Real.logb 2 (1/(1-ε)) : ℝ) : EReal) := hupper
      _ ≤ petz α ρn.1 σ +
          ((α/(α-1)*Real.logb 2 (1/(1-ε)) : ℝ) : EReal) :=
        add_le_add hcompare le_rfl
      _ = _ := by rw [hmin]
  · intro α hα
    refine le_iInf fun σ => le_iInf fun hσ => ?_
    have hlower := (GourResource.gsl_h01 ρn ⟨σ, hFd hσ⟩ ε hε).2 α hα
    have hres : res (petz α) (pow ρ n) (F n) ≤ petz α ρn.1 σ :=
      iInf_le_of_le σ (iInf_le_of_le hσ le_rfl)
    exact (add_le_add hres le_rfl).trans hlower

end GourResource

