/-
α→1+ after regularization.
-/
import Quantum.QuantumEntropy.GourResource.Regularization
import Quantum.QuantumEntropy.GourResource.ResourceRenyi
import Quantum.QuantumEntropy.GourQuantumRelativeEntropySemicontinuity.GSLCore
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private lemma c25_petz_spectral
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L.{u} A) (hρ : IsDensity.{u} ρ) (hσ : IsDensity.{u} σ)
    (α : ℝ) (hα : 1 < α) :
    petz.{u} α ρ σ =
      ((OPT.classicalRenyiDivBitsFinitePMF ⟨α, lt_trans zero_lt_one hα⟩
        (OPT.petzSpectralP ρ σ hρ hσ)
        (OPT.petzSpectralQ ρ σ hρ hσ) : ENNReal) : EReal) := by
  classical
  have hα0 : 0 ≤ α := le_of_lt (lt_trans zero_lt_one hα)
  have hαne : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  have hα1 : α ≠ 1 := ne_of_gt hα
  have hαlt : ¬ α < 1 := not_lt_of_ge hα.le
  simpa only [petz, dif_pos hα0, dif_pos hρ, dif_pos hσ,
    OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
    dif_neg hαne, dif_neg hα1, hαlt, false_and, or_false] using
    OPT.petzFiniteLogFormula_eq_classicalSpectral_of_one_lt
      ⟨α, lt_trans zero_lt_one hα⟩ hα ρ σ hρ hσ

private lemma c25_petz_monotone
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L.{u} A) (hρ : IsDensity.{u} ρ) (hσ : IsDensity.{u} σ) :
    MonotoneOn (fun α : ℝ => petz.{u} α ρ σ) (Set.Ioi 1) := by
  intro α hα β hβ hαβ
  change petz.{u} α ρ σ ≤ petz.{u} β ρ σ
  rw [c25_petz_spectral ρ σ hρ hσ α hα,
    c25_petz_spectral ρ σ hρ hσ β hβ]
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  exact ENNReal.div_le_div_right
    (OPT.classicalRenyiDivPMF_monotone_order hαβ _ _) _

private lemma c25_rate_monotone
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid.{u} ρ F) (n : PNat) :
    MonotoneOn
      (fun α : ℝ => rate (fun k => res.{u} (petz.{u} α) (pow.{u} ρ k) (F k)) n)
      (Set.Ioi 1) := by
  intro α hα β hβ hαβ
  simp only [rate, ne_of_gt n.pos, ↓reduceIte]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply iInf_mono
  intro σ
  apply iInf_mono
  intro hσ
  exact c25_petz_monotone (pow.{u} ρ n) σ
    ((w42_tensor_spectral_dictionary.{u}).1 ρ n).2.1
    (hF.1 n n.pos hσ) hα hβ hαβ

private lemma c25_monotone_limit (f : ℝ → EReal)
    (hf : MonotoneOn f (Set.Ioi 1)) :
    Tendsto f (𝓝[Set.Ioi 1] 1) (𝓝 (⨅ α : Set.Ioi (1 : ℝ), f α)) := by
  simpa only [sInf_image, iInf_subtype] using
    hf.tendsto_nhdsGT (OrderBot.bddBelow _)

private lemma c25_rate_limit
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (n : PNat)
    (h : Tendsto (fun α : ℝ => res.{u} (petz.{u} α) (pow.{u} ρ n) (F n))
      (𝓝[Set.Ioi 1] 1) (𝓝 (res.{u} du.{u} (pow.{u} ρ n) (F n)))) :
    Tendsto
      (fun α : ℝ => rate (fun k => res.{u} (petz.{u} α) (pow.{u} ρ k) (F k)) n)
      (𝓝[Set.Ioi 1] 1) (𝓝 (uRate.{u} ρ F n)) := by
  simpa only [uRate, rate, ne_of_gt n.pos, ↓reduceIte] using
    EReal.Tendsto.const_mul (a := ((1 / (n : ℝ) : ℝ) : EReal)) h
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))

theorem gsl_c25 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  Tendsto (renyiReg.{u} ρ F) (𝓝[Set.Ioi 1] 1) (𝓝 (reg.{u} ρ F)))
:= by
  intro A _ _ ρ F hF
  obtain ⟨r, hr⟩ := (GourResource.gsl_c23.{u} ρ F hF).2
  have hmono : MonotoneOn (renyiReg.{u} ρ F) (Set.Ioi 1) := by
    intro α hα β hβ hαβ
    exact iInf_mono fun n => c25_rate_monotone ρ F hF n hα hβ hαβ
  have hn (n : PNat) :
      (⨅ α : Set.Ioi (1 : ℝ),
        rate (fun k => res.{u} (petz.{u} α) (pow.{u} ρ k) (F k)) n) =
      uRate.{u} ρ F n :=
    tendsto_nhds_unique
      (c25_monotone_limit _ (c25_rate_monotone ρ F hF n))
      (c25_rate_limit ρ F n (GourResource.gsl_c24.{u} ρ F hF n n.pos))
  have hinf : (⨅ α : Set.Ioi (1 : ℝ), renyiReg.{u} ρ F α) = (r : EReal) := by
    simp only [renyiReg, iInf_comm (ι := Set.Ioi (1 : ℝ)) (ι' := PNat), hn]
    exact hr
  rw [hr, ← hinf]
  exact c25_monotone_limit _ hmono

end GourResource

