/-
Constructs an improvement sequence and a finite nonnegative improvement rate for finite rates r,s.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.FixedBlockImprovement
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore
import Quantum.QuantumEntropy.GourResource.TestingContinuity.OptimalSequence


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem y47_du_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) : 0 ≤ du ρ.1 σ.1 := by
  let D : OPT.GourMatrixStateDivergence.{u} :=
    fun ρ σ hρ hσ => OPT.petzQuantumRenyiDivergence OPT.petzRenyiOrderOne ρ σ hρ hσ
  have hP := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  have hD : OPT.GourMatrixRelativeEntropyLaws.{u} D :=
    ⟨hP.dataProcessing, fun {_ _} _ _ _ _ _ => hP.tensorAdditivity,
      hP.binaryNormalization⟩
  simpa only [D, OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN, du] using
    (w37_relative_diagonal_calibration D hD).1 ρ σ

private theorem y47_liminf_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (τ : OpSeq.{u} A)
    (hτ : admissible F τ) : 0 ≤ Filter.liminf (seqRate ρ τ) atTop := by
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hρ : IsDensity (pow ρ n) := (w42_tensor_spectral_dictionary.1 ρ n).2.1
  have hdu := y47_du_nonneg ⟨pow ρ n, hρ⟩ ⟨τ n, (hτ n hn).2⟩
  simp only [seqRate, rate, if_neg (ne_of_gt hn)]
  exact mul_nonneg (EReal.coe_nonneg.mpr (by positivity)) hdu

private theorem y47_finite_nonneg (x : EReal) (b : ℝ) (hx : 0 ≤ x)
    (hb : x ≤ (b : EReal)) : ∃ r : ℝ, 0 ≤ r ∧ x = (r : EReal) ∧ r ≤ b := by
  have hmem : x ∈ Set.range Real.toEReal := by
    rw [EReal.range_coe_eq_Ioo]
    exact ⟨lt_of_lt_of_le EReal.bot_lt_zero hx, lt_of_le_of_lt hb (EReal.coe_lt_top b)⟩
  obtain ⟨r, rfl⟩ := hmem
  exact ⟨r, EReal.coe_nonneg.mp hx, rfl, EReal.coe_le_coe_iff.mp hb⟩

theorem gsl_y47 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (τ : OpSeq.{u} A) (r s ε η : ℝ), admissible.{u} F τ →
  0 ≤ s → s ≤ r → ε ∈ Set.Ioo 0 1 → η ∈ Set.Ioo 0 ε →
  Filter.liminf (seqRate.{u} ρ τ) atTop = (r : EReal) →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) →
  ∃ (τ' : OpSeq.{u} A) (r' : ℝ), admissible.{u} F τ' ∧ 0 ≤ r' ∧
    Filter.liminf (seqRate.{u} ρ τ') atTop = (r' : EReal) ∧
    r'-s ≤ (1-η)*(r-s)
:= by
  intro A _ _ ρ F hF τ r s ε η hτ hs hsr hε hη hr hsrate
  rcases eq_or_lt_of_le hsr with heq | hlt
  · refine ⟨τ, r, hτ, heq ▸ hs, hr, ?_⟩
    simp only [heq, sub_self, mul_zero, le_refl]
  · let ε₀ : ℝ := (ε - η) * (r - s) / (1 - ε)
    have hden : 0 < 1 - ε := sub_pos.mpr hε.2
    have hε₀ : 0 < ε₀ := div_pos (mul_pos (sub_pos.mpr hη.2) (sub_pos.mpr hlt)) hden
    have hgap : (1 - ε) * ε₀ = (ε - η) * (r - s) := by
      dsimp only [ε₀]
      field_simp
    have hfreq : ∃ᶠ n in atTop, seqRate ρ τ n < ((r + ε₀ : ℝ) : EReal) := by
      apply Filter.frequently_lt_of_liminf_lt (by isBoundedDefault)
      rw [hr]
      exact EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r hε₀)
    obtain ⟨m, hm, hmrate⟩ := Filter.frequently_atTop.1 hfreq 1
    have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    have hblock : ((1 / (m : ℝ) : ℝ) : EReal) * du (pow ρ m) (τ m) ≤
        ((r + ε₀ : ℝ) : EReal) := by
      simpa only [seqRate, rate, if_neg (ne_of_gt hmpos)] using hmrate.le
    obtain ⟨z, hz⟩ := GourResource.gsl_y11.{u} ρ F hF ε hε
    obtain ⟨γ, lam, hγpos, hlam, hγpow⟩ := GourResource.gsl_y06.{u} ρ F hF
    have hγF : pow γ 1 ∈ F 1 := (hγpow 1 Nat.zero_lt_one).1
    have hmix : admissible F (mixHY ρ γ m (τ m) z) :=
      ((GourResource.gsl_y12.{u} ρ F hF).2 γ m (τ m) z hmpos hγF
        (hτ m hmpos).1 hz.1).2.1
    have hbound := GourResource.gsl_y46.{u} ρ F hF γ lam m (τ m) z ε hγpos hγF
      hlam (fun n hn => (hγpow n hn).2.2.1) hmpos (hτ m hmpos).1 hε hz
      s (r + ε₀) hs hsrate (le_trans hsr (le_add_of_nonneg_right hε₀.le)) hblock
    obtain ⟨r', hr'nonneg, hr'rate, hr'bound⟩ :=
      y47_finite_nonneg (Filter.liminf (seqRate ρ (mixHY ρ γ m (τ m) z)) atTop)
        (s + (1 - ε) * (r + ε₀ - s)) (y47_liminf_nonneg ρ F _ hmix) hbound
    refine ⟨mixHY ρ γ m (τ m) z, r', hmix, hr'nonneg, hr'rate, ?_⟩
    nlinarith [hgap]

end GourResource

