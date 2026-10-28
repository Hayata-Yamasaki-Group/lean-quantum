/-
Upper estimate of the GSL.
Source context: Gour, Theorem 11.4.
-/
/-
Making the lower testing limit s a finite real number.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4; Hayashi–Yamasaki, Lemma 5.
-/
import Quantum.QuantumEntropy.GourResource.SmoothBoundsOne
import Quantum.QuantumEntropy.GourResource.GeneralizedAEPUpper

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c27_resource_bound {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid ρ F)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo 0 1) (hδ : δ ∈ Set.Ioo 0 1)
    (hsum : δ + ε < 1) (n : ℕ) (hn : 0 < n) :
    res (fun X Y => dh X Y ε) (pow ρ n) (F n) +
      ((Real.logb 2 (1 - δ - ε) : ℝ) : EReal) ≤
        res (fun X Y => smoothMax X Y δ) (pow ρ n) (F n) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro hσ
  have hρn := (w42_tensor_spectral_dictionary.1 ρ n).2.1
  have hlow : res (fun X Y => dh X Y ε) (pow ρ n) (F n) ≤ dh (pow ρ n) σ ε :=
    iInf_le_of_le σ (iInf_le _ hσ)
  exact (add_le_add hlow (le_refl _)).trans
    (GourResource.gsl_c16 ⟨pow ρ n, hρn⟩ ⟨σ, hF.1 n hn hσ⟩ δ ε hδ hε hsum)

private theorem c27_rate_bound {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid ρ F)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo 0 1) (hδ : δ ∈ Set.Ioo 0 1)
    (hsum : δ + ε < 1) (n : ℕ) (hn : 0 < n) :
    hRate ρ F ε n + ((Real.logb 2 (1 - δ - ε) / (n : ℝ) : ℝ) : EReal) ≤
      mRate ρ F δ n := by
  have hnonneg : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by positivity
  have h := mul_le_mul_of_nonneg_left
    (c27_resource_bound ρ F hF ε δ hε hδ hsum n hn) hnonneg
  rw [EReal.left_distrib_of_nonneg_of_ne_top hnonneg (EReal.coe_ne_top _) _ _,
    ← EReal.coe_mul] at h
  simpa only [hRate, mRate, rate, if_neg (Nat.ne_of_gt hn), one_div_mul_eq_div] using h

/-- Upper bound on the upper limit of the testing rate: under `hyValid ρ F`, for every
`ε ∈ (0, 1)`, `limsup (hRate ρ F ε) ≤ reg ρ F`. This is an auxiliary result, derived from
`gsl_c26` and the comparison `gsl_c16`; it therefore depends on the strong converse bound
`gsl_y10` and is weaker than it (`gsl_y10` also covers `ε = 0`). It is not used in the proof
of the main theorem. -/
theorem gsl_c27 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F
  → ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
  Filter.limsup (hRate.{u} ρ F ε) atTop ≤ reg.{u} ρ F)
:= by
  intro A _ _ ρ F hF ε hε
  let δ : ℝ := (1 - ε) / 2
  have hδ : δ ∈ Set.Ioo 0 1 := by
    dsimp [δ]
    constructor <;> linarith [hε.1, hε.2]
  have hsum : δ + ε < 1 := by
    dsimp [δ]
    linarith [hε.2]
  let c : ℝ := Real.logb 2 (1 - δ - ε)
  have hc : Tendsto (fun n : ℕ => ((c / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 0) := by
    simpa only [EReal.coe_zero] using
      EReal.tendsto_coe.mpr (tendsto_const_div_atTop_nhds_zero_nat c)
  have hbound : (fun n => hRate ρ F ε n + ((c / (n : ℝ) : ℝ) : EReal))
      ≤ᶠ[atTop] mRate ρ F δ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact c27_rate_bound ρ F hF ε δ hε hδ hsum n hn
  have hlim := EReal.le_limsup_add (u := hRate ρ F ε)
    (v := fun n : ℕ => ((c / (n : ℝ) : ℝ) : EReal)) (f := atTop)
  rw [hc.liminf_eq, add_zero] at hlim
  exact hlim.trans ((limsup_le_limsup hbound).trans (GourResource.gsl_c26.{u} ρ F hF δ hδ))

end GourResource
