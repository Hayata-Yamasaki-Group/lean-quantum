/-
Upper bound on the upper limit of the smoothed max-relative entropy rate (the upper-bound part of Gour, Lemma 11.3), derived from the strong converse bound gsl_y10 and the comparison gsl_c19 (gsl_c26).
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumEntropy.GourResource.SmoothBoundsThree
import Quantum.QuantumEntropy.GourResource.BlockConverse

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c26_parameter {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) :
    Real.sqrt (1 - ε ^ 2) ∈ Set.Ioo 0 1 ∧
      Real.sqrt (1 - Real.sqrt (1 - ε ^ 2) ^ 2) = ε := by
  have hs : 0 < 1 - ε ^ 2 := by nlinarith [hε.1, hε.2]
  have he : Real.sqrt (1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt hs.le
  refine ⟨⟨Real.sqrt_pos.2 hs, ?_⟩, ?_⟩
  · nlinarith [Real.sqrt_nonneg (1 - ε ^ 2), sq_pos_of_pos hε.1]
  · rw [he, sub_sub_cancel, Real.sqrt_sq hε.1.le]

private theorem c26_resource_bound {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid ρ F)
    (ε t : ℝ) (ht : t ∈ Set.Ioo 0 1) (he : Real.sqrt (1 - t ^ 2) = ε)
    (n : ℕ) (hn : 0 < n) :
    res (fun X Y => smoothMax X Y ε) (pow ρ n) (F n) +
      ((Real.logb 2 (t / (1 - t)) : ℝ) : EReal) ≤
        res (fun X Y => dh X Y t) (pow ρ n) (F n) := by
  apply le_iInf
  intro σ
  apply le_iInf
  intro hσ
  have hb := GourResource.gsl_c19
    (⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩ : State (Copy A n))
    ⟨σ, hF.1 n hn hσ⟩ t ht
  rw [he] at hb
  exact (add_le_add
    (iInf_le_of_le σ (iInf_le_of_le hσ le_rfl)) le_rfl).trans hb

private theorem c26_rate_bound {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid ρ F)
    (ε t : ℝ) (ht : t ∈ Set.Ioo 0 1) (he : Real.sqrt (1 - t ^ 2) = ε)
    (n : ℕ) (hn : 0 < n) :
    mRate ρ F ε n + ((Real.logb 2 (t / (1 - t)) / (n : ℝ) : ℝ) : EReal) ≤
      hRate ρ F t n := by
  have hn0 : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by positivity
  have hb := mul_le_mul_of_nonneg_left (c26_resource_bound ρ F hF ε t ht he n hn) hn0
  rw [EReal.left_distrib_of_nonneg_of_ne_top hn0 (EReal.coe_ne_top _) _ _] at hb
  simpa only [mRate, hRate, rate, if_neg (Nat.ne_of_gt hn), ← EReal.coe_mul,
    one_div_mul_eq_div] using hb

/-- Upper-bound part of the asymptotic equipartition property (Gour, Lemma 11.3): under
`hyValid ρ F`, for every `ε ∈ (0, 1)`, the upper limit of the smoothed max-relative entropy
rate `mRate ρ F ε` is at most `reg ρ F`. Permutation invariance is not assumed, and the full
AEP equality is not formalized. The proof derives it from the strong converse bound
`gsl_y10` and the comparison `gsl_c19`. -/
theorem gsl_c26 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F
  → ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
  Filter.limsup (mRate.{u} ρ F ε) atTop ≤ reg.{u} ρ F)
:= by
  intro A _ _ ρ F hF ε hε
  obtain ⟨ht, he⟩ := c26_parameter hε
  let t := Real.sqrt (1 - ε ^ 2)
  let c := Real.logb 2 (t / (1 - t))
  let v : ℕ → EReal := fun n => ((c / (n : ℝ) : ℝ) : EReal)
  have hv : Tendsto v atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using
      EReal.tendsto_coe.2 (tendsto_const_div_atTop_nhds_zero_nat c)
  have hb : ∀ᶠ n in atTop, (mRate ρ F ε + v) n ≤ hRate ρ F t n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact c26_rate_bound ρ F hF ε t ht he n hn
  have hl := EReal.le_limsup_add (u := mRate ρ F ε) (v := v) (f := atTop)
  rw [hv.liminf_eq, add_zero] at hl
  exact hl.trans ((limsup_le_limsup hb).trans (GourResource.gsl_y10.{u} ρ F hF t ⟨ht.1.le, ht.2⟩))

end GourResource

