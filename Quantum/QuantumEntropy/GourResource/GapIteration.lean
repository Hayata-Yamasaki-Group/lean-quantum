/-
Constructs a choice map Φ with stopping that contracts the positive-part gap.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Obtains the geometric gap estimate for arbitrary k from a finite initial rate.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.Improvement
import Quantum.QuantumEntropy.GourResource.FiniteSeedRate

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem seq_liminf_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (τ : OpSeq.{u} A)
    (hτ : admissible.{u} F τ) : 0 ≤ Filter.liminf (seqRate.{u} ρ τ) atTop := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [seqRate, rate, if_neg (Nat.ne_of_gt hn)]
  apply EReal.mul_nonneg (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Nat.cast_nonneg n)))
  exact (w37_relative_diagonal_calibration umegakiBits
    w38_vn_spectral_dictionary.2.2.1).1
    ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩ ⟨τ n, (hτ n hn).2⟩

theorem gsl_y48 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ s ε η : ℝ, 0 ≤ s → ε ∈ Set.Ioo 0 1 → η ∈ Set.Ioo 0 ε →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) →
  ∃ Φ : OpSeq.{u} A → OpSeq.{u} A,
    ∀ (τ : OpSeq.{u} A) (r : ℝ), admissible.{u} F τ →
    Filter.liminf (seqRate.{u} ρ τ) atTop = (r : EReal) →
    ∃ r' : ℝ, admissible.{u} F (Φ τ) ∧ 0 ≤ r' ∧
      Filter.liminf (seqRate.{u} ρ (Φ τ)) atTop = (r' : EReal) ∧
      max 0 (r'-s) ≤ (1-η)*max 0 (r-s)
:= by
  classical
  intro A _ _ ρ F hF s ε η hs hε hη hlim
  have hcoef : 0 ≤ 1 - η := sub_nonneg.mpr (hη.2.le.trans hε.2.le)
  have improve (τ : OpSeq.{u} A)
      (h : admissible.{u} F τ ∧ ∃ r : ℝ,
        s < r ∧ Filter.liminf (seqRate.{u} ρ τ) atTop = (r : EReal)) :
      ∃ (τ' : OpSeq.{u} A) (r' : ℝ), admissible.{u} F τ' ∧ 0 ≤ r' ∧
        Filter.liminf (seqRate.{u} ρ τ') atTop = (r' : EReal) ∧
        r' - s ≤ (1 - η) * (Classical.choose h.2 - s) := by
    exact GourResource.gsl_y47.{u} ρ F hF τ (Classical.choose h.2) s ε η h.1 hs
      (Classical.choose_spec h.2).1.le hε hη (Classical.choose_spec h.2).2 hlim
  let Φ : OpSeq.{u} A → OpSeq.{u} A := fun τ =>
    if h : admissible.{u} F τ ∧ ∃ r : ℝ,
        s < r ∧ Filter.liminf (seqRate.{u} ρ τ) atTop = (r : EReal) then
      Classical.choose (improve τ h)
    else τ
  refine ⟨Φ, ?_⟩
  intro τ r hτ hr
  by_cases h : admissible.{u} F τ ∧ ∃ q : ℝ,
      s < q ∧ Filter.liminf (seqRate.{u} ρ τ) atTop = (q : EReal)
  · obtain ⟨r', hτ', hr'0, hr', hgap⟩ := Classical.choose_spec (improve τ h)
    have heq : Classical.choose h.2 = r :=
      EReal.coe_injective ((Classical.choose_spec h.2).2.symm.trans hr)
    rw [heq] at hgap
    refine ⟨r', ?_, hr'0, ?_, ?_⟩
    · simpa only [Φ, dif_pos h] using hτ'
    · simpa only [Φ, dif_pos h] using hr'
    · exact max_le (mul_nonneg hcoef (le_max_left 0 (r - s)))
        (hgap.trans (mul_le_mul_of_nonneg_left (le_max_right 0 (r - s)) hcoef))
  · have hrs : r ≤ s := le_of_not_gt (fun hsr => h ⟨hτ, r, hsr, hr⟩)
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · simpa only [Φ, dif_neg h] using hτ
    · exact EReal.coe_nonneg.mp (hr ▸ seq_liminf_nonneg ρ F τ hτ)
    · simpa only [Φ, dif_neg h] using hr
    · simp only [max_eq_left (sub_nonpos.mpr hrs), mul_zero, le_refl]

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y49 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ s ε η : ℝ, 0 ≤ s → ε ∈ Set.Ioo 0 1 → η ∈ Set.Ioo 0 ε →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) →
  ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∃ (τ : OpSeq.{u} A) (r : ℝ),
    admissible.{u} F τ ∧ 0 ≤ r ∧
    Filter.liminf (seqRate.{u} ρ τ) atTop = (r : EReal) ∧
    max 0 (r-s) ≤ (1-η)^k * R
:= by
  intro A _ _ ρ F hF s ε η hs hε hη hlim
  obtain ⟨γ, lam, hγ, _, hseed⟩ := GourResource.gsl_y06.{u} ρ F hF
  obtain ⟨hγadm, r₀, hr₀, _, _, hconv⟩ :=
    GourResource.gsl_y60.{u} ρ F hF γ hγ (hseed 1 (by decide)).1
  obtain ⟨Φ, hΦ⟩ := GourResource.gsl_y48.{u} ρ F hF s ε η hs hε hη hlim
  have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr (le_of_lt (lt_trans hη.2 hε.2))
  refine ⟨max 0 (r₀ - s), le_max_left _ _, ?_⟩
  intro k
  induction k with
  | zero =>
      refine ⟨(fun n => pow γ n), r₀, hγadm, hr₀, hconv.liminf_eq, ?_⟩
      simp only [pow_zero, one_mul, le_refl]
  | succ k ih =>
      obtain ⟨τ, r, hτ, _, hr, hgap⟩ := ih
      obtain ⟨r', hτ', hr'0, hr', himprove⟩ := hΦ τ r hτ hr
      refine ⟨Φ τ, r', hτ', hr'0, hr', ?_⟩
      calc
        max 0 (r' - s) ≤ (1 - η) * max 0 (r - s) := himprove
        _ ≤ (1 - η) * ((1 - η) ^ k * max 0 (r₀ - s)) :=
          mul_le_mul_of_nonneg_left hgap hfactor
        _ = (1 - η) ^ (k + 1) * max 0 (r₀ - s) := by
          rw [pow_succ, mul_comm ((1 - η) ^ k) (1 - η), mul_assoc]

end GourResource

