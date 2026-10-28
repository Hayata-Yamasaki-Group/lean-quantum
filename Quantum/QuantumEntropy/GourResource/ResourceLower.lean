/-
For every admissible free sequence, the liminf is at least reg.
Proof construction: a composition moving each inf comparison for n>0 to the full-length tail.
Proof construction: uses the convergence of uRate to reg (gsl_c23). Each free σₙ is evaluated by iInf_le_of_le of GourResource.res, multiplied by the positive 1/n, and compared by Filter.liminf_le_liminf and Tendsto.liminf_eq. No condition on F₀ is added for n=0.
Lemma used: GourResource.gsl_c23.{u}
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  Tendsto (uRate.{u} ρ F) atTop (𝓝 (reg.{u} ρ F)) ∧ ∃ r : ℝ, reg.{u} ρ F = (r : EReal))
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4; Hayashi–Yamasaki, Lemma 5.
-/
import Quantum.QuantumEntropy.GourResource.Regularization

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y50 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ τ : OpSeq.{u} A, admissible.{u} F τ →
    reg.{u} ρ F ≤ Filter.liminf (seqRate.{u} ρ τ) atTop
:= by
  intro A _ _ ρ F hF τ hτ
  have hb : uRate ρ F ≤ᶠ[atTop] seqRate ρ τ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [uRate, seqRate, rate, if_neg (Nat.ne_of_gt hn)]
    apply mul_le_mul_of_nonneg_left
    · exact iInf_le_of_le (τ n) (iInf_le _ (hτ n hn).1)
    · exact EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Nat.cast_nonneg n))
  have hc := (GourResource.gsl_c23.{u} ρ F hF).1
  rw [← hc.liminf_eq]
  exact Filter.liminf_le_liminf hb

end GourResource

