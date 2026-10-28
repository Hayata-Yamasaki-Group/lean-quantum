/-
The order of passing from the upper bound for fixed m,σ to inf_m inf_σ. Limits are not interchanged while changing the sequence.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4; Hayashi–Yamasaki, Lemmas 5 and 6.
-/
import Quantum.QuantumEntropy.GourResource.Regularization
import Quantum.QuantumEntropy.GourResource.BlockConverse.Limit
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


/-- Strong converse bound: under `hyValid ρ F`, for every `ε ∈ [0, 1)`,
`limsup (hRate ρ F ε) ≤ reg ρ F`; the case `ε = 0` is included. In the proof of
Hayashi–Yamasaki, Theorem 4, it follows by optimizing the fixed-block estimate of their
Lemma 6. -/
theorem gsl_y10 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ico 0 1 →
    Filter.limsup (hRate.{u} ρ F ε) atTop ≤ reg.{u} ρ F
:= by
  intro A _ _ ρ F hF ε hε
  obtain ⟨γ, hγ, hγF⟩ := hF.2.2.2
  apply ge_of_tendsto (GourResource.gsl_c23 ρ F hF).1
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hc : (0 : EReal) < ((1 / (m : ℝ) : ℝ) : EReal) := by
    exact EReal.coe_pos.mpr (one_div_pos.mpr (Nat.cast_pos.mpr hm))
  rw [uRate, rate, if_neg (Nat.ne_of_gt hm)]
  apply (EReal.div_le_iff_le_mul hc (EReal.coe_ne_top _)).mp
  refine le_iInf fun σ => le_iInf fun hσ => ?_
  apply (EReal.div_le_iff_le_mul hc (EReal.coe_ne_top _)).mpr
  let σs : State (Copy A m) := ⟨σ, hF.1 m hm hσ⟩
  have hadm := GourResource.gsl_y07.{u} ρ F hF γ m σ hm hγF hσ
  have hcomparison :
      hRate ρ F ε ≤ᶠ[atTop]
        rate (fun n => dh (pow ρ n) (padded ρ γ m σ n) ε) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [hRate, rate, if_neg (Nat.ne_of_gt hn)]
    apply mul_le_mul_of_nonneg_left
    · exact iInf_le_of_le (padded ρ γ m σ n) (iInf_le_of_le (hadm n hn).1 le_rfl)
    · exact EReal.coe_nonneg.mpr (le_of_lt (one_div_pos.mpr (Nat.cast_pos.mpr hn)))
  exact (Filter.limsup_le_limsup hcomparison).trans (GourResource.gsl_y09.{u} ρ γ m σs ε hm hγ hε)

end GourResource

