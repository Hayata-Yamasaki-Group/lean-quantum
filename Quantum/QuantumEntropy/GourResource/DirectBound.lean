/-
Removes the geometric gap and obtains the direct bound for the liminf of the testing rate.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.GSLUpper
import Quantum.QuantumEntropy.GourResource.GapIteration
import Quantum.QuantumEntropy.GourResource.ResourceLower

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


/-- Lower bound: under `hyValid ρ F`, for every `ε ∈ (0, 1)`,
`reg ρ F ≤ liminf (hRate ρ F ε)`. This is the direct part of the proof of
Hayashi–Yamasaki, Theorem 4, obtained by iterating their Lemma 7. -/
theorem gsl_y51 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    reg.{u} ρ F ≤ Filter.liminf (hRate.{u} ρ F ε) atTop
:= by
  intro A _ _ ρ F hF ε hε
  obtain ⟨s, hs, hlim⟩ := GourResource.gsl_c65.{u} ρ F hF ε hε
  have hη : ε / 2 ∈ Set.Ioo 0 ε := ⟨by linarith [hε.1], by linarith [hε.1]⟩
  obtain ⟨R, _hR, hiter⟩ := GourResource.gsl_y49.{u} ρ F hF s ε (ε / 2) hs hε hη hlim
  have hbound (k : ℕ) : reg ρ F ≤ ((s + (1 - ε / 2) ^ k * R : ℝ) : EReal) := by
    obtain ⟨τ, r, hτ, _hr, hrate, hgap⟩ := hiter k
    have hrbound : r ≤ s + (1 - ε / 2) ^ k * R := by
      have := le_trans (le_max_right 0 (r - s)) hgap
      linarith
    calc
      reg ρ F ≤ Filter.liminf (seqRate ρ τ) atTop := GourResource.gsl_y50.{u} ρ F hF τ hτ
      _ = (r : EReal) := hrate
      _ ≤ ((s + (1 - ε / 2) ^ k * R : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hrbound
  have hpow : Tendsto (fun k : ℕ => (1 - ε / 2) ^ k) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hε.2]) (by linarith [hε.1])
  have hreal : Tendsto (fun k : ℕ => s + (1 - ε / 2) ^ k * R) atTop (𝓝 s) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hpow.mul_const R)
  rw [hlim]
  exact ge_of_tendsto (continuous_coe_real_ereal.tendsto s |>.comp hreal)
    (Filter.Eventually.of_forall hbound)

end GourResource

