/-
For fixed ρ and ε∈[0,1), σ↦β(ρ,σ,ε) is continuous on the subtype of density states.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
import Quantum.QuantumEntropy.GourResource.KWTestingBridge

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y02_pairing_bound {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X M : L.{u} A) (hX : IsSelfAdjoint X) (hM : effect M) :
    |pairing X M| ≤ w40T₁ X := by
  have hzero : (0 : L A) ≤ M := (LinearMap.nonneg_iff_isPositive M).mpr hM.1
  have hone : M ≤ 1 := sub_nonneg.mp
    ((LinearMap.nonneg_iff_isPositive (1 - M)).mpr hM.2)
  have hlow : -(1 : L A) ≤ M := (neg_nonpos.mpr zero_le_one).trans hzero
  have hupper := (w40_trace_norm_spectral_variational X hX).2.1 M
    hM.1.isSelfAdjoint hlow hone
  have hlower := (w40_trace_norm_spectral_variational X hX).2.1 (-M)
    hM.1.isSelfAdjoint.neg (neg_le_neg hone) (by simpa only [neg_neg] using neg_le_neg hlow)
  rw [LinearMap.trace_mul_comm ℂ M X] at hupper
  rw [neg_mul, map_neg, Complex.neg_re, LinearMap.trace_mul_comm ℂ M X] at hlower
  exact abs_le.mpr ⟨by change -w40T₁ X ≤ (Tr (X * M)).re; linarith, hupper⟩

private theorem gsl_y02_beta_le_pairing {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) (ε : ℝ) (M : L.{u} A)
    (hM : effect M) (haccept : 1 - ε ≤ pairing ρ.1 M) :
    beta ρ.1 σ.1 ε ≤ pairing σ.1 M := by
  unfold beta
  refine csInf_le ?_ ⟨M, hM, haccept, rfl⟩
  refine ⟨-w40T₁ σ.1, ?_⟩
  rintro b ⟨N, hN, _, rfl⟩
  exact (abs_le.mp (gsl_y02_pairing_bound σ.1 N σ.2.1.isSelfAdjoint hN)).1

private theorem gsl_y02_beta_difference {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (ε : ℝ)
    (hopt : ∀ σ : State.{u} A, ∃ M : L.{u} A,
      effect M ∧ 1 - ε ≤ pairing ρ.1 M ∧ pairing σ.1 M = beta ρ.1 σ.1 ε)
    (σ τ : State.{u} A) :
    |beta ρ.1 σ.1 ε - beta ρ.1 τ.1 ε| ≤ w40T₁ (σ.1 - τ.1) := by
  obtain ⟨M, hM, hMaccept, hMopt⟩ := hopt σ
  obtain ⟨N, hN, hNaccept, hNopt⟩ := hopt τ
  have hσ := gsl_y02_beta_le_pairing ρ σ ε N hN hNaccept
  have hτ := gsl_y02_beta_le_pairing ρ τ ε M hM hMaccept
  have hdiff : IsSelfAdjoint (σ.1 - τ.1) :=
    σ.2.1.isSelfAdjoint.sub τ.2.1.isSelfAdjoint
  have hMb := abs_le.mp (gsl_y02_pairing_bound (σ.1 - τ.1) M hdiff hM)
  have hNb := abs_le.mp (gsl_y02_pairing_bound (σ.1 - τ.1) N hdiff hN)
  have hsub (K : L A) : pairing (σ.1 - τ.1) K = pairing σ.1 K - pairing τ.1 K := by
    simp only [pairing, sub_mul, map_sub, Complex.sub_re]
  rw [hsub M, hMopt] at hMb
  rw [hsub N, hNopt] at hNb
  exact abs_le.mpr ⟨by linarith [hMb.1], by linarith [hNb.2]⟩

private theorem gsl_y02_trace_difference_continuous {A : Type u} [Qudit.{u} A]
    [Nontrivial A] (τ : State.{u} A) :
    Continuous (fun σ : State.{u} A => w40T₁ (σ.1 - τ.1)) := by
  let f : State A → {X : L A // IsSelfAdjoint X} := fun σ =>
    ⟨σ.1 - τ.1, σ.2.1.isSelfAdjoint.sub τ.2.1.isSelfAdjoint⟩
  have hf : Continuous f :=
    (continuous_subtype_val.sub continuous_const).subtype_mk _
  have h := (w40_trace_norm_continuity (H := A)).1.comp hf
  exact h.congr (fun σ => rfl)

private theorem gsl_y02_trace_difference_tendsto {A : Type u} [Qudit.{u} A]
    [Nontrivial A] (τ : State.{u} A) :
    Tendsto (fun σ : State.{u} A => w40T₁ (σ.1 - τ.1)) (𝓝 τ) (𝓝 0) := by
  simpa only [sub_self, w40T₁, star_zero, zero_mul, CFC.sqrt_zero, map_zero,
    Complex.zero_re] using (gsl_y02_trace_difference_continuous τ).tendsto τ

private theorem gsl_y02_continuous_of_optimal {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (ε : ℝ)
    (hopt : ∀ σ : State.{u} A, ∃ M : L.{u} A,
      effect M ∧ 1 - ε ≤ pairing ρ.1 M ∧ pairing σ.1 M = beta ρ.1 σ.1 ε) :
    Continuous (fun σ : State.{u} A => beta ρ.1 σ.1 ε) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (σ : State A) :
      ‖beta ρ.1 σ.1 ε - beta ρ.1 τ.1 ε‖ ≤ w40T₁ (σ.1 - τ.1) := by
    simpa only [Real.norm_eq_abs] using gsl_y02_beta_difference ρ ε hopt σ τ
  exact squeeze_zero (fun σ => norm_nonneg _) hbound (gsl_y02_trace_difference_tendsto τ)

theorem gsl_y02 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (ε : ℝ), ε ∈ Set.Ico 0 1 →
  Continuous (fun σ : State.{u} A => beta.{u} ρ.1 σ.1 ε)
:= by
  intro A _ _ ρ ε hε
  exact gsl_y02_continuous_of_optimal ρ ε (fun σ => GourResource.gsl_b02.{u}.2.2.2.1 ρ σ ε hε)

end GourResource

