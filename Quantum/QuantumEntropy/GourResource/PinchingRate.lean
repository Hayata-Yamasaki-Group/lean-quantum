/-
The liminfs of DU before and after the pinching fixed to rounded agree.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityTensorFoundation.GSLCore
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore
import Quantum.QuantumEntropy.GourResource.SpectralRounding
import Quantum.QuantumEntropy.GourResource.PinchingEntropy


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem du_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) : 0 ≤ du ρ.1 σ.1 := by
  let D : OPT.GourMatrixStateDivergence.{u} :=
    fun ρ σ hρ hσ => OPT.petzQuantumRenyiDivergence OPT.petzRenyiOrderOne ρ σ hρ hσ
  have hP := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  have hD : OPT.GourMatrixRelativeEntropyLaws.{u} D :=
    ⟨hP.dataProcessing, fun {_ _} _ _ _ _ _ => hP.tensorAdditivity,
      hP.binaryNormalization⟩
  simpa only [D, OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN, du] using
    (w37_relative_diagonal_calibration D hD).1 ρ σ

private theorem log_rate_tendsto :
    Tendsto (fun n : ℕ => ((1 / (n : ℝ) * Real.logb 2 ((n : ℝ) + 1) : ℝ) : EReal))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-1) 1 one_ne_zero).comp hn
  have hr : Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.logb 2 ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right,
      div_eq_mul_inv, one_mul, mul_comm, mul_one] using h
  exact EReal.tendsto_coe.mpr hr

private theorem liminf_add_zero (a b : ℕ → EReal) (ha : Tendsto a atTop (𝓝 0)) :
    liminf (a + b) atTop = liminf b atTop := by
  apply le_antisymm
  · have h := EReal.liminf_add_le (u := a) (v := b) (f := atTop)
      (Or.inl (ha.limsup_eq ▸ EReal.zero_ne_bot))
      (Or.inl (ha.limsup_eq ▸ EReal.zero_ne_top))
    simpa only [ha.limsup_eq, zero_add] using h
  · have h := EReal.le_liminf_add (u := a) (v := b) (f := atTop)
    simpa only [ha.liminf_eq, zero_add] using h

theorem gsl_y25 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (S : OpSeq.{u} A) (lam : ℝ),
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → IsDensity.{u} (S n) ∧
    (lam^n/3 : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ S n) →
  let T := fun n => rounded.{u} lam n (S n)
  Filter.liminf (seqRate.{u} ρ T) atTop =
    Filter.liminf (entRate.{u} (fun n => pin.{u} (T n) (pow.{u} ρ n)) T) atTop
:= by
  intro A instA instN ρ S lam hlam hS
  classical
  let T := fun n => rounded lam n (S n)
  let loss := rate (fun n => du (pow ρ n) (pin (T n) (pow ρ n)))
  have hT (n : ℕ) (hn : 0 < n) : IsDensity (T n) ∧
      Fintype.card (spectralEigenvalue (T n)) ≤ n + 1 :=
    GourResource.gsl_y20.{u} ⟨S n, (hS n hn).1⟩ lam n hlam hn (hS n hn).2
  have hpow (n : ℕ) : IsDensity (pow ρ n) :=
    (w42_tensor_spectral_dictionary.1 ρ n).2.1
  have hloss (n : ℕ) (hn : 0 < n) :
      0 ≤ loss n ∧
        loss n ≤ ((1 / (n : ℝ) * Real.logb 2 ((n : ℝ) + 1) : ℝ) : EReal) := by
    have ht := hT n hn
    have hp : IsDensity (pin (T n) (pow ρ n)) :=
      spectralPinchingChannel_isDensity (T n) ht.1.1.isSymmetric (pow ρ n) (hpow n)
    have hnonneg := du_nonneg ⟨pow ρ n, hpow n⟩ ⟨pin (T n) (pow ρ n), hp⟩
    have hbound := GourResource.gsl_y22.{u} ⟨pow ρ n, hpow n⟩ ⟨T n, ht.1⟩
    have hlog : Real.logb 2 (Fintype.card (spectralEigenvalue (T n))) ≤
        Real.logb 2 ((n : ℝ) + 1) := by
      by_cases hc : Fintype.card (spectralEigenvalue (T n)) = 0
      · simp only [hc, Nat.cast_zero, Real.logb_zero]
        exact Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      · apply Real.logb_le_logb_of_le (by norm_num)
        · exact_mod_cast Nat.pos_of_ne_zero hc
        · exact_mod_cast ht.2
    have hscale : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by positivity
    dsimp [loss, rate]
    rw [if_neg hn.ne']
    constructor
    · exact mul_nonneg hscale hnonneg
    · exact mul_le_mul_of_nonneg_left (hbound.trans (EReal.coe_le_coe_iff.mpr hlog)) hscale
  have hzero : Tendsto loss atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds log_rate_tendsto
    · filter_upwards [eventually_gt_atTop 0] with n hn using (hloss n hn).1
    · filter_upwards [eventually_gt_atTop 0] with n hn using (hloss n hn).2
  have heq : seqRate ρ T =ᶠ[atTop]
      loss + entRate (fun n => pin (T n) (pow ρ n)) T := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hp := GourResource.gsl_y21.{u} ⟨pow ρ n, hpow n⟩ ⟨T n, (hT n hn).1⟩
    simp only [Pi.add_apply, seqRate, entRate, loss, rate, if_neg hn.ne']
    rw [hp]
    exact EReal.left_distrib_of_nonneg_of_ne_top (by positivity) (EReal.coe_ne_top _) _ _
  exact (liminf_congr heq).trans (liminf_add_zero loss _ hzero)

end GourResource

