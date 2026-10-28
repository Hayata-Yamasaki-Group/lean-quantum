/-
Obtains the additive upper bound on DH for finite n from domination on the right.
Source context: Gour, Theorem 11.4; Gour, Example 11.8; Hayashi–Yamasaki, Lemma S3.
-/
/-
Composes the liminf version of S3 from CPTP and sublinear domination.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemmas S1 and S3.
-/
/-
Composes the limsup version of S3 from CPTP and sublinear domination.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemmas S1 and S3.
-/
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.TestingSDP

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y30_pairing_nonneg {A : Type u} [Qudit A] [Nontrivial A]
    {X M : L A} (hX : 0 ≤ X) (hM : 0 ≤ M) : 0 ≤ pairing X M := by
  by_cases h : X * M = 0
  · simp only [pairing, h, map_zero, Complex.zero_re, le_refl]
  · exact (OPT.trace_re_pos_mul_of_nonneg_of_ne_zero hX hM h).le

theorem gsl_y30 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ τ : State.{u} A) (a ε : ℝ),
  0 ≤ a → ε ∈ Set.Ico 0 1 →
  (Real.rpow 2 (-a) : ℝ) • τ.1 ≤ σ.1 →
    dh.{u} ρ.1 σ.1 ε ≤ dh.{u} ρ.1 τ.1 ε + (a : EReal)
:= by
  intro A _ _ ρ σ τ a ε _ hε hdom
  have hc : 0 < Real.rpow 2 (-a) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨M, hM, hacc, hopt⟩ := GourResource.gsl_b02.{u}.2.2.2.1 ρ σ ε hε
  have hM0 : 0 ≤ M := (LinearMap.nonneg_iff_isPositive M).mpr hM.1
  have hτ0 : 0 ≤ τ.1 := (LinearMap.nonneg_iff_isPositive τ.1).mpr τ.2.1
  have hnonneg : ∀ b ∈ {b : ℝ | ∃ N : L A,
      effect N ∧ 1 - ε ≤ pairing ρ.1 N ∧ b = pairing τ.1 N}, 0 ≤ b := by
    rintro b ⟨N, hN, _, rfl⟩
    exact gsl_y30_pairing_nonneg hτ0 ((LinearMap.nonneg_iff_isPositive N).mpr hN.1)
  have hmem : pairing τ.1 M ∈ {b : ℝ | ∃ N : L A,
      effect N ∧ 1 - ε ≤ pairing ρ.1 N ∧ b = pairing τ.1 N} :=
    ⟨M, hM, hacc, rfl⟩
  have hbτ0 : 0 ≤ beta ρ.1 τ.1 ε := le_csInf ⟨_, hmem⟩ hnonneg
  have hbτ : beta ρ.1 τ.1 ε ≤ pairing τ.1 M := csInf_le ⟨0, hnonneg⟩ hmem
  have hpair := gsl_y30_pairing_nonneg (sub_nonneg.mpr hdom) hM0
  have hpair_le : Real.rpow 2 (-a) * pairing τ.1 M ≤ pairing σ.1 M := by
    simpa [pairing, sub_mul, smul_mul_assoc, sub_nonneg] using hpair
  have hb : Real.rpow 2 (-a) * beta ρ.1 τ.1 ε ≤ beta ρ.1 σ.1 ε := by
    rw [← hopt]
    exact (mul_le_mul_of_nonneg_left hbτ hc.le).trans hpair_le
  by_cases hzero : beta ρ.1 τ.1 ε = 0
  · simp only [dh, hzero, Real.toNNReal_zero, OPT.binaryNegLog2_zero,
      EReal.top_add_coe]
    exact le_top
  have hτpos : 0 < beta ρ.1 τ.1 ε := lt_of_le_of_ne hbτ0 (Ne.symm hzero)
  have hprod : 0 < Real.rpow 2 (-a) * beta ρ.1 τ.1 ε := mul_pos hc hτpos
  have hσpos : 0 < beta ρ.1 σ.1 ε := hprod.trans_le hb
  have hσdh : dh ρ.1 σ.1 ε = ((-Real.logb 2 (beta ρ.1 σ.1 ε) : ℝ) : EReal) := by
    rw [dh, OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hσpos)),
      Real.coe_toNNReal _ hσpos.le]
  have hτdh : dh ρ.1 τ.1 ε = ((-Real.logb 2 (beta ρ.1 τ.1 ε) : ℝ) : EReal) := by
    rw [dh, OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hτpos)),
      Real.coe_toNNReal _ hτpos.le]
  rw [hσdh, hτdh, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hprod hb
  rw [Real.logb_mul (ne_of_gt hc) (ne_of_gt hτpos),
    Real.rpow_eq_pow, Real.logb_rpow (b := 2) (x := -a) (by norm_num) (by norm_num)] at hlog
  linarith

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y31 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X σ τ : OpSeq.{u} A)
  (E : (n : ℕ) → CPTP.{u,u} (Copy.{u} A n) (Copy.{u} A n))
  (f : ℕ → ℝ) (ε : ℝ),
  (∀ n : ℕ, 0 < n → IsDensity.{u} (X n) ∧ IsDensity.{u} (σ n) ∧ IsDensity.{u} (τ n)) →
  ε ∈ Set.Ico 0 1 → (∀ n, 0 ≤ f n) →
  Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0) →
  (∀ n : ℕ, 0 < n → (Real.rpow 2 (-f n) : ℝ) • τ n ≤ σ n) →
  Filter.liminf (pairRate.{u} (fun n => (E n).toFun (X n))
    (fun n => (E n).toFun (σ n)) ε) atTop ≤
  Filter.liminf (pairRate.{u} X τ ε) atTop
:= by
  intro A _ _ X σ τ E f ε hD hε hf hlim hdom
  have herror : Tendsto (fun n : ℕ => ((f n / (n : ℝ) : ℝ) : EReal))
      atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hlim
  have herrlim := herror.limsup_eq
  have hpoint : ∀ᶠ n : ℕ in atTop,
      pairRate (fun n => (E n).toFun (X n)) (fun n => (E n).toFun (σ n)) ε n ≤
        ((f n / (n : ℝ) : ℝ) : EReal) + pairRate X τ ε n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    obtain ⟨hX, hσ, hτ⟩ := hD n hn
    have hdpi := GourResource.gsl_b02.{u}.2.2.2.2.2.2
      (⟨X n, hX⟩ : State (Copy A n)) ⟨σ n, hσ⟩ (E n) ε hε
    have hbound := hdpi.trans (GourResource.gsl_y30.{u} ⟨X n, hX⟩ ⟨σ n, hσ⟩ ⟨τ n, hτ⟩
      (f n) ε (hf n) hε (hdom n hn))
    have hscale : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by
      exact_mod_cast (one_div_nonneg.mpr (Nat.cast_nonneg n) : 0 ≤ 1 / (n : ℝ))
    have hscaled := mul_le_mul_of_nonneg_left hbound hscale
    rw [EReal.left_distrib_of_nonneg_of_ne_top hscale (EReal.coe_ne_top _),
      ← EReal.coe_mul] at hscaled
    simpa only [pairRate, rate, if_neg (Nat.ne_of_gt hn),
      one_div_mul_eq_div, add_comm] using hscaled
  refine (Filter.liminf_le_liminf hpoint).trans ?_
  have hadd := EReal.liminf_add_le
    (u := fun n : ℕ => ((f n / (n : ℝ) : ℝ) : EReal))
    (v := pairRate X τ ε) (f := atTop)
    (Or.inl (by rw [herrlim]; exact EReal.coe_ne_bot 0))
    (Or.inl (by rw [herrlim]; exact EReal.coe_ne_top 0))
  simpa only [Pi.add_apply, herrlim, zero_add] using hadd

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y32 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X σ τ : OpSeq.{u} A)
  (E : (n : ℕ) → CPTP.{u,u} (Copy.{u} A n) (Copy.{u} A n))
  (f : ℕ → ℝ) (ε : ℝ),
  (∀ n : ℕ, 0 < n → IsDensity.{u} (X n) ∧ IsDensity.{u} (σ n) ∧ IsDensity.{u} (τ n)) →
  ε ∈ Set.Ico 0 1 → (∀ n, 0 ≤ f n) →
  Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0) →
  (∀ n : ℕ, 0 < n → (Real.rpow 2 (-f n) : ℝ) • τ n ≤ σ n) →
  Filter.limsup (pairRate.{u} (fun n => (E n).toFun (X n))
    (fun n => (E n).toFun (σ n)) ε) atTop ≤
  Filter.limsup (pairRate.{u} X τ ε) atTop
:= by
  intro A _ _ X σ τ E f ε hstates hε hf hlim hdom
  have htail : ∀ᶠ n : ℕ in atTop,
      pairRate (fun n => (E n).toFun (X n)) (fun n => (E n).toFun (σ n)) ε n ≤
        pairRate X τ ε n + ((f n / (n : ℝ) : ℝ) : EReal) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    obtain ⟨hX, hσ, hτ⟩ := hstates n hn
    have hmono := GourResource.gsl_b02.{u}.2.2.2.2.2.2
      (⟨X n, hX⟩ : State (Copy A n)) ⟨σ n, hσ⟩ (E n) ε hε
    have hbound := GourResource.gsl_y30.{u} (⟨X n, hX⟩ : State (Copy A n))
      ⟨σ n, hσ⟩ ⟨τ n, hτ⟩ (f n) ε (hf n) hε (hdom n hn)
    have hnonneg : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by
      exact_mod_cast (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg n))
    have hscaled := mul_le_mul_of_nonneg_left (hmono.trans hbound) hnonneg
    rw [EReal.left_distrib_of_nonneg_of_ne_top hnonneg (EReal.coe_ne_top _) _ _,
      ← EReal.coe_mul] at hscaled
    simpa only [pairRate, rate, if_neg (Nat.ne_of_gt hn), one_div,
      div_eq_mul_inv, one_mul, mul_comm (f n)] using hscaled
  have hzero : Filter.limsup (fun n : ℕ => ((f n / (n : ℝ) : ℝ) : EReal)) atTop = 0 := by
    have ht : Tendsto (fun n : ℕ => ((f n / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 0) := by
      simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hlim
    exact ht.limsup_eq
  have hadd := EReal.limsup_add_le
    (u := pairRate X τ ε) (v := fun n : ℕ => ((f n / (n : ℝ) : ℝ) : EReal))
    (f := atTop) (Or.inr (by rw [hzero]; exact EReal.zero_ne_top))
    (Or.inr (by rw [hzero]; exact EReal.zero_ne_bot))
  exact (Filter.limsup_le_limsup htail).trans (by simpa only [hzero, add_zero] using hadd)

end GourResource

