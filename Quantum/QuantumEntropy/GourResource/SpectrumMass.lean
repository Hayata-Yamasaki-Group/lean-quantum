/-
Obtains a liminf upper bound on the high-threshold mass from a liminf upper bound on the testing rate.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma S2.
-/
/-
Obtains a limsup upper bound on the high-threshold mass from a limsup upper bound on the testing rate.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma S2.
-/
import Quantum.QuantumEntropy.GourResource.JordanTestingProjection
import Quantum.QuantumEntropy.GourResource.KWTestingBridge

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem y28_pairing_nonneg {A : Type u} [Qudit A] {X M : L A}
    (hX : X.IsPositive) (hM : M.IsPositive) : 0 ≤ pairing X M := by
  have hM0 := (LinearMap.nonneg_iff_isPositive _).mpr hM
  have hs : IsSelfAdjoint (CFC.sqrt M) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
  have hp : 0 ≤ CFC.sqrt M * X * CFC.sqrt M := by
    simpa only [hs.star_eq] using
      star_left_conjugate_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hX) (CFC.sqrt M)
  have ht := (Complex.nonneg_iff.mp
    ((LinearMap.nonneg_iff_isPositive _).mp hp).trace_nonneg).1
  have he : Tr (CFC.sqrt M * X * CFC.sqrt M) = Tr (X * M) := by
    rw [mul_assoc, LinearMap.trace_mul_comm ℂ (CFC.sqrt M), mul_assoc,
      CFC.sqrt_mul_sqrt_self M hM0]
  change 0 ≤ (Tr (X * M)).re
  rwa [he] at ht

private theorem y28_beta_le {A : Type u} [Qudit A] (ρ σ : State A)
    (ε : ℝ) (M : L A) (hM : effect M) (hacc : 1 - ε ≤ pairing ρ.1 M) :
    beta ρ.1 σ.1 ε ≤ pairing σ.1 M := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro b ⟨N, hN, _, rfl⟩
    exact y28_pairing_nonneg σ.2.1 hN.1
  · exact ⟨M, hM, hacc, rfl⟩

private theorem y28_neglog_exp (a : ℝ) :
    OPT.binaryNegLog2 (Real.toNNReal (Real.rpow 2 (-a))) = (a : EReal) := by
  have hp : 0 < Real.rpow 2 (-a) := Real.rpow_pos_of_pos (by norm_num) _
  rw [OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hp)),
    Real.coe_toNNReal _ hp.le, Real.rpow_eq_pow,
    Real.logb_rpow (b := (2 : ℝ)) (x := -a) (by norm_num) (by norm_num), neg_neg]

private theorem y28_dh_lower {A : Type u} [Qudit A] (ρ σ : State A)
    (ε a : ℝ) (hM : effect (testHi ρ.1 σ.1 a))
    (hacc : 1 - ε ≤ testMass ρ.1 σ.1 a)
    (hbound : pairing σ.1 (testHi ρ.1 σ.1 a) ≤
      Real.rpow 2 (-a) * testMass ρ.1 σ.1 a)
    (hmass : testMass ρ.1 σ.1 a ≤ 1) : (a : EReal) ≤ dh ρ.1 σ.1 ε := by
  have hb : beta ρ.1 σ.1 ε ≤ Real.rpow 2 (-a) := calc
    _ ≤ pairing σ.1 (testHi ρ.1 σ.1 a) := y28_beta_le ρ σ ε _ hM hacc
    _ ≤ Real.rpow 2 (-a) * testMass ρ.1 σ.1 a := hbound
    _ ≤ Real.rpow 2 (-a) := mul_le_of_le_one_right (Real.rpow_nonneg (by norm_num) _) hmass
  have hl := QuantumModel.NativeHypothesisTesting.Internal.binaryNegLog2_antitone
    (Real.toNNReal_mono hb)
  change OPT.binaryNegLog2 (Real.toNNReal (Real.rpow 2 (-a))) ≤ dh ρ.1 σ.1 ε at hl
  rw [y28_neglog_exp] at hl
  exact hl

private theorem y28_rate_lower (f : ℕ → EReal) (n : ℕ) (hn : 0 < n) (r : ℝ)
    (h : (((n : ℝ) * r : ℝ) : EReal) ≤ f n) : (r : EReal) ≤ rate f n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale : ((1 / (n : ℝ) : ℝ) : EReal) * (((n : ℝ) * r : ℝ) : EReal) =
      (r : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    field_simp
  rw [rate, if_neg hn.ne', ← hscale]
  exact mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr (by positivity))

theorem gsl_y28 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X σ : OpSeq.{u} A) (ε δ R : ℝ),
  (∀ n : ℕ, 0 < n → IsDensity.{u} (X n) ∧ IsDensity.{u} (σ n)) →
  ε ∈ Set.Ico 0 1 → 0 < δ →
  Filter.liminf (pairRate.{u} X σ ε) atTop ≤ (R : EReal) →
  Filter.liminf (fun n : ℕ => testMass.{u} (X n) (σ n) ((n : ℝ)*(R+δ))) atTop ≤ 1-ε
:= by
  intro A _ _ X σ ε δ R hden _ hδ hrate
  have hmass : ∀ᶠ n : ℕ in atTop,
      testMass (X n) (σ n) ((n : ℝ) * (R + δ)) ∈ Set.Icc 0 1 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (GourResource.gsl_y27.{u} ⟨X n, (hden n hn).1⟩ ⟨σ n, (hden n hn).2⟩ _).2.2
  by_contra h
  have hlarge := eventually_lt_of_lt_liminf (lt_of_not_ge h)
    (isBoundedUnder_of_eventually_ge (hmass.mono fun _ hn => hn.1))
  have hrlower : ((R + δ : ℝ) : EReal) ≤ Filter.liminf (pairRate X σ ε) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hlarge, eventually_gt_atTop 0] with n hacc hn
    obtain ⟨htest, hbound, hmem⟩ :=
      GourResource.gsl_y27.{u} ⟨X n, (hden n hn).1⟩ ⟨σ n, (hden n hn).2⟩ ((n : ℝ) * (R + δ))
    exact y28_rate_lower _ n hn (R + δ)
      (y28_dh_lower ⟨X n, (hden n hn).1⟩ ⟨σ n, (hden n hn).2⟩ ε _
        htest hacc.le hbound hmem.2)
  have hreal := EReal.coe_le_coe_iff.mp (hrlower.trans hrate)
  linarith

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y29 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X σ : OpSeq.{u} A) (ε δ R : ℝ),
  (∀ n : ℕ, 0 < n → IsDensity.{u} (X n) ∧ IsDensity.{u} (σ n)) →
  ε ∈ Set.Ico 0 1 → 0 < δ →
  Filter.limsup (pairRate.{u} X σ ε) atTop ≤ (R : EReal) →
  Filter.limsup (fun n : ℕ => testMass.{u} (X n) (σ n) ((n : ℝ)*(R+δ))) atTop ≤ 1-ε
:= by
  intro A _ _ X σ ε δ R hstate _hε hδ hrate
  have hmass : ∀ᶠ n : ℕ in atTop,
      testMass (X n) (σ n) ((n : ℝ) * (R + δ)) ∈ Set.Icc 0 1 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (GourResource.gsl_y27.{u} ⟨X n, (hstate n hn).1⟩ ⟨σ n, (hstate n hn).2⟩
      ((n : ℝ) * (R + δ))).2.2
  have htail : ∀ᶠ n : ℕ in atTop, pairRate X σ ε n < ((R + δ / 2 : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt (hrate.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
  apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop
    (hmass.mono fun _ hn => hn.1))
  filter_upwards [eventually_gt_atTop 0, htail] with n hn hr
  by_contra hm
  have hacc : 1 - ε ≤ testMass (X n) (σ n) ((n : ℝ) * (R + δ)) :=
    (lt_of_not_ge hm).le
  obtain ⟨hM, hII, hIcc⟩ := GourResource.gsl_y27.{u} ⟨X n, (hstate n hn).1⟩
    ⟨σ n, (hstate n hn).2⟩ ((n : ℝ) * (R + δ))
  have hb : beta (X n) (σ n) ε ≤ Real.rpow 2 (-((n : ℝ) * (R + δ))) := by
    have hbM : beta (X n) (σ n) ε ≤
        pairing (σ n) (testHi (X n) (σ n) ((n : ℝ) * (R + δ))) := by
      unfold beta
      refine csInf_le ?_ ⟨_, hM, hacc, rfl⟩
      refine ⟨0, ?_⟩
      rintro b ⟨M, hN, _, rfl⟩
      unfold pairing
      by_cases hz : σ n * M = 0
      · simp only [hz, map_zero, Complex.zero_re, le_refl]
      · exact (OPT.trace_re_pos_mul_of_nonneg_of_ne_zero
          ((LinearMap.nonneg_iff_isPositive _).mpr (hstate n hn).2.1)
          ((LinearMap.nonneg_iff_isPositive _).mpr hN.1) hz).le
    exact hbM.trans (hII.trans (mul_le_of_le_one_right
      (Real.rpow_nonneg (by norm_num) _) hIcc.2))
  have hd : (((n : ℝ) * (R + δ) : ℝ) : EReal) ≤ dh (X n) (σ n) ε := by
    by_cases hz : beta (X n) (σ n) ε ≤ 0
    · rw [dh, Real.toNNReal_of_nonpos hz, OPT.binaryNegLog2_zero]
      exact le_top
    have hp : 0 < beta (X n) (σ n) ε := lt_of_not_ge hz
    have hfinite : dh (X n) (σ n) ε =
        ((-Real.logb 2 (beta (X n) (σ n) ε) : ℝ) : EReal) := by
      rw [dh, OPT.binaryNegLog2,
        if_neg (ne_of_gt (Real.toNNReal_pos.mpr hp)), Real.coe_toNNReal _ hp.le]
    rw [hfinite, EReal.coe_le_coe_iff]
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hb
    have hlog' : Real.logb 2 (beta (X n) (σ n) ε) ≤ -((n : ℝ) * (R + δ)) :=
      hlog.trans_eq (Real.logb_rpow (by norm_num) (by norm_num))
    linarith
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hscale : ((R + δ : ℝ) : EReal) ≤ pairRate X σ ε n := by
    unfold pairRate rate
    rw [if_neg (Nat.ne_of_gt hn)]
    have hmul := mul_le_mul_of_nonneg_left hd
      (EReal.coe_nonneg.mpr (one_div_nonneg.mpr hnreal.le))
    rw [← EReal.coe_mul] at hmul
    convert hmul using 1
    congr 1
    field_simp [ne_of_gt hnreal]
  have hlt := hscale.trans_lt hr
  have : R + δ < R + δ / 2 := EReal.coe_lt_coe_iff.mp hlt
  linarith

end GourResource

