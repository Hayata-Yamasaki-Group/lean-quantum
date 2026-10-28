/-
σ_m and ρ are allowed to be rank deficient.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 6.
-/
import Quantum.QuantumModel.KW.Entropies.SteinPrerequisites
import Quantum.QuantumEntropy.GourResource.KWEntropyBridge
import Quantum.QuantumEntropy.GourResource.BlockConverse.Padding
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein
import Quantum.QuantumModel.KW.Distances.HypothesisTestingBounds.RelativeEntropy.GSLCore

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem y09_E5 {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) :
    Tendsto (fun α : ℝ => sand α ρ.1 σ.1) (𝓝[>] (1 : ℝ)) (𝓝 (du ρ.1 σ.1)) := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.{u}.1 (A := A)
  obtain ⟨e, he⟩ := (GourResource.gsl_b01.{u}.2.1 S U).1
  have hs := GourResource.gsl_b03.{u}.1 S (e ρ) (e σ)
  have ht := GourResource.gsl_b03.{u}.2.1 S U ρ σ
  have hd : QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits
      (e ρ) (e σ).operator = du ρ.1 σ.1 := by
    rw [← hs.1, he ρ, he σ]
    exact ht.1
  have hl :=
    QuantumModel.NativeStein.sandwichedRenyiDivBits_tendsto_umegaki
      (e ρ) (e σ)
  rw [hd] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  calc
    QuantumModel.NativeHypothesisTesting.sandwichedRenyiDivBits
        α (e ρ) (e σ).operator = sand α (e ρ).operator (e σ).operator := (hs.2.1 α hα).symm
    _ = sand α ρ.1 σ.1 := by rw [he ρ, he σ]; exact ht.2.1 α hα

private theorem y09_pow_density {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n : ℕ) : IsDensity (pow ρ n) :=
  (w42_tensor_spectral_dictionary.1 ρ n).2.1

private theorem y09_block_density {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (m : ℕ) (σ : State (Copy A m)) (k : ℕ) :
    IsDensity (blockPower ρ m σ.1 k) := by
  induction k with
  | zero =>
    have h : IsDensity (1 : L (Copy A 0)) := by
      rw [← (w42_tensor_spectral_dictionary.1 ρ 0).2.2.2]
      exact y09_pow_density ρ 0
    simpa only [blockPower] using h
  | succ k ih =>
    simpa only [blockPower] using (gsl_y05 ρ ρ (m * k) m).2.1 _ _ ih σ.2

private theorem y09_cast_density {A : Type u} [Qudit A] {j k : ℕ}
    (h : j = k) (X : L (Copy A j)) (hX : IsDensity X) :
    IsDensity (cast (congrArg (fun i => L (Copy A i)) h) X) := by
  subst k
  exact hX

private theorem y09_padded_density {A : Type u} [Qudit A] [Nontrivial A]
    (ρ γ : State A) (m : ℕ) (σ : State (Copy A m)) (n : ℕ) :
    IsDensity (padded ρ γ m σ.1 n) := by
  unfold padded
  apply y09_cast_density (Nat.div_add_mod n m)
  exact (gsl_y05 ρ γ (m * (n / m)) (n % m)).2.1 _ _
    (y09_block_density ρ m σ (n / m)) (y09_pow_density γ (n % m))

private theorem y09_sand_standard {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (α : ℝ) (hα : 1 < α) :
    sand α ρ.1 σ.1 =
      SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite α ρ.1 σ.1 := by
  classical
  have hα0 : 0 ≤ α := by linarith
  have hzero : ENNReal.ofReal α ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hone : ENNReal.ofReal α ≠ 1 := by
    intro h
    have := congrArg ENNReal.toReal h
    simp only [ENNReal.toReal_ofReal hα0, ENNReal.toReal_one] at this
    linarith
  rw [sand, dif_pos ρ.2, dif_pos σ.2,
    SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits_standard_order
      hzero hone ENNReal.ofReal_ne_top
      (by rw [ENNReal.toReal_ofReal hα0]; linarith),
    ENNReal.toReal_ofReal hα0]

private theorem y09_sand_real_or_top {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (α : ℝ) (hα : 1 < α) :
    sand α ρ.1 σ.1 = ⊤ ∨ ∃ r : ℝ, sand α ρ.1 σ.1 = (r : EReal) := by
  rw [y09_sand_standard ρ σ α hα]
  unfold SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite
  split_ifs
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

private theorem y09_sand_pd_real {A : Type u} [Qudit A] [Nontrivial A]
    (ρ γ : State A) (α : ℝ) (hα : 1 < α) (hγ : IsPositiveDefinite γ.1) :
    ∃ r : ℝ, sand α ρ.1 γ.1 = (r : EReal) := by
  have hs := SandwichedRenyiRelativeEntropy.suppLE_of_pdSetLM_right ρ.1
    ((OPT.isPositiveDefinite_iff_mem_pdSetLM γ.1).mp hγ)
  rw [y09_sand_standard ρ γ α hα]
  simp only [SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite,
    ne_of_gt hα, hs, not_true_eq_false, and_false, false_and, or_self,
    not_lt_of_ge hα.le, if_false]
  exact ⟨_, rfl⟩
private theorem y09_quotient_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n / m : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / (m : ℝ))) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_mod_div_atTop_nhds_zero_nat hm)).div_const
    (m : ℝ)
  have hlim' : Tendsto (fun n : ℕ => (1 - ((n % m : ℕ) : ℝ) / (n : ℝ)) / (m : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (m : ℝ) * (n / m : ℕ) + (n % m : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.div_add_mod n m
  field_simp [hn0, hm0]
  nlinarith

private theorem y09_numeric_limit (m : ℕ) (hm : 0 < m) (a b c : ℝ) :
    Tendsto (fun n : ℕ =>
      ((((n / m : ℕ) : ℝ) * a + ((n % m : ℕ) : ℝ) * b + c) / (n : ℝ) : EReal))
      atTop (𝓝 (((1 / (m : ℝ)) * a : ℝ) : EReal)) := by
  have hlim := ((y09_quotient_limit m hm).mul_const a).add
    ((tendsto_mod_div_atTop_nhds_zero_nat hm).mul_const b)
  have hc : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hreal : Tendsto (fun n : ℕ =>
      (((n / m : ℕ) : ℝ) * a + ((n % m : ℕ) : ℝ) * b + c) / (n : ℝ))
      atTop (𝓝 ((1 / (m : ℝ)) * a)) := by
    simpa only [add_div, mul_div_right_comm, zero_mul, add_zero] using hlim.add hc
  exact EReal.tendsto_coe.mpr hreal

private theorem y09_rate_bound (f : ℕ → EReal) (m : ℕ) (hm : 0 < m) (a b c : ℝ)
    (hf : ∀ n : ℕ, f n ≤
      ((n / m : ℕ) : EReal) * (a : EReal) +
        ((n % m : ℕ) : EReal) * (b : EReal) + (c : EReal)) :
    limsup (rate f) atTop ≤ ((1 / (m : ℝ) : ℝ) : EReal) * (a : EReal) := by
  have he : ∀ᶠ n : ℕ in atTop, rate f n ≤
      ((((n / m : ℕ) : ℝ) * a + ((n % m : ℕ) : ℝ) * b + c) / (n : ℝ) : EReal) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [rate, if_neg hn.ne']
    calc
      ((1 / (n : ℝ) : ℝ) : EReal) * f n ≤
          ((1 / (n : ℝ) : ℝ) : EReal) *
            (((n / m : ℕ) : EReal) * (a : EReal) +
              ((n % m : ℕ) : EReal) * (b : EReal) + (c : EReal)) :=
        mul_le_mul_of_nonneg_left (hf n) (by positivity)
      _ = _ := by
        simp only [← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add]
        congr 1
        ring
  simpa only [EReal.coe_mul] using
    (limsup_le_limsup he).trans_eq (y09_numeric_limit m hm a b c).limsup_eq

private theorem y09_fixed_alpha {A : Type u} [Qudit A] [Nontrivial A]
    (ρ γ : State A) (m : ℕ) (σ : State (Copy A m)) (ε α : ℝ)
    (hm : 0 < m) (hγ : IsPositiveDefinite γ.1) (hε : ε ∈ Set.Ico 0 1) (hα : 1 < α)
    (hadd : ∀ n : ℕ, sand α (pow ρ n) (padded ρ γ m σ.1 n) =
      ((n / m : ℕ) : EReal) * sand α (pow ρ m) σ.1 +
        ((n % m : ℕ) : EReal) * sand α ρ.1 γ.1) :
    limsup (rate (fun n => dh (pow ρ n) (padded ρ γ m σ.1 n) ε)) atTop ≤
      ((1 / (m : ℝ) : ℝ) : EReal) * sand α (pow ρ m) σ.1 := by
  have hmpos : 0 < 1 / (m : ℝ) := by positivity
  rcases y09_sand_real_or_top ⟨pow ρ m, y09_pow_density ρ m⟩ σ α hα with ht | ⟨a, ha⟩
  · change sand α (pow ρ m) σ.1 = ⊤ at ht
    rw [ht, EReal.coe_mul_top_of_pos hmpos]
    exact le_top
  · change sand α (pow ρ m) σ.1 = (a : EReal) at ha
    obtain ⟨b, hb⟩ := y09_sand_pd_real ρ γ α hα hγ
    rw [ha]
    apply y09_rate_bound _ m hm a b (α / (α - 1) * Real.logb 2 (1 / (1 - ε)))
    intro n
    have htest := gsl_b03.{u}.2.2.1
      ⟨pow ρ n, y09_pow_density ρ n⟩
      ⟨padded ρ γ m σ.1 n, y09_padded_density ρ γ m σ n⟩ ε α hε hα
    change dh (pow ρ n) (padded ρ γ m σ.1 n) ε ≤
      sand α (pow ρ n) (padded ρ γ m σ.1 n) +
        ((α / (α - 1) * Real.logb 2 (1 / (1 - ε)) : ℝ) : EReal) at htest
    rwa [hadd n, ha, hb] at htest

theorem gsl_y09 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ γ : State.{u} A) (m : ℕ)
  (σ : State.{u} (Copy.{u} A m)) (ε : ℝ),
  0 < m → IsPositiveDefinite.{u} γ.1 → ε ∈ Set.Ico 0 1 →
  Filter.limsup (rate (fun n => dh.{u} (pow.{u} ρ n) (padded.{u} ρ γ m σ.1 n) ε)) atTop ≤
    ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ.1
:= by
  intro A _ _ ρ γ m σ ε hm hγ hε
  have hmpos : 0 < 1 / (m : ℝ) := by positivity
  by_cases ht : du (pow ρ m) σ.1 = ⊤
  · rw [ht, EReal.coe_mul_top_of_pos hmpos]
    exact le_top
  · have hlim := EReal.Tendsto.const_mul
      (y09_E5 ⟨pow ρ m, y09_pow_density ρ m⟩ σ)
      (a := ((1 / (m : ℝ) : ℝ) : EReal))
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact y09_fixed_alpha ρ γ m σ ε α hm hγ hε hα (GourResource.gsl_y08.{u} ρ γ m σ α hm hα)

end GourResource

