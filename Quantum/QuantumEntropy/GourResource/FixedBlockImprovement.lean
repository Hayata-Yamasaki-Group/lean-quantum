/-
Divides the three-region estimate for finite n by n and moves it to an entropy-rate upper bound with a constant C uniform in δ.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Bounds the pinched-entropy liminf of a fixed block, ε and optimal sequence by s+(1−ε)(b−s).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Returns the estimate from the pinched entropy to the seqRate of the free mixture sequence before rounding.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.ThreeRegions
import Quantum.QuantumEntropy.GourResource.RateLimits
import Mathlib.Data.EReal.Operations
import Quantum.QuantumEntropy.GourResource.TwoMasses
import Quantum.QuantumEntropy.GourResource.RelativeDomination
import Quantum.QuantumEntropy.GourResource.PinchingRate

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem cap_floor (lam b δ : ℝ) (n : ℕ) (hlam : 0 < lam) (hn : 0 < n) :
    Real.rpow 2 (-((n : ℝ) * cap lam b δ n)) ≤
      Real.rpow 2 (-cBits lam n) * (lam ^ n / 3) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hlog : Real.logb 2 (lam ^ n / 3) = -(n : ℝ) * cBits lam n := by
    rw [Real.logb_div (ne_of_gt (pow_pos hlam n)) (by norm_num), Real.logb_pow]
    simp only [cBits, max_eq_left (Nat.succ_le_iff.mpr hn), one_div, Real.logb_inv]
    field_simp [hn0]
    ring
  have heq : Real.rpow 2 (-(n : ℝ) * cBits lam n) = lam ^ n / 3 := by
    rw [← hlog]
    exact Real.rpow_logb (by norm_num) (by norm_num)
      (div_pos (pow_pos hlam n) (by norm_num))
  have hcap := mul_le_mul_of_nonneg_left
    (le_max_left (cBits lam n + cBits lam n / (n : ℝ)) (b + δ)) hnpos.le
  have hcancel : (n : ℝ) * (cBits lam n + cBits lam n / (n : ℝ)) =
      (n : ℝ) * cBits lam n + cBits lam n := by
    field_simp
  calc
    Real.rpow 2 (-((n : ℝ) * cap lam b δ n)) ≤
        Real.rpow 2 (-cBits lam n + -(n : ℝ) * cBits lam n) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      change (n : ℝ) * (cBits lam n + cBits lam n / (n : ℝ)) ≤
        (n : ℝ) * cap lam b δ n at hcap
      rw [hcancel] at hcap
      linarith
    _ = Real.rpow 2 (-cBits lam n) * (lam ^ n / 3) := by
      calc
        _ = Real.rpow 2 (-cBits lam n) * Real.rpow 2 (-(n : ℝ) * cBits lam n) :=
          Real.rpow_add (by norm_num) _ _
        _ = _ := by rw [heq]

private theorem rounded_floor {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (S : State.{u} A) (lam b δ : ℝ) (n : ℕ) (hlam : lam ∈ Set.Ioc 0 1)
    (hn : 0 < n) (hS : (lam ^ n / 3 : ℝ) • (1 : L.{u} A) ≤ S.1) :
    (Real.rpow 2 (-((n : ℝ) * cap lam b δ n)) : ℝ) • (1 : L.{u} A) ≤
      rounded lam n S.1 := by
  calc
    _ ≤ (Real.rpow 2 (-cBits lam n) * (lam ^ n / 3)) • (1 : L.{u} A) :=
      smul_le_smul_of_nonneg_right (cap_floor lam b δ n hlam.1 hn) zero_le_one
    _ = Real.rpow 2 (-cBits lam n) • ((lam ^ n / 3 : ℝ) • (1 : L.{u} A)) :=
      (smul_smul _ _ _).symm
    _ ≤ Real.rpow 2 (-cBits lam n) • S.1 :=
      smul_le_smul_of_nonneg_left hS (Real.rpow_pos_of_pos (by norm_num) _).le
    _ ≤ rounded lam n S.1 := (GourResource.gsl_y19 S lam n hlam hn hS).2.2.1

theorem gsl_y44 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (γ : State.{u} A) (lam : ℝ) (m : ℕ) (σ : L.{u} (Copy.{u} A m))
    (z : OpSeq.{u} A) (ε : ℝ),
  IsPositiveDefinite.{u} γ.1 → pow.{u} γ 1 ∈ F 1 →
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → (lam^n : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ pow.{u} γ n) →
  0 < m → σ ∈ F m → ε ∈ Set.Ioo 0 1 → optSeq.{u} ρ F ε z →
  let S := mixHY.{u} ρ γ m σ z
  let T := fun n => rounded.{u} lam n (S n)
  let X := fun n => pin.{u} (T n) (pow.{u} ρ n)
  ∀ s b : ℝ, 0 ≤ s →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) → s ≤ b →
  ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ ≤ (b : EReal) →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, δ ∈ Set.Ioo 0 1 →
    ∀ᶠ n in atTop, entRate.{u} X T n ≤
      ((s+δ + (b-s)*testMass.{u} (X n) (T n) ((n : ℝ)*(s+δ)) +
        C*testMass.{u} (X n) (T n) ((n : ℝ)*(b+δ)) : ℝ) : EReal)
:= by
  intro A _ _ ρ F hF γ lam m σ z ε _ hγ hlam hpow hm hσ _ hz
  dsimp only
  intro s b hs _ hsb _
  obtain ⟨C, hC, htail⟩ := GourResource.gsl_y40 lam b hlam
  refine ⟨C, hC, ?_⟩
  intro δ hδ
  filter_upwards [htail δ hδ, eventually_gt_atTop 0] with n hcap hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  obtain ⟨hS, hSlower, _⟩ :=
    GourResource.gsl_y13 ρ F hF γ lam m σ z hm hγ hσ hz.1 hlam hpow n hn
  let S : State (Copy A n) := ⟨mixHY ρ γ m σ z n, hS⟩
  obtain ⟨hT, hTpos, _⟩ := GourResource.gsl_y19 S lam n hlam hn hSlower
  let T : State (Copy A n) := ⟨rounded lam n S.1, hT⟩
  have hX : IsDensity (pin T.1 (pow ρ n)) :=
    spectralPinchingChannel_isDensity T.1 hT.1.isSymmetric (pow ρ n)
      (w42_tensor_spectral_dictionary.1 ρ n).2.1
  let X : State (Copy A n) := ⟨pin T.1 (pow ρ n), hX⟩
  have hcomm : Commute X.1 T.1 :=
    spectralPinchingChannel_commute T.1 hT.1.isSymmetric (pow ρ n)
  have hab : (n : ℝ) * (s + δ) ≤ (n : ℝ) * (b + δ) :=
    mul_le_mul_of_nonneg_left (add_le_add hsb le_rfl) hnpos.le
  have hbc : (n : ℝ) * (b + δ) ≤ (n : ℝ) * cap lam b δ n :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hnpos.le
  have hbound := GourResource.gsl_y38.{u} X T ((n : ℝ) * (s + δ)) ((n : ℝ) * (b + δ))
    ((n : ℝ) * cap lam b δ n) hTpos hcomm hab hbc
    (rounded_floor S lam b δ n hlam hn hSlower)
  have hmass : 0 ≤ testMass X.1 T.1 ((n : ℝ) * (b + δ)) :=
    (GourResource.gsl_y27 X T ((n : ℝ) * (b + δ))).2.2.1
  have hcoeff : cap lam b δ n - (b + δ) ≤ C := by linarith [hδ.1]
  have hreal :
      (1 / (n : ℝ)) *
        ((n : ℝ) * (s + δ) +
          ((n : ℝ) * (b + δ) - (n : ℝ) * (s + δ)) *
            testMass X.1 T.1 ((n : ℝ) * (s + δ)) +
          ((n : ℝ) * cap lam b δ n - (n : ℝ) * (b + δ)) *
            testMass X.1 T.1 ((n : ℝ) * (b + δ))) ≤
        s + δ + (b - s) * testMass X.1 T.1 ((n : ℝ) * (s + δ)) +
          C * testMass X.1 T.1 ((n : ℝ) * (b + δ)) := by
    calc
      _ = s + δ + (b - s) * testMass X.1 T.1 ((n : ℝ) * (s + δ)) +
          (cap lam b δ n - (b + δ)) * testMass X.1 T.1 ((n : ℝ) * (b + δ)) := by
        field_simp
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hmass)
  change entRate (fun k => pin (rounded lam k (mixHY ρ γ m σ z k)) (pow ρ k))
    (fun k => rounded lam k (mixHY ρ γ m σ z k)) n ≤ _
  rw [entRate, rate, if_neg (Nat.ne_of_gt hn)]
  exact (mul_le_mul_of_nonneg_left hbound
    (show (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) by positivity)).trans
    (by simpa only [← EReal.coe_mul, EReal.coe_le_coe_iff] using hreal)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem le_of_small_add (x : EReal) (a : ℝ)
    (h : ∀ δ : ℝ, δ ∈ Set.Ioo 0 1 → x ≤ ((a + δ : ℝ) : EReal)) :
    x ≤ (a : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r hr
  have har : a < r := EReal.coe_lt_coe_iff.mp hr
  obtain ⟨δ, hδ0, hδ⟩ := exists_between (show (0 : ℝ) < min 1 (r - a) by
    exact lt_min (by norm_num) (sub_pos.mpr har))
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδr : δ < r - a := lt_of_lt_of_le hδ (min_le_right _ _)
  exact (h δ ⟨hδ0, hδ1⟩).trans (EReal.coe_le_coe_iff.mpr (by linarith))

theorem gsl_y45 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (γ : State.{u} A) (lam : ℝ) (m : ℕ) (σ : L.{u} (Copy.{u} A m))
    (z : OpSeq.{u} A) (ε : ℝ),
  IsPositiveDefinite.{u} γ.1 → pow.{u} γ 1 ∈ F 1 →
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → (lam^n : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ pow.{u} γ n) →
  0 < m → σ ∈ F m → ε ∈ Set.Ioo 0 1 → optSeq.{u} ρ F ε z →
  let S := mixHY.{u} ρ γ m σ z
  let T := fun n => rounded.{u} lam n (S n)
  let X := fun n => pin.{u} (T n) (pow.{u} ρ n)
  ∀ s b : ℝ, 0 ≤ s →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) → s ≤ b →
  ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ ≤ (b : EReal) →
  Filter.liminf (entRate.{u} X T) atTop ≤ ((s+(1-ε)*(b-s) : ℝ) : EReal)
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγ hγF hlam hpow hm hσ hε hz
  dsimp only
  intro s b hs hlim hsb hdu
  obtain ⟨C, hC, hbound⟩ :=
    GourResource.gsl_y44.{u} ρ F hF γ lam m σ z ε hγ hγF hlam hpow hm hσ hε hz s b hs hlim hsb hdu
  apply le_of_small_add
  intro δ hδ
  obtain ⟨hp, hq, hpq⟩ :=
    GourResource.gsl_y43.{u} ρ F hF γ lam m σ z ε hγ hγF hlam hpow hm hσ hε hz s b hs hlim hsb hdu
      δ hδ.1
  have hrate := GourResource.gsl_y39 _ _ _ (s + δ) (b - s) C (1 - ε)
    (sub_nonneg.mpr hsb) hC hpq hp hq (hbound δ hδ)
  convert hrate using 1
  congr 1
  ring

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y46 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (γ : State.{u} A) (lam : ℝ) (m : ℕ) (σ : L.{u} (Copy.{u} A m))
    (z : OpSeq.{u} A) (ε : ℝ),
  IsPositiveDefinite.{u} γ.1 → pow.{u} γ 1 ∈ F 1 →
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → (lam^n : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ pow.{u} γ n) →
  0 < m → σ ∈ F m → ε ∈ Set.Ioo 0 1 → optSeq.{u} ρ F ε z →
  let S := mixHY.{u} ρ γ m σ z
  let T := fun n => rounded.{u} lam n (S n)
  let _X := fun n => pin.{u} (T n) (pow.{u} ρ n)
  ∀ s b : ℝ, 0 ≤ s →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) → s ≤ b →
  ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ ≤ (b : EReal) →
  Filter.liminf (seqRate.{u} ρ S) atTop ≤ ((s+(1-ε)*(b-s) : ℝ) : EReal)
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγpos hγ hlam hpow hm hσ hε hz
  dsimp only
  intro s b hs hlim hsb hdu
  have hS : ∀ n : ℕ, 0 < n → IsDensity (mixHY ρ γ m σ z n) ∧
      (lam^n/3 : ℝ) • (1 : L (Copy A n)) ≤ mixHY ρ γ m σ z n := by
    intro n hn
    have h := GourResource.gsl_y13.{u} ρ F hF γ lam m σ z
      hm hγ hσ hz.1 hlam hpow n hn
    exact ⟨h.1, h.2.1⟩
  have hround := GourResource.gsl_y24.{u} ρ (mixHY ρ γ m σ z) lam hlam hS
  have hpin := GourResource.gsl_y25.{u} ρ (mixHY ρ γ m σ z) lam hlam hS
  exact (hround.trans hpin).le.trans
    (GourResource.gsl_y45.{u} ρ F hF γ lam m σ z ε hγpos hγ hlam hpow hm hσ hε hz s b hs hlim hsb
      hdu)

end GourResource

