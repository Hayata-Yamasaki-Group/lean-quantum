/-
Obtains, from an optimal free sequence, a liminf upper bound on the low-threshold testing rate after rounding and pinching.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
From a fixed block and a full-support seed, evaluates the limsup of the high-threshold testing rate by block DU/m.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.FreeMixture
import Quantum.QuantumEntropy.GourResource.SpectralRounding
import Quantum.QuantumEntropy.GourResource.TestingDomination
import Quantum.QuantumEntropy.GourResource.BlockConverse

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem error_properties (lam : ℝ) (hlam : lam ∈ Set.Ioc 0 1) :
    (∀ n : ℕ, 0 ≤ cBits lam n + Real.logb 2 3) ∧
    Tendsto (fun n : ℕ => (cBits lam n + Real.logb 2 3) / (n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨hpos, hlim⟩ := GourResource.gsl_y14 lam hlam
  constructor
  · intro n
    exact add_nonneg (hpos n).le (Real.logb_nonneg (by norm_num) (by norm_num))
  · simpa only [add_div, add_zero] using
      hlim.add (tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 3))

private theorem combine_domination {A : Type u} [Qudit A]
    (S T z : L A) (c : ℝ) (hmix : (1 / 3 : ℝ) • z ≤ S)
    (hround : Real.rpow 2 (-c) • S ≤ T) :
    Real.rpow 2 (-(c + Real.logb 2 3)) • z ≤ T := by
  have hfactor : Real.rpow 2 (-(c + Real.logb 2 3)) =
      Real.rpow 2 (-c) * (1 / 3 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [neg_add, Real.rpow_add (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 3),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [hfactor, ← smul_smul]
  exact (smul_le_smul_of_nonneg_left hmix (Real.rpow_nonneg (by norm_num) _)).trans hround

theorem gsl_y33 :
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
  Filter.liminf (pairRate.{u} X T ε) atTop ≤ Filter.liminf (hRate.{u} ρ F ε) atTop
:= by
  intro A _ _ ρ F hF γ lam m σ z ε _ hγ hlam hpow hm hσ hε hz
  dsimp only
  let S := mixHY ρ γ m σ z
  let T := fun n => rounded lam n (S n)
  have hmix := GourResource.gsl_y13 ρ F hF γ lam m σ z hm hγ hσ hz.1 hlam hpow
  have hround (n : ℕ) (hn : 0 < n) :=
    GourResource.gsl_y19 (⟨S n, (hmix n hn).1⟩ : State (Copy A n))
      lam n hlam hn (hmix n hn).2.1
  let E : (n : ℕ) → CPTP (Copy A n) (Copy A n) := fun n =>
    if hn : 0 < n then spectralPinchingChannel (T n) (hround n hn).1.1.isSymmetric
    else spectralPinchingChannel 0 (by exact LinearMap.IsSymmetric.zero)
  have hE (n : ℕ) (hn : 0 < n) :
      E n = spectralPinchingChannel (T n) (hround n hn).1.1.isSymmetric := by
    simp only [E, dif_pos hn]
  have hfix (n : ℕ) (hn : 0 < n) : (E n).toFun (T n) = T n := by
    rw [hE n hn]
    exact (spectralPinchingChannel_eq_iff_commute _ _ _).mpr (Commute.refl _)
  obtain ⟨hf, hlim⟩ := error_properties lam hlam
  have hbound := GourResource.gsl_y31 (fun n => pow ρ n) T z E
    (fun n => cBits lam n + Real.logb 2 3) ε
    (fun n hn => ⟨(w42_tensor_spectral_dictionary.1 ρ n).2.1,
      (hround n hn).1, (hz.1 n hn).2⟩) ⟨hε.1.le, hε.2⟩ hf hlim
    (fun n hn => combine_domination (S n) (T n) (z n) (cBits lam n)
      (hmix n hn).2.2.2.2.2.2.1 (hround n hn).2.2.1)
  have hleft : Filter.liminf
      (pairRate (fun n => (E n).toFun (pow ρ n)) (fun n => (E n).toFun (T n)) ε)
      atTop = Filter.liminf (pairRate (fun n => pin (T n) (pow ρ n)) T ε) atTop := by
    apply Filter.liminf_congr
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [pairRate, rate, if_neg (Nat.ne_of_gt hn)]
    rw [hfix n hn, hE n hn]
    rfl
  have hright : Filter.liminf (pairRate (fun n => pow ρ n) z ε) atTop =
      Filter.liminf (hRate ρ F ε) atTop := by
    apply Filter.liminf_congr
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [pairRate, hRate, rate, if_neg (Nat.ne_of_gt hn), hz.2 n hn]
  rw [hleft, hright] at hbound
  exact hbound

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem rounded_symmetric {A : Type u} [Qudit A]
    (lam : ℝ) (n : ℕ) (X : L A) : (rounded lam n X).IsSymmetric := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
  exact IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff]) IsSelfAdjoint.cfc

private theorem rounding_padding_domination {A : Type u} [Qudit A]
    (P S T : L A) (c : ℝ) (hP : 0 ≤ P)
    (hPS : (1 / 3 : ℝ) • P ≤ S)
    (hST : Real.rpow 2 (-c) • S ≤ T) :
    Real.rpow 2 (-(c + 2)) • P ≤ T := by
  have hquarter : (1 / 4 : ℝ) • P ≤ S :=
    (smul_le_smul_of_nonneg_right (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3) hP).trans hPS
  have hscale := smul_le_smul_of_nonneg_left hquarter
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-c))
  have heq : Real.rpow 2 (-(c + 2)) = Real.rpow 2 (-c) * (1 / 4) := by
    simp only [Real.rpow_eq_pow]
    rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Real.rpow_neg]
  rw [heq, mul_smul]
  exact hscale.trans hST

theorem gsl_y34 :
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
  ∀ η : ℝ, η ∈ Set.Ioo 0 1 →
  Filter.limsup (pairRate.{u} X T (1-η)) atTop ≤
    ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγ hγF hlam hseed hm hσ _ hz
  dsimp only
  intro η hη
  let S := mixHY ρ γ m σ z
  let T := fun n => rounded lam n (S n)
  let P := padded ρ γ m σ
  have hS := GourResource.gsl_y13 ρ F hF γ lam m σ z hm hγF hσ hz.1 hlam hseed
  have hT (n : ℕ) (hn : 0 < n) :=
    GourResource.gsl_y19 (⟨S n, (hS n hn).1⟩ : State (Copy A n))
      lam n hlam hn (hS n hn).2.1
  let E : (n : ℕ) → CPTP (Copy A n) (Copy A n) :=
    fun n => spectralPinchingChannel (T n) (rounded_symmetric lam n (S n))
  have hfix (n : ℕ) : (E n).toFun (T n) = T n :=
    (spectralPinchingChannel_eq_iff_commute (T n)
      (rounded_symmetric lam n (S n)) (T n)).mpr (Commute.refl _)
  have hη' : 1 - η ∈ Set.Ico (0 : ℝ) 1 := by
    constructor <;> linarith [hη.1, hη.2]
  have hc := GourResource.gsl_y14 lam hlam
  have hlim : Tendsto (fun n : ℕ => (cBits lam n + 2) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      hc.2.add (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  have hdom (n : ℕ) (hn : 0 < n) :
      Real.rpow 2 (-(cBits lam n + 2)) • P n ≤ T n := by
    exact rounding_padding_domination (P n) (S n) (T n) (cBits lam n)
      ((LinearMap.nonneg_iff_isPositive _).mpr (hS n hn).2.2.2.2.1.1)
      (hS n hn).2.2.2.2.2.2.2.1 (hT n hn).2.2.1
  have hbound := GourResource.gsl_y32 (pow ρ) T P E
    (fun n => cBits lam n + 2) (1 - η)
    (fun n hn => ⟨(w42_tensor_spectral_dictionary.1 ρ n).2.1,
      (hT n hn).1, (hS n hn).2.2.2.2.1⟩)
    hη' (fun n => by linarith [(hc.1 n)]) hlim hdom
  have hblock := GourResource.gsl_y09 ρ γ m
    (⟨σ, hF.1 m hm hσ⟩ : State (Copy A m)) (1 - η) hm hγ hη'
  have hresult := hbound.trans hblock
  simpa only [hfix] using hresult

end GourResource

