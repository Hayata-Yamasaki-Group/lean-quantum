/-
Admissibility of the tensor-power sequence and of the free mixture mixHY under hyValid (gsl_y12).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Bounds the free mixture from below by λ^n/3 and obtains full support.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.BlockConverse.Padding

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem pow_admissible {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (F : Family A) (hF : hyValid ρ F)
    (γ : State A) (hγ : pow γ 1 ∈ F 1) :
    admissible F (fun n => pow γ n) := by
  have hmem (n : ℕ) (hn : 0 < n) : pow γ n ∈ F n := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hz : n = 0
      · subst n
        exact hγ
      · have hn' : 0 < n := Nat.pos_of_ne_zero hz
        rw [← (GourResource.gsl_y05 ρ γ n 1).1]
        exact hF.2.2.1 n 1 hn' (by decide) _ (ih hn') _ hγ
  intro n hn
  exact ⟨hmem n hn, hF.1 n hn (hmem n hn)⟩

private theorem third_mix_mem {A : Type u} [Qudit A]
    (S : Set (L A)) (hS : Convex ℝ S) (X Y Z : L A)
    (hX : X ∈ S) (hY : Y ∈ S) (hZ : Z ∈ S) :
    (1 / 3 : ℝ) • (X + Y + Z) ∈ S := by
  have hXY : (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y ∈ S :=
    hS hX hY (by norm_num) (by norm_num) (by norm_num)
  have hXYZ := hS hXY hZ (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) (by norm_num)
  simpa only [smul_add, smul_smul, show (2 / 3 : ℝ) * (1 / 2) = 1 / 3 by norm_num]
    using hXYZ

private theorem third_mix_bounds {A : Type u} [Qudit A]
    (X Y Z : L A) (hX : IsDensity X) (hY : IsDensity Y) (hZ : IsDensity Z) :
    (1 / 3 : ℝ) • X ≤ (1 / 3 : ℝ) • (X + Y + Z) ∧
    (1 / 3 : ℝ) • Y ≤ (1 / 3 : ℝ) • (X + Y + Z) ∧
    (1 / 3 : ℝ) • Z ≤ (1 / 3 : ℝ) • (X + Y + Z) := by
  -- One shared nonnegativity step: each `smul_nonneg` on `L A` re-runs the costly
  -- `PosSMulMono ℝ (L A)` instance search, so it is elaborated once.
  have key : ∀ W : L A, IsDensity W → 0 ≤ (1 / 3 : ℝ) • W := fun W hW =>
    smul_nonneg (by norm_num) ((LinearMap.nonneg_iff_isPositive W).mpr hW.1)
  have hXs := key X hX
  have hYs := key Y hY
  have hZs := key Z hZ
  simp only [smul_add]
  exact ⟨(le_add_of_nonneg_right hYs).trans (le_add_of_nonneg_right hZs),
    (le_add_of_nonneg_left hXs).trans (le_add_of_nonneg_right hZs),
    le_add_of_nonneg_left (add_nonneg hXs hYs)⟩

theorem gsl_y12 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  (∀ γ : State.{u} A, pow.{u} γ 1 ∈ F 1 →
    admissible.{u} F (fun n => pow.{u} γ n)) ∧
  ∀ (γ : State.{u} A) (m : ℕ) (σ : L.{u} (Copy.{u} A m)) (z : OpSeq.{u} A),
  0 < m → pow.{u} γ 1 ∈ F 1 → σ ∈ F m → admissible.{u} F z →
    admissible.{u} F (fun n => pow.{u} γ n) ∧
    admissible.{u} F (mixHY.{u} ρ γ m σ z) ∧
    ∀ n : ℕ, 0 < n →
      IsDensity.{u} (z n) ∧ IsDensity.{u} (padded.{u} ρ γ m σ n) ∧ IsDensity.{u} (pow.{u} γ n) ∧
      (1/3 : ℝ) • z n ≤ mixHY.{u} ρ γ m σ z n ∧
      (1/3 : ℝ) • padded.{u} ρ γ m σ n ≤ mixHY.{u} ρ γ m σ z n ∧
      (1/3 : ℝ) • pow.{u} γ n ≤ mixHY.{u} ρ γ m σ z n
:= by
  intro A _ _ ρ F hF
  have hpow := pow_admissible ρ F hF
  refine ⟨hpow, ?_⟩
  intro γ m σ z hm hγ hσ hz
  have hp := hpow γ hγ
  have hpad := GourResource.gsl_y07 ρ F hF γ m σ hm hγ hσ
  refine ⟨hp, ?_, ?_⟩
  · intro n hn
    have hmem : mixHY ρ γ m σ z n ∈ F n :=
      third_mix_mem (F n) (hF.2.1 n hn).2 _ _ _
        (hz n hn).1 (hpad n hn).1 (hp n hn).1
    exact ⟨hmem, hF.1 n hn hmem⟩
  · intro n hn
    exact ⟨(hz n hn).2, (hpad n hn).2, (hp n hn).2,
      third_mix_bounds _ _ _ (hz n hn).2 (hpad n hn).2 (hp n hn).2⟩

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y13 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (γ : State.{u} A) (lam : ℝ) (m : ℕ) (σ : L.{u} (Copy.{u} A m)) (z : OpSeq.{u} A),
  0 < m → pow.{u} γ 1 ∈ F 1 → σ ∈ F m → admissible.{u} F z →
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → (lam^n : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ pow.{u} γ n) →
  ∀ n : ℕ, 0 < n →
    IsDensity.{u} (mixHY.{u} ρ γ m σ z n) ∧
    (lam^n/3 : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ mixHY.{u} ρ γ m σ z n ∧
    IsPositiveDefinite.{u} (mixHY.{u} ρ γ m σ z n) ∧
    IsDensity.{u} (z n) ∧ IsDensity.{u} (padded.{u} ρ γ m σ n) ∧ IsDensity.{u} (pow.{u} γ n) ∧
    (1/3 : ℝ) • z n ≤ mixHY.{u} ρ γ m σ z n ∧
    (1/3 : ℝ) • padded.{u} ρ γ m σ n ≤ mixHY.{u} ρ γ m σ z n ∧
    (1/3 : ℝ) • pow.{u} γ n ≤ mixHY.{u} ρ γ m σ z n
:= by
  intro A _ _ ρ F hF γ lam m σ z hm hγ hσ hz hlam hpow n hn
  obtain ⟨_, hmix, hparts⟩ := (GourResource.gsl_y12.{u} ρ F hF).2 γ m σ z hm hγ hσ hz
  have hdensity := (hmix n hn).2
  have hparts := hparts n hn
  have hbound : (lam^n/3 : ℝ) • (1 : L (Copy A n)) ≤ mixHY ρ γ m σ z n := by
    calc
      (lam^n/3 : ℝ) • (1 : L (Copy A n)) =
          (1/3 : ℝ) • ((lam^n : ℝ) • (1 : L (Copy A n))) := by
        rw [smul_smul]
        congr 1
        ring
      _ ≤ (1/3 : ℝ) • pow γ n :=
        smul_le_smul_of_nonneg_left (hpow n hn) (by norm_num)
      _ ≤ mixHY ρ γ m σ z n := hparts.2.2.2.2.2
  refine ⟨hdensity, hbound, ⟨hdensity.1, ?_⟩, hparts⟩
  intro hdet
  apply (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hquad := ((LinearMap.le_def _ _).mp hbound).re_inner_nonneg_left x
  have hquad' : 0 ≤ -(lam^n/3) * ‖x‖ ^ 2 := by
    simp only [← Complex.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hx, zero_sub, inner_neg_left, inner_smul_left,
      Complex.conj_ofReal, map_neg] at hquad
    change 0 ≤ -(((lam^n/3 : ℝ) : ℂ) * inner ℂ x x).re at hquad
    rw [Complex.re_ofReal_mul] at hquad
    change 0 ≤ -((lam^n/3) * RCLike.re (inner ℂ x x)) at hquad
    simpa only [inner_self_eq_norm_sq, neg_mul] using hquad
  have hpos : 0 < lam^n/3 := div_pos (pow_pos hlam.1 n) (by norm_num)
  have hnorm : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

end GourResource

