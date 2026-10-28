/-
Composition of the constant rate of tensor DU for an arbitrary admissible full-support γ with admissibility.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4; Hayashi–Yamasaki, Lemma 5.
-/
import Quantum.QuantumEntropy.GourResource.TensorSeed

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem seed_density {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (γ : State.{u} A) (n : ℕ) : IsDensity (pow γ n) :=
  (w42_tensor_spectral_dictionary.1 γ n).2.1

private theorem seed_finite {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State.{u} A) (hγ : IsPositiveDefinite γ.1) :
    ∃ r : ℝ, 0 ≤ r ∧ du ρ.1 γ.1 = (r : EReal) := by
  have hker : LinearMap.ker γ.1 = ⊥ := by
    by_contra hne
    exact hγ.2 (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ.1 γ.1 := by
    rw [SandwichedRenyiRelativeEntropy.suppLE, SandwichedRenyiRelativeEntropy.SupportLE, hker]
    exact bot_le
  have heq := w38_vn_spectral_dictionary.2.2.2 ρ.1 γ.1 ρ.2 γ.2 hsupp
  change du ρ.1 γ.1 = _ at heq
  refine ⟨_, ?_, heq⟩
  apply EReal.coe_nonneg.mp
  rw [← heq]
  exact (w37_relative_diagonal_calibration umegakiBits
    w38_vn_spectral_dictionary.2.2.1).1 ρ γ

private theorem seed_power_value {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State.{u} A) (r : ℝ) (hr : du ρ.1 γ.1 = (r : EReal)) (n : ℕ) :
    du (pow ρ n) (pow γ n) = ((n : ℝ) * r : ℝ) := by
  induction n with
  | zero =>
    simp [w42OperatorPower, du,
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
      SandwichedRenyiRelativeEntropy.SupportLE,
      SandwichedRenyiRelativeEntropy.umegakiNorm]
  | succ n ih =>
    have ht := w38_vn_spectral_dictionary.2.2.1.tensorAdditivity
      ρ.1 γ.1 (pow ρ n) (pow γ n) ρ.2 γ.2 (seed_density ρ n) (seed_density γ n)
    change du (pow ρ (n + 1)) (pow γ (n + 1)) =
      du ρ.1 γ.1 + du (pow ρ n) (pow γ n) at ht
    rw [ht, hr, ih, ← EReal.coe_add]
    congr 1
    push_cast
    ring

private theorem seed_rate_value {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State.{u} A) (r : ℝ) (hr : du ρ.1 γ.1 = (r : EReal))
    (n : ℕ) (hn : 0 < n) :
    rate (fun k => du (pow ρ k) (pow γ k)) n = (r : EReal) := by
  rw [rate, if_neg (Nat.ne_of_gt hn), seed_power_value ρ γ r hr n,
    ← EReal.coe_mul]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

theorem gsl_y60 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A),
  hyValid.{u} ρ F → ∀ γ : State.{u} A, IsPositiveDefinite.{u} γ.1 → pow.{u} γ 1 ∈ F 1 →
  admissible.{u} F (fun n => pow.{u} γ n) ∧
  ∃ r : ℝ, 0 ≤ r ∧ du.{u} ρ.1 γ.1 = (r : EReal) ∧
    (∀ n : ℕ, 0 < n → rate (fun k => du.{u} (pow.{u} ρ k) (pow.{u} γ k)) n = (r : EReal)) ∧
    Tendsto (seqRate.{u} ρ (fun n => pow.{u} γ n)) atTop (𝓝 (r : EReal))
:= by
  intro A _ _ ρ F hF γ hγ hγF
  have hmem : ∀ n : ℕ, 0 < n → pow γ n ∈ F n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hγF
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hj := hF.2.2.1 n 1 hnpos (by omega)
          (pow γ n) (ih hnpos) (pow γ 1) hγF
        rwa [(GourResource.gsl_y05.{u} ρ γ n 1).1] at hj
  refine ⟨fun n hn => ⟨hmem n hn, seed_density γ n⟩, ?_⟩
  obtain ⟨r, hr0, hr⟩ := seed_finite ρ γ hγ
  have hrate := seed_rate_value ρ γ r hr
  refine ⟨r, hr0, hr, hrate, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (hrate n hn).symm

end GourResource

