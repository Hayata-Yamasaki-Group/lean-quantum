/-
Makes the liminf of the mass at the low threshold n(s+δ) at most 1−ε.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7; Hayashi–Yamasaki, Lemma S2.
-/
/-
Makes the mass at the high threshold n(b+δ) converge to 0 along every tail.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7; Hayashi–Yamasaki, Lemma S2.
-/
/-
Publishes the liminf, the Tendsto and the eventual Icc statements for the two masses together.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.SpectrumMass
import Quantum.QuantumEntropy.GourResource.PinchedRates

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y41 :
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
  ∀ s δ : ℝ, 0 < δ →
  Filter.liminf (hRate.{u} ρ F ε) atTop = (s : EReal) →
    Filter.liminf (fun n : ℕ => testMass.{u} (X n) (T n) ((n : ℝ)*(s+δ))) atTop ≤ 1-ε
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγpos hγ hlam hpow hm hσ hε hz
  dsimp only
  intro s δ hδ hs
  let S := mixHY ρ γ m σ z
  let T := fun n => rounded lam n (S n)
  let X := fun n => pin (T n) (pow ρ n)
  have hden : ∀ n : ℕ, 0 < n → IsDensity (X n) ∧ IsDensity (T n) := by
    intro n hn
    have hS := GourResource.gsl_y13 ρ F hF γ lam m σ z hm hγ hσ hz.1 hlam hpow n hn
    have hT : IsDensity (T n) :=
      (GourResource.gsl_y19 ⟨S n, hS.1⟩ lam n hlam hn hS.2.1).1
    have hρ : IsDensity (pow ρ n) := (w42_tensor_spectral_dictionary.1 ρ n).2.1
    exact ⟨spectralPinchingChannel_isDensity (T n) hT.1.isSymmetric (pow ρ n) hρ, hT⟩
  have hrate : Filter.liminf (pairRate X T ε) atTop ≤ (s : EReal) := by
    rw [← hs]
    exact GourResource.gsl_y33.{u} ρ F hF γ lam m σ z ε hγpos hγ hlam hpow hm hσ hε hz
  exact GourResource.gsl_y28 X T ε δ s hden ⟨hε.1.le, hε.2⟩ hδ hrate

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem mass_tendsto_zero (f : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, f n ∈ Set.Icc 0 1)
    (hs : ∀ η : ℝ, η ∈ Set.Ioo 0 1 → Filter.limsup f atTop ≤ η) :
    Tendsto f atTop (𝓝 0) := by
  have hlo : ∀ᶠ n in atTop, 0 ≤ f n := hf.mono fun _ h => h.1
  have hhi : ∀ᶠ n in atTop, f n ≤ 1 := hf.mono fun _ h => h.2
  have hsup : Filter.limsup f atTop ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η, hη0, hη⟩ := exists_between (lt_min hε zero_lt_one)
    exact (hs η ⟨hη0, (lt_min_iff.mp hη).2⟩).trans
      (by simpa using (lt_min_iff.mp hη).1.le)
  exact tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop hhi) hlo)
    hsup ⟨1, hhi⟩ ⟨0, hlo⟩

theorem gsl_y42 :
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
  ∀ b δ : ℝ, 0 < δ →
  ((1/(m : ℝ) : ℝ) : EReal) * du.{u} (pow.{u} ρ m) σ ≤ (b : EReal) →
    Tendsto (fun n : ℕ => testMass.{u} (X n) (T n) ((n : ℝ)*(b+δ))) atTop (𝓝 0)
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγ hγF hlam hlower hm hσ hε hz
  dsimp only
  let S := mixHY ρ γ m σ z
  let T := fun n => rounded lam n (S n)
  let X := fun n => pin (T n) (pow ρ n)
  have hstate : ∀ n : ℕ, 0 < n → IsDensity (X n) ∧ IsDensity (T n) := by
    intro n hn
    have hS := GourResource.gsl_y13 ρ F hF γ lam m σ z hm hγF hσ hz.1
      hlam hlower n hn
    have hT : IsDensity (T n) :=
      (GourResource.gsl_y19 ⟨S n, hS.1⟩ lam n hlam hn hS.2.1).1
    have hρ : IsDensity (pow ρ n) := (w42_tensor_spectral_dictionary.1 ρ n).2.1
    exact ⟨spectralPinchingChannel_isDensity (T n) hT.1.isSymmetric (pow ρ n) hρ, hT⟩
  intro b δ hδ hb
  apply mass_tendsto_zero
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (GourResource.gsl_y27 ⟨X n, (hstate n hn).1⟩
      ⟨T n, (hstate n hn).2⟩ ((n : ℝ) * (b + δ))).2.2
  · intro η hη
    have hrate := GourResource.gsl_y34.{u} ρ F hF γ lam m σ z ε hγ hγF hlam hlower hm hσ hε hz η hη
    have hcomp : 1 - η ∈ Set.Ico (0 : ℝ) 1 := by
      constructor <;> linarith [hη.1, hη.2]
    have hmass := GourResource.gsl_y29 X T (1 - η) δ b hstate hcomp hδ (hrate.trans hb)
    simpa only [sub_sub_cancel] using hmass

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y43 :
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
  ∀ δ : ℝ, 0 < δ →
  Filter.liminf (fun n : ℕ => testMass.{u} (X n) (T n) ((n : ℝ)*(s+δ))) atTop ≤ 1-ε ∧
  Tendsto (fun n : ℕ => testMass.{u} (X n) (T n) ((n : ℝ)*(b+δ))) atTop (𝓝 0) ∧
  (∀ᶠ n in atTop,
    testMass.{u} (X n) (T n) ((n : ℝ)*(s+δ)) ∈ Set.Icc 0 1 ∧
    testMass.{u} (X n) (T n) ((n : ℝ)*(b+δ)) ∈ Set.Icc 0 1)
:= by
  intro A _ _ ρ F hF γ lam m σ z ε hγpos hγ hlam hfloor hm hσ hε hz
  dsimp only
  intro s b _hs hs _hsb hb δ hδ
  refine ⟨GourResource.gsl_y41.{u} ρ F hF γ lam m σ z ε hγpos hγ hlam hfloor hm hσ hε hz s δ hδ hs,
    GourResource.gsl_y42.{u} ρ F hF γ lam m σ z ε hγpos hγ hlam hfloor hm hσ hε hz b δ hδ hb, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hS := GourResource.gsl_y13.{u} ρ F hF γ lam m σ z
    hm hγ hσ hz.1 hlam hfloor n hn
  have hT := (GourResource.gsl_y19.{u}
    ⟨mixHY ρ γ m σ z n, hS.1⟩ lam n hlam hn hS.2.1).1
  have hpow : IsDensity (pow ρ n) :=
    (w42_tensor_spectral_dictionary.1 ρ n).2.1
  have hX : IsDensity (pin (rounded lam n (mixHY ρ γ m σ z n)) (pow ρ n)) :=
    spectralPinchingChannel_isDensity _ hT.1.isSymmetric _ hpow
  exact ⟨(GourResource.gsl_y27.{u} ⟨_, hX⟩ ⟨_, hT⟩ ((n : ℝ) * (s + δ))).2.2,
    (GourResource.gsl_y27.{u} ⟨_, hX⟩ ⟨_, hT⟩ ((n : ℝ) * (b + δ))).2.2⟩

end GourResource

