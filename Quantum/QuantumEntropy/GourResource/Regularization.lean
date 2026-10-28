/-
Fekete normalized sequence.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Theorem 4.
-/
/-
Existence of the resource regularization.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.ResourceSubadditivity

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c22 :
(∀ a : ℕ → ℝ, a 0 = 0 → (∀ n, 0 ≤ a n) →
  (∀ n m, a (n+m) ≤ a n + a m) →
  Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 (⨅ n : PNat, a n / (n : ℝ))))
:= by
  intro a _ hnon hsub
  have hs : Subadditive a := hsub
  have hb : BddBelow (Set.range (fun n : ℕ => a n / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (hnon n) (Nat.cast_nonneg n)
  have he : (fun n : ℕ => a n / (n : ℝ)) '' Set.Ici 1 =
      Set.range (fun n : PNat => a n / (n : ℝ)) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
  simpa only [Subadditive.lim, he, sInf_range] using hs.tendsto_lim hb

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c23 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  Tendsto (uRate.{u} ρ F) atTop (𝓝 (reg.{u} ρ F)) ∧ ∃ r : ℝ, reg.{u} ρ F = (r : EReal))
:= by
  classical
  intro A _ _ ρ F hvalid
  obtain ⟨hfinite, hsub⟩ := GourResource.gsl_c21.{u} ρ F hvalid
  let a : ℕ → ℝ := fun n => if hn : 0 < n then (hfinite n hn).choose else 0
  have ha0 : a 0 = 0 := by simp [a]
  have hapos (n : ℕ) (hn : 0 < n) :
      0 ≤ a n ∧ res du (pow ρ n) (F n) = (a n : EReal) := by
    simpa only [a, dif_pos hn] using (hfinite n hn).choose_spec
  have hnonneg (n : ℕ) : 0 ≤ a n := by
    rcases n.eq_zero_or_pos with hn | hn
    · simp [hn, ha0]
    · exact (hapos n hn).1
  have hsuba (n m : ℕ) : a (n+m) ≤ a n + a m := by
    rcases n.eq_zero_or_pos with hn | hn
    · simp [hn, ha0]
    rcases m.eq_zero_or_pos with hm | hm
    · simp [hm, ha0]
    have h := hsub n m hn hm
    rw [(hapos (n+m) (Nat.add_pos_left hn m)).2,
      (hapos n hn).2, (hapos m hm).2, ← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.mp h
  have hrate (n : ℕ) : uRate ρ F n = ((a n / (n : ℝ) : ℝ) : EReal) := by
    rcases n.eq_zero_or_pos with hn | hn
    · simp [hn, uRate, rate]
    · rw [uRate, rate, if_neg (Nat.ne_of_gt hn), (hapos n hn).2,
        ← EReal.coe_mul]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
  have hbdd : BddBelow (Set.range (fun n : PNat => a n / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (hnonneg n) (by positivity)
  have hreg : reg ρ F = ((⨅ n : PNat, a n / (n : ℝ) : ℝ) : EReal) := by
    unfold reg
    simp_rw [hrate]
    exact (Monotone.map_ciInf_of_continuousAt
      continuous_coe_real_ereal.continuousAt EReal.coe_strictMono.monotone hbdd).symm
  refine ⟨?_, ⟨_, hreg⟩⟩
  rw [hreg]
  simpa only [Function.comp_def, ← hrate] using
    (continuous_coe_real_ereal.continuousAt.tendsto.comp (GourResource.gsl_c22 a ha0 hnonneg hsuba))

end GourResource

