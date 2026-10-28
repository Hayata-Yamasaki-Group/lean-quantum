import Quantum.TraceInequality.Loewner.Koranyi.SignedPoints

import Mathlib.Analysis.SpecificLimits.Basic

namespace Quantum.TraceInequality.Loewner

open Set Filter

open scoped Topology

noncomputable section

/-!
Step 87h5 (route B): build an explicit `signedPoints` approximating sequence.

This upgrades the existence statement from `SignedApproximation` to an actual choice of indices
`i : ∀ n, Fin (φ n + 1)` with:
* head allowed to be `0`, but `i n ≠ 0` eventually, and
* `signedPoints (φ n) (i n) → x`.

We use an explicit rate `2 / (φ n + 2)`, which tends to `0` as `φ n → ∞`.
-/

/-- Density of the signed grid points with an explicit rate `2/(φ n + 2)`: for `x ∈ (-1, 1)` with
`x ≠ 0`, for all large `n` some nonzero index yields a signed point within `2/(φ n + 2)` of `x`. -/
lemma eventually_exists_signedPoints_close_rate_along_subseq
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      ∃ i : Fin (φ n + 1), i ≠ 0 ∧ |signedPoints (φ n) i - x| < 2 / ((φ n + 2 : ℕ) : ℝ) := by
  classical
  have hx_abs_lt : |x| < 1 := by
    have hx' : (-1 : ℝ) < x ∧ x < 1 := hx
    simpa [abs_lt] using hx'
  have hx_abs_pos : 0 < |x| := abs_pos.2 hx0
  have hx_one_minus_pos : 0 < 1 - |x| := sub_pos.2 hx_abs_lt
  -- A single large bound `R` forcing:
  -- (i) `2 / |x| < N`, (ii) `2 / (1 - |x|) < N`.
  set R : ℝ := max ((2 : ℝ) / |x|) ((2 : ℝ) / (1 - |x|)) with hR
  rcases exists_nat_gt R with ⟨N0, hN0⟩
  refine (Filter.eventually_atTop.2 ⟨N0, ?_⟩)
  intro n hn
  have hφ_id_le : n ≤ φ n := (StrictMono.id_le (β := ℕ) hφ) n
  have hN0_le_phi : (N0 : ℕ) ≤ φ n := le_trans hn hφ_id_le
  set N : ℕ := φ n + 2
  have hN0_le_N : (N0 : ℕ) ≤ N := le_trans hN0_le_phi (Nat.le_add_right _ _)
  have hR_lt_N : R < (N : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hN0_le_N)
  have hN_pos : 0 < (N : ℝ) := by positivity
  -- Useful consequences of the bound `R < N`.
  have h2_over_abs_lt_N : (2 : ℝ) / |x| < (N : ℝ) := by
    have : (2 : ℝ) / |x| ≤ R := by
      simp [R]
    exact lt_of_le_of_lt this hR_lt_N
  have h2_over_one_minus_lt_N : (2 : ℝ) / (1 - |x|) < (N : ℝ) := by
    have : (2 : ℝ) / (1 - |x|) ≤ R := by
      simp [R]
    exact lt_of_le_of_lt this hR_lt_N
  -- Abbreviate `a := |x|` and `m := floor ((a/2) * N)`.
  set a : ℝ := |x|
  let m : ℕ := ⌊(a / 2) * (N : ℝ)⌋₊
  -- `m` is large enough so that the even numerator `2*m` is nonzero (needed for `i ≠ 0`).
  have hm_pos : 0 < m := by
    have haN_ge_two : (2 : ℝ) ≤ a * (N : ℝ) := by
      have : (2 : ℝ) < a * (N : ℝ) := by
        have := mul_lt_mul_of_pos_left h2_over_abs_lt_N hx_abs_pos
        simpa [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hx_abs_pos.ne'] using this
      exact this.le
    have haN_div_two : (1 : ℝ) ≤ (a / 2) * (N : ℝ) := by
      have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
      have := (div_le_div_of_nonneg_right haN_ge_two (le_of_lt h2pos))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have : 1 ≤ m := (Nat.one_le_floor_iff (x := (a / 2) * (N : ℝ))).2 haN_div_two
    exact Nat.succ_le_iff.1 this
  -- A convenient upper bound: `a * N < N - 2`.
  have haN_lt_N_sub_two : a * (N : ℝ) < (N : ℝ) - 2 := by
    have hmul : (2 : ℝ) < (1 - a) * (N : ℝ) := by
      have := mul_lt_mul_of_pos_left h2_over_one_minus_lt_N hx_one_minus_pos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hx_one_minus_pos.ne'] using this
    have hrewrite : a * (N : ℝ) = (N : ℝ) - (1 - a) * (N : ℝ) := by ring
    have : (N : ℝ) - (1 - a) * (N : ℝ) < (N : ℝ) - 2 := by
      exact sub_lt_sub_left hmul _
    simpa [hrewrite] using this
  -- Build an approximating index depending on the sign of `x`.
  have hm_le : (m : ℝ) ≤ (a / 2) * (N : ℝ) := by
    have hnonneg : 0 ≤ (a / 2) * (N : ℝ) := by
      have : 0 ≤ a / 2 := div_nonneg (le_of_lt hx_abs_pos) (by norm_num)
      exact mul_nonneg this (le_of_lt hN_pos)
    simpa [m] using (Nat.floor_le hnonneg)
  by_cases hxpos : 0 < x
  · -- Positive `x`: use the even numerator `k := 2*m`.
    let k : ℕ := 2 * m
    have hk_pos : 0 < k := Nat.mul_pos (by norm_num) hm_pos
    have hk_le_real : (k : ℝ) ≤ a * (N : ℝ) := by
      have h2 :
          (2 : ℝ) * (m : ℝ) ≤ (2 : ℝ) * ((a / 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hm_le (by norm_num)
      have : (2 : ℝ) * (m : ℝ) ≤ a * (N : ℝ) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (h2.trans_eq (by ring))
      simpa [k, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using this
    have hk_lt : k < φ n + 1 := by
      -- `k = 2*m ≤ a*N < N-2 = φ n`.
      have hk_lt_real : (k : ℝ) < (N : ℝ) - 2 := hk_le_real.trans_lt haN_lt_N_sub_two
      have hk_lt_nat : k < N - 2 := by
        have hNge : (2 : ℕ) ≤ N := by
          -- `N = φ n + 2`.
          exact Nat.le_add_left 2 (φ n)
        have : (k : ℝ) < (N - 2 : ℕ) := by
          simpa [Nat.cast_sub hNge, Nat.cast_ofNat] using hk_lt_real
        exact Nat.cast_lt.1 this
      -- `N - 2 = φ n`.
      have : k < φ n := by simpa [N, Nat.add_sub_cancel] using hk_lt_nat
      exact lt_trans this (Nat.lt_succ_self _)
    let i : Fin (φ n + 1) := ⟨k, hk_lt⟩
    have hi0 : (i : Fin (φ n + 1)) ≠ 0 := by
      intro hi
      have : k = 0 := by simpa [i] using congrArg Fin.val hi
      exact Nat.ne_of_gt hk_pos this
    have hk_even : Even k := by
      refine ⟨m, by simp [k, two_mul]⟩
    have hxgt : 0 < x := hxpos
    have hsigned : signedPoints (φ n) i = (k : ℝ) / (N : ℝ) := by
      -- `(-1)^k = 1` for even `k`.
      have hpow : (-1 : ℝ) ^ k = 1 := by
        simpa using hk_even.neg_one_pow
      simp [signedPoints, i, N, k, hpow]
    have habs_num : |(k : ℝ) / (N : ℝ) - x| < (2 : ℝ) / (N : ℝ) := by
      -- This follows the positive-`x` branch of the signed approximation argument,
      -- stopping at the `2/N` bound.
      have hfloor_lt : (a / 2) * (N : ℝ) < (m : ℝ) + 1 := by
        simpa [m] using Nat.lt_floor_add_one ((a / 2) * (N : ℝ))
      have hle : (k : ℝ) / (N : ℝ) ≤ a := by
        have : (k : ℝ) ≤ a * (N : ℝ) := hk_le_real
        have := (div_le_div_of_nonneg_right this (le_of_lt hN_pos))
        simpa [div_eq_mul_inv, mul_assoc] using this
      have hlt : a < (k : ℝ) / (N : ℝ) + (2 : ℝ) / (N : ℝ) := by
        have : a < ((2 : ℝ) * ((m : ℝ) + 1)) / (N : ℝ) := by
          have := (mul_lt_mul_of_pos_left hfloor_lt (by norm_num : (0 : ℝ) < 2))
          have := (div_lt_div_of_pos_right this hN_pos)
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
        have hrhs :
            ((2 : ℝ) * ((m : ℝ) + 1)) / (N : ℝ) =
              (k : ℝ) / (N : ℝ) + (2 : ℝ) / (N : ℝ) := by
          simp [k, div_eq_mul_inv]
          ring
        simpa [hrhs] using this
      have hdiff : 0 ≤ a - (k : ℝ) / (N : ℝ) := sub_nonneg.2 hle
      have hdiff_lt : a - (k : ℝ) / (N : ℝ) < (2 : ℝ) / (N : ℝ) := by
        have : a - (k : ℝ) / (N : ℝ) <
            (k : ℝ) / (N : ℝ) + (2 : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ) :=
          sub_lt_sub_right hlt _
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have habs_a : |a - (k : ℝ) / (N : ℝ)| < (2 : ℝ) / (N : ℝ) := by
        simpa [abs_of_nonneg hdiff] using hdiff_lt
      have ha : a = x := by simp [a, abs_of_pos hxgt]
      have : |(k : ℝ) / (N : ℝ) - x| = |a - (k : ℝ) / (N : ℝ)| := by
        simp [ha, abs_sub_comm]
      simpa [this] using habs_a
    refine ⟨i, hi0, ?_⟩
    simpa [hsigned] using habs_num
  · -- Negative `x`: use the odd numerator `k := 2*m + 1`.
    have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    let k : ℕ := 2 * m + 1
    have hk_pos : 0 < k := Nat.succ_pos _
    have hk_lt : k < φ n + 1 := by
      -- Same bound as the signed approximation argument:
      -- `k ≤ a*N + 1 < N - 1 = φ n + 1`.
      have hm_le : (m : ℝ) ≤ (a / 2) * (N : ℝ) := by
        have hnonneg : 0 ≤ (a / 2) * (N : ℝ) := by
          have : 0 ≤ a / 2 := div_nonneg (le_of_lt hx_abs_pos) (by norm_num)
          exact mul_nonneg this (le_of_lt hN_pos)
        simpa [m] using (Nat.floor_le hnonneg)
      have hk_le_real : (k : ℝ) ≤ a * (N : ℝ) + 1 := by
        have : (2 : ℝ) * (m : ℝ) ≤ a * (N : ℝ) := by
          calc
            (2 : ℝ) * (m : ℝ) ≤ 2 * ((a / 2) * (N : ℝ)) := by gcongr
            _ = a * (N : ℝ) := by ring
        have : (2 : ℝ) * (m : ℝ) + 1 ≤ a * (N : ℝ) + 1 := by linarith
        simpa [k, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, two_mul, add_assoc, add_left_comm,
          add_comm, mul_assoc, mul_left_comm, mul_comm] using this
      have hk_lt_real : (k : ℝ) < (N : ℝ) - 1 := by
        have : a * (N : ℝ) + 1 < (N : ℝ) - 1 := by
          linarith [haN_lt_N_sub_two]
        exact lt_of_le_of_lt hk_le_real this
      have hNat : (k : ℕ) < N - 1 := by
        have : (k : ℝ) < (N - 1 : ℕ) := by
          have hNge : (1 : ℕ) ≤ N := by
            simp [N]
          simpa [Nat.cast_sub hNge, Nat.cast_one] using hk_lt_real
        exact Nat.cast_lt.1 this
      simpa [N, Nat.add_sub_cancel] using hNat
    let i : Fin (φ n + 1) := ⟨k, hk_lt⟩
    have hi0 : (i : Fin (φ n + 1)) ≠ 0 := by
      intro hi
      have : k = 0 := by simpa [i] using congrArg Fin.val hi
      exact Nat.ne_of_gt hk_pos this
    have hk_odd : Odd k := by
      refine ⟨m, by simp [k, two_mul, add_assoc]⟩
    have hsigned : signedPoints (φ n) i = -((k : ℝ) / (N : ℝ)) := by
      have hpow : (-1 : ℝ) ^ k = -1 := hk_odd.neg_one_pow
      have :
          signedPoints (φ n) i = ((-1 : ℝ) ^ k * (k : ℝ)) / (N : ℝ) := by
        simp [signedPoints, i, N, k]
      simp [this, hpow, div_eq_mul_inv]
    -- Copy the signed approximation `1/N` control and strengthen it to a `2/N` control.
    have hfloor_lt : (a / 2) * (N : ℝ) < (m : ℝ) + 1 := by
      simpa [m] using Nat.lt_floor_add_one ((a / 2) * (N : ℝ))
    have hlow : (k : ℝ) / (N : ℝ) - (1 : ℝ) / (N : ℝ) ≤ a := by
      -- Convert to `k/N ≤ a + 1/N`, then use the `2*m` bound.
      have : (2 : ℝ) * (m : ℝ) ≤ a * (N : ℝ) := by
        calc
          (2 : ℝ) * (m : ℝ) ≤ 2 * ((a / 2) * (N : ℝ)) := by gcongr
          _ = a * (N : ℝ) := by ring
      have hm_div_le : (2 : ℝ) * (m : ℝ) / (N : ℝ) ≤ a := by
        have := (div_le_div_of_nonneg_right this (le_of_lt hN_pos))
        simpa [div_eq_mul_inv, mul_assoc] using this
      have hk_div :
          (k : ℝ) / (N : ℝ) =
            (2 : ℝ) * (m : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
        simp [k, two_mul, div_eq_mul_inv]
        ring
      have hk_le : (k : ℝ) / (N : ℝ) ≤ a + (1 : ℝ) / (N : ℝ) := by
        have := add_le_add_right hm_div_le ((1 : ℝ) / (N : ℝ))
        simpa [hk_div, add_assoc, add_left_comm, add_comm] using this
      exact (sub_le_iff_le_add).2 hk_le
    have hhigh : a ≤ (k : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
      have : a < ((2 : ℝ) * ((m : ℝ) + 1)) / (N : ℝ) := by
        have := (mul_lt_mul_of_pos_left hfloor_lt (by norm_num : (0 : ℝ) < 2))
        have := (div_lt_div_of_pos_right this hN_pos)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hk' :
          ((2 : ℝ) * ((m : ℝ) + 1)) / (N : ℝ) =
            (k : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
        simp [k, two_mul, div_eq_mul_inv]
        ring
      exact (le_of_lt (by simpa [hk'] using this))
    have habs_a : |a - (k : ℝ) / (N : ℝ)| ≤ (1 : ℝ) / (N : ℝ) := by
      refine (abs_sub_le_iff).2 ?_
      refine ⟨?_, ?_⟩
      · simpa [add_assoc, add_left_comm, add_comm] using hhigh
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlow
    have h1_over_N_lt_two_over_N : (1 : ℝ) / (N : ℝ) < (2 : ℝ) / (N : ℝ) := by
      have hNpos : 0 < (N : ℝ) := by positivity
      have : (1 : ℝ) < 2 := by norm_num
      exact div_lt_div_of_pos_right this hNpos
    have habs_a_lt : |a - (k : ℝ) / (N : ℝ)| < (2 : ℝ) / (N : ℝ) :=
      lt_of_le_of_lt habs_a h1_over_N_lt_two_over_N
    have ha : a = -x := by
      have : |x| = -x := abs_of_neg hxneg
      simpa [a] using this
    have habs' : |signedPoints (φ n) i - x| = |a - (k : ℝ) / (N : ℝ)| := by
      calc
        |signedPoints (φ n) i - x| = |-( (k : ℝ) / (N : ℝ)) - x| := by
          simp [hsigned]
        _ = |-( (k : ℝ) / (N : ℝ)) + (-x)| := by
          simp [sub_eq_add_neg]
        _ = |-( (k : ℝ) / (N : ℝ)) + a| := by
          simp [ha]
        _ = |a - (k : ℝ) / (N : ℝ)| := by
          simp [sub_eq_add_neg, add_comm]
    refine ⟨i, hi0, ?_⟩
    simpa [habs'] using habs_a_lt

/-- Choose an explicit sequence of eventually-nonzero indices `i n` so that
`signedPoints (φ n) (i n) → x`. -/
theorem exists_signedPoints_indexSeq_tendsto_along_subseq
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    ∃ i : ∀ n : ℕ, Fin (φ n + 1),
      (∀ᶠ n : ℕ in atTop, i n ≠ 0) ∧
        Tendsto (fun n : ℕ => signedPoints (φ n) (i n)) atTop (𝓝 x) := by
  classical
  have hev :=
    eventually_exists_signedPoints_close_rate_along_subseq (φ := φ) hφ (x := x) hx hx0
  rcases (Filter.eventually_atTop.1 hev) with ⟨N0, hN0⟩
  let i : ∀ n : ℕ, Fin (φ n + 1) :=
    fun n =>
      if h : n < N0 then 0 else Classical.choose (hN0 n (Nat.le_of_not_lt h))
  have hi0 : ∀ᶠ n : ℕ in atTop, i n ≠ 0 := by
    refine Filter.eventually_atTop.2 ⟨N0, ?_⟩
    intro n hn
    have hnot : ¬ n < N0 := not_lt.mpr hn
    -- On the tail, `i n` is chosen from the existence statement.
    simpa [i, hnot] using (Classical.choose_spec (hN0 n hn)).1
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        |signedPoints (φ n) (i n) - x| < 2 / ((φ n + 2 : ℕ) : ℝ) := by
    refine Filter.eventually_atTop.2 ⟨N0, ?_⟩
    intro n hn
    have hnot : ¬ n < N0 := not_lt.mpr hn
    have hi0n : i n ≠ 0 := by
      simpa [i, hnot] using (Classical.choose_spec (hN0 n hn)).1
    have hdist := (Classical.choose_spec (hN0 n hn)).2
    simpa [i, hnot] using hdist
  have htendsto_bound :
      Tendsto (fun n : ℕ => 2 / ((φ n + 2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hφ_atTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hadd : Tendsto (fun n : ℕ => φ n + 2) atTop atTop :=
      (Filter.tendsto_add_atTop_nat 2).comp hφ_atTop
    have hcast : Tendsto (fun n : ℕ => ((φ n + 2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hadd
    -- `2 / t → 0` as `t → ∞`.
    have hinv : Tendsto (fun n : ℕ => ((φ n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_inv_atTop_zero).comp hcast
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  have hdist : Tendsto (fun n : ℕ => dist (signedPoints (φ n) (i n)) x) atTop (𝓝 (0 : ℝ)) := by
    -- Squeeze `dist` by the explicit rate.
    have hle :
        (fun n : ℕ => dist (signedPoints (φ n) (i n)) x) ≤ᶠ[atTop]
          fun n : ℕ => 2 / ((φ n + 2 : ℕ) : ℝ) := by
      filter_upwards [hbound] with n hn
      have : dist (signedPoints (φ n) (i n)) x = |signedPoints (φ n) (i n) - x| := by
        simp [Real.dist_eq, abs_sub_comm]
      -- Convert `<` to `≤`.
      simpa [this] using (le_of_lt hn)
    have hnonneg :
        (fun n : ℕ => (0 : ℝ)) ≤ᶠ[atTop] fun n : ℕ => dist (signedPoints (φ n) (i n)) x :=
      Filter.Eventually.of_forall (fun _n => dist_nonneg)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htendsto_bound hnonneg hle
  refine ⟨i, hi0, ?_⟩
  exact (tendsto_iff_dist_tendsto_zero).2 hdist

end

end Quantum.TraceInequality.Loewner
