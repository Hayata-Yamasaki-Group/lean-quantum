import Quantum.TraceInequality.Loewner.Koranyi.DyadicInsideMass

import Mathlib.Analysis.SpecificLimits.Normed

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

noncomputable section

open scoped Topology

/-!
Step 44 (utility): a uniform inverse-square bound forces the inside mass to be zero.

Step 43 shows that, at dyadic scale `m`, the mass of `[-1,1]` is bounded by
`ENNReal.ofReal (8 * dyadicRadius m) * K` under a uniform bound on the inverse-square `lintegral`
at dyadic centers.

If the inverse-square bound holds uniformly for all `m`, then letting `m → ∞` forces the mass of
`[-1,1]` to be zero since `dyadicRadius m = 1 / 2^m → 0`.
-/

/-- The dyadic radius `2^{-m}` tends to zero. -/
lemma tendsto_dyadicRadius_zero : Tendsto dyadicRadius atTop (𝓝 (0 : ℝ)) := by
  -- `dyadicRadius m = (2^m)⁻¹` and `2^m → ∞`.
  have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hinv : Tendsto (fun m : ℕ => ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow
  have hinv' : Tendsto (fun m : ℕ => 1 / ((2 : ℝ) ^ m)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using hinv
  have : Tendsto (fun m : ℕ => dyadicRadius m) atTop (𝓝 (0 : ℝ)) := by
    simpa [dyadicRadius] using hinv'
  simpa using this

/--
A finite uniform inverse-square bound at every dyadic scale forces zero mass on
`[-1,1]`.
-/
theorem measure_Icc_eq_zero_of_uniform_sqInvDist_bound
    (μ : Measure ℝ) (K : ENNReal) (hK : K < ⊤)
    (hKbound :
      ∀ m : ℕ, ∀ k : ℤ, k ∈ dyadicCenters m →
        (∫⁻ y, sqInvDist (dyadicCenter m k) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) = 0 := by
  -- Step 43 gives the scale-dependent bound.
  have hmass :
      ∀ m : ℕ,
        μ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (8 * dyadicRadius m) * K := by
    intro m
    refine measure_Icc_le_of_uniform_sqInvDist_bound (μ := μ) (m := m) (K := K) ?_
    intro k hk
    exact hKbound m k hk
  -- Work in `ℝ` via `toReal`.
  set a : ENNReal := μ (Set.Icc (-1 : ℝ) 1)
  have ha_le (m : ℕ) : a.toReal ≤ (ENNReal.ofReal (8 * dyadicRadius m) * K).toReal := by
    have hb_ne_top : ENNReal.ofReal (8 * dyadicRadius m) * K ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hK)
    have hab : a ≤ ENNReal.ofReal (8 * dyadicRadius m) * K := by
      simpa [a] using hmass m
    have ha_ne_top : a ≠ ⊤ := ne_top_of_le_ne_top hb_ne_top hab
    -- Convert the inequality to `toReal`.
    exact (ENNReal.toReal_le_toReal ha_ne_top hb_ne_top).2 hab
  have hb_toReal (m : ℕ) :
      (ENNReal.ofReal (8 * dyadicRadius m) * K).toReal = (8 * dyadicRadius m) * K.toReal := by
    have hnonneg : 0 ≤ 8 * dyadicRadius m := by
      have : 0 ≤ dyadicRadius m := le_of_lt (dyadicRadius_pos m)
      nlinarith
    simpa using (ENNReal.toReal_ofReal_mul (c := 8 * dyadicRadius m) (a := K) hnonneg)
  -- Show `a.toReal = 0` by contradiction using the bound and `dyadicRadius m → 0`.
  have hdy (m : ℕ) : (ENNReal.ofReal (dyadicRadius m)).toReal = dyadicRadius m := by
    have : 0 ≤ dyadicRadius m := le_of_lt (dyadicRadius_pos m)
    simpa using (ENNReal.toReal_ofReal this)
  have hlim :
      Tendsto
        (fun m : ℕ => (ENNReal.ofReal (8 * dyadicRadius m) * K).toReal)
        atTop (𝓝 (0 : ℝ)) := by
    have hrad : Tendsto (fun m : ℕ => 8 * dyadicRadius m) atTop (𝓝 (0 : ℝ)) := by
      have h0 : Tendsto (fun m : ℕ => (8 : ℝ)) atTop (𝓝 (8 : ℝ)) := tendsto_const_nhds
      simpa [mul_zero] using (h0.mul tendsto_dyadicRadius_zero)
    -- `dyadicRadius m ≥ 0`, so `((ENNReal.ofReal (dyadicRadius m)).toReal) = dyadicRadius m`.
    simpa [hb_toReal, hdy, mul_assoc] using (hrad.mul tendsto_const_nhds)
  have ha_toReal_zero : a.toReal = 0 := by
    by_contra hne
    have ha_pos : 0 < a.toReal := lt_of_le_of_ne (by exact ENNReal.toReal_nonneg) (Ne.symm hne)
    have hhalf_pos : 0 < a.toReal / 2 := by linarith
    have hnhds : Set.Iio (a.toReal / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hhalf_pos
    have hevent :
        ∀ᶠ m : ℕ in atTop,
          (ENNReal.ofReal (8 * dyadicRadius m) * K).toReal < a.toReal / 2 :=
      (tendsto_def.1 hlim _ hnhds)
    rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
    have hlt : (ENNReal.ofReal (8 * dyadicRadius N) * K).toReal < a.toReal / 2 := hN N le_rfl
    have hle : a.toReal ≤ (ENNReal.ofReal (8 * dyadicRadius N) * K).toReal := ha_le N
    have hlt' : (ENNReal.ofReal (8 * dyadicRadius N) * K).toReal < a.toReal := by
      have : a.toReal / 2 < a.toReal := by linarith
      exact lt_trans hlt this
    exact (not_lt_of_ge hle) hlt'
  -- Since `a < ⊤`, `toReal = 0` implies `a = 0`.
  have ha_ne_top : a ≠ ⊤ := by
    have hb_ne_top : ENNReal.ofReal (8 * dyadicRadius 0) * K ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hK)
    have : a ≤ ENNReal.ofReal (8 * dyadicRadius 0) * K := by simpa [a] using hmass 0
    exact ne_of_lt (lt_of_le_of_lt this (lt_top_iff_ne_top.2 hb_ne_top))
  have : a = 0 := by
    -- `ofReal (toReal a) = a` since `a ≠ ⊤`.
    simpa [ha_toReal_zero] using (ENNReal.ofReal_toReal ha_ne_top).symm
  simpa [a] using this

end

end Quantum.TraceInequality.Loewner
