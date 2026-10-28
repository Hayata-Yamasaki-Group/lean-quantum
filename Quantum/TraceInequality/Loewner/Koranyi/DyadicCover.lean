import Quantum.Analysis.Real.DyadicGrid

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped BigOperators

/-!
Step 41 (utility): dyadic coverings of `[-1,1]` and a basic `lintegral` estimate.

This file provides two reusable ingredients for the "support elimination" route:

* a finite dyadic covering of `[-1,1]` by closed balls of radius `2^{-m}`, and
* a pointwise-to-integral inequality bounding the measure of such a ball in terms of a
  `lintegral` of the squared inverse distance kernel.

The kernel is expressed in `ENNReal` to avoid the `inv 0 = 0` convention in `ℝ`.
-/

/-- The `ENNReal` inverse-square distance kernel centered at `c`. -/
def sqInvDist (c : ℝ) (y : ℝ) : ENNReal :=
  ((ENNReal.ofReal (abs (y - c)))⁻¹) ^ (2 : ℕ)

/--
The mass of a closed ball is bounded by radius squared times the inverse-square
distance integral.
-/
lemma measure_closedBall_le_mul_lintegral_sqInvDist (μ : Measure ℝ) {c r : ℝ} (hr : 0 < r) :
    μ (Metric.closedBall c r) ≤ (ENNReal.ofReal r) ^ (2 : ℕ) * ∫⁻ y, sqInvDist c y ∂μ := by
  classical
  have hle_pointwise :
      (Metric.closedBall c r).indicator (fun _y : ℝ => (1 : ENNReal)) ≤
        fun y : ℝ => (ENNReal.ofReal r) ^ (2 : ℕ) * sqInvDist c y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall c r
    · have hy' : abs (y - c) ≤ r := by
        have : dist y c ≤ r := Metric.mem_closedBall.1 hy
        simpa [Real.dist_eq, abs_sub_comm] using this
      have hmono : ENNReal.ofReal (abs (y - c)) ≤ ENNReal.ofReal r :=
        ENNReal.ofReal_le_ofReal hy'
      have hinv :
          (ENNReal.ofReal r)⁻¹ ≤ (ENNReal.ofReal (abs (y - c)))⁻¹ :=
        ENNReal.inv_le_inv' hmono
      have hpow :
          ((ENNReal.ofReal r)⁻¹) ^ (2 : ℕ) ≤ ((ENNReal.ofReal (abs (y - c)))⁻¹) ^ (2 : ℕ) :=
        pow_le_pow_left' hinv (2 : ℕ)
      have hr0 : (ENNReal.ofReal r) ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le.mpr hr]
      have hrT : (ENNReal.ofReal r) ≠ (⊤ : ENNReal) := by simp
      have hmul :
          (ENNReal.ofReal r) ^ (2 : ℕ) * ((ENNReal.ofReal r)⁻¹) ^ (2 : ℕ) = (1 : ENNReal) := by
        have h0 : (ENNReal.ofReal r) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hr0
        have hT : (ENNReal.ofReal r) ^ (2 : ℕ) ≠ (⊤ : ENNReal) := by simp
        -- Rewrite `((a^2)⁻¹)` as `(a⁻¹)^2`.
        simpa [ENNReal.inv_pow] using (ENNReal.mul_inv_cancel h0 hT)
      have hle1 :
          (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ (2 : ℕ) * sqInvDist c y := by
        have :
            (ENNReal.ofReal r) ^ (2 : ℕ) * ((ENNReal.ofReal r)⁻¹) ^ (2 : ℕ) ≤
              (ENNReal.ofReal r) ^ (2 : ℕ) * sqInvDist c y := by
          have hnonneg : 0 ≤ (ENNReal.ofReal r) ^ (2 : ℕ) := by simp
          simpa [sqInvDist, mul_assoc] using (mul_le_mul_of_nonneg_left hpow hnonneg)
        simpa [hmul] using this
      simpa [Set.indicator, hy] using hle1
    · simp [Set.indicator, hy]
  have hmeas : MeasurableSet (Metric.closedBall c r) := measurableSet_closedBall
  have hμ :
      μ (Metric.closedBall c r) =
        ∫⁻ y, (Metric.closedBall c r).indicator (fun _y : ℝ => (1 : ENNReal)) y ∂μ := by
    simp [MeasureTheory.lintegral_indicator, hmeas]
  have hmeas_sq : Measurable (sqInvDist c) := by
    have habs : Measurable fun y : ℝ => abs (y - c) :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    have hof : Measurable fun y : ℝ => ENNReal.ofReal (abs (y - c)) :=
      ENNReal.measurable_ofReal.comp habs
    have hinv : Measurable fun y : ℝ => (ENNReal.ofReal (abs (y - c)))⁻¹ :=
      hof.inv
    simpa [sqInvDist] using (hinv.pow_const (2 : ℕ))
  calc
    μ (Metric.closedBall c r)
        = ∫⁻ y, (Metric.closedBall c r).indicator (fun _y : ℝ => (1 : ENNReal)) y ∂μ := hμ
    _ ≤ ∫⁻ y, (ENNReal.ofReal r) ^ (2 : ℕ) * sqInvDist c y ∂μ := lintegral_mono hle_pointwise
    _ = (ENNReal.ofReal r) ^ (2 : ℕ) * ∫⁻ y, sqInvDist c y ∂μ := by
          simpa using (lintegral_const_mul (μ := μ) ((ENNReal.ofReal r) ^ (2 : ℕ)) hmeas_sq)

/-- The finite integer indices for dyadic centers covering `[-1,1]` at scale `2^{-m}`. -/
def dyadicCenters (m : ℕ) : Finset ℤ :=
  let N : ℤ := (2 : ℤ) ^ (m + 1)
  Finset.Icc (-N) N

/-- The real dyadic center `k / 2^m`. -/
def dyadicCenter (m : ℕ) (k : ℤ) : ℝ :=
  (k : ℝ) / ((2 : ℝ) ^ m)

/-- The dyadic covering radius `2^{-m}`. -/
def dyadicRadius (m : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ m)

/-- The dyadic covering radius is positive. -/
lemma dyadicRadius_pos (m : ℕ) : 0 < dyadicRadius m := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpow : 0 < (2 : ℝ) ^ m := pow_pos h2 m
  dsimp [dyadicRadius]
  rw [one_div]
  exact inv_pos.2 hpow

/-- The dyadic closed balls with radius `2^{-m}` cover `[-1,1]`. -/
lemma Icc_subset_biUnion_dyadicClosedBall (m : ℕ) :
    Set.Icc (-1 : ℝ) 1 ⊆
      ⋃ k ∈ (dyadicCenters m : Set ℤ),
        Metric.closedBall (dyadicCenter m k) (dyadicRadius m) := by
  intro y hy
  rcases exists_int_abs_sub_le_div_pow_two m y with ⟨k, hk⟩
  -- Show the chosen center index `k` lies in the finite range `dyadicCenters m`.
  have hdpos : 0 < ((2 : ℝ) ^ m) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact pow_pos h2 m
  have hdne : ((2 : ℝ) ^ m) ≠ 0 := ne_of_gt hdpos
  have hyabs : |y| ≤ 1 := by
    have : - (1 : ℝ) ≤ y ∧ y ≤ 1 := ⟨hy.1, hy.2⟩
    simpa [abs_le] using this
  have habs_div' : |(k : ℝ) / ((2 : ℝ) ^ m)| ≤ 1 + (1 / ((2 : ℝ) ^ m)) := by
    have htri0 :
        |(k : ℝ) / ((2 : ℝ) ^ m)| ≤
          |(k : ℝ) / ((2 : ℝ) ^ m) - y| + |y| := by
      simpa using (abs_sub_le ((k : ℝ) / ((2 : ℝ) ^ m)) y 0)
    have htri :
        |(k : ℝ) / ((2 : ℝ) ^ m)| ≤
          |y - (k : ℝ) / ((2 : ℝ) ^ m)| + |y| := by
      simpa [abs_sub_comm] using htri0
    have hsum :
        |y - (k : ℝ) / ((2 : ℝ) ^ m)| + |y| ≤ (1 / ((2 : ℝ) ^ m)) + 1 := by
      exact add_le_add hk hyabs
    have : |(k : ℝ) / ((2 : ℝ) ^ m)| ≤ (1 / ((2 : ℝ) ^ m)) + 1 :=
      (le_trans htri hsum)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hkabs : |(k : ℝ)| ≤ (2 : ℝ) ^ (m + 1) := by
    have hkMul : ((k : ℝ) / ((2 : ℝ) ^ m)) * ((2 : ℝ) ^ m) = (k : ℝ) := by
      simp [div_eq_mul_inv, hdne]
    have hk' : |(k : ℝ)| = |(k : ℝ) / ((2 : ℝ) ^ m)| * ((2 : ℝ) ^ m) := by
      have habs : |(k : ℝ)| = |((k : ℝ) / ((2 : ℝ) ^ m)) * ((2 : ℝ) ^ m)| := by
        simp [hkMul]
      calc
        |(k : ℝ)| = |((k : ℝ) / ((2 : ℝ) ^ m)) * ((2 : ℝ) ^ m)| := habs
        _ = |(k : ℝ) / ((2 : ℝ) ^ m)| * |((2 : ℝ) ^ m)| := by
          simpa using (abs_mul ((k : ℝ) / ((2 : ℝ) ^ m)) ((2 : ℝ) ^ m))
        _ = |(k : ℝ) / ((2 : ℝ) ^ m)| * ((2 : ℝ) ^ m) := by
          simp [abs_of_pos hdpos]
    have hmul := mul_le_mul_of_nonneg_right habs_div' (le_of_lt hdpos)
    have hmul' :
        |(k : ℝ)| ≤ (1 + (1 / ((2 : ℝ) ^ m))) * ((2 : ℝ) ^ m) := by
      simpa [hk'] using hmul
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hbound :
        (1 + (1 / ((2 : ℝ) ^ m))) * ((2 : ℝ) ^ m) ≤ (2 : ℝ) ^ (m + 1) := by
      calc
        (1 + (1 / ((2 : ℝ) ^ m))) * ((2 : ℝ) ^ m) = (2 : ℝ) ^ m + 1 := by
          field_simp [hdne]
        _ ≤ (2 : ℝ) ^ m + (2 : ℝ) ^ m := by
          gcongr
        _ = (2 : ℝ) ^ (m + 1) := by
          -- `a+a = 2*a = a*2 = 2^(m+1)`.
          simp [pow_succ, two_mul, mul_comm]
    exact hmul'.trans hbound
  have hk_mem : k ∈ dyadicCenters m := by
    have hk_cast : (-((2 : ℝ) ^ (m + 1))) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      simpa [abs_le] using hkabs
    have hk1 : -((2 : ℤ) ^ (m + 1)) ≤ k := by
      exact_mod_cast hk_cast.1
    have hk2 : k ≤ (2 : ℤ) ^ (m + 1) := by
      exact_mod_cast hk_cast.2
    simp [dyadicCenters, Finset.mem_Icc, hk1, hk2]
  -- Membership in the union.
  refine mem_iUnion.2 ?_
  refine ⟨k, mem_iUnion.2 ?_⟩
  have hk_mem' : k ∈ (dyadicCenters m : Set ℤ) := by
    simpa using hk_mem
  refine ⟨hk_mem', ?_⟩
  -- Finally, show `y` lies in the appropriate closed ball.
  have : dist y (dyadicCenter m k) ≤ dyadicRadius m := by
    simpa [dyadicCenter, dyadicRadius, Real.dist_eq, abs_sub_comm] using hk
  exact Metric.mem_closedBall.2 this

/-- The mass of `[-1,1]` is bounded by the sum of the dyadic ball masses. -/
theorem measure_Icc_le_sum_measure_dyadicClosedBall (μ : Measure ℝ) (m : ℕ) :
    μ (Set.Icc (-1 : ℝ) 1) ≤
      (dyadicCenters m).sum (fun k =>
        μ (Metric.closedBall (dyadicCenter m k) (dyadicRadius m))) := by
  have hcov : Set.Icc (-1 : ℝ) 1 ⊆
      ⋃ k ∈ (dyadicCenters m : Set ℤ),
        Metric.closedBall (dyadicCenter m k) (dyadicRadius m) :=
    Icc_subset_biUnion_dyadicClosedBall (m := m)
  have hμmono :
      μ (Set.Icc (-1 : ℝ) 1) ≤
        μ (⋃ k ∈ (dyadicCenters m : Set ℤ),
          Metric.closedBall (dyadicCenter m k) (dyadicRadius m)) :=
    measure_mono hcov
  have hUnion :
      μ (⋃ k ∈ (dyadicCenters m : Set ℤ),
          Metric.closedBall (dyadicCenter m k) (dyadicRadius m)) ≤
        (dyadicCenters m).sum (fun k =>
          μ (Metric.closedBall (dyadicCenter m k) (dyadicRadius m))) := by
    -- Use the general subadditivity of measure over finite unions.
    simpa using
      (measure_biUnion_finset_le (μ := μ) (I := dyadicCenters m)
        (s := fun k : ℤ => Metric.closedBall (dyadicCenter m k) (dyadicRadius m)))
  exact hμmono.trans hUnion

/--
A uniform inverse-square integral bound controls the mass of `[-1,1]` at dyadic
scale `m`.
-/
theorem measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound (μ : Measure ℝ) (m : ℕ)
    (K : ENNReal)
    (hK :
      ∀ k ∈ dyadicCenters m, (∫⁻ y, sqInvDist (dyadicCenter m k) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) ≤
      (dyadicCenters m).card * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := by
  -- First cover `[-1,1]` by dyadic balls.
  have hcover := measure_Icc_le_sum_measure_dyadicClosedBall (μ := μ) (m := m)
  -- Bound each ball measure by the corresponding `lintegral`.
  have hrpos : 0 < dyadicRadius m := dyadicRadius_pos m
  have hball :
      ∀ k ∈ dyadicCenters m,
        μ (Metric.closedBall (dyadicCenter m k) (dyadicRadius m)) ≤
          ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := by
    intro k hk
    have h1 :=
      measure_closedBall_le_mul_lintegral_sqInvDist (μ := μ) (c := dyadicCenter m k)
        (r := dyadicRadius m) hrpos
    exact h1.trans (by gcongr; exact hK k hk)
  -- Sum the bounds.
  have :
      (dyadicCenters m).sum (fun k =>
          μ (Metric.closedBall (dyadicCenter m k) (dyadicRadius m))) ≤
        (dyadicCenters m).sum (fun _k =>
          ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K) := by
    exact Finset.sum_le_sum fun k hk => hball k hk
  -- Evaluate the RHS as `card * c * K`.
  have hsum :
      (dyadicCenters m).sum (fun _k =>
          ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K) =
        (dyadicCenters m).card * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := by
    simp [Finset.sum_const, mul_left_comm, mul_comm]
  calc
    μ (Set.Icc (-1 : ℝ) 1) ≤
        (dyadicCenters m).sum (fun k =>
          μ (Metric.closedBall (dyadicCenter m k) (dyadicRadius m))) := hcover
    _ ≤ (dyadicCenters m).sum (fun _k =>
          ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K) := this
    _ = (dyadicCenters m).card * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := hsum

/-- Cardinality of the dyadic center index set as an integer `toNat` formula. -/
lemma dyadicCenters_card (m : ℕ) :
    (dyadicCenters m).card = (((2 : ℤ) ^ (m + 2)) + 1).toNat := by
  classical
  have hcard :
      (dyadicCenters m).card =
        (((2 : ℤ) ^ (m + 1) + 1 - (-(2 : ℤ) ^ (m + 1))).toNat) := by
    rw [dyadicCenters]
    exact Int.card_Icc (a := (-(2 : ℤ) ^ (m + 1))) (b := ((2 : ℤ) ^ (m + 1)))
  have harith :
      ((2 : ℤ) ^ (m + 1) + 1 - (-(2 : ℤ) ^ (m + 1))) =
        ((2 : ℤ) ^ (m + 2) + 1) := by
    -- `N + 1 - (-N) = 2*N + 1` and `2 * 2^(m+1) = 2^(m+2)`.
    simp [sub_eq_add_neg, add_left_comm, add_comm, pow_succ, mul_comm, two_mul]
  -- Rewrite the RHS via `harith`.
  simpa [harith] using hcard

/-- Convert the positive integer expression `2^n + 1` through `Int.toNat`. -/
lemma two_pow_add_one_toNat (n : ℕ) :
    (((2 : ℤ) ^ n + 1).toNat) = (2 : ℕ) ^ n + 1 := by
  have hcast : ((2 : ℤ) ^ n + 1) = ((2 : ℕ) ^ n + 1 : ℤ) := by
    norm_cast
  calc
    (((2 : ℤ) ^ n + 1).toNat) = (((2 : ℕ) ^ n + 1 : ℤ).toNat) := by
        simp
    _ = (2 : ℕ) ^ n + 1 := Int.toNat_natCast ((2 : ℕ) ^ n + 1)

/-- Cardinality of the dyadic center index set as a natural-number formula. -/
lemma dyadicCenters_card_nat (m : ℕ) :
    (dyadicCenters m).card = (2 : ℕ) ^ (m + 2) + 1 := by
  simpa [two_pow_add_one_toNat] using dyadicCenters_card (m := m)

end

end Quantum.TraceInequality.Loewner
