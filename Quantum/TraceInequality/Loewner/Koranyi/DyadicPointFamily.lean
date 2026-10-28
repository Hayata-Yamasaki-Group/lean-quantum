import Mathlib.Data.Finset.Sort
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData
import Quantum.Analysis.Real.DyadicGrid
import Quantum.TraceInequality.Loewner.Koranyi.DyadicCover
import Quantum.TraceInequality.Loewner.Koranyi.DyadicInsideMass

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

/--
Dyadic points on `[-1,1]` for the Korányi construction.

This adapter exposes dyadic grid terminology using the dyadic cover utilities.
-/
def dyadicGridIndices (m : ℕ) : Finset ℤ :=
  Quantum.TraceInequality.Loewner.dyadicCenters m

/-- The `k`-th dyadic point with denominator `2^m`. -/
def dyadicGridPoint (m : ℕ) (k : ℤ) : ℝ :=
  Quantum.TraceInequality.Loewner.dyadicCenter m k

/-- Dyadic radius `2^{-m}` used for the covering argument on `[-1,1]`. -/
def dyadicGridRadius (m : ℕ) : ℝ :=
  Quantum.TraceInequality.Loewner.dyadicRadius m

/-- The dyadic grid radius is positive. -/
lemma dyadicGridRadius_pos (m : ℕ) : 0 < dyadicGridRadius m := by
  simpa [dyadicGridRadius] using Quantum.TraceInequality.Loewner.dyadicRadius_pos m

/-- The dyadic index set contains the center index `0`. -/
lemma dyadicGridIndices_contains_zero (m : ℕ) : (0 : ℤ) ∈ dyadicGridIndices m := by
  simp [dyadicGridIndices, Quantum.TraceInequality.Loewner.dyadicCenters]

/-- At a fixed scale, distinct dyadic indices give distinct dyadic points. -/
lemma dyadicGridPoint_injective (m : ℕ) : Function.Injective (dyadicGridPoint m) := by
  intro k l hkl
  have hpow_pos : 0 < (2 : ℝ) ^ m := by
    exact pow_pos (by norm_num) m
  have hpow_ne : ((2 : ℝ) ^ m) ≠ 0 := ne_of_gt hpow_pos
  have hmul := congrArg (fun x : ℝ => x * ((2 : ℝ) ^ m)) hkl
  have hk : (k : ℝ) = l := by
    simpa [dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter, div_eq_mul_inv,
      mul_assoc, hpow_ne] using hmul
  exact_mod_cast hk

/-- A dyadic point is zero exactly when its integer index is zero. -/
lemma dyadicGridPoint_eq_zero_iff_k_eq_zero (m : ℕ) (k : ℤ)
    (_hk : k ∈ dyadicGridIndices m) : dyadicGridPoint m k = 0 ↔ k = 0 := by
  constructor
  · intro hzero
    exact (dyadicGridPoint_injective m) (by
      simpa [dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter] using hzero)
  · intro hk0
    simp [hk0, dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter]

/-- The nonzero dyadic centers that lie strictly inside `(-1,1)`. -/
def nonzeroInteriorDyadicIndices (m : ℕ) : Finset ℤ :=
  (dyadicGridIndices m).filter fun k => -(2 : ℤ) ^ m < k ∧ k < (2 : ℤ) ^ m ∧ k ≠ 0

/-- Membership criterion for the nonzero interior dyadic center indices. -/
lemma mem_nonzeroInteriorDyadicIndices_iff (m : ℕ) (k : ℤ) :
    k ∈ nonzeroInteriorDyadicIndices m ↔
      k ∈ dyadicGridIndices m ∧ -(2 : ℤ) ^ m < k ∧ k < (2 : ℤ) ^ m ∧ k ≠ 0 := by
  simp [nonzeroInteriorDyadicIndices]

/-- The interior nonzero dyadic index set is a subset of the full dyadic grid. -/
lemma nonzeroInteriorDyadicIndices_subset_dyadicGridIndices (m : ℕ) :
    nonzeroInteriorDyadicIndices m ⊆ dyadicGridIndices m := by
  intro k hk
  exact (mem_nonzeroInteriorDyadicIndices_iff m k).1 hk |>.1

/-- Every nonzero interior dyadic index represents a point of the interval `(-1,1)`. -/
lemma nonzeroInteriorDyadicIndices_subset_Ioo (m : ℕ) (k : ℤ)
    (hk : k ∈ nonzeroInteriorDyadicIndices m) : dyadicGridPoint m k ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases (mem_nonzeroInteriorDyadicIndices_iff m k).1 hk with ⟨_, hk_lower, hk_upper, _⟩
  have hpow_pos : 0 < (2 : ℝ) ^ m := by
    exact pow_pos (by norm_num) m
  have hk_lower_real : -((2 : ℝ) ^ m) < (k : ℝ) := by
    exact_mod_cast hk_lower
  have hk_upper_real : (k : ℝ) < (2 : ℝ) ^ m := by
    exact_mod_cast hk_upper
  constructor
  · change -1 < (k : ℝ) / ((2 : ℝ) ^ m)
    exact (lt_div_iff₀ hpow_pos).2 (by simpa using hk_lower_real)
  · change (k : ℝ) / ((2 : ℝ) ^ m) < 1
    exact (div_lt_iff₀ hpow_pos).2 (by simpa using hk_upper_real)

/-- A dyadic point indexed by the nonzero interior grid is nonzero. -/
lemma dyadicGridPoint_ne_zero_of_mem_nonzeroInteriorDyadicIndices (m : ℕ) (k : ℤ)
    (hk : k ∈ nonzeroInteriorDyadicIndices m) : dyadicGridPoint m k ≠ 0 := by
  have hk_mem : k ∈ dyadicGridIndices m :=
    nonzeroInteriorDyadicIndices_subset_dyadicGridIndices m hk
  have hk_ne : k ≠ 0 := (mem_nonzeroInteriorDyadicIndices_iff m k).1 hk |>.2.2.2
  intro hzero
  exact hk_ne ((dyadicGridPoint_eq_zero_iff_k_eq_zero m k hk_mem).1 hzero)

/-- The number of nonzero interior dyadic grid points at scale `m`. -/
def nonzeroInteriorDyadicPointCount (m : ℕ) : ℕ :=
  (nonzeroInteriorDyadicIndices m).card

/-- At scale zero there are no nonzero interior dyadic grid points. -/
lemma nonzeroInteriorDyadicPointCount_zero : nonzeroInteriorDyadicPointCount 0 = 0 := by
  have hopen : nonzeroInteriorDyadicIndices 0 = ∅ := by
    ext k
    simp [nonzeroInteriorDyadicIndices, dyadicGridIndices,
      Quantum.TraceInequality.Loewner.dyadicCenters]
    omega
  simp [nonzeroInteriorDyadicPointCount, hopen]

/-- Passing from scale `m` to `m + 1` preserves every nonzero interior dyadic index. -/
lemma nonzeroInteriorDyadicIndices_subset_succ (m : ℕ) :
    nonzeroInteriorDyadicIndices m ⊆ nonzeroInteriorDyadicIndices (m + 1) := by
  intro k hk
  rcases (mem_nonzeroInteriorDyadicIndices_iff m k).1 hk with ⟨_, hk_lower, hk_upper, hk_ne⟩
  have hpow_pos : 0 < (2 : ℤ) ^ m := by positivity
  have hpow_lt : (2 : ℤ) ^ m < (2 : ℤ) ^ (m + 1) := by
    rw [pow_succ]
    nlinarith
  have hpow_lt_succ : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 2) := by
    have hpow_pos' : 0 < (2 : ℤ) ^ (m + 1) := by positivity
    have hlt :
        (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
      nlinarith
    rw [show (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) by
      rw [pow_succ]
      ring]
    exact hlt
  have hk_mem_succ : k ∈ dyadicGridIndices (m + 1) := by
    change k ∈
      Finset.Icc (-((2 : ℤ) ^ ((m + 1) + 1))) ((2 : ℤ) ^ ((m + 1) + 1))
    rw [Finset.mem_Icc]
    constructor
    · have hneg_lt_succ : -((2 : ℤ) ^ (m + 2)) < -((2 : ℤ) ^ (m + 1)) := by
        simpa [Nat.add_assoc] using neg_lt_neg hpow_lt_succ
      have hneg_lt : -((2 : ℤ) ^ (m + 1)) < -((2 : ℤ) ^ m) := by
        simpa using neg_lt_neg hpow_lt
      exact (lt_trans hneg_lt_succ (lt_trans hneg_lt hk_lower)).le
    · have hpow_le_two : (2 : ℤ) ^ m ≤ (2 : ℤ) ^ (m + 2) := by
        simpa [Nat.add_assoc] using (lt_trans hpow_lt hpow_lt_succ).le
      exact (lt_of_lt_of_le hk_upper hpow_le_two).le
  have hk_lower_succ : -((2 : ℤ) ^ (m + 1)) < k := by
    calc
      -((2 : ℤ) ^ (m + 1)) < -((2 : ℤ) ^ m) := by
        simpa using neg_lt_neg hpow_lt
      _ < k := hk_lower
  have hk_upper_succ : k < (2 : ℤ) ^ (m + 1) := by
    exact lt_trans hk_upper hpow_lt
  exact (mem_nonzeroInteriorDyadicIndices_iff (m + 1) k).2
    ⟨hk_mem_succ, hk_lower_succ, hk_upper_succ, hk_ne⟩

/-- The nonzero interior dyadic index set strictly grows when the scale is refined. -/
lemma nonzeroInteriorDyadicIndices_ssubset_succ (m : ℕ) :
    nonzeroInteriorDyadicIndices m ⊂ nonzeroInteriorDyadicIndices (m + 1) := by
  refine (Finset.ssubset_iff_of_subset (nonzeroInteriorDyadicIndices_subset_succ m)).2 ?_
  have hmem : ((2 : ℤ) ^ m) ∈ nonzeroInteriorDyadicIndices (m + 1) := by
    have hk_mem : (2 : ℤ) ^ m ∈ dyadicGridIndices (m + 1) := by
      change (2 : ℤ) ^ m ∈
        Finset.Icc (-((2 : ℤ) ^ ((m + 1) + 1))) ((2 : ℤ) ^ ((m + 1) + 1))
      rw [Finset.mem_Icc]
      have hpow_nonneg : 0 ≤ (2 : ℤ) ^ m := by positivity
      constructor
      · calc
          -((2 : ℤ) ^ (m + 2)) ≤ 0 := by
            exact neg_nonpos.mpr (by positivity)
          _ ≤ (2 : ℤ) ^ m := hpow_nonneg
      · have hpow_pos : 0 < (2 : ℤ) ^ m := by positivity
        have hlt : (2 : ℤ) ^ m < (2 : ℤ) ^ (m + 1) := by
          rw [pow_succ]
          nlinarith
        have hpow_pos' : 0 < (2 : ℤ) ^ (m + 1) := by positivity
        have hlt_succ : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 2) := by
          have hlt' :
              (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
            nlinarith
          rw [show (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) by
            rw [pow_succ]
            ring]
          exact hlt'
        exact (lt_trans hlt hlt_succ).le
    have hk_lower : -((2 : ℤ) ^ (m + 1)) < (2 : ℤ) ^ m := by
      have hpow_pos : 0 < (2 : ℤ) ^ m := by positivity
      have hpow_pos_succ : 0 < (2 : ℤ) ^ (m + 1) := by positivity
      calc
        -((2 : ℤ) ^ (m + 1)) < 0 := by
          linarith
        _ < (2 : ℤ) ^ m := hpow_pos
    have hk_upper : (2 : ℤ) ^ m < (2 : ℤ) ^ (m + 1) := by
      have hpow_pos : 0 < (2 : ℤ) ^ m := by positivity
      rw [pow_succ]
      nlinarith
    exact (mem_nonzeroInteriorDyadicIndices_iff (m + 1) ((2 : ℤ) ^ m)).2
      ⟨hk_mem, hk_lower, hk_upper, by positivity⟩
  refine ⟨(2 : ℤ) ^ m, hmem, ?_⟩
  intro hk
  rcases (mem_nonzeroInteriorDyadicIndices_iff m ((2 : ℤ) ^ m)).1 hk with ⟨_, _, hk_upper, _⟩
  exact lt_irrefl _ hk_upper

/-- The count of nonzero interior dyadic grid points is strictly increasing in the scale. -/
lemma nonzeroInteriorDyadicPointCount_strictMono : StrictMono nonzeroInteriorDyadicPointCount := by
  refine strictMono_nat_of_lt_succ ?_
  intro m
  exact Finset.card_lt_card (nonzeroInteriorDyadicIndices_ssubset_succ m)

/-- The ordered dyadic point family with `0` inserted as its first point. -/
noncomputable def zeroAnchoredDyadicPointFamily (m : ℕ) :
    Fin (nonzeroInteriorDyadicPointCount m + 1) → ℝ :=
  Fin.cases 0 fun i => dyadicGridPoint m ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl i)

/-- The first point of the ordered dyadic family is the distinguished base point `0`. -/
@[simp] lemma zeroAnchoredDyadicPointFamily_zero (m : ℕ) :
    zeroAnchoredDyadicPointFamily m 0 = 0 := rfl

/-- Successor indices of the ordered dyadic family enumerate the nonzero interior grid. -/
@[simp] lemma zeroAnchoredDyadicPointFamily_succ (m : ℕ)
    (i : Fin (nonzeroInteriorDyadicPointCount m)) :
    zeroAnchoredDyadicPointFamily m i.succ =
      dyadicGridPoint m ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl i) := rfl

/-- Every point in the ordered dyadic family lies in `(-1,1)`. -/
lemma zeroAnchoredDyadicPointFamily_mem_Ioo (m : ℕ)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    zeroAnchoredDyadicPointFamily m i ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine Fin.cases ?_ ?_ i
  · constructor <;> norm_num
  · intro j
    simpa [zeroAnchoredDyadicPointFamily_succ] using
      nonzeroInteriorDyadicIndices_subset_Ioo m
        ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j)
        ((nonzeroInteriorDyadicIndices m).orderEmbOfFin_mem rfl j)

/-- Only the distinguished first point of the ordered dyadic family is zero. -/
lemma zeroAnchoredDyadicPointFamily_ne_zero_of_ne_zero (m : ℕ)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1))
    (hi : i ≠ 0) : zeroAnchoredDyadicPointFamily m i ≠ 0 := by
  cases i using Fin.cases with
  | zero => exact (hi rfl).elim
  | succ j =>
      intro hzero
      have hk_mem :
          ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j) ∈ dyadicGridIndices m := by
        exact nonzeroInteriorDyadicIndices_subset_dyadicGridIndices m
          ((nonzeroInteriorDyadicIndices m).orderEmbOfFin_mem rfl j)
      have hk_eq_zero :
          ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j) = 0 := by
        exact (dyadicGridPoint_eq_zero_iff_k_eq_zero m _ hk_mem).1
          (by simpa [zeroAnchoredDyadicPointFamily_succ] using hzero)
      have hk_ne_zero :
          ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j) ≠ 0 := by
        exact ((mem_nonzeroInteriorDyadicIndices_iff m _).1
          ((nonzeroInteriorDyadicIndices m).orderEmbOfFin_mem rfl j)).2.2.2
      exact hk_ne_zero hk_eq_zero

/-- The ordered dyadic point family is injective. -/
lemma zeroAnchoredDyadicPointFamily_injective (m : ℕ) :
    Function.Injective (zeroAnchoredDyadicPointFamily m) := by
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · simp [hj]
    · exfalso
      exact zeroAnchoredDyadicPointFamily_ne_zero_of_ne_zero m j hj (by
        simpa [zeroAnchoredDyadicPointFamily_zero] using hij.symm)
  · by_cases hj : j = 0
    · exfalso
      exact zeroAnchoredDyadicPointFamily_ne_zero_of_ne_zero m i hi (by
        simpa [hj, zeroAnchoredDyadicPointFamily_zero] using hij)
    · cases i using Fin.cases with
      | zero => exact (hi rfl).elim
      | succ i' =>
          cases j using Fin.cases with
          | zero => exact (hj rfl).elim
          | succ j' =>
              have hpoints :
                  (nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl i' =
                    (nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j' := by
                apply dyadicGridPoint_injective m
                simpa [zeroAnchoredDyadicPointFamily_succ] using hij
              have : i' = j' :=
                ((nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl).injective hpoints
              cases this
              rfl

/-- The ordered dyadic family satisfies the finite point hypotheses used in Koranyi. -/
lemma pointsHyp_zeroAnchoredDyadicPointFamily (m : ℕ) :
    Quantum.TraceInequality.pointsHyp (n := nonzeroInteriorDyadicPointCount m)
      (zeroAnchoredDyadicPointFamily m) := by
  refine ⟨zeroAnchoredDyadicPointFamily_zero m, zeroAnchoredDyadicPointFamily_injective m,
    zeroAnchoredDyadicPointFamily_mem_Ioo m, ?_⟩
  intro i hi
  exact zeroAnchoredDyadicPointFamily_ne_zero_of_ne_zero m i hi

/--
Every point in `[-1,1]` admits a dyadic approximation at scale `2^{-m}`.

This follows from the dyadic approximation lemma in `Step34`.
-/
theorem exists_dyadicGridPoint_dist_le (m : ℕ) (y : ℝ) :
    ∃ k : ℤ, |y - dyadicGridPoint m k| ≤ dyadicGridRadius m := by
  rcases Quantum.TraceInequality.Loewner.exists_int_abs_sub_le_div_pow_two m y with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [dyadicGridPoint, dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicCenter,
    Quantum.TraceInequality.Loewner.dyadicRadius, one_div] using hk

/-- The position of a nonzero interior dyadic index in the ordered dyadic family. -/
noncomputable def nonzeroInteriorDyadicPointIndex (m : ℕ) (k : ℤ)
    (hk : k ∈ nonzeroInteriorDyadicIndices m) : Fin (nonzeroInteriorDyadicPointCount m) :=
  ((nonzeroInteriorDyadicIndices m).orderIsoOfFin rfl).symm ⟨k, hk⟩

/-- The ordered family at an open-index successor recovers the corresponding dyadic point. -/
lemma zeroAnchoredDyadicPointFamily_succ_openIndex (m : ℕ) (k : ℤ)
    (hk : k ∈ nonzeroInteriorDyadicIndices m) :
    zeroAnchoredDyadicPointFamily m (nonzeroInteriorDyadicPointIndex m k hk).succ =
      dyadicGridPoint m k := by
  have hidx :
      (nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl
        (nonzeroInteriorDyadicPointIndex m k hk) = k := by
    have happly :
        (nonzeroInteriorDyadicIndices m).orderIsoOfFin rfl
            (nonzeroInteriorDyadicPointIndex m k hk) =
          ⟨k, hk⟩ := by
      simp [nonzeroInteriorDyadicPointIndex]
    exact congrArg Subtype.val happly
  simpa [zeroAnchoredDyadicPointFamily_succ] using congrArg (dyadicGridPoint m) hidx

private lemma dyadicGridPoint_neg_pow (m : ℕ) :
    dyadicGridPoint m (-((2 : ℤ) ^ m)) = (-1 : ℝ) := by
  have hpow_ne : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  simp [dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter, hpow_ne]

private lemma dyadicGridPoint_pos_pow (m : ℕ) :
    dyadicGridPoint m ((2 : ℤ) ^ m) = (1 : ℝ) := by
  have hpow_ne : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  simp [dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter, hpow_ne]

private lemma dyadicGridPoint_neg_pow_add_one (m : ℕ) :
    dyadicGridPoint (m + 1) (-((2 : ℤ) ^ (m + 1)) + 1) =
      (-1 : ℝ) + dyadicGridRadius (m + 1) := by
  have hpow_ne : ((2 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  simp [dyadicGridPoint, dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicCenter,
    Quantum.TraceInequality.Loewner.dyadicRadius, hpow_ne, add_div]

private lemma dyadicGridPoint_pos_pow_sub_one (m : ℕ) :
    dyadicGridPoint (m + 1) ((2 : ℤ) ^ (m + 1) - 1) =
      (1 : ℝ) - dyadicGridRadius (m + 1) := by
  have hpow_ne : ((2 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  simp [dyadicGridPoint, dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicCenter,
    Quantum.TraceInequality.Loewner.dyadicRadius, hpow_ne, sub_eq_add_neg, add_div]
  ring_nf

private lemma neg_pow_add_one_mem_nonzeroInteriorDyadicIndices (m : ℕ) :
    -((2 : ℤ) ^ (m + 1)) + 1 ∈ nonzeroInteriorDyadicIndices (m + 1) := by
  have hpow_pos : 0 < (2 : ℤ) ^ (m + 1) := by positivity
  have hpow_two : (2 : ℤ) ≤ (2 : ℤ) ^ (m + 1) := by
    rw [pow_succ]
    have h : (1 : ℤ) ≤ (2 : ℤ) ^ m := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
    nlinarith
  have hk_mem : -((2 : ℤ) ^ (m + 1)) + 1 ∈ dyadicGridIndices (m + 1) := by
    change -((2 : ℤ) ^ (m + 1)) + 1 ∈
      Finset.Icc (-((2 : ℤ) ^ ((m + 1) + 1))) ((2 : ℤ) ^ ((m + 1) + 1))
    rw [Finset.mem_Icc]
    constructor
    · have hlt : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ ((m + 1) + 1) := by
        calc
          (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
            nlinarith
          _ = (2 : ℤ) ^ ((m + 1) + 1) := by
            rw [pow_succ]
            ring
      have : -((2 : ℤ) ^ ((m + 1) + 1)) < -((2 : ℤ) ^ (m + 1)) := by
        exact neg_lt_neg hlt
      linarith
    · have hle_big : (2 : ℤ) ^ (m + 1) ≤ (2 : ℤ) ^ ((m + 1) + 1) := by
        have hlt : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ ((m + 1) + 1) := by
          calc
            (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
              nlinarith
            _ = (2 : ℤ) ^ ((m + 1) + 1) := by
              rw [pow_succ]
              ring
        exact hlt.le
      linarith
  refine (mem_nonzeroInteriorDyadicIndices_iff (m + 1) (-((2 : ℤ) ^ (m + 1)) + 1)).2 ?_
  constructor
  · exact hk_mem
  constructor
  · linarith
  constructor
  · linarith
  · omega

private lemma pos_pow_sub_one_mem_nonzeroInteriorDyadicIndices (m : ℕ) :
    (2 : ℤ) ^ (m + 1) - 1 ∈ nonzeroInteriorDyadicIndices (m + 1) := by
  have hpow_pos : 0 < (2 : ℤ) ^ (m + 1) := by positivity
  have hpow_two : (2 : ℤ) ≤ (2 : ℤ) ^ (m + 1) := by
    rw [pow_succ]
    have h : (1 : ℤ) ≤ (2 : ℤ) ^ m := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
    nlinarith
  have hk_mem : (2 : ℤ) ^ (m + 1) - 1 ∈ dyadicGridIndices (m + 1) := by
    change (2 : ℤ) ^ (m + 1) - 1 ∈
      Finset.Icc (-((2 : ℤ) ^ ((m + 1) + 1))) ((2 : ℤ) ^ ((m + 1) + 1))
    rw [Finset.mem_Icc]
    constructor
    · have hnonneg : 0 ≤ (2 : ℤ) ^ (m + 1) - 1 := by omega
      have hneg : -((2 : ℤ) ^ ((m + 1) + 1)) ≤ 0 := by
        exact neg_nonpos.mpr (by positivity)
      linarith
    · have hlt : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ ((m + 1) + 1) := by
        calc
          (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
            nlinarith
          _ = (2 : ℤ) ^ ((m + 1) + 1) := by
            rw [pow_succ]
            ring
      linarith
  refine (mem_nonzeroInteriorDyadicIndices_iff (m + 1) ((2 : ℤ) ^ (m + 1) - 1)).2 ?_
  constructor
  · exact hk_mem
  constructor
  · have hnonneg : 0 ≤ (2 : ℤ) ^ (m + 1) - 1 := by omega
    have hneg : -((2 : ℤ) ^ (m + 1)) < 0 := by linarith
    linarith
  constructor
  · linarith
  · omega

/-- Every point of `[-1,1]` is within one dyadic radius of the ordered dyadic family. -/
theorem exists_zeroAnchoredDyadicPointFamily_dist_le (m : ℕ) (y : ℝ)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
      dist y (zeroAnchoredDyadicPointFamily m i) ≤ dyadicGridRadius m := by
  rcases m with _ | m
  · refine ⟨0, ?_⟩
    have hy_abs : |y| ≤ 1 := by
      simpa [abs_le] using hy
    simpa [dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicRadius, Real.dist_eq,
      zeroAnchoredDyadicPointFamily_zero] using hy_abs
  · let d : ℝ := (2 : ℝ) ^ (m + 1)
    let k : ℤ := Int.floor (y * d)
    have hdpos : 0 < d := by
      have htwo : (0 : ℝ) < 2 := by norm_num
      exact pow_pos htwo (m + 1)
    have hdne : d ≠ 0 := ne_of_gt hdpos
    have hk0 : (k : ℝ) ≤ y * d := by
      exact Int.floor_le (y * d)
    have hk1 : y * d < (k : ℝ) + 1 := by
      exact Int.lt_floor_add_one (y * d)
    have hk_div_le : dyadicGridPoint (m + 1) k ≤ y := by
      have := mul_le_mul_of_nonneg_right hk0 (le_of_lt (inv_pos.2 hdpos))
      simpa [dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter, d, div_eq_mul_inv,
        mul_assoc, hdne] using this
    have hy_lt_next : y < ((k : ℝ) + 1) / d := by
      have := mul_lt_mul_of_pos_right hk1 (inv_pos.2 hdpos)
      simpa [div_eq_mul_inv, mul_assoc, hdne] using this
    have hkdist : dist y (dyadicGridPoint (m + 1) k) ≤ dyadicGridRadius (m + 1) := by
      have hdiff0 : 0 ≤ y - dyadicGridPoint (m + 1) k := sub_nonneg.mpr hk_div_le
      have hdiff_lt : y - dyadicGridPoint (m + 1) k < dyadicGridRadius (m + 1) := by
        have hsub :
            y - dyadicGridPoint (m + 1) k <
              ((k : ℝ) + 1) / d - dyadicGridPoint (m + 1) k :=
          sub_lt_sub_right hy_lt_next (dyadicGridPoint (m + 1) k)
        have hright :
            ((k : ℝ) + 1) / d - dyadicGridPoint (m + 1) k =
              dyadicGridRadius (m + 1) := by
          simp [dyadicGridPoint, dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicCenter,
            Quantum.TraceInequality.Loewner.dyadicRadius, d]
          field_simp [hdne]
          ring
        simpa [hright] using hsub
      have hdiff_le : y - dyadicGridPoint (m + 1) k ≤ dyadicGridRadius (m + 1) :=
        le_of_lt hdiff_lt
      simpa [Real.dist_eq, abs_of_nonneg hdiff0] using hdiff_le
    have hk_le_pow : k ≤ (2 : ℤ) ^ (m + 1) := by
      have hk_real : (k : ℝ) ≤ ((2 : ℤ) ^ (m + 1) : ℝ) := by
        have hy_mul_le : y * d ≤ 1 * d := mul_le_mul_of_nonneg_right hy.2 hdpos.le
        calc
          (k : ℝ) ≤ y * d := hk0
          _ ≤ 1 * d := hy_mul_le
          _ = ((2 : ℤ) ^ (m + 1) : ℝ) := by simp [d]
      exact_mod_cast hk_real
    have hk_ge_neg_pow : -((2 : ℤ) ^ (m + 1)) ≤ k := by
      by_contra hnot
      have hk1_int : k + 1 ≤ -((2 : ℤ) ^ (m + 1)) := by omega
      have hk1_real : (k : ℝ) + 1 ≤ -d := by
        have : ((k + 1 : ℤ) : ℝ) ≤ ((-((2 : ℤ) ^ (m + 1)) : ℤ) : ℝ) := by
          exact_mod_cast hk1_int
        simpa [d] using this
      have hy_mul_ge : -d ≤ y * d := by
        have := mul_le_mul_of_nonneg_right hy.1 hdpos.le
        simpa using this
      linarith
    by_cases hk_zero : k = 0
    · refine ⟨0, ?_⟩
      simpa [hk_zero, dyadicGridPoint, Quantum.TraceInequality.Loewner.dyadicCenter] using hkdist
    by_cases hk_left : k = -((2 : ℤ) ^ (m + 1))
    · let k' : ℤ := -((2 : ℤ) ^ (m + 1)) + 1
      have hk'_mem : k' ∈ nonzeroInteriorDyadicIndices (m + 1) := by
        simpa [k'] using neg_pow_add_one_mem_nonzeroInteriorDyadicIndices m
      refine ⟨(nonzeroInteriorDyadicPointIndex (m + 1) k' hk'_mem).succ, ?_⟩
      have htarget :
          zeroAnchoredDyadicPointFamily (m + 1)
              (nonzeroInteriorDyadicPointIndex (m + 1) k' hk'_mem).succ =
            (-1 : ℝ) + dyadicGridRadius (m + 1) := by
        simpa [k', dyadicGridPoint_neg_pow_add_one m] using
          zeroAnchoredDyadicPointFamily_succ_openIndex (m + 1) k' hk'_mem
      have hy_le : y ≤ (-1 : ℝ) + dyadicGridRadius (m + 1) := by
        have hy_le_next : y ≤ ((k : ℝ) + 1) / d := le_of_lt hy_lt_next
        have hconv : ((k : ℝ) + 1) / d = (-1 : ℝ) + dyadicGridRadius (m + 1) := by
          simp [hk_left, dyadicGridRadius, Quantum.TraceInequality.Loewner.dyadicRadius, d]
          field_simp [hdne]
        simpa [hconv] using hy_le_next
      have hdist_target :
          dist y ((-1 : ℝ) + dyadicGridRadius (m + 1)) ≤ dyadicGridRadius (m + 1) := by
        rw [Real.dist_eq]
        have habs : |y - ((-1 : ℝ) + dyadicGridRadius (m + 1))| =
            ((-1 : ℝ) + dyadicGridRadius (m + 1)) - y := by
          rw [abs_of_nonpos (sub_nonpos.mpr hy_le)]
          ring
        rw [habs]
        linarith [hy.1]
      simpa [htarget] using hdist_target
    by_cases hk_right : k = (2 : ℤ) ^ (m + 1)
    · let k' : ℤ := (2 : ℤ) ^ (m + 1) - 1
      have hk'_mem : k' ∈ nonzeroInteriorDyadicIndices (m + 1) := by
        simpa [k'] using pos_pow_sub_one_mem_nonzeroInteriorDyadicIndices m
      refine ⟨(nonzeroInteriorDyadicPointIndex (m + 1) k' hk'_mem).succ, ?_⟩
      have htarget :
          zeroAnchoredDyadicPointFamily (m + 1)
              (nonzeroInteriorDyadicPointIndex (m + 1) k' hk'_mem).succ =
            (1 : ℝ) - dyadicGridRadius (m + 1) := by
        simpa [k', dyadicGridPoint_pos_pow_sub_one m] using
          zeroAnchoredDyadicPointFamily_succ_openIndex (m + 1) k' hk'_mem
      have hy_eq_one : y = 1 := by
        have hle : (1 : ℝ) ≤ y := by
          simpa [hk_right, dyadicGridPoint_pos_pow (m + 1)] using hk_div_le
        exact le_antisymm hy.2 hle
      have hdist_target :
          dist y ((1 : ℝ) - dyadicGridRadius (m + 1)) ≤ dyadicGridRadius (m + 1) := by
        rw [hy_eq_one, Real.dist_eq]
        have hr_nonneg : 0 ≤ dyadicGridRadius (m + 1) := le_of_lt (dyadicGridRadius_pos (m + 1))
        have habs : |(1 : ℝ) - (1 - dyadicGridRadius (m + 1))| =
            dyadicGridRadius (m + 1) := by
          rw [show (1 : ℝ) - (1 - dyadicGridRadius (m + 1)) =
            dyadicGridRadius (m + 1) by ring]
          exact abs_of_nonneg hr_nonneg
        rw [habs]
      simpa [htarget] using hdist_target
    · have hk_lower : -((2 : ℤ) ^ (m + 1)) < k :=
        lt_of_le_of_ne hk_ge_neg_pow (Ne.symm hk_left)
      have hk_upper : k < (2 : ℤ) ^ (m + 1) :=
        lt_of_le_of_ne hk_le_pow hk_right
      have hk_mem_open : k ∈ nonzeroInteriorDyadicIndices (m + 1) := by
        have hpow_pos : 0 < (2 : ℤ) ^ (m + 1) := by positivity
        have hbig : (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ ((m + 1) + 1) := by
          calc
            (2 : ℤ) ^ (m + 1) < (2 : ℤ) ^ (m + 1) + (2 : ℤ) ^ (m + 1) := by
              nlinarith
            _ = (2 : ℤ) ^ ((m + 1) + 1) := by
              rw [pow_succ]
              ring
        have hk_mem : k ∈ dyadicGridIndices (m + 1) := by
          change k ∈
            Finset.Icc (-((2 : ℤ) ^ ((m + 1) + 1))) ((2 : ℤ) ^ ((m + 1) + 1))
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact (mem_nonzeroInteriorDyadicIndices_iff (m + 1) k).2
          ⟨hk_mem, hk_lower, hk_upper, hk_zero⟩
      refine ⟨(nonzeroInteriorDyadicPointIndex (m + 1) k hk_mem_open).succ, ?_⟩
      simpa [zeroAnchoredDyadicPointFamily_succ_openIndex (m + 1) k hk_mem_open] using hkdist

/-- The dyadic point family covers `[-1,1]` by closed balls at the dyadic radius. -/
theorem Icc_subset_iUnion_zeroAnchoredDyadicPointFamily_closedBall (m : ℕ) :
    Set.Icc (-1 : ℝ) 1 ⊆
      ⋃ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m) := by
  intro y hy
  rcases exists_zeroAnchoredDyadicPointFamily_dist_le m y hy with ⟨i, hi⟩
  exact Set.mem_iUnion.2 ⟨i, Metric.mem_closedBall.2 hi⟩

/--
Chapter 20/27 inside-mass estimate in dyadic-grid language.

The proof applies the estimate from `Step43` to the dyadic grid.
-/
theorem measure_Icc_le_of_uniform_sqInvDist_bound_dyadic
    (μ : Measure ℝ) (m : ℕ) (K : ENNReal)
    (hK : ∀ k ∈ dyadicGridIndices m,
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (dyadicGridPoint m k) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (8 * dyadicGridRadius m) * K := by
  simpa [dyadicGridIndices, dyadicGridPoint, dyadicGridRadius] using
    Quantum.TraceInequality.Loewner.measure_Icc_le_of_uniform_sqInvDist_bound
      (μ := μ) (m := m) (K := K) hK

end

end Loewner
end TraceInequality
end Quantum
