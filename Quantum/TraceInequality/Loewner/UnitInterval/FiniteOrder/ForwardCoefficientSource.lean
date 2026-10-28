import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ConditionalKernelPSD
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Taylor

/-!
# Chapter 20 forward top-coefficient finite-difference source

This file contains the finite-difference moment algebra and top-coefficient
quadratic source used to extract odd derivative nonnegativity from public
Löwner positivity.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution
open scoped fwdDiff

noncomputable section

/-- Right-sided forward nodes `x, x+h, ..., x+k*h`. -/
def forwardCoeffNodes (k : ℕ) (x h : ℝ) : Fin (k + 1) → ℝ :=
  fun i => x + (i.val : ℝ) * h

/--
Top-coefficient forward finite-difference weights.  For `k = 3,4,...` this
specializes to the previously hand-expanded four-, five-, ... point weights.
-/
def forwardTopCoeffWeights (k : ℕ) (h : ℝ) : Fin (k + 1) → ℝ :=
  fun i =>
    ((-1 : ℝ) ^ (k - i.val) * (Nat.choose k i.val : ℝ)) /
      ((Nat.factorial k : ℝ) * h ^ k)

/-- Unnormalized top-coefficient forward weights. -/
def forwardTopCoeffRawWeight (k : ℕ) : Fin (k + 1) → ℝ :=
  fun i => (-1 : ℝ) ^ (k - i.val) * (Nat.choose k i.val : ℝ)

/-- The real Löwner quadratic form in the top-coefficient forward basis. -/
def forwardTopCoeffQuadratic
    (k : ℕ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  let w := forwardTopCoeffWeights k h
  star w ⬝ᵥ
    (Matrix.of (fun i j : Fin (k + 1) =>
      loewnerKernel f (forwardCoeffNodes k x h i)
        (forwardCoeffNodes k x h j))).mulVec w

/--
Unnormalized forward top-coefficient moments vanish below the top degree.

This is the Mathlib `ForwardDiff` identity specialized to the binomial weights
used by `forwardTopCoeffWeights`; it is the reusable replacement for
the deleted hand-expanded C7/C9/... arithmetic.
-/
lemma forwardTopCoeff_moment_eq_zero_of_lt
    {k r : ℕ} (hr : r < k) :
    (∑ i : Fin (k + 1),
      ((-1 : ℝ) ^ (k - i.val) * (Nat.choose k i.val : ℝ)) *
        (i.val : ℝ) ^ r) = 0 := by
  have hfun : (Δ_[(1 : ℝ)]^[k] (fun x : ℝ => x ^ r)) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hr
  have h0 := congrFun hfun 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simpa [Finset.sum_range, nsmul_eq_mul, zsmul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using h0

/--
The top unnormalized forward moment is `k!`.

After division by `(k! * h^k)`, this is the statement that the forward
top-coefficient weights extract the leading `k`th Taylor coefficient with
unit mass.
-/
lemma forwardTopCoeff_moment_top
    (k : ℕ) :
    (∑ i : Fin (k + 1),
      ((-1 : ℝ) ^ (k - i.val) * (Nat.choose k i.val : ℝ)) *
        (i.val : ℝ) ^ k) = (Nat.factorial k : ℝ) := by
  have hfun :
      (Δ_[(1 : ℝ)]^[k] (fun x : ℝ => x ^ k)) =
        fun _ : ℝ => (Nat.factorial k : ℝ) :=
    fwdDiff_iter_eq_factorial (R := ℝ) (n := k)
  have h0 := congrFun hfun 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simpa [Finset.sum_range, nsmul_eq_mul, zsmul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using h0

/--
Raw forward top-coefficient weights have zero moments in degrees below `k`.
-/
lemma forwardTopCoeffRawWeight_moment_eq_zero_of_lt
    {k r : ℕ} (hr : r < k) :
    (∑ i : Fin (k + 1),
      forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ r) = 0 := by
  simpa [forwardTopCoeffRawWeight] using
    forwardTopCoeff_moment_eq_zero_of_lt (k := k) (r := r) hr

/--
Raw forward top-coefficient weights have top moment equal to `k!`.
-/
lemma forwardTopCoeffRawWeight_moment_top
    (k : ℕ) :
    (∑ i : Fin (k + 1),
      forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ k) =
        (Nat.factorial k : ℝ) := by
  simpa [forwardTopCoeffRawWeight] using
    forwardTopCoeff_moment_top k

/--
The product of two raw moment sums vanishes below total degree `2*k`.
-/
lemma forwardTopCoeffRawWeight_momentProduct_eq_zero_of_lt
    {k r : ℕ} (hr : r < 2 * k) :
    (∑ p ∈ Finset.range (r + 1),
      (∑ i : Fin (k + 1),
        forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ p) *
      (∑ j : Fin (k + 1),
        forwardTopCoeffRawWeight k j * (j.val : ℝ) ^ (r - p))) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro p hp
  have hple : p ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  by_cases hpk : p < k
  · rw [forwardTopCoeffRawWeight_moment_eq_zero_of_lt (k := k) hpk]
    simp
  · have hrp : r - p < k := by omega
    rw [forwardTopCoeffRawWeight_moment_eq_zero_of_lt (k := k) hrp]
    simp

/--
At total degree `2*k`, the product of raw moment sums is `(k!)^2`.
-/
lemma forwardTopCoeffRawWeight_momentProduct_top
    (k : ℕ) :
    (∑ p ∈ Finset.range (2 * k + 1),
      (∑ i : Fin (k + 1),
        forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ p) *
      (∑ j : Fin (k + 1),
        forwardTopCoeffRawWeight k j * (j.val : ℝ) ^ (2 * k - p))) =
        (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) := by
  rw [Finset.sum_eq_single k]
  · have hsub : 2 * k - k = k := by omega
    rw [hsub, forwardTopCoeffRawWeight_moment_top]
  · intro p hp hpk
    have hple : p ≤ 2 * k := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
    by_cases hp_lt : p < k
    · rw [forwardTopCoeffRawWeight_moment_eq_zero_of_lt (k := k) hp_lt]
      simp
    · have hk_lt : k < p := by omega
      have hcomp : 2 * k - p < k := by omega
      rw [forwardTopCoeffRawWeight_moment_eq_zero_of_lt (k := k) hcomp]
      simp
  · intro hknot
    exact (hknot (Finset.mem_range.mpr (by omega))).elim

/--
The Löwner kernel of a shifted monomial on forward nodes reduces to the usual
finite geometric sum.
-/
lemma loewnerKernel_shiftPow_forward_nodes_eq
    {k r : ℕ} {x h : ℝ} (hh : h ≠ 0) (i j : Fin (k + 1)) :
    loewnerKernel (fun y : ℝ => (y - x) ^ r)
      (forwardCoeffNodes k x h i)
      (forwardCoeffNodes k x h j) =
    h ^ (r - 1) *
      ∑ p ∈ Finset.range r, (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p) := by
  by_cases hr : r = 0
  · subst r
    simp [loewnerKernel]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    by_cases hij : i = j
    · subst j
      rw [loewnerKernel_self]
      have hderiv :
          deriv (fun y : ℝ => (y - x) ^ r)
              (forwardCoeffNodes k x h i) =
            (r : ℝ) * ((i.val : ℝ) * h) ^ (r - 1) := by
        have hdiff : DifferentiableAt ℝ (fun y : ℝ => y - x)
            (forwardCoeffNodes k x h i) := by fun_prop
        rw [deriv_fun_pow hdiff r]
        simp [forwardCoeffNodes]
      rw [hderiv]
      have hsum :
          (∑ p ∈ Finset.range r,
            (i.val : ℝ) ^ p * (i.val : ℝ) ^ (r.pred - p)) =
            (r : ℝ) * (i.val : ℝ) ^ (r - 1) := by
        have hterm :
            ∀ p ∈ Finset.range r,
              (i.val : ℝ) ^ p * (i.val : ℝ) ^ (r.pred - p) =
                (i.val : ℝ) ^ (r - 1) := by
          intro p hp
          rw [← pow_add]
          congr 1
          have hplt : p < r := Finset.mem_range.mp hp
          have hpred : r.pred = r - 1 := rfl
          omega
        calc
          (∑ p ∈ Finset.range r,
              (i.val : ℝ) ^ p * (i.val : ℝ) ^ (r.pred - p)) =
                ∑ _p ∈ Finset.range r, (i.val : ℝ) ^ (r - 1) := by
                  exact Finset.sum_congr rfl hterm
          _ = (r : ℝ) * (i.val : ℝ) ^ (r - 1) := by simp
      rw [hsum]
      rw [mul_pow]
      ring
    · have hval_ne : (i.val : ℝ) - (j.val : ℝ) ≠ 0 := by
        intro hsub
        apply hij
        apply Fin.ext
        exact Nat.cast_injective (sub_eq_zero.mp hsub)
      have hnodes_ne :
          forwardCoeffNodes k x h i ≠
            forwardCoeffNodes k x h j := by
        intro hnode
        apply hval_ne
        dsimp [forwardCoeffNodes] at hnode
        have hmul : ((i.val : ℝ) - (j.val : ℝ)) * h = 0 := by
          nlinarith
        exact (mul_eq_zero.mp hmul).resolve_right hh
      rw [loewnerKernel_eq_div (f := fun y : ℝ => (y - x) ^ r) hnodes_ne]
      have hgeom := (Commute.all (i.val : ℝ) (j.val : ℝ)).geom_sum₂_mul r
      have hgeom' :
          (∑ p ∈ Finset.range r,
            (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p)) *
              ((i.val : ℝ) - (j.val : ℝ)) =
            (i.val : ℝ) ^ r - (j.val : ℝ) ^ r := by
        simpa [Nat.pred_eq_sub_one] using hgeom
      dsimp [forwardCoeffNodes]
      have hxi : x + (i.val : ℝ) * h - x = (i.val : ℝ) * h := by ring
      have hxj : x + (j.val : ℝ) * h - x = (j.val : ℝ) * h := by ring
      have hden :
          x + (i.val : ℝ) * h - (x + (j.val : ℝ) * h) =
            ((i.val : ℝ) - (j.val : ℝ)) * h := by ring
      rw [hxi, hxj, hden, mul_pow, mul_pow]
      have hnum :
          (i.val : ℝ) ^ r * h ^ r - (j.val : ℝ) ^ r * h ^ r =
            ((∑ p ∈ Finset.range r,
              (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p)) *
                ((i.val : ℝ) - (j.val : ℝ))) * h ^ r := by
        rw [hgeom']
        ring
      field_simp [hh, hval_ne]
      rw [← hgeom']
      simp only [Nat.pred_eq_sub_one]
      have hpow : h ^ r = h * h ^ (r - 1) := by
        have hr' : r = (r - 1) + 1 := by omega
        conv_lhs =>
          rw [hr', pow_succ]
        ring
      rw [hpow]
      ring_nf

/--
The raw weighted sum of the monomial kernel factors into products of forward
moments.
-/
lemma forwardTopCoeffRawWeight_powerKernel_sum_eq (k r : ℕ) :
    (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      forwardTopCoeffRawWeight k i * forwardTopCoeffRawWeight k j *
        (∑ p ∈ Finset.range r,
          (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p))) =
    (∑ p ∈ Finset.range r,
      (∑ i : Fin (k + 1),
        forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ p) *
      (∑ j : Fin (k + 1),
        forwardTopCoeffRawWeight k j * (j.val : ℝ) ^ (r.pred - p))) := by
  calc
    (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      forwardTopCoeffRawWeight k i * forwardTopCoeffRawWeight k j *
        (∑ p ∈ Finset.range r,
          (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p))) =
        ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), ∑ p ∈ Finset.range r,
          forwardTopCoeffRawWeight k i *
            forwardTopCoeffRawWeight k j *
              ((i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p)) := by
      simp [Finset.mul_sum, mul_assoc]
    _ = ∑ i : Fin (k + 1), ∑ p ∈ Finset.range r, ∑ j : Fin (k + 1),
          forwardTopCoeffRawWeight k i *
            forwardTopCoeffRawWeight k j *
              ((i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p)) := by
      congr 1 with i
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.range r, ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          forwardTopCoeffRawWeight k i *
            forwardTopCoeffRawWeight k j *
              ((i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p)) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.range r,
      (∑ i : Fin (k + 1),
        forwardTopCoeffRawWeight k i * (i.val : ℝ) ^ p) *
      (∑ j : Fin (k + 1),
        forwardTopCoeffRawWeight k j * (j.val : ℝ) ^ (r.pred - p)) := by
      congr 1 with p
      rw [Finset.sum_mul]
      congr 1 with i
      rw [Finset.mul_sum]
      congr 1 with j
      ring

/--
The raw weighted power-kernel sum vanishes through total degree `2*k`.
-/
lemma forwardTopCoeffRawWeight_powerKernel_sum_eq_zero_of_le_two_mul
    {k r : ℕ} (hr : r ≤ 2 * k) :
    (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      forwardTopCoeffRawWeight k i * forwardTopCoeffRawWeight k j *
        (∑ p ∈ Finset.range r,
          (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p))) = 0 := by
  rw [forwardTopCoeffRawWeight_powerKernel_sum_eq]
  cases r with
  | zero => simp
  | succ r =>
      have hrlt : r < 2 * k := by omega
      simpa using
        forwardTopCoeffRawWeight_momentProduct_eq_zero_of_lt
          (k := k) (r := r) hrlt

/--
At degree `2*k + 1`, the raw weighted power-kernel sum is `(k!)^2`.
-/
lemma forwardTopCoeffRawWeight_powerKernel_sum_top (k : ℕ) :
    (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      forwardTopCoeffRawWeight k i * forwardTopCoeffRawWeight k j *
        (∑ p ∈ Finset.range (2 * k + 1),
          (i.val : ℝ) ^ p * (j.val : ℝ) ^ ((2 * k + 1).pred - p))) =
      (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) := by
  rw [forwardTopCoeffRawWeight_powerKernel_sum_eq]
  simpa using forwardTopCoeffRawWeight_momentProduct_top k

/-- A real quadratic form with scaled weights `a i * c` and kernel `t * P i j` is
`t * c ^ 2` times the unscaled double sum. -/
private lemma quadratic_form_scaled_weights_eq {n : ℕ} (a : Fin n → ℝ) (c t : ℝ)
    (P : Fin n → Fin n → ℝ) :
    star (fun i => a i * c) ⬝ᵥ
        (Matrix.of (fun i j : Fin n => t * P i j)).mulVec (fun i => a i * c) =
      t * c ^ 2 * ∑ i : Fin n, ∑ j : Fin n, a i * a j * P i j := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/--
The forward top-coefficient quadratic for a shifted monomial is the raw
power-kernel sum times the normalizing scale.
-/
lemma forward_topCoeffQuadratic_shiftPow_raw
    {k r : ℕ} {x h : ℝ} (hh : h ≠ 0) :
    forwardTopCoeffQuadratic k (fun y : ℝ => (y - x) ^ r) x h =
      (h ^ (r - 1) / (((Nat.factorial k : ℝ) * h ^ k) ^ 2)) *
        (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
          forwardTopCoeffRawWeight k i * forwardTopCoeffRawWeight k j *
            (∑ p ∈ Finset.range r,
              (i.val : ℝ) ^ p * (j.val : ℝ) ^ (r.pred - p))) := by
  have hw : forwardTopCoeffWeights k h =
      fun i => forwardTopCoeffRawWeight k i * ((Nat.factorial k : ℝ) * h ^ k)⁻¹ := by
    funext i
    exact div_eq_mul_inv _ _
  unfold forwardTopCoeffQuadratic
  simp_rw [loewnerKernel_shiftPow_forward_nodes_eq (k := k) (x := x) (h := h) hh]
  rw [hw, div_eq_mul_inv, ← inv_pow]
  exact quadratic_form_scaled_weights_eq _ _ _ _

/--
The forward top-coefficient quadratic vanishes on shifted monomials of degree
at most `2*k`.
-/
lemma forward_topCoeffQuadratic_shiftPow_eq_zero_of_le_two_mul
    {k r : ℕ} {x h : ℝ} (hh : h ≠ 0) (hr : r ≤ 2 * k) :
    forwardTopCoeffQuadratic k (fun y : ℝ => (y - x) ^ r) x h = 0 := by
  rw [forward_topCoeffQuadratic_shiftPow_raw
    (k := k) (r := r) (x := x) (h := h) hh]
  rw [forwardTopCoeffRawWeight_powerKernel_sum_eq_zero_of_le_two_mul
    (k := k) (r := r) hr]
  simp

/--
The forward top-coefficient quadratic evaluates to `1` on the shifted monomial
of degree `2*k + 1`.
-/
lemma forward_topCoeffQuadratic_shiftPow_top
    {k : ℕ} {x h : ℝ} (hh : h ≠ 0) :
    forwardTopCoeffQuadratic k
        (fun y : ℝ => (y - x) ^ (2 * k + 1)) x h = 1 := by
  rw [forward_topCoeffQuadratic_shiftPow_raw
    (k := k) (r := 2 * k + 1) (x := x) (h := h) hh]
  rw [forwardTopCoeffRawWeight_powerKernel_sum_top k]
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hsub]
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hpow : h ^ (2 * k) ≠ 0 := pow_ne_zero (2 * k) hh
  have hfact_sq :
      (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) =
        (Nat.factorial k : ℝ) ^ 2 := by ring
  have hden :
      (((Nat.factorial k : ℝ) * h ^ k) ^ 2) =
        (Nat.factorial k : ℝ) ^ 2 * h ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]
    ring_nf
  rw [hfact_sq, hden]
  field_simp [hfact, hpow]

/--
The Löwner kernel is linear over a finite shifted-power expansion.
-/
lemma loewnerKernel_finset_sum_shiftPow
    {N : ℕ} (coeff : ℕ → ℝ) {x u v : ℝ} :
    loewnerKernel
        (fun y : ℝ => ∑ r ∈ Finset.range N, coeff r * (y - x) ^ r) u v =
      ∑ r ∈ Finset.range N,
        coeff r * loewnerKernel (fun y : ℝ => (y - x) ^ r) u v := by
  by_cases huv : u = v
  · subst v
    rw [loewnerKernel_self]
    have hdiff :
        ∀ r ∈ Finset.range N,
          DifferentiableAt ℝ (fun y : ℝ => coeff r * (y - x) ^ r) u := by
      intro r _hr
      fun_prop
    have hderiv :=
      deriv_sum (u := Finset.range N)
        (A := fun (r : ℕ) (y : ℝ) => coeff r * (y - x) ^ r) hdiff
    have hfun :
        (fun y : ℝ => ∑ r ∈ Finset.range N, coeff r * (y - x) ^ r) =
          (∑ r ∈ Finset.range N,
            (fun y : ℝ => coeff r * (y - x) ^ r)) := by
      funext y
      simp
    rw [hfun]
    simpa [loewnerKernel_self, deriv_const_mul_field, Finset.sum_apply, mul_assoc,
      mul_comm, mul_left_comm] using hderiv
  · rw [loewnerKernel_eq_div (f := fun y : ℝ =>
        ∑ r ∈ Finset.range N, coeff r * (y - x) ^ r) huv]
    have hrhs :
        (∑ r ∈ Finset.range N,
          coeff r * loewnerKernel (fun y : ℝ => (y - x) ^ r) u v) =
        ∑ r ∈ Finset.range N,
          coeff r * (((u - x) ^ r - (v - x) ^ r) / (u - v)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [loewnerKernel_eq_div (f := fun y : ℝ => (y - x) ^ r) huv]
    rw [hrhs]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    ring

/--
The forward top-coefficient quadratic is linear over finite shifted-power
expansions.
-/
lemma forward_topCoeffQuadratic_finset_sum_shiftPow
    {k N : ℕ} {x h : ℝ} (coeff : ℕ → ℝ) :
    forwardTopCoeffQuadratic k
        (fun y : ℝ => ∑ r ∈ Finset.range N, coeff r * (y - x) ^ r) x h =
      ∑ r ∈ Finset.range N,
        coeff r *
          forwardTopCoeffQuadratic k (fun y : ℝ => (y - x) ^ r) x h := by
  unfold forwardTopCoeffQuadratic
  simp_rw [loewnerKernel_finset_sum_shiftPow (coeff := coeff) (x := x)]
  simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul] using by
    calc
      (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), ∑ r ∈ Finset.range N,
        forwardTopCoeffWeights k h i *
          (coeff r *
              loewnerKernel (fun y : ℝ => (y - x) ^ r)
                (forwardCoeffNodes k x h i)
                (forwardCoeffNodes k x h j) *
            forwardTopCoeffWeights k h j)) =
          ∑ i : Fin (k + 1), ∑ r ∈ Finset.range N, ∑ j : Fin (k + 1),
            forwardTopCoeffWeights k h i *
              (coeff r *
                  loewnerKernel (fun y : ℝ => (y - x) ^ r)
                    (forwardCoeffNodes k x h i)
                    (forwardCoeffNodes k x h j) *
                forwardTopCoeffWeights k h j) := by
        congr 1 with i
        rw [Finset.sum_comm]
      _ = ∑ r ∈ Finset.range N, ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
            forwardTopCoeffWeights k h i *
              (coeff r *
                  loewnerKernel (fun y : ℝ => (y - x) ^ r)
                    (forwardCoeffNodes k x h i)
                    (forwardCoeffNodes k x h j) *
                forwardTopCoeffWeights k h j) := by
        rw [Finset.sum_comm]
      _ = ∑ r ∈ Finset.range N, ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
            coeff r *
              (forwardTopCoeffWeights k h i *
                (loewnerKernel (fun y : ℝ => (y - x) ^ r)
                    (forwardCoeffNodes k x h i)
                    (forwardCoeffNodes k x h j) *
                  forwardTopCoeffWeights k h j)) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = ∑ r ∈ Finset.range N, ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
            coeff r *
              (forwardTopCoeffWeights k h i *
                (loewnerKernel (fun y : ℝ => (y - x) ^ r)
                    (forwardCoeffNodes k x h i)
                    (forwardCoeffNodes k x h j) *
                  forwardTopCoeffWeights k h j)) := rfl

/--
On the Taylor polynomial of order `2*k + 1`, the forward quadratic extracts the
confluent diagonal coefficient.
-/
lemma forward_topCoeffQuadratic_taylorWithinEval_eq
    {f : ℝ → ℝ} {k : ℕ} {x h : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hh : h ≠ 0) :
    forwardTopCoeffQuadratic k
        (fun y : ℝ =>
          taylorWithinEval f (2 * k + 1) (Set.Ioo (-1 : ℝ) 1) x y) x h =
      (deriv^[2 * k] (deriv f)) x /
        (Nat.factorial (2 * k + 1) : ℝ) := by
  let coeff : ℕ → ℝ := fun r =>
    (Nat.factorial r : ℝ)⁻¹ * (deriv^[r] f) x
  have hpoly :
      (fun y : ℝ =>
          taylorWithinEval f (2 * k + 1) (Set.Ioo (-1 : ℝ) 1) x y) =
        fun y : ℝ => ∑ r ∈ Finset.range (2 * k + 1 + 1),
          coeff r * (y - x) ^ r := by
    funext y
    simp_rw [taylor_within_apply]
    simp [coeff, iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
      iteratedDeriv_eq_iterate, mul_assoc, mul_comm]
  rw [hpoly]
  rw [forward_topCoeffQuadratic_finset_sum_shiftPow
    (k := k) (N := 2 * k + 1 + 1) (x := x) (h := h) (coeff := coeff)]
  rw [Finset.sum_eq_single (2 * k + 1)]
  · rw [forward_topCoeffQuadratic_shiftPow_top (k := k) (x := x) (h := h) hh]
    have hiter :
        (deriv^[2 * k + 1] f) x = (deriv^[2 * k] (deriv f)) x := by
      rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
      exact congrFun (iteratedDeriv_succ' (n := 2 * k) (f := f)) x
    simp [coeff, div_eq_mul_inv, mul_comm, mul_left_comm]
  · intro r hrange hrne
    have hrle : r ≤ 2 * k := by
      have hrlt : r < 2 * k + 1 + 1 := Finset.mem_range.mp hrange
      omega
    rw [forward_topCoeffQuadratic_shiftPow_eq_zero_of_le_two_mul
      (k := k) (r := r) (x := x) (h := h) hh hrle]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/--
Small positive forward nodes starting from an interior point remain in the open
unit interval.
-/
lemma forwardCoeffNodes_mem_Ioo_of_pos_lt
    {k : ℕ} {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h * (k : ℝ) < 1 - x) :
    ∀ i, forwardCoeffNodes k x h i ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro i
  have hi_nonneg : 0 ≤ (i.val : ℝ) := by exact_mod_cast Nat.zero_le i.val
  have hi_le_k : (i.val : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hmul_nonneg : 0 ≤ (i.val : ℝ) * h := mul_nonneg hi_nonneg hhpos.le
  have hmul_le : (i.val : ℝ) * h ≤ (k : ℝ) * h :=
    mul_le_mul_of_nonneg_right hi_le_k hhpos.le
  constructor
  · dsimp [forwardCoeffNodes]
    linarith [hx.1, hmul_nonneg]
  · dsimp [forwardCoeffNodes]
    nlinarith [hhsmall, hmul_le]

/--
Forward nodes are injective when the step size is positive.
-/
lemma forwardCoeffNodes_injective
    {k : ℕ} {x h : ℝ} (hhpos : 0 < h) :
    Function.Injective (forwardCoeffNodes k x h) := by
  intro i j hij
  have hval : (i.val : ℝ) = (j.val : ℝ) := by
    dsimp [forwardCoeffNodes] at hij
    nlinarith [hhpos]
  exact Fin.ext (Nat.cast_injective hval)

/--
Public Löwner positivity makes the forward top-coefficient quadratic
nonnegative on sufficiently small forward node families.
-/
theorem forward_topCoeffQuadratic_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) {k : ℕ}
    {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h * (k : ℝ) < 1 - x) :
    0 ≤ forwardTopCoeffQuadratic k f x h := by
  let nodes : Fin (k + 1) → ℝ := forwardCoeffNodes k x h
  let weights : Fin (k + 1) → ℝ := forwardTopCoeffWeights k h
  have hpsd :
      (Matrix.of (fun i j : Fin (k + 1) =>
        loewnerKernel f (nodes i) (nodes j))).PosSemidef :=
    loewnerKernel_real_posSemidef_of_loewnerPosOnUnitInterval
      (f := f) hpos
      (by
        intro i
        exact forwardCoeffNodes_mem_Ioo_of_pos_lt hx hhpos hhsmall i)
      (forwardCoeffNodes_injective (k := k) (x := x) hhpos)
  simpa [forwardTopCoeffQuadratic, nodes, weights] using
    hpsd.dotProduct_mulVec_nonneg weights

/--
Eventually nonnegative form of the forward top-coefficient quadratic test.

This is the exact positivity input consumed, together with the
confluent-diagonal limit `forward_topCoeffQuadratic_tendsto_confluentDiagonal`,
by `oddIteratedDeriv_nonneg_of_loewnerPosOnUnitInterval` (`FiniteOrderLadder.lean`).
-/
theorem forward_topCoeffQuadratic_nonneg_eventually_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) {k : ℕ}
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      0 ≤ forwardTopCoeffQuadratic k f x h := by
  have hmargin : 0 < 1 - x := by linarith [hx.2]
  by_cases hk : k = 0
  · filter_upwards [self_mem_nhdsWithin] with h hhpos
    have hhsmall : h * (k : ℝ) < 1 - x := by
      simp [hk, hmargin]
    exact
      forward_topCoeffQuadratic_nonneg_of_loewnerPosOnUnitInterval
        (f := f) (k := k) hpos hx hhpos hhsmall
  · have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hδ : 0 < (1 - x) / (k : ℝ) := div_pos hmargin hkpos
    have hsmall :
        ∀ᶠ h in 𝓝[>] (0 : ℝ), h < (1 - x) / (k : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hhpos hhsmall'
    have hhsmall : h * (k : ℝ) < 1 - x := by
      simpa [mul_comm] using (lt_div_iff₀' hkpos).mp hhsmall'
    exact
      forward_topCoeffQuadratic_nonneg_of_loewnerPosOnUnitInterval
        (f := f) (k := k) hpos hx hhpos hhsmall

end

end Quantum.TraceInequality.Loewner
