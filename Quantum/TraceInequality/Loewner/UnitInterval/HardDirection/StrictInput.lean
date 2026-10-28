import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.ContinuousMap.Interval
import Quantum.TraceInequality.Loewner.Koranyi.StrictIntegralInput

/-!
# Chapter 20 strict book input

This file contains the auxiliary book function `g₀`, its strict Löwner
positivity package, and the strictness theorem for the concrete Theorem 20.1
smooth approximants.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open Filter

open scoped NNReal
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

noncomputable section

/-- The auxiliary strictly positive kernel from Theorem 20.1. -/
def bookG0 (x : ℝ) : ℝ :=
  Real.log ((3 - x) / (2 - x))

/-- The Theorem 20.1 smooth strict approximation family. -/
def bookSmoothApprox (f : ℝ → ℝ) (ε δ x : ℝ) : ℝ :=
  f ((1 - δ) * x) + ε * bookG0 x

/-- Canonical positive perturbation parameter used for the book approximants. -/
def bookEpsilon (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹

/-- Canonical positive interior scaling parameter used for the book approximants. -/
def bookDelta (n : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ)⁻¹

/-- Cauchy vector used in the book proof of strict positivity of `g₀`. -/
def bookCauchyCombo {n : ℕ} (y : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin (n + 1), c i / ((t - y i : ℝ) : ℂ)

/-- Numerator polynomial clearing the Cauchy denominators in `bookCauchyCombo`. -/
def bookCauchyNumerator {n : ℕ} (y : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1),
    Polynomial.C (c i) *
      ∏ j ∈ (Finset.univ.erase i),
        (Polynomial.X - Polynomial.C ((y j : ℝ) : ℂ))

/-- The real square integral of the Cauchy vector on the book interval `[2,3]`. -/
def bookCauchyNormSqIntegral {n : ℕ} (y : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → ℂ) : ℝ :=
  ∫ t in (2 : ℝ)..3, ‖bookCauchyCombo y c t‖ ^ (2 : ℕ)

private theorem bookCauchyNumerator_eval_at_node {n : ℕ}
    {y : Fin (n + 1) → ℝ} (c : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) :
    (bookCauchyNumerator y c).eval ((y k : ℝ) : ℂ) =
      c k * ∏ j ∈ (Finset.univ.erase k), (((y k - y j : ℝ) : ℂ)) := by
  classical
  unfold bookCauchyNumerator
  rw [Polynomial.eval_finset_sum]
  refine (Finset.sum_eq_single (s := Finset.univ) (a := k) (M := ℂ) ?_ ?_).trans ?_
  · intro i _hi hik
    rw [Polynomial.eval_mul]
    suffices
        (Polynomial.eval ((y k : ℝ) : ℂ)
          (∏ j ∈ (Finset.univ.erase i),
            (Polynomial.X - Polynomial.C ((y j : ℝ) : ℂ)))) = 0 by
      simp [this]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (i := k) (by simp [hik.symm])
      (by simp)
  · intro hk
    exact (hk (Finset.mem_univ k)).elim
  · simp [Polynomial.eval_prod]

private theorem bookCauchyNumerator_coeff_zero_of_eq_zero {n : ℕ}
    {y : Fin (n + 1) → ℝ} {c : Fin (n + 1) → ℂ}
    (hy : Function.Injective y)
    (hP : bookCauchyNumerator y c = 0) :
    c = 0 := by
  funext k
  have heval :
      (bookCauchyNumerator y c).eval ((y k : ℝ) : ℂ) = 0 := by
    rw [hP]
    simp
  have hprod_ne :
      (∏ j ∈ (Finset.univ.erase k), (((y k - y j : ℝ) : ℂ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
    have hyne : y k - y j ≠ 0 := by
      exact sub_ne_zero.mpr (fun h => hjne (hy h.symm))
    exact_mod_cast hyne
  have hmul :
      c k * ∏ j ∈ (Finset.univ.erase k), (((y k - y j : ℝ) : ℂ)) = 0 := by
    simpa [bookCauchyNumerator_eval_at_node c k] using heval
  exact (mul_eq_zero.mp hmul).resolve_right hprod_ne

private theorem bookCauchyNumerator_eval_eq_combo_mul_denominator {n : ℕ}
    (y : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℂ) {t : ℝ}
    (ht : ∀ i : Fin (n + 1), t - y i ≠ 0) :
    (bookCauchyNumerator y c).eval (t : ℂ) =
      bookCauchyCombo y c t *
        ∏ i : Fin (n + 1), ((t - y i : ℝ) : ℂ) := by
  classical
  unfold bookCauchyNumerator bookCauchyCombo
  rw [Polynomial.eval_finset_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hprod :
      ((t - y i : ℝ) : ℂ) *
        (∏ j ∈ (Finset.univ.erase i), (((t - y j : ℝ) : ℂ))) =
          ∏ j : Fin (n + 1), (((t - y j : ℝ) : ℂ)) := by
    simpa using
      (Finset.mul_prod_erase (s := Finset.univ)
        (f := fun j : Fin (n + 1) => ((t - y j : ℝ) : ℂ))
        (a := i) (by simp))
  have hden : ((t - y i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht i
  calc
    Polynomial.eval (↑t)
        (Polynomial.C (c i) *
          ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C ↑(y j)))
        = c i * (∏ j ∈ (Finset.univ.erase i), (((t - y j : ℝ) : ℂ))) := by
          simp [Polynomial.eval_prod]
    _ = (c i / ((t - y i : ℝ) : ℂ)) *
          ∏ j : Fin (n + 1), (((t - y j : ℝ) : ℂ)) := by
          rw [← hprod]
          field_simp [hden]

/-- Nonzero Cauchy coefficients cannot vanish throughout the interval `(2,3)`. -/
theorem bookCauchyCombo_exists_nonzero_of_ne_zero {n : ℕ}
    {y : Fin (n + 1) → ℝ} {c : Fin (n + 1) → ℂ}
    (hy : Function.Injective y) (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ≠ 0) :
    ∃ t ∈ Set.Ioo (2 : ℝ) 3, bookCauchyCombo y c t ≠ 0 := by
  classical
  by_contra hno
  have hzero :
      ∀ t ∈ Set.Ioo (2 : ℝ) 3, bookCauchyCombo y c t = 0 := by
    intro t ht
    by_contra htne
    exact hno ⟨t, ht, htne⟩
  let P : Polynomial ℂ := bookCauchyNumerator y c
  have hroot_subset :
      ((fun t : ℝ => ((t : ℝ) : ℂ)) '' Set.Ioo (2 : ℝ) 3) ⊆
        {z : ℂ | Polynomial.IsRoot P z} := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have htden : ∀ i : Fin (n + 1), t - y i ≠ 0 := by
      intro i
      have ht2 : 2 < t := ht.1
      have hyi : y i < 1 := (hymem i).2
      linarith
    have heval :=
      bookCauchyNumerator_eval_eq_combo_mul_denominator y c htden
    have hcombo : bookCauchyCombo y c t = 0 := hzero t ht
    simpa [Polynomial.IsRoot.def, hcombo] using heval
  have hroots_infinite : {z : ℂ | Polynomial.IsRoot P z}.Infinite := by
    refine (Set.Ioo_infinite (show (2 : ℝ) < 3 by norm_num)).image ?_ |>.mono hroot_subset
    intro a ha b hb hab
    exact Complex.ofReal_injective hab
  have hPzero : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hroots_infinite
  have hc_zero : c = 0 :=
    bookCauchyNumerator_coeff_zero_of_eq_zero hy (by simpa [P] using hPzero)
  exact hc hc_zero

private theorem bookCauchyCombo_norm_sq_eq_sum {n : ℕ}
    (y : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℂ) (t : ℝ) :
    ((‖bookCauchyCombo y c t‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        c i * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * star (c j) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [bookCauchyCombo, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

private theorem bookCauchyCombo_continuousOn_Icc {n : ℕ}
    {y : Fin (n + 1) → ℝ} (c : Fin (n + 1) → ℂ)
    (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun t : ℝ => bookCauchyCombo y c t)
      (Set.Icc (2 : ℝ) 3) := by
  classical
  unfold bookCauchyCombo
  refine continuousOn_finset_sum _ fun i _hi => ?_
  refine continuousOn_const.div ?_ ?_
  · fun_prop
  · intro t ht
    have hyi : y i < 1 := (hymem i).2
    exact_mod_cast (by linarith [ht.1] : t - y i ≠ 0)

/-- The Cauchy square integral is strictly positive for nonzero coefficients. -/
theorem bookCauchyCombo_normSq_intervalIntegral_pos_of_ne_zero {n : ℕ}
    {y : Fin (n + 1) → ℝ} {c : Fin (n + 1) → ℂ}
    (hy : Function.Injective y) (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ≠ 0) :
    0 < ∫ t in (2 : ℝ)..3, ‖bookCauchyCombo y c t‖ ^ (2 : ℕ) := by
  have hcont_combo := bookCauchyCombo_continuousOn_Icc (y := y) c hymem
  have hcont :
      ContinuousOn (fun t : ℝ => ‖bookCauchyCombo y c t‖ ^ (2 : ℕ))
        (Set.Icc (2 : ℝ) 3) :=
    hcont_combo.norm.pow 2
  refine intervalIntegral.integral_pos (by norm_num : (2 : ℝ) < 3) hcont ?_ ?_
  · intro t _ht
    positivity
  · rcases bookCauchyCombo_exists_nonzero_of_ne_zero hy hymem hc with
      ⟨t, ht, htne⟩
    refine ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
    exact pow_pos (norm_pos_iff.mpr htne) 2

private theorem bookG0_den_ne_zero_of_lt_two {x : ℝ} (hx : x < 2) :
    2 - x ≠ 0 := by
  linarith

private theorem bookG0_ratio_ne_zero_of_lt_two {x : ℝ} (hx : x < 2) :
    (3 - x) / (2 - x) ≠ 0 := by
  have hnum : 3 - x ≠ 0 := by linarith
  have hden : 2 - x ≠ 0 := bookG0_den_ne_zero_of_lt_two hx
  exact div_ne_zero hnum hden

private theorem intervalIntegral_one_div_sub_eq_log_sub {x : ℝ} (hx : x < 2) :
    (∫ t in (2 : ℝ)..3, (1 / (t - x) : ℝ)) =
      Real.log (3 - x) - Real.log (2 - x) := by
  have hderiv :
      ∀ t ∈ Set.uIcc (2 : ℝ) 3,
        HasDerivAt (fun u : ℝ => Real.log (u - x)) (1 / (t - x)) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have ht2 : 2 ≤ t := htIcc.1
    have hne : t - x ≠ 0 := by linarith
    have hsub : HasDerivAt (fun u : ℝ => u - x) (1 - 0) t :=
      (hasDerivAt_id t).sub (hasDerivAt_const (x := t) (c := x))
    simpa using hsub.log hne
  have hcont : ContinuousOn (fun t : ℝ => (1 / (t - x) : ℝ)) (Set.uIcc (2 : ℝ) 3) := by
    refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have ht2 : 2 ≤ t := htIcc.1
    linarith
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

private theorem intervalIntegrable_one_div_sub_of_lt_two {x : ℝ} (hx : x < 2) :
    IntervalIntegrable (fun t : ℝ => (1 / (t - x) : ℝ)) volume (2 : ℝ) 3 := by
  have hcont : ContinuousOn (fun t : ℝ => (1 / (t - x) : ℝ)) (Set.uIcc (2 : ℝ) 3) := by
    refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have ht2 : 2 ≤ t := htIcc.1
    linarith
  exact hcont.intervalIntegrable

/-- Resolvent interval representation of the auxiliary book function `g₀`. -/
theorem bookG0_eq_intervalIntegral_resolvent {x : ℝ} (hx : x < 2) :
    bookG0 x = ∫ t in (2 : ℝ)..3, (1 / (t - x) : ℝ) := by
  have hnum : 3 - x ≠ 0 := by linarith
  have hden : 2 - x ≠ 0 := bookG0_den_ne_zero_of_lt_two hx
  rw [intervalIntegral_one_div_sub_eq_log_sub hx]
  simp [bookG0, Real.log_div hnum hden]

private theorem intervalIntegral_resolvent_mul_eq_div
    {x y : ℝ} (hx : x < 2) (hy : y < 2) (hxy : x ≠ y) :
    (∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - y)) : ℝ)) =
      (bookG0 x - bookG0 y) / (x - y) := by
  have hxint := intervalIntegrable_one_div_sub_of_lt_two hx
  have hyint := intervalIntegrable_one_div_sub_of_lt_two hy
  have hcongr :
      (∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - y)) : ℝ)) =
        ∫ t in (2 : ℝ)..3,
          ((1 / (t - x) : ℝ) - (1 / (t - y) : ℝ)) / (x - y) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have htx : t - x ≠ 0 := by linarith [htIcc.1]
    have hty : t - y ≠ 0 := by linarith [htIcc.1]
    field_simp [htx, hty, sub_ne_zero.mpr hxy]
    ring
  calc
    (∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - y)) : ℝ))
        = ∫ t in (2 : ℝ)..3,
            ((1 / (t - x) : ℝ) - (1 / (t - y) : ℝ)) / (x - y) := hcongr
    _ = ((∫ t in (2 : ℝ)..3, (1 / (t - x) : ℝ)) -
            (∫ t in (2 : ℝ)..3, (1 / (t - y) : ℝ))) / (x - y) := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hxint hyint]
    _ = (bookG0 x - bookG0 y) / (x - y) := by
          rw [← bookG0_eq_intervalIntegral_resolvent hx,
            ← bookG0_eq_intervalIntegral_resolvent hy]

private theorem intervalIntegral_resolvent_sq_eq_deriv {x : ℝ} (hx : x < 2) :
    (∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - x)) : ℝ)) =
      1 / ((2 - x) * (3 - x)) := by
  have hderiv :
      ∀ t ∈ Set.uIcc (2 : ℝ) 3,
        HasDerivAt (fun u : ℝ => -((u - x)⁻¹))
          (1 / ((t - x) * (t - x))) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have hne : t - x ≠ 0 := by linarith [htIcc.1]
    have hsub : HasDerivAt (fun u : ℝ => u - x) (1 - 0) t :=
      (hasDerivAt_id t).sub (hasDerivAt_const (x := t) (c := x))
    convert (hsub.inv hne).neg using 1
    field_simp [hne]
    ring
  have hcont :
      ContinuousOn (fun t : ℝ => (1 / ((t - x) * (t - x)) : ℝ)) (Set.uIcc (2 : ℝ) 3) := by
    refine continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).mul (continuousOn_id.sub continuousOn_const)) ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have hne : t - x ≠ 0 := by linarith [htIcc.1]
    exact mul_ne_zero hne hne
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have h2 : 2 - x ≠ 0 := by linarith
  have h3 : 3 - x ≠ 0 := by linarith
  calc
    (∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - x)) : ℝ))
        = (-(3 - x)⁻¹) - (-(2 - x)⁻¹) := hftc
    _ = 1 / ((2 - x) * (3 - x)) := by
      field_simp [h2, h3]
      ring

/-- The auxiliary book function `g₀` is smooth on the left neighborhood `(-∞, 2)`. -/
theorem bookG0_contDiffOn_Iio_two :
    ContDiffOn ℝ loewnerBookSmoothOrder bookG0 (Set.Iio (2 : ℝ)) := by
  unfold bookG0
  refine ContDiffOn.log ?_ ?_
  · exact
      (contDiffOn_const.sub contDiffOn_id).div
        (contDiffOn_const.sub contDiffOn_id)
        (fun x hx => bookG0_den_ne_zero_of_lt_two hx)
  · intro x hx
    exact bookG0_ratio_ne_zero_of_lt_two hx

/-- Derivative of the auxiliary book function on its natural left domain. -/
theorem bookG0_hasDerivAt_of_lt_two {x : ℝ} (hx : x < 2) :
    HasDerivAt bookG0 (1 / ((2 - x) * (3 - x))) x := by
  unfold bookG0
  have hden : 2 - x ≠ 0 := bookG0_den_ne_zero_of_lt_two hx
  have hnum : 3 - x ≠ 0 := by linarith
  have hratio : (3 - x) / (2 - x) ≠ 0 :=
    bookG0_ratio_ne_zero_of_lt_two hx
  have htop : HasDerivAt (fun y : ℝ => 3 - y) (-1) x := by
    simpa using (hasDerivAt_const (x := x) (c := (3 : ℝ))).sub (hasDerivAt_id x)
  have hbot : HasDerivAt (fun y : ℝ => 2 - y) (-1) x := by
    simpa using (hasDerivAt_const (x := x) (c := (2 : ℝ))).sub (hasDerivAt_id x)
  have hquot :
      HasDerivAt (fun y : ℝ => (3 - y) / (2 - y))
        (1 / (2 - x) ^ (2 : ℕ)) x := by
    convert htop.div hbot hden using 1
    field_simp [hden]
    ring
  convert hquot.log hratio using 1
  field_simp [hden, hnum]

/-- Formula for the derivative of the auxiliary book function on `(-∞, 2)`. -/
theorem bookG0_deriv_eq_of_lt_two {x : ℝ} (hx : x < 2) :
    deriv bookG0 x = 1 / ((2 - x) * (3 - x)) :=
  (bookG0_hasDerivAt_of_lt_two hx).deriv

/-- The Löwner kernel of `g₀` is the interval Gram kernel of the Cauchy resolvents. -/
theorem bookG0_loewnerKernel_eq_intervalIntegral
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    loewnerKernel bookG0 x y =
      ∫ t in (2 : ℝ)..3, (1 / ((t - x) * (t - y)) : ℝ) := by
  have hxlt : x < 2 := lt_trans hx.2 (by norm_num)
  have hylt : y < 2 := lt_trans hy.2 (by norm_num)
  by_cases hxy : x = y
  · subst hxy
    rw [loewnerKernel_self, bookG0_deriv_eq_of_lt_two hxlt,
      intervalIntegral_resolvent_sq_eq_deriv hxlt]
  · rw [loewnerKernel_eq_div (f := bookG0) hxy,
      intervalIntegral_resolvent_mul_eq_div hxlt hylt hxy]

private theorem bookCauchyQuadraticTerm_continuousOn {n : ℕ}
    {y : Fin (n + 1) → ℝ} (c : Fin (n + 1) → ℂ)
    (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1)
    (i j : Fin (n + 1)) :
    ContinuousOn
      (fun t : ℝ =>
        star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j)
      (Set.uIcc (2 : ℝ) 3) := by
  have hreal :
      ContinuousOn (fun t : ℝ => (1 / ((t - y i) * (t - y j)) : ℝ))
        (Set.uIcc (2 : ℝ) 3) := by
    refine continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_id.sub continuousOn_const)) ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht
    have hyi : y i < 1 := (hymem i).2
    have hyj : y j < 1 := (hymem j).2
    have hi : t - y i ≠ 0 := by linarith [htIcc.1]
    have hj : t - y j ≠ 0 := by linarith [htIcc.1]
    exact mul_ne_zero hi hj
  have hcomplex :
      ContinuousOn
        (fun t : ℝ => (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)))
        (Set.uIcc (2 : ℝ) 3) :=
    Complex.continuous_ofReal.comp_continuousOn hreal
  exact (continuousOn_const.mul hcomplex).mul continuousOn_const

private theorem bookCauchyQuadraticTerm_intervalIntegrable {n : ℕ}
    {y : Fin (n + 1) → ℝ} (c : Fin (n + 1) → ℂ)
    (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1)
    (i j : Fin (n + 1)) :
    IntervalIntegrable
      (fun t : ℝ =>
        star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j)
      volume (2 : ℝ) 3 :=
  (bookCauchyQuadraticTerm_continuousOn c hymem i j).intervalIntegrable

private theorem bookCauchyQuadraticTerm_integral_eq {n : ℕ}
    {y : Fin (n + 1) → ℝ} (c : Fin (n + 1) → ℂ)
    (i j : Fin (n + 1)) :
    star (c i) *
        (((∫ t in (2 : ℝ)..3,
          (1 / ((t - y i) * (t - y j)) : ℝ)) : ℝ) : ℂ) * c j =
      ∫ t in (2 : ℝ)..3,
        star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j := by
  calc
    star (c i) *
        (((∫ t in (2 : ℝ)..3,
          (1 / ((t - y i) * (t - y j)) : ℝ)) : ℝ) : ℂ) * c j =
        (star (c i) * ∫ t in (2 : ℝ)..3,
          (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ))) * c j := by
      rw [← intervalIntegral.integral_ofReal]
    _ =
        (∫ t in (2 : ℝ)..3,
          star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ))) * c j := by
      exact congrArg (fun z : ℂ => z * c j)
        (intervalIntegral.integral_const_mul (star (c i))
          (fun t : ℝ => (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)))).symm
    _ =
        ∫ t in (2 : ℝ)..3,
          star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j := by
      exact (intervalIntegral.integral_mul_const (c j)
        (fun t : ℝ =>
          star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)))).symm

/-- Quadratic form of the `g₀` Löwner matrix as the Cauchy square integral. -/
theorem bookG0_loewnerMatrix_quadratic_eq_intervalIntegral_normSq
    {n : ℕ} {y : Fin (n + 1) → ℝ}
    (hymem : ∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1)
    (c : Fin (n + 1) → ℂ) :
    star c ⬝ᵥ ((loewnerMatrix (n := n) bookG0 y) *ᵥ c) =
      (bookCauchyNormSqIntegral y (fun i => star (c i)) : ℂ) := by
  classical
  calc
    star c ⬝ᵥ ((loewnerMatrix (n := n) bookG0 y) *ᵥ c)
        = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            star (c i) * (loewnerMatrix (n := n) bookG0 y i j) * c j := by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            star (c i) *
              (((∫ t in (2 : ℝ)..3,
                (1 / ((t - y i) * (t - y j)) : ℝ)) : ℝ) : ℂ) * c j := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [loewnerMatrix, bookG0_loewnerKernel_eq_intervalIntegral
            (hymem i) (hymem j)]
    _ = ∫ t in (2 : ℝ)..3,
          ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j := by
          simp_rw [bookCauchyQuadraticTerm_integral_eq c]
          calc
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                ∫ t in (2 : ℝ)..3,
                  star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j)
                = ∑ i : Fin (n + 1), ∫ t in (2 : ℝ)..3,
                    ∑ j : Fin (n + 1),
                      star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  rw [← intervalIntegral.integral_finset_sum]
                  intro j _hj
                  exact bookCauchyQuadraticTerm_intervalIntegrable c hymem i j
            _ = ∫ t in (2 : ℝ)..3,
                  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                    star (c i) * (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j := by
                  rw [← intervalIntegral.integral_finset_sum]
                  intro i _hi
                  have hcont :
                      ContinuousOn
                        (fun t : ℝ =>
                          ∑ j : Fin (n + 1),
                            star (c i) *
                              (((1 / ((t - y i) * (t - y j)) : ℝ) : ℂ)) * c j)
                        (Set.uIcc (2 : ℝ) 3) := by
                    refine continuousOn_finset_sum _ fun j _hj => ?_
                    exact bookCauchyQuadraticTerm_continuousOn c hymem i j
                  exact hcont.intervalIntegrable
    _ = ∫ t in (2 : ℝ)..3,
          ((‖bookCauchyCombo y (fun i => star (c i)) t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          simpa using
            (bookCauchyCombo_norm_sq_eq_sum y (fun i => star (c i)) t).symm
    _ = (bookCauchyNormSqIntegral y (fun i => star (c i)) : ℂ) := by
          rw [bookCauchyNormSqIntegral]
          rw [← intervalIntegral.integral_ofReal
            (a := (2 : ℝ)) (b := 3) (μ := volume)
            (f := fun t : ℝ =>
              ‖bookCauchyCombo y (fun i => star (c i)) t‖ ^ (2 : ℕ))]

/-- The finite Löwner matrices of the book auxiliary function `g₀` are positive definite. -/
theorem bookG0_loewnerMatrix_posDef {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    (loewnerMatrix (n := n) bookG0 y).PosDef := by
  classical
  have hHerm : (loewnerMatrix (n := n) bookG0 y).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp [loewnerMatrix, loewnerKernel_swap]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro c hc
  have hstar_ne : (fun i : Fin (n + 1) => star (c i)) ≠ 0 := by
    intro hstar
    apply hc
    funext i
    have hi := congrFun hstar i
    simpa using congrArg star hi
  have hpos :
      0 < bookCauchyNormSqIntegral y (fun i => star (c i)) := by
    simpa [bookCauchyNormSqIntegral] using
      bookCauchyCombo_normSq_intervalIntegral_pos_of_ne_zero
        hy.2.1 hy.2.2.1 hstar_ne
  rw [bookG0_loewnerMatrix_quadratic_eq_intervalIntegral_normSq
    hy.2.2.1 c]
  exact_mod_cast hpos

/-- The book auxiliary function `g₀` satisfies the global strict Löwner input. -/
theorem bookG0_globalStrictPosDef :
    GlobalStrictPosDef bookG0 := by
  intro n y hy
  exact bookG0_loewnerMatrix_posDef hy

/-- On `[-1,1]`, the auxiliary book function has derivative bounded by `1`. -/
theorem bookG0_deriv_le_one_on_Icc :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, deriv bookG0 x ≤ 1 := by
  intro x hx
  have hxlt : x < 2 := lt_of_le_of_lt hx.2 (by norm_num)
  rw [bookG0_deriv_eq_of_lt_two hxlt]
  have h2 : 1 ≤ 2 - x := by linarith [hx.2]
  have h3 : 2 ≤ 3 - x := by linarith [hx.2]
  have hprod : 1 ≤ (2 - x) * (3 - x) := by nlinarith
  simpa [one_div] using inv_le_one_of_one_le₀ hprod

private theorem pointsHyp_const_mul_of_pos_of_le_one
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    pointsHyp (n := n) (fun i : Fin (n + 1) => a * y i) := by
  refine ⟨by simp [hy.1], ?_, ?_, ?_⟩
  · intro i j hij
    exact hy.2.1 (mul_left_cancel₀ ha.ne' hij)
  · intro i
    have hyi := hy.2.2.1 i
    constructor
    · change -1 < a * y i
      by_cases hneg : y i < 0
      · have hyle : y i ≤ a * y i := by nlinarith
        exact lt_of_lt_of_le hyi.1 hyle
      · have hy_nonneg : 0 ≤ y i := le_of_not_gt hneg
        have hprod_nonneg : 0 ≤ a * y i := mul_nonneg ha.le hy_nonneg
        linarith
    · change a * y i < 1
      by_cases hneg : y i < 0
      · have hprod_neg : a * y i < 0 := mul_neg_of_pos_of_neg ha hneg
        linarith
      · have hlt_a : a * y i < a * 1 := mul_lt_mul_of_pos_left hyi.2 ha
        have ha_le_one : a * 1 ≤ 1 := by simpa using ha1
        exact lt_of_lt_of_le hlt_a ha_le_one
  · intro i hi
    exact mul_ne_zero ha.ne' (hy.2.2.2 i hi)

private theorem loewnerMatrix_comp_const_mul_eq_smul
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    loewnerMatrix (n := n) (fun x : ℝ => f (a * x)) y =
      a • loewnerMatrix (n := n) f (fun i : Fin (n + 1) => a * y i) := by
  ext i j
  by_cases hij : y i = y j
  · have hymem : a * y i ∈ Set.Ioo (-1 : ℝ) 1 :=
      (pointsHyp_const_mul_of_pos_of_le_one ha ha1 hy).2.2.1 i
    have hlin : HasDerivAt (fun x : ℝ => a * x) a (y i) := by
      simpa using (hasDerivAt_id (y i)).const_mul a
    have hdf := (differentiableAt_of_globalStrictPosDef hf hymem).hasDerivAt
    have hcomp : HasDerivAt (fun x : ℝ => f (a * x))
        (a * deriv f (a * y i)) (y i) := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hdf.comp (y i) hlin
    simp [loewnerMatrix, loewnerKernel, hij.symm, hcomp.deriv]
  · have hscaled : a * y i ≠ a * y j := by
      intro h
      exact hij (mul_left_cancel₀ ha.ne' h)
    have hsub : y i - y j ≠ 0 := sub_ne_zero.mpr hij
    simp [loewnerMatrix, loewnerKernel_eq_div (f := fun x : ℝ => f (a * x)) hij,
      loewnerKernel_eq_div (f := f) hscaled]
    field_simp [ha.ne', hsub]

/-- Positive scalar shrink of the argument preserves the strict Löwner input. -/
theorem globalStrictPosDef_comp_const_mul_of_globalStrictPosDef
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    GlobalStrictPosDef (fun x : ℝ => f (a * x)) := by
  intro n y hy
  have hscaled := hf n (fun i : Fin (n + 1) => a * y i)
    (pointsHyp_const_mul_of_pos_of_le_one ha ha1 hy)
  rw [loewnerMatrix_comp_const_mul_eq_smul hf ha ha1 hy]
  exact hscaled.smul (α := ℝ) ha

private theorem loewnerMatrix_add_const_mul_eq
    {f g : ℝ → ℝ} (hf : GlobalStrictPosDef f) (hg : GlobalStrictPosDef g)
    (ε : ℝ) {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    loewnerMatrix (n := n) (fun x : ℝ => f x + ε * g x) y =
      loewnerMatrix (n := n) f y + ε • loewnerMatrix (n := n) g y := by
  ext i j
  by_cases hij : y i = y j
  · have hymem : y i ∈ Set.Ioo (-1 : ℝ) 1 := hy.2.2.1 i
    have hdf := (differentiableAt_of_globalStrictPosDef hf hymem).hasDerivAt
    have hdg := (differentiableAt_of_globalStrictPosDef hg hymem).hasDerivAt
    have hsum : HasDerivAt (fun x : ℝ => f x + ε * g x)
        (deriv f (y i) + ε * deriv g (y i)) (y i) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdf.add (hdg.const_mul ε)
    simp [loewnerMatrix, loewnerKernel, hij.symm, hsum.deriv]
  · have hsub : y i - y j ≠ 0 := sub_ne_zero.mpr hij
    simp [loewnerMatrix, loewnerKernel_eq_div (f := fun x : ℝ => f x + ε * g x) hij,
      loewnerKernel_eq_div (f := f) hij, loewnerKernel_eq_div (f := g) hij]
    field_simp [hsub]
    ring

/-- Adding a positive multiple of a strict Löwner input preserves strictness. -/
theorem globalStrictPosDef_add_pos_const_mul_of_globalStrictPosDef
    {f g : ℝ → ℝ} (hf : GlobalStrictPosDef f) (hg : GlobalStrictPosDef g)
    {ε : ℝ} (hε : 0 < ε) :
    GlobalStrictPosDef (fun x : ℝ => f x + ε * g x) := by
  intro n y hy
  rw [loewnerMatrix_add_const_mul_eq hf hg ε hy]
  exact (hf n y hy).add (((hg n y hy).smul (α := ℝ) hε))

/--
The concrete Theorem 20.1 approximant is strict once `g₀` is strict and the
parameters satisfy `0 < ε` and `0 < δ < 1`.
-/
theorem bookSmoothApprox_globalStrictPosDef_of_globalStrictPosDef_of_g0_strict
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    (hg0 : GlobalStrictPosDef bookG0)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    GlobalStrictPosDef (bookSmoothApprox f ε δ) := by
  have ha_pos : 0 < 1 - δ := by linarith [hδ.2]
  have ha_le : 1 - δ ≤ 1 := by linarith [hδ.1.le]
  have hscaled :
      GlobalStrictPosDef (fun x : ℝ => f ((1 - δ) * x)) :=
    globalStrictPosDef_comp_const_mul_of_globalStrictPosDef hf ha_pos ha_le
  simpa [bookSmoothApprox] using
    globalStrictPosDef_add_pos_const_mul_of_globalStrictPosDef hscaled hg0 hε
end

end Quantum.TraceInequality.Loewner
