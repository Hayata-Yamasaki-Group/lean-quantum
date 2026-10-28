import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.TwoThreePointDiagnostics
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Chapter 20 generic forward finite-difference limit

This file contains the generic confluent-diagonal limit used by the
finite-order regularity ladder.  The former fixed C7/C9 pilot sources have
been deleted in favor of this generic top-coefficient source.
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

private lemma natCast_withTopENat_le {m n : ℕ} (h : m ≤ n) :
    (m : WithTop ℕ∞) ≤ (n : ℕ) :=
  WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

private lemma natCast_withTopENat_lt {m n : ℕ} (h : m < n) :
    (m : WithTop ℕ∞) < (n : ℕ) :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)

/-- The order-3 Taylor polynomial for `f` on `(-1,1)` at `x + h`. -/
lemma taylor3_eval_Ioo {f : ℝ → ℝ} {x h : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    taylorWithinEval f 3 (Set.Ioo (-1 : ℝ) 1) x (x + h) =
      f x +
        h * deriv f x +
          h ^ 2 / 2 * (deriv^[1] (deriv f)) x +
            h ^ 3 / 6 * (deriv^[2] (deriv f)) x := by
  rw [taylor_within_apply]
  simp [iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDeriv_eq_iterate]
  norm_num [Finset.sum_range_succ]
  ring_nf

/-- The order-5 Taylor polynomial for `f` on `(-1,1)` at `x + h`. -/
lemma taylor5_eval_Ioo {f : ℝ → ℝ} {x h : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    taylorWithinEval f 5 (Set.Ioo (-1 : ℝ) 1) x (x + h) =
      f x +
        h * deriv f x +
          h ^ 2 / 2 * (deriv^[1] (deriv f)) x +
            h ^ 3 / 6 * (deriv^[2] (deriv f)) x +
              h ^ 4 / 24 * (deriv^[3] (deriv f)) x +
                h ^ 5 / 120 * (deriv^[4] (deriv f)) x := by
  rw [taylor_within_apply]
  simp [iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDeriv_eq_iterate]
  norm_num [Finset.sum_range_succ]
  ring_nf

/-- As `h → 0+`, the translated point `x + h` tends to `x` within `(-1,1)`. -/
lemma tendsto_add_right_nhdsWithin_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun h : ℝ => x + h) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioo (-1 : ℝ) 1] x) := by
  have hnhds :
      Tendsto (fun h : ℝ => x + h) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := x)).add hid
  have hmem :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), x + h ∈ Set.Ioo (-1 : ℝ) 1 :=
    hnhds (isOpen_Ioo.mem_nhds hx)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hmem⟩

/-- As `h → 0+`, the translated point `x - h` tends to `x` within `(-1,1)`. -/
lemma tendsto_sub_right_nhdsWithin_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun h : ℝ => x - h) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioo (-1 : ℝ) 1] x) := by
  have hnhds :
      Tendsto (fun h : ℝ => x - h) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [sub_eq_add_neg] using (tendsto_const_nhds (x := x)).sub hid
  have hmem :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), x - h ∈ Set.Ioo (-1 : ℝ) 1 :=
    hnhds (isOpen_Ioo.mem_nhds hx)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hmem⟩

/-- As `h → 0+`, the affine point `x + c * h` tends to `x` within `(-1,1)`. -/
lemma tendsto_affine_nhdsWithin_Ioo {x c : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun h : ℝ => x + c * h) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioo (-1 : ℝ) 1] x) := by
  have hzero : Tendsto (fun h : ℝ => c * h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := c)).mul hid
  have hnhds :
      Tendsto (fun h : ℝ => x + c * h) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add hzero
  have hmem :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), x + c * h ∈ Set.Ioo (-1 : ℝ) 1 :=
    hnhds (isOpen_Ioo.mem_nhds hx)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hmem⟩

/--
The Taylor remainder of a `C^n` function, evaluated along `x + c * h`, is
`o(h^n)` as `h → 0+`.
-/
lemma taylor_remainder_scaled_tendsto
    {f : ℝ → ℝ} {n : ℕ}
    (hC : ContDiffOn ℝ n f (Set.Ioo (-1 : ℝ) 1))
    {x c : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (f (x + c * h) -
          taylorWithinEval f n (Set.Ioo (-1 : ℝ) 1) x (x + c * h)) / h ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards with h
    simp [taylorWithinEval_self]
  · have ht :=
      Real.taylor_tendsto (f := f) (x₀ := x) (n := n)
        (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hC
    have htcomp := ht.comp (tendsto_affine_nhdsWithin_Ioo (c := c) hx)
    have hscaled :
        Tendsto
          (fun h : ℝ =>
            c ^ n *
              ((f (x + c * h) -
                taylorWithinEval f n (Set.Ioo (-1 : ℝ) 1) x (x + c * h)) /
                  ((x + c * h) - x) ^ n))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := c ^ n)).mul htcomp
    refine Tendsto.congr' ?_ hscaled
    filter_upwards [self_mem_nhdsWithin] with h hhpos
    have hh : h ≠ 0 := ne_of_gt hhpos
    field_simp [hh, hc]
    ring

/--
The Taylor remainder for `deriv f`, evaluated along `x + c * h`, is
`o(h^n)` when `f` is `C^(n+1)`.
-/
lemma deriv_taylor_remainder_scaled_tendsto
    {f : ℝ → ℝ} {n : ℕ}
    (hC : ContDiffOn ℝ (n + 1) f (Set.Ioo (-1 : ℝ) 1))
    {x c : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (deriv f (x + c * h) -
          taylorWithinEval (deriv f) n (Set.Ioo (-1 : ℝ) 1) x
            (x + c * h)) / h ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hderivC :
      ContDiffOn ℝ n (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC.deriv_of_isOpen (m := n) isOpen_Ioo (by simp)
  exact
    taylor_remainder_scaled_tendsto
      (f := deriv f) (n := n) hderivC hx

/--
Differentiating the order-`n+1` Taylor polynomial of `f` gives the order-`n`
Taylor polynomial of `deriv f`.
-/
lemma deriv_taylorWithinEval_eq
    {f : ℝ → ℝ} {n : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun z : ℝ =>
      taylorWithinEval f (n + 1) (Set.Ioo (-1 : ℝ) 1) x z) y =
    taylorWithinEval (deriv f) n (Set.Ioo (-1 : ℝ) 1) x y := by
  let s : Set ℝ := Set.Ioo (-1 : ℝ) 1
  rw [(hasDerivAt_taylorWithinEval_succ
    (f := f) (n := n) (s := s) (x₀ := x) (x := y)).deriv]
  have hEqOn : Set.EqOn (derivWithin f s) (deriv f) s := by
    intro z hz
    exact derivWithin_of_isOpen isOpen_Ioo hz
  simp_rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  have hiter :
      iteratedDerivWithin r (derivWithin f s) s x =
        iteratedDerivWithin r (deriv f) s x :=
    iteratedDerivWithin_congr (n := r) hEqOn hx
  simp [s, hiter]

/-- The Löwner kernel of a difference is the difference of the Löwner kernels. -/
lemma loewnerKernel_sub
    {f g : ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
    loewnerKernel (fun y : ℝ => f y - g y) u v =
      loewnerKernel f u v - loewnerKernel g u v := by
  by_cases huv : u = v
  · subst v
    simp [loewnerKernel_self, hf, hg]
  · rw [loewnerKernel_eq_div (f := fun y : ℝ => f y - g y) huv,
      loewnerKernel_eq_div (f := f) huv,
      loewnerKernel_eq_div (f := g) huv]
    ring

/--
The top-coefficient forward quadratic form is additive with respect to
subtracting functions.
-/
lemma forward_topCoeffQuadratic_sub
    {k : ℕ} {f g : ℝ → ℝ} {x h : ℝ}
    (hf : ∀ i : Fin (k + 1),
      DifferentiableAt ℝ f (forwardCoeffNodes k x h i))
    (hg : ∀ i : Fin (k + 1),
      DifferentiableAt ℝ g (forwardCoeffNodes k x h i)) :
    forwardTopCoeffQuadratic k (fun y : ℝ => f y - g y) x h =
      forwardTopCoeffQuadratic k f x h -
        forwardTopCoeffQuadratic k g x h := by
  unfold forwardTopCoeffQuadratic
  simp_rw [loewnerKernel_sub (hf := hf _) (hg := hg _)]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, mul_sub, mul_left_comm]

/--
The top-coefficient forward quadratic form of the Taylor remainder tends to
zero on the positive side.
-/
lemma forward_topCoeffQuadratic_taylorRemainder_tendsto_zero
    {f : ℝ → ℝ} {k : ℕ}
    (hC : ContDiffOn ℝ (2 * k + 1) f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        forwardTopCoeffQuadratic k
          (fun y : ℝ => f y -
            taylorWithinEval f (2 * k + 1) (Set.Ioo (-1 : ℝ) 1) x y) x h)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let q : ℕ := 2 * k + 1
  let T : ℝ → ℝ := fun y : ℝ =>
    taylorWithinEval f q (Set.Ioo (-1 : ℝ) 1) x y
  let R : ℝ → ℝ := fun y : ℝ => f y - T y
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hqpos : (1 : WithTop ℕ∞) ≤ (q : ℕ) := by
    dsimp [q]
    exact natCast_withTopENat_le (by omega : 1 ≤ 2 * k + 1)
  have hqne : (2 * (k : WithTop ℕ∞) + 1) ≠ 0 := by
    norm_num
  have hvalue : ∀ c : ℝ,
      Tendsto (fun h : ℝ => R (x + c * h) / h ^ q)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro c
    simpa [R, T, q] using
      taylor_remainder_scaled_tendsto
        (f := f) (n := q) hC (x := x) (c := c) hx
  have hTderiv : ∀ y : ℝ,
      deriv T y = taylorWithinEval (deriv f) (2 * k)
        (Set.Ioo (-1 : ℝ) 1) x y := by
    intro y
    simpa [T, q] using
      deriv_taylorWithinEval_eq
        (f := f) (n := 2 * k) (x := x) (y := y) hx
  have hderivR : ∀ c : ℝ,
      Tendsto (fun h : ℝ => deriv R (x + c * h) / h ^ (2 * k))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro c
    have hbase :=
      deriv_taylor_remainder_scaled_tendsto
        (f := f) (n := 2 * k) hC (x := x) (c := c) hx
    refine Tendsto.congr' ?_ hbase
    have hmem : ∀ᶠ h in 𝓝[>] (0 : ℝ),
        x + c * h ∈ Set.Ioo (-1 : ℝ) 1 :=
      (tendsto_affine_nhdsWithin_Ioo (x := x) (c := c) hx)
        self_mem_nhdsWithin
    filter_upwards [hmem] with h hy
    have hfDiff : DifferentiableAt ℝ f (x + c * h) :=
      (hC.differentiableOn hqne (x + c * h) hy).differentiableAt
        (isOpen_Ioo.mem_nhds hy)
    have hTDiff : DifferentiableAt ℝ T (x + c * h) := by
      dsimp [T, q]
      exact (hasDerivAt_taylorWithinEval_succ
        (f := f) (n := 2 * k) (s := Set.Ioo (-1 : ℝ) 1)
        (x₀ := x) (x := x + c * h)).differentiableAt
    have hderivSub :
        deriv (fun y : ℝ => f y - T y) (x + c * h) =
          deriv f (x + c * h) - deriv T (x + c * h) := by
      simpa using deriv_sub hfDiff hTDiff
    dsimp [R]
    rw [hderivSub, hTderiv]
  have hterm : ∀ i j : Fin (k + 1),
      Tendsto
        (fun h : ℝ =>
          star (forwardTopCoeffWeights k h i) *
            (loewnerKernel R (forwardCoeffNodes k x h i)
              (forwardCoeffNodes k x h j) *
                forwardTopCoeffWeights k h j))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hd := hderivR (i.val : ℝ)
      have hconst :
          Tendsto
            (fun h : ℝ =>
              (forwardTopCoeffRawWeight k i *
                forwardTopCoeffRawWeight k i /
                  ((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ))) *
                (deriv R (x + (i.val : ℝ) * h) / h ^ (2 * k)))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hd)
      refine Tendsto.congr' ?_ hconst
      filter_upwards [self_mem_nhdsWithin] with h hhpos
      have hh : h ≠ 0 := ne_of_gt hhpos
      simp [forwardTopCoeffWeights, forwardTopCoeffRawWeight,
        forwardCoeffNodes, loewnerKernel_self]
      field_simp [hh, hfact]
      ring
    · have hval_ne : (i.val : ℝ) - (j.val : ℝ) ≠ 0 := by
        intro hsub
        apply hij
        apply Fin.ext
        exact Nat.cast_injective (sub_eq_zero.mp hsub)
      have hnodes_ne : ∀ᶠ h in 𝓝[>] (0 : ℝ),
          forwardCoeffNodes k x h i ≠
            forwardCoeffNodes k x h j := by
        filter_upwards [self_mem_nhdsWithin] with h hhpos hnode
        have hh : h ≠ 0 := ne_of_gt hhpos
        apply hval_ne
        dsimp [forwardCoeffNodes] at hnode
        have hmul : ((i.val : ℝ) - (j.val : ℝ)) * h = 0 := by
          nlinarith
        exact (mul_eq_zero.mp hmul).resolve_right hh
      have hvi := hvalue (i.val : ℝ)
      have hvj := hvalue (j.val : ℝ)
      have hdiff :
          Tendsto
            (fun h : ℝ =>
              (R (x + (i.val : ℝ) * h) / h ^ q -
                R (x + (j.val : ℝ) * h) / h ^ q))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hvi.sub hvj
      have hconst :
          Tendsto
            (fun h : ℝ =>
              (forwardTopCoeffRawWeight k i *
                forwardTopCoeffRawWeight k j /
                  (((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) *
                    ((i.val : ℝ) - (j.val : ℝ)))) *
                (R (x + (i.val : ℝ) * h) / h ^ q -
                  R (x + (j.val : ℝ) * h) / h ^ q))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hdiff)
      refine Tendsto.congr' ?_ hconst
      filter_upwards [self_mem_nhdsWithin, hnodes_ne] with h hhpos hnode_ne
      have hh : h ≠ 0 := ne_of_gt hhpos
      rw [loewnerKernel_eq_div (f := R) hnode_ne]
      simp [forwardTopCoeffWeights, forwardTopCoeffRawWeight,
        forwardCoeffNodes]
      field_simp [hh, hfact, hval_ne]
      dsimp [q]
      ring
  have hsum :
      Tendsto
        (fun h : ℝ =>
          ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
            star (forwardTopCoeffWeights k h i) *
              (loewnerKernel R (forwardCoeffNodes k x h i)
                (forwardCoeffNodes k x h j) *
                  forwardTopCoeffWeights k h j))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using
      (tendsto_finset_sum Finset.univ fun i _hi =>
        tendsto_finset_sum Finset.univ fun j _hj => hterm i j)
  have hsumNested :
      Tendsto
        (fun h : ℝ =>
          ∑ i : Fin (k + 1),
            star (forwardTopCoeffWeights k h i) *
              ∑ j : Fin (k + 1),
                loewnerKernel R (forwardCoeffNodes k x h i)
                  (forwardCoeffNodes k x h j) *
                    forwardTopCoeffWeights k h j)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ hsum
    filter_upwards with h
    simp [Finset.mul_sum]
  simpa [forwardTopCoeffQuadratic, Matrix.mulVec, dotProduct, R, T, q] using hsumNested

/--
The top-coefficient forward quadratic form converges to the confluent diagonal
derivative value from Simon Chapter 20.
-/
theorem forward_topCoeffQuadratic_tendsto_confluentDiagonal
    {f : ℝ → ℝ} {k : ℕ}
    (hC : ContDiffOn ℝ (2 * k + 1) f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun h : ℝ => forwardTopCoeffQuadratic k f x h)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((deriv^[2 * k] (deriv f)) x /
        (Nat.factorial (2 * k + 1) : ℝ))) := by
  let q : ℕ := 2 * k + 1
  let T : ℝ → ℝ := fun y : ℝ =>
    taylorWithinEval f q (Set.Ioo (-1 : ℝ) 1) x y
  have hqpos : (1 : WithTop ℕ∞) ≤ (q : ℕ) := by
    dsimp [q]
    exact natCast_withTopENat_le (by omega : 1 ≤ 2 * k + 1)
  have hqne : (2 * (k : WithTop ℕ∞) + 1) ≠ 0 := by
    norm_num
  have hrem :=
    forward_topCoeffQuadratic_taylorRemainder_tendsto_zero
      (f := f) (k := k) hC hx
  have hpoly :
      Tendsto (fun h : ℝ => forwardTopCoeffQuadratic k T x h)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((deriv^[2 * k] (deriv f)) x /
          (Nat.factorial (2 * k + 1) : ℝ))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with h hhpos
    have hh : h ≠ 0 := ne_of_gt hhpos
    simpa [T, q] using
      (forward_topCoeffQuadratic_taylorWithinEval_eq
        (f := f) (k := k) (x := x) (h := h) hx hh).symm
  have hsum :
      Tendsto
        (fun h : ℝ =>
          forwardTopCoeffQuadratic k
            (fun y : ℝ => f y -
              taylorWithinEval f (2 * k + 1) (Set.Ioo (-1 : ℝ) 1) x y) x h +
          forwardTopCoeffQuadratic k T x h)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((deriv^[2 * k] (deriv f)) x /
          (Nat.factorial (2 * k + 1) : ℝ))) := by
    simpa using hrem.add hpoly
  refine Tendsto.congr' ?_ hsum
  have hnodes : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ i : Fin (k + 1),
        forwardCoeffNodes k x h i ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine eventually_all.mpr ?_
    intro i
    simpa only [forwardCoeffNodes] using
      (tendsto_affine_nhdsWithin_Ioo
        (x := x) (c := (i.val : ℝ)) hx) self_mem_nhdsWithin
  filter_upwards [hnodes] with h hnode
  have hfDiff : ∀ i : Fin (k + 1),
      DifferentiableAt ℝ f (forwardCoeffNodes k x h i) := by
    intro i
    exact (hC.differentiableOn hqne _ (hnode i)).differentiableAt
      (isOpen_Ioo.mem_nhds (hnode i))
  have hTDiff : ∀ i : Fin (k + 1),
      DifferentiableAt ℝ T (forwardCoeffNodes k x h i) := by
    intro i
    dsimp [T, q]
    exact (hasDerivAt_taylorWithinEval_succ
      (f := f) (n := 2 * k) (s := Set.Ioo (-1 : ℝ) 1)
      (x₀ := x) (x := forwardCoeffNodes k x h i)).differentiableAt
  have hsub :=
    forward_topCoeffQuadratic_sub
      (k := k) (f := f) (g := T) (x := x) (h := h) hfDiff hTDiff
  linarith


end

end Quantum.TraceInequality.Loewner
