import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ForwardFiniteDifferenceLow
import Mathlib.Analysis.Calculus.Taylor

/-!
# Chapter 20 C5 confluent Hankel and affine transfer

This file contains the C5 Taylor/confluent Hankel limit package and affine
pullback transfer lemmas used before applying the package to Hiai
regularizations.
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

/--
For a `C⁵` function, the fourth-order Taylor remainder for the derivative
at `x + h` is `o(h^4)` from the right.
-/
lemma deriv_taylor4_remainder_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (deriv f (x + h) -
          (deriv f x +
            h * (deriv^[1] (deriv f)) x +
              h ^ 2 / 2 * (deriv^[2] (deriv f)) x +
                h ^ 3 / 6 * (deriv^[3] (deriv f)) x +
                  h ^ 4 / 24 * (deriv^[4] (deriv f)) x)) / h ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC5.deriv_of_isOpen (m := 4) isOpen_Ioo (by decide)
  have ht :=
    Real.taylor_tendsto (f := deriv f) (x₀ := x) (n := 4)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hderivC4
  have htcomp := ht.comp (tendsto_add_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  refine Eventually.of_forall ?_
  intro h
  simp [Function.comp_apply,
    iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDeriv_eq_iterate, sub_eq_add_neg]
  ring_nf

/--
For a `C⁵` function, the right secant slope has fifth-order Taylor remainder
`o(h^4)` after division by `h`.
-/
lemma secant_taylor5_remainder_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (((f (x + h) - f x) / h -
          (deriv f x +
            h / 2 * (deriv^[1] (deriv f)) x +
              h ^ 2 / 6 * (deriv^[2] (deriv f)) x +
                h ^ 3 / 24 * (deriv^[3] (deriv f)) x +
                  h ^ 4 / 120 * (deriv^[4] (deriv f)) x)) / h ^ 4))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht :=
    Real.taylor_tendsto (f := f) (x₀ := x) (n := 5)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hC5
  have htcomp := ht.comp (tendsto_add_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhne : h ≠ 0 := ne_of_gt hh
  simp only [Function.comp_apply]
  rw [taylor5_eval_Ioo (f := f) hx]
  field_simp [hhne]
  ring

/--
For a `C⁵` function, the fourth-order Taylor remainder for the derivative
at `x - h` is `o(h^4)` from the right.
-/
lemma deriv_taylor4_left_remainder_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (deriv f (x - h) -
          (deriv f x -
            h * (deriv^[1] (deriv f)) x +
              h ^ 2 / 2 * (deriv^[2] (deriv f)) x -
                h ^ 3 / 6 * (deriv^[3] (deriv f)) x +
                  h ^ 4 / 24 * (deriv^[4] (deriv f)) x)) / h ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC5.deriv_of_isOpen (m := 4) isOpen_Ioo (by decide)
  have ht :=
    Real.taylor_tendsto (f := deriv f) (x₀ := x) (n := 4)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hderivC4
  have htcomp := ht.comp (tendsto_sub_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  refine Eventually.of_forall ?_
  intro h
  simp [Function.comp_apply,
    iteratedDerivWithin_of_isOpen isOpen_Ioo hx,
    iteratedDeriv_eq_iterate, sub_eq_add_neg]
  ring_nf

/--
For a `C⁵` function, the left secant slope has fifth-order Taylor remainder
`o(h^4)` after division by `h`.
-/
lemma left_secant_taylor5_remainder_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        (((f x - f (x - h)) / h -
          (deriv f x -
            h / 2 * (deriv^[1] (deriv f)) x +
              h ^ 2 / 6 * (deriv^[2] (deriv f)) x -
                h ^ 3 / 24 * (deriv^[3] (deriv f)) x +
                  h ^ 4 / 120 * (deriv^[4] (deriv f)) x)) / h ^ 4))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht :=
    Real.taylor_tendsto (f := f) (x₀ := x) (n := 5)
      (s := Set.Ioo (-1 : ℝ) 1) (convex_Ioo (-1 : ℝ) 1) hx hC5
  have htcomp := ht.comp (tendsto_sub_right_nhdsWithin_Ioo hx)
  refine Tendsto.congr' ?_ htcomp
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhne : h ≠ 0 := ne_of_gt hh
  simp only [Function.comp_apply]
  rw [show x - h = x + (-h) by ring]
  rw [taylor5_eval_Ioo (f := f) (x := x) (h := -h) hx]
  field_simp [hhne]
  ring

/--
The central secant of a `C⁵` function has the even Taylor expansion up to order
four, with `o(h^4)` remainder.
-/
lemma central_secant_taylor5_remainder_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ =>
        ((centralSecant f x h -
          (deriv f x +
            h ^ 2 / 6 * (deriv^[2] (deriv f)) x +
              h ^ 4 / 120 * (deriv^[4] (deriv f)) x)) / h ^ 4))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let a : ℝ := deriv f x
  let b : ℝ := (deriv^[1] (deriv f)) x
  let c : ℝ := (deriv^[2] (deriv f)) x
  let d : ℝ := (deriv^[3] (deriv f)) x
  let e : ℝ := (deriv^[4] (deriv f)) x
  let RR : ℝ → ℝ := fun h =>
    (((f (x + h) - f x) / h -
      (a + h / 2 * b + h ^ 2 / 6 * c + h ^ 3 / 24 * d + h ^ 4 / 120 * e)) /
        h ^ 4)
  let RL : ℝ → ℝ := fun h =>
    (((f x - f (x - h)) / h -
      (a - h / 2 * b + h ^ 2 / 6 * c - h ^ 3 / 24 * d + h ^ 4 / 120 * e)) /
        h ^ 4)
  have hRR : Tendsto RR (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [RR, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc] using
      secant_taylor5_remainder_tendsto_C5 (f := f) hC5 hx
  have hRL : Tendsto RL (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [RL, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using
      left_secant_taylor5_remainder_tendsto_C5 (f := f) hC5 hx
  have havg :
      Tendsto (fun h : ℝ => (RR h + RL h) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hRR.add hRL).div_const (2 : ℝ)
  refine Tendsto.congr' ?_ havg
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhne : h ≠ 0 := ne_of_gt hh
  dsimp [RR, RL, a, b, c, d, e, centralSecant]
  field_simp [hhne]
  ring

/--
The symmetric three-point Löwner matrix converges to the confluent Hankel matrix
for a `C⁵` function.
-/
lemma symmThreePointConfluentMatrix_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun h : ℝ => symmThreePointConfluentMatrix f x h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (confluentLoewnerHankel3 f x)) := by
  let a : ℝ := deriv f x
  let b : ℝ := (deriv^[1] (deriv f)) x
  let c : ℝ := (deriv^[2] (deriv f)) x
  let d : ℝ := (deriv^[3] (deriv f)) x
  let e : ℝ := (deriv^[4] (deriv f)) x
  let UR : ℝ → ℝ := fun h =>
    (deriv f (x + h) - (a + h * b + h ^ 2 / 2 * c + h ^ 3 / 6 * d +
      h ^ 4 / 24 * e)) / h ^ 4
  let UL : ℝ → ℝ := fun h =>
    (deriv f (x - h) - (a - h * b + h ^ 2 / 2 * c - h ^ 3 / 6 * d +
      h ^ 4 / 24 * e)) / h ^ 4
  let VR : ℝ → ℝ := fun h =>
    (((f (x + h) - f x) / h -
      (a + h / 2 * b + h ^ 2 / 6 * c + h ^ 3 / 24 * d + h ^ 4 / 120 * e)) /
        h ^ 4)
  let VL : ℝ → ℝ := fun h =>
    (((f x - f (x - h)) / h -
      (a - h / 2 * b + h ^ 2 / 6 * c - h ^ 3 / 24 * d + h ^ 4 / 120 * e)) /
        h ^ 4)
  let VC : ℝ → ℝ := fun h =>
    ((centralSecant f x h - (a + h ^ 2 / 6 * c + h ^ 4 / 120 * e)) /
      h ^ 4)
  have hUR : Tendsto UR (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [UR, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc] using
      deriv_taylor4_remainder_tendsto_C5 (f := f) hC5 hx
  have hUL : Tendsto UL (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [UL, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using
      deriv_taylor4_left_remainder_tendsto_C5 (f := f) hC5 hx
  have hVR : Tendsto VR (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [VR, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc] using
      secant_taylor5_remainder_tendsto_C5 (f := f) hC5 hx
  have hVL : Tendsto VL (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [VL, a, b, c, d, e, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using
      left_secant_taylor5_remainder_tendsto_C5 (f := f) hC5 hx
  have hVC : Tendsto VC (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [VC, a, c, e, mul_comm, mul_left_comm, mul_assoc] using
      central_secant_taylor5_remainder_tendsto_C5 (f := f) hC5 hx
  have hhlim : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have htuple :
      Tendsto (fun h : ℝ => (((((h, UR h), UL h), VR h), VL h), VC h))
        (𝓝[>] (0 : ℝ)) (𝓝 ((((((0 : ℝ), 0), 0), 0), 0), 0)) :=
    (((((hhlim.prodMk_nhds hUR).prodMk_nhds hUL).prodMk_nhds hVR).prodMk_nhds hVL).prodMk_nhds hVC)
  let expanded : (((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ) →
      Matrix (Fin 3) (Fin 3) ℝ := fun p =>
    let h := p.1.1.1.1.1
    let uR := p.1.1.1.1.2
    let uL := p.1.1.1.2
    let vR := p.1.1.2
    let vL := p.1.2
    let vC := p.2
    Matrix.of
      (fun i j : Fin 3 =>
        match i, j with
        | 0, 0 => a
        | 0, 1 => b / 2 + h ^ 2 * d / 24 + h ^ 3 * (vR - vL) / 2
        | 1, 0 => b / 2 + h ^ 2 * d / 24 + h ^ 3 * (vR - vL) / 2
        | 0, 2 => c / 6 + h ^ 2 * e / 120 + h ^ 2 * (vL + vR) / 2
        | 2, 0 => c / 6 + h ^ 2 * e / 120 + h ^ 2 * (vL + vR) / 2
        | 1, 1 => c / 6 + h ^ 2 * e / 60 + h ^ 2 * (uL + uR - 2 * vC) / 4
        | 1, 2 => d / 24 + h * (uR - uL + 2 * vL - 2 * vR) / 4
        | 2, 1 => d / 24 + h * (uR - uL + 2 * vL - 2 * vR) / 4
        | 2, 2 => e / 120 + (uL + uR + 2 * vC - 4 * vL - 4 * vR) / 4)
  have hcont :
      ContinuousAt expanded ((((((0 : ℝ), 0), 0), 0), 0), 0) := by
    exact (continuous_matrix
      (fun i j => by
        fin_cases i <;> fin_cases j <;> dsimp [expanded] <;> fun_prop)).continuousAt
  have htarget :
      expanded ((((((0 : ℝ), 0), 0), 0), 0), 0) =
        confluentLoewnerHankel3 f x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [expanded, confluentLoewnerHankel3, a, b, c, d, e]
  have hexp :
      Tendsto
        (fun h : ℝ => expanded (((((h, UR h), UL h), VR h), VL h), VC h))
        (𝓝[>] (0 : ℝ))
        (𝓝 (confluentLoewnerHankel3 f x)) := by
    simpa [htarget] using hcont.tendsto.comp htuple
  refine Tendsto.congr' ?_ hexp
  filter_upwards [self_mem_nhdsWithin] with h hhpos
  have hhne : h ≠ 0 := ne_of_gt hhpos
  symm
  ext i j
  fin_cases i
  all_goals fin_cases j
  · change symmThreePointConfluentMatrix f x h 0 0 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 0 0
    rw [symmThreePointConfluentMatrix_apply_zero_zero]
    simp [expanded, a]
  · change symmThreePointConfluentMatrix f x h 0 1 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 0 1
    rw [symmThreePointConfluentMatrix_apply_zero_one (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e, rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 0 2 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 0 2
    rw [symmThreePointConfluentMatrix_apply_zero_two (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e, rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 1 0 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 1 0
    rw [symmThreePointConfluentMatrix_apply_one_zero (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e, rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 1 1 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 1 1
    rw [symmThreePointConfluentMatrix_apply_one_one (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e, centralSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 1 2 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 1 2
    rw [symmThreePointConfluentMatrix_apply_one_two (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e,
      rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 2 0 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 2 0
    rw [symmThreePointConfluentMatrix_apply_two_zero (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e, rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 2 1 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 2 1
    rw [symmThreePointConfluentMatrix_apply_two_one (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e,
      rightSecant, leftSecant]
    field_simp [hhne]
    ring
  · change symmThreePointConfluentMatrix f x h 2 2 =
      expanded (((((h, UR h), UL h), VR h), VL h), VC h) 2 2
    rw [symmThreePointConfluentMatrix_apply_two_two (f := f) (x := x) (h := h) hhne]
    dsimp [expanded, UR, UL, VR, VL, VC, a, b, c, d, e,
      rightSecant, leftSecant, centralSecant]
    field_simp [hhne]
    ring

/--
The scaled symmetric three-point determinant tends to four times the confluent
Hankel determinant.
-/
theorem threePoint_det_scaled_tendsto_C5 {f : ℝ → ℝ}
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun h : ℝ => threePointSymmScaledDet f x h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (confluentLoewnerHankel3 f x).det)) := by
  have hM :=
    symmThreePointConfluentMatrix_tendsto_C5 (f := f) hC5 hx
  have hdet :
      Tendsto
        (fun h : ℝ => (symmThreePointConfluentMatrix f x h).det)
        (𝓝[>] (0 : ℝ))
        (𝓝 (confluentLoewnerHankel3 f x).det) := by
    have hdet_cont :
        ContinuousAt
          (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det)
          (confluentLoewnerHankel3 f x) :=
      continuous_id.matrix_det.continuousAt
    exact hdet_cont.tendsto.comp hM
  have hfour :
      Tendsto
        (fun h : ℝ => 4 * (symmThreePointConfluentMatrix f x h).det)
        (𝓝[>] (0 : ℝ))
        (𝓝 (4 * (confluentLoewnerHankel3 f x).det)) :=
    tendsto_const_nhds.mul hdet
  refine Tendsto.congr' ?_ hfour
  filter_upwards [self_mem_nhdsWithin] with h hhpos
  exact (threePointSymmScaledDet_eq_four_confluentMatrix_det
    (f := f) (x := x) (h := h) (ne_of_gt hhpos)).symm

/--
For a `C⁵` public Löwner-positive function, the order-three confluent Hankel
matrix is positive semidefinite.
-/
theorem confluentLoewnerHankel3_posSemidef_of_loewnerPosOnUnitInterval_C5
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (confluentLoewnerHankel3 f x).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, confluentLoewnerHankel3,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  · intro w
    have hM :=
      symmThreePointConfluentMatrix_tendsto_C5
        (f := f) hC5 hx
    have hquad_cont :
        ContinuousAt
          (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
            star w ⬝ᵥ Matrix.mulVec M w)
          (confluentLoewnerHankel3 f x) := by
      fun_prop
    have hquad_tendsto :
        Tendsto
          (fun h : ℝ =>
            star w ⬝ᵥ
              Matrix.mulVec (symmThreePointConfluentMatrix f x h) w)
          (𝓝[>] (0 : ℝ))
          (𝓝 (star w ⬝ᵥ
              Matrix.mulVec (confluentLoewnerHankel3 f x) w)) :=
      hquad_cont.tendsto.comp hM
    have hmargin : 0 < min (x + 1) (1 - x) := by
      exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
    have hsmall :
        ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min (x + 1) (1 - x) :=
      (eventually_lt_nhds hmargin).filter_mono nhdsWithin_le_nhds
    have hnonneg :
        ∀ᶠ h in 𝓝[>] (0 : ℝ),
          0 ≤
            star w ⬝ᵥ
              Matrix.mulVec (symmThreePointConfluentMatrix f x h) w := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with h hhpos hhsmall
      exact
        (symmThreePointConfluentMatrix_posSemidef_of_loewnerPosOnUnitInterval
          (f := f) hpos hx hhpos hhsmall).dotProduct_mulVec_nonneg w
    exact ge_of_tendsto hquad_tendsto hnonneg

/--
For a `C⁵` public Löwner-positive function, the order-three confluent Hankel
determinant is nonnegative.
-/
theorem confluentLoewnerHankel3_det_nonneg_of_loewnerPosOnUnitInterval_C5
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hC5 : ContDiffOn ℝ 5 f (Set.Ioo (-1 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ (confluentLoewnerHankel3 f x).det :=
  hankel3_det_nonneg_of_threePoint_symm_det_scaled_tendsto
    (f := f) hpos hx
    (threePoint_det_scaled_tendsto_C5 (f := f) hC5 hx)

/--
The confluent Hankel matrix depends only on the germ of the function at the
base point.
-/
lemma confluentLoewnerHankel3_congr_nhds
    {f g : ℝ → ℝ} {x : ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    confluentLoewnerHankel3 f x =
      confluentLoewnerHankel3 g x := by
  ext i j
  have hderiv := hfg.iteratedDeriv_eq (i.val + j.val + 1)
  simpa [confluentLoewnerHankel3, iteratedDeriv_eq_iterate,
    Function.iterate_succ_apply, Nat.succ_eq_add_one] using congrArg
      (fun y : ℝ => y / ((Nat.factorial (i.val + j.val + 1) : ℕ) : ℝ)) hderiv

/--
Iterated derivatives of an affine pullback scale by `r^n` for any order within
the available smoothness.
-/
lemma affinePullback_iteratedDeriv_eq_anyOrder
    {F : ℝ → ℝ} {M n : ℕ} (hF : ContDiff ℝ M F)
    (x r u : ℝ) (hn : n ≤ M) :
    iteratedDeriv n (fun v : ℝ => F (x + r * v)) u =
      r ^ n * iteratedDeriv n F (x + r * u) := by
  have hn' : (n : WithTop ℕ∞) ≤ (M : ℕ) := by
    exact natCast_withTopENat_le hn
  have hshift : ContDiff ℝ n (fun t : ℝ => F (x + t)) := by
    have hF' : ContDiff ℝ n F := hF.of_le hn'
    have hlin : ContDiff ℝ n (fun t : ℝ => x + t) := by
      fun_prop
    simpa [Function.comp_def] using hF'.comp hlin
  have hmul := congrFun
    (iteratedDeriv_comp_const_mul (n := n) (f := fun t : ℝ => F (x + t)) hshift r) u
  have hadd := congrFun (iteratedDeriv_comp_const_add (𝕜 := ℝ) n F x) (r * u)
  rw [hadd] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/--
Undoing the affine pullback on the confluent Hankel matrix is a positive scalar
and diagonal congruence.  This is the PSD analogue of the determinant scaling
identity below.
-/
theorem confluentLoewnerHankel3_eq_inv_smul_inverseDiagonal_affinePullback
    {F : ℝ → ℝ} (hF : ContDiff ℝ 5 F) {x r u : ℝ} (hr : r ≠ 0) :
    confluentLoewnerHankel3 F (x + r * u) =
      r⁻¹ •
        ((Matrix.diagonal (fun i : Fin 3 => (r ^ i.val)⁻¹)) *
          confluentLoewnerHankel3 (fun v : ℝ => F (x + r * v)) u *
            (Matrix.diagonal (fun i : Fin 3 => (r ^ i.val)⁻¹))) := by
  let z : ℝ := x + r * u
  let Dinv : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal (fun i : Fin 3 => (r ^ i.val)⁻¹)
  have h1 : deriv (fun v : ℝ => F (x + r * v)) u = r * deriv F z := by
    simpa [z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 1) hF x r u (by norm_num)
  have h2 :
      deriv (deriv (fun v : ℝ => F (x + r * v))) u =
        r ^ 2 * deriv (deriv F) z := by
    simpa [z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 2) hF x r u (by norm_num)
  have h3 : deriv (deriv (deriv (fun v : ℝ => F (x + r * v)))) u =
      r ^ 3 * deriv (deriv (deriv F)) z := by
    simpa [z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 3) hF x r u (by norm_num)
  have h4 :
      deriv (deriv (deriv (deriv (fun v : ℝ => F (x + r * v))))) u =
      r ^ 4 * deriv (deriv (deriv (deriv F))) z := by
    simpa [z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 4) hF x r u (by norm_num)
  have h5 :
      deriv (deriv (deriv (deriv (deriv (fun v : ℝ => F (x + r * v)))))) u =
      r ^ 5 * deriv (deriv (deriv (deriv (deriv F)))) z := by
    simpa [z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 5) hF x r u (by norm_num)
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals
    simp [confluentLoewnerHankel3, Matrix.mul_apply,
      Matrix.diagonal, z, h1, h2, h3, h4, h5, hr]
  all_goals
    field_simp [hr]

/--
Positive semidefiniteness of the affine-pullback confluent Hankel matrix
transfers back to the original point.
-/
theorem confluentLoewnerHankel3_posSemidef_of_affinePullback_posSemidef
    {F : ℝ → ℝ} (hF : ContDiff ℝ 5 F) {x r u : ℝ} (hr : 0 < r)
    (hA :
      (confluentLoewnerHankel3
        (fun v : ℝ => F (x + r * v)) u).PosSemidef) :
    (confluentLoewnerHankel3 F (x + r * u)).PosSemidef := by
  let Dinv : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal (fun i : Fin 3 => (r ^ i.val)⁻¹)
  have hconj : (Dinv * confluentLoewnerHankel3
        (fun v : ℝ => F (x + r * v)) u * Dinv).PosSemidef := by
    simpa [Dinv] using hA.conjTranspose_mul_mul_same Dinv
  have hscaled :
      (r⁻¹ •
        (Dinv * confluentLoewnerHankel3
          (fun v : ℝ => F (x + r * v)) u * Dinv)).PosSemidef :=
    hconj.smul (inv_nonneg.2 hr.le)
  have heq :=
    confluentLoewnerHankel3_eq_inv_smul_inverseDiagonal_affinePullback
      (F := F) hF (x := x) (r := r) (u := u) hr.ne'
  simpa [Dinv, heq]

/--
For a `C⁵` function, the confluent three-point Hankel determinant scales under
the affine pullback `u ↦ x + r*u` by the expected factor `r^9`.
-/
theorem confluentLoewnerHankel3_affinePullback_det_eq
    {F : ℝ → ℝ} (hF : ContDiff ℝ 5 F) (x r u : ℝ) :
    (confluentLoewnerHankel3 (fun v : ℝ => F (x + r * v)) u).det =
      r ^ 9 * (confluentLoewnerHankel3 F (x + r * u)).det := by
  let A : ℝ → ℝ := fun v : ℝ => F (x + r * v)
  let z : ℝ := x + r * u
  have h1 : deriv A u = r * deriv F z := by
    simpa [A, z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 1) hF x r u (by norm_num)
  have h2 : deriv (deriv A) u = r ^ 2 * deriv (deriv F) z := by
    simpa [A, z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 2) hF x r u (by norm_num)
  have h3 : deriv (deriv (deriv A)) u =
      r ^ 3 * deriv (deriv (deriv F)) z := by
    simpa [A, z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 3) hF x r u (by norm_num)
  have h4 : deriv (deriv (deriv (deriv A))) u =
      r ^ 4 * deriv (deriv (deriv (deriv F))) z := by
    simpa [A, z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 4) hF x r u (by norm_num)
  have h5 : deriv (deriv (deriv (deriv (deriv A)))) u =
      r ^ 5 * deriv (deriv (deriv (deriv (deriv F)))) z := by
    simpa [A, z, iteratedDeriv_eq_iterate] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := F) (M := 5) (n := 5) hF x r u (by norm_num)
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  norm_num [confluentLoewnerHankel3, A, z]
  rw [h1, h2, h3, h4, h5]
  ring

end

end Quantum.TraceInequality.Loewner
