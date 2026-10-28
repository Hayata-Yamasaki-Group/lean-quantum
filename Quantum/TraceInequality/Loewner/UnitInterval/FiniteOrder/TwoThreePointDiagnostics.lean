import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.HiaiSlopeCore
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 20 two- and three-point determinant diagnostics

This file contains the principal two- and three-point Löwner kernel diagnostics and
related symmetric determinant packages used by the finite-order regularity
ladder.
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

/-!
### Public regularity audit

Hiai Theorem 2.4.1 (the Japanese excerpt's Theorem 2.6(1)) assumes
`2`-monotonicity: order monotonicity for arbitrary self-adjoint `2 × 2`
matrices.  Its proof derives the four-point determinant inequality from an
actual matrix comparison `A ≤ B`.

The public hypothesis `LoewnerPosOnUnitInterval f` used in this file is
different: it provides differentiability and finite Löwner-kernel positive
semidefiniteness.  Therefore we do not declare a broad public `C¹` theorem by
applying Hiai's `2`-monotone theorem directly to `f`.  The non-circular book
route regularizes `f` first: prove that the mollified functions `fε` have the
required smooth `2`-monotone input, run Hiai's smooth argument for `fε`, and
only then let `ε ↓ 0` to obtain continuity of `deriv f`.

The direct two/three-point diagnostics below do not manufacture
`2`-monotonicity from the opposite implication, the integral representation,
or the normalized main theorem, since that would be circular.  The active
public route instead uses the completed regularization ladder.  The four-point
cross-minor lemmas are retained as conditional diagnostics; they are not used
as the public PSD extraction target, since generic PSD does not control
non-principal minors.
-/

/-- The real Löwner kernel is symmetric in its two nodes. -/
lemma loewnerKernel_symm (f : ℝ → ℝ) (x y : ℝ) :
    loewnerKernel f x y = loewnerKernel f y x := by
  by_cases h : y = x
  · subst y
    rfl
  · calc
      loewnerKernel f x y = slope f x y :=
        (slope_eq_loewnerKernel_of_ne (f := f) h).symm
      _ = slope f y x := slope_comm f x y
      _ = loewnerKernel f y x :=
        slope_eq_loewnerKernel_of_ne (f := f) (Ne.symm h)

/--
The principal `2 × 2` minor of a public Löwner kernel matrix is nonnegative.
This is the determinant extraction used by the smooth `C³` Hiai body; unlike
the earlier four-point diagnostics, it only uses a genuine principal minor.
-/
theorem loewnerKernel_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : x ≠ y) :
    0 ≤
      loewnerKernel f x x * loewnerKernel f y y -
        loewnerKernel f x y * loewnerKernel f y x := by
  let nodes : Fin 2 → ℝ := fun i => if i = 0 then x else y
  have hnodes : ∀ i, nodes i ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro i
    fin_cases i <;> simp [nodes, hx, hy]
  have hinj : Function.Injective nodes := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hxy' : x = y := by
        simpa [nodes] using hij
      exact False.elim (hxy hxy')
    · have hyx' : y = x := by
        simpa [nodes] using hij
      exact False.elim (hxy hyx'.symm)
    · rfl
  have hpsd := hpos.posSemidef 2 nodes hnodes hinj
  have hdetc :
      0 ≤
        (Matrix.of
          (fun i j : Fin 2 =>
            (loewnerKernel f (nodes i) (nodes j) : ℂ))).det :=
    Matrix.PosSemidef.det_nonneg hpsd
  rw [Matrix.det_fin_two] at hdetc
  have hdetc' :
      0 ≤
        ((loewnerKernel f x x * loewnerKernel f y y -
          loewnerKernel f x y * loewnerKernel f y x : ℝ) : ℂ) := by
    simpa [nodes, Matrix.of_apply, Complex.ofReal_mul, Complex.ofReal_sub] using hdetc
  exact (RCLike.ofReal_nonneg (K := ℂ)).1 hdetc'

/-- Principal two-point determinant inequality in secant-slope form. -/
theorem slope_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : x ≠ y) :
    0 ≤ deriv f x * deriv f y - slope f x y * slope f x y := by
  have hdet :=
    loewnerKernel_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
      hpos hx hy hxy
  have hyx : y ≠ x := hxy.symm
  simpa [loewnerKernel_self,
    ← slope_eq_loewnerKernel_of_ne (f := f) hyx,
    ← slope_eq_loewnerKernel_of_ne (f := f) hxy,
    slope_comm f y x] using hdet

/-- Principal two-point determinant inequality in explicit difference-quotient form. -/
theorem diffQuot_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : x ≠ y) :
    0 ≤ deriv f x * deriv f y - ((f y - f x) / (y - x)) ^ 2 := by
  have hdet :=
    slope_twoPoint_det_nonneg_of_loewnerPosOnUnitInterval
      hpos hx hy hxy
  simpa [slope_def_field, pow_two] using hdet

/--
The public PSD hypothesis restricted to three interior nodes.  This is the
principal `3 × 3` source used, through the confluent Hankel determinant, by the
local third-derivative bounds of the finite-order regularity proof.
-/
theorem loewnerKernel_threePoint_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    (Matrix.of
      (fun i j : Fin 3 => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef :=
  hpos.posSemidef 3 x hx hinj

/-- Real-valued PSD form of the principal three-point public Löwner matrix. -/
theorem loewnerKernel_threePoint_real_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    (Matrix.of
      (fun i j : Fin 3 => loewnerKernel f (x i) (x j))).PosSemidef := by
  have hpsdC :=
    loewnerKernel_threePoint_posSemidef_of_loewnerPosOnUnitInterval
      (f := f) hpos hx hinj
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.of_apply,
      loewnerKernel_symm]
  · intro w
    have hquadC :=
      hpsdC.dotProduct_mulVec_nonneg (fun i : Fin 3 => (w i : ℂ))
    have hquadC' :
        0 ≤
          ((star w ⬝ᵥ
            (Matrix.mulVec
              (Matrix.of
                (fun i j : Fin 3 => loewnerKernel f (x i) (x j))) w) : ℝ) : ℂ) := by
      simpa [Matrix.mulVec, dotProduct, Matrix.of_apply,
        Complex.ofReal_sum, Complex.ofReal_mul] using hquadC
    exact (RCLike.ofReal_nonneg (K := ℂ)).1 hquadC'

/-- The determinant of the principal three-point public Löwner matrix is nonnegative. -/
theorem loewnerKernel_threePoint_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    0 ≤
      (Matrix.of
        (fun i j : Fin 3 => (loewnerKernel f (x i) (x j) : ℂ))).det :=
  Matrix.PosSemidef.det_nonneg
    (loewnerKernel_threePoint_posSemidef_of_loewnerPosOnUnitInterval
      hpos hx hinj)

/-- Real-valued determinant form of the principal three-point public Löwner matrix. -/
theorem loewnerKernel_threePoint_real_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    0 ≤
      (Matrix.of
        (fun i j : Fin 3 => loewnerKernel f (x i) (x j))).det := by
  have hdetc :=
    loewnerKernel_threePoint_det_nonneg_of_loewnerPosOnUnitInterval
      (f := f) hpos hx hinj
  rw [Matrix.det_fin_three] at hdetc
  have hdetc' :
      0 ≤
        (((Matrix.of
          (fun i j : Fin 3 => loewnerKernel f (x i) (x j))).det : ℝ) : ℂ) := by
    rw [Matrix.det_fin_three]
    simpa [Matrix.of_apply, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_add] using hdetc
  exact (RCLike.ofReal_nonneg (K := ℂ)).1 hdetc'

/-- Symmetric three-point nodes `x - h`, `x`, `x + h`. -/
def symmThreePointNodes (x h : ℝ) : Fin 3 → ℝ
  | 0 => x - h
  | 1 => x
  | 2 => x + h

/-- The real public Löwner matrix on the symmetric nodes `x - h`, `x`, `x + h`. -/
def symmThreePointLoewnerMatrix
    (f : ℝ → ℝ) (x h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    (fun i j : Fin 3 =>
      loewnerKernel f
        (symmThreePointNodes x h i)
        (symmThreePointNodes x h j))

/-- The `h^6`-scaled symmetric three-point determinant. -/
def threePointSymmScaledDet (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (symmThreePointLoewnerMatrix f x h).det / h ^ 6

/--
The confluent `3 × 3` Hankel matrix expected in the symmetric three-point
determinant limit.
-/
def confluentLoewnerHankel3
    (f : ℝ → ℝ) (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of
    (fun i j : Fin 3 =>
      (deriv^[i.val + j.val] (deriv f)) x /
        ((Nat.factorial (i.val + j.val + 1) : ℕ) : ℝ))

/-- The upper-left diagonal entry of the confluent Hankel matrix is `f'`. -/
lemma confluentLoewnerHankel3_apply_zero_zero
    (f : ℝ → ℝ) (x : ℝ) :
    confluentLoewnerHankel3 f x 0 0 = deriv f x := by
  norm_num [confluentLoewnerHankel3]

/-- The middle diagonal entry of the confluent Hankel matrix is `f''' / 6`. -/
lemma confluentLoewnerHankel3_apply_one_one
    (f : ℝ → ℝ) (x : ℝ) :
    confluentLoewnerHankel3 f x 1 1 =
      deriv (deriv (deriv f)) x / 6 := by
  norm_num [confluentLoewnerHankel3]

/-- The lower-right diagonal entry of the confluent Hankel matrix is `f''''' / 120`. -/
lemma confluentLoewnerHankel3_apply_two_two
    (f : ℝ → ℝ) (x : ℝ) :
    confluentLoewnerHankel3 f x 2 2 =
      deriv (deriv (deriv (deriv (deriv f)))) x / 120 := by
  norm_num [confluentLoewnerHankel3]

/--
Bounding the middle diagonal Hankel entry bounds the ordinary third derivative.
This is the algebraic bridge used by the conditional Hankel producer below.
-/
lemma abs_thirdDeriv_le_of_confluentLoewnerHankel3_apply_one_one_bound
    {F : ℝ → ℝ} {z C : ℝ}
    (hentry : |confluentLoewnerHankel3 F z 1 1| ≤ C) :
    |deriv (deriv (deriv F)) z| ≤ 6 * C := by
  have hdiv : |deriv (deriv (deriv F)) z / 6| ≤ C := by
    simpa [confluentLoewnerHankel3_apply_one_one] using hentry
  have hdiv' : |deriv (deriv (deriv F)) z| / 6 ≤ C := by
    simpa [abs_div] using hdiv
  nlinarith [abs_nonneg (deriv (deriv (deriv F)) z), hdiv']

/--
Finite-difference change-of-basis matrix for the symmetric nodes.  The columns
extract the center value, the central first difference, and one half of the
central second difference.
-/
def symmThreePointConfluentTransform
    (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ
  | 0, 0 => 0
  | 0, 1 => -1 / (2 * h)
  | 0, 2 => 1 / (2 * h ^ 2)
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => -1 / h ^ 2
  | 2, 0 => 0
  | 2, 1 => 1 / (2 * h)
  | 2, 2 => 1 / (2 * h ^ 2)

/-- The symmetric Löwner matrix in the confluent finite-difference basis. -/
def symmThreePointConfluentMatrix
    (f : ℝ → ℝ) (x h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (symmThreePointConfluentTransform h).transpose *
    symmThreePointLoewnerMatrix f x h *
      symmThreePointConfluentTransform h

/-- Determinant of the symmetric three-point confluent change-of-basis matrix. -/
lemma symmThreePointConfluentTransform_det
    {h : ℝ} (hh : h ≠ 0) :
    (symmThreePointConfluentTransform h).det = 1 / (2 * h ^ 3) := by
  rw [Matrix.det_fin_three]
  simp [symmThreePointConfluentTransform]
  field_simp [hh]
  ring

/-- Determinant of the transformed matrix is `det U ^ 2` times the original one. -/
lemma symmThreePointConfluentMatrix_det_eq
    (f : ℝ → ℝ) (x h : ℝ) :
    (symmThreePointConfluentMatrix f x h).det =
      (symmThreePointConfluentTransform h).det ^ 2 *
        (symmThreePointLoewnerMatrix f x h).det := by
  rw [symmThreePointConfluentMatrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  ring

/-- The `h^6` scaled symmetric determinant is four times the confluent determinant. -/
lemma threePointSymmScaledDet_eq_four_confluentMatrix_det
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    threePointSymmScaledDet f x h =
      4 * (symmThreePointConfluentMatrix f x h).det := by
  rw [symmThreePointConfluentMatrix_det_eq,
    symmThreePointConfluentTransform_det hh]
  dsimp [threePointSymmScaledDet]
  field_simp [hh]
  ring

/-- Right secant from `x` to `x + h`. -/
def rightSecant (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- Left secant from `x - h` to `x`. -/
def leftSecant (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f x - f (x - h)) / h

/-- Central secant from `x - h` to `x + h`. -/
def centralSecant (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f (x - h)) / (2 * h)

/-- Diagonal entries of the symmetric three-point Löwner matrix are derivatives. -/
lemma symmThreePointLoewnerMatrix_apply_self
    (f : ℝ → ℝ) (x h : ℝ) (i : Fin 3) :
    symmThreePointLoewnerMatrix f x h i i =
      deriv f (symmThreePointNodes x h i) := by
  simp [symmThreePointLoewnerMatrix, loewnerKernel_self]

/-- The `(0,1)` entry of the symmetric Löwner matrix is the left secant. -/
lemma symmThreePointLoewnerMatrix_apply_zero_one
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 0 1 =
      leftSecant f x h := by
  have hne : x - h ≠ x := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f (x - h) x = leftSecant f x h
  rw [leftSecant, loewnerKernel_eq_div (f := f) hne]
  field_simp [hh]
  ring

/-- The `(1,0)` entry of the symmetric Löwner matrix is the left secant. -/
lemma symmThreePointLoewnerMatrix_apply_one_zero
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 1 0 =
      leftSecant f x h := by
  have hne : x ≠ x - h := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f x (x - h) = leftSecant f x h
  rw [leftSecant, loewnerKernel_eq_div (f := f) hne]
  field_simp [hh]
  ring

/-- The `(1,2)` entry of the symmetric Löwner matrix is the right secant. -/
lemma symmThreePointLoewnerMatrix_apply_one_two
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 1 2 =
      rightSecant f x h := by
  have hne : x ≠ x + h := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f x (x + h) = rightSecant f x h
  rw [rightSecant, loewnerKernel_eq_div (f := f) hne]
  field_simp [hh]
  ring

/-- The `(2,1)` entry of the symmetric Löwner matrix is the right secant. -/
lemma symmThreePointLoewnerMatrix_apply_two_one
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 2 1 =
      rightSecant f x h := by
  have hne : x + h ≠ x := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f (x + h) x = rightSecant f x h
  rw [rightSecant, loewnerKernel_eq_div (f := f) hne]
  field_simp [hh]
  ring

/-- The `(0,2)` entry of the symmetric Löwner matrix is the central secant. -/
lemma symmThreePointLoewnerMatrix_apply_zero_two
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 0 2 =
      centralSecant f x h := by
  have hne : x - h ≠ x + h := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f (x - h) (x + h) = centralSecant f x h
  rw [centralSecant, loewnerKernel_eq_div (f := f) hne]
  have hden : x - h - (x + h) ≠ 0 := by
    intro hzero
    exact hh (by linarith)
  field_simp [hh, hden]
  ring

/-- The `(2,0)` entry of the symmetric Löwner matrix is the central secant. -/
lemma symmThreePointLoewnerMatrix_apply_two_zero
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointLoewnerMatrix f x h 2 0 =
      centralSecant f x h := by
  have hne : x + h ≠ x - h := by
    intro hx'
    exact hh (by linarith)
  rw [symmThreePointLoewnerMatrix, Matrix.of_apply]
  change loewnerKernel f (x + h) (x - h) = centralSecant f x h
  rw [centralSecant, loewnerKernel_eq_div (f := f) hne]
  have hden : x + h - (x - h) ≠ 0 := by
    intro hzero
    exact hh (by linarith)
  field_simp [hh, hden]
  ring

/-- The `(0,0)` confluent entry is the center derivative `f' x`. -/
lemma symmThreePointConfluentMatrix_apply_zero_zero
    {f : ℝ → ℝ} {x h : ℝ} :
    symmThreePointConfluentMatrix f x h 0 0 = deriv f x := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]

/-- The `(0,1)` confluent entry is the centered first difference of secants. -/
lemma symmThreePointConfluentMatrix_apply_zero_one
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 0 1 =
      (rightSecant f x h - leftSecant f x h) / (2 * h) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_one_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_two (f := f) (x := x) (h := h) hh]
  field_simp [hh]
  ring

/-- The `(1,0)` confluent entry is the same centered first difference of secants. -/
lemma symmThreePointConfluentMatrix_apply_one_zero
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 1 0 =
      (rightSecant f x h - leftSecant f x h) / (2 * h) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_one (f := f) (x := x) (h := h) hh]
  field_simp [hh]
  ring

/-- The `(0,2)` confluent entry is the centered second-difference expression. -/
lemma symmThreePointConfluentMatrix_apply_zero_two
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 0 2 =
      (leftSecant f x h + rightSecant f x h - 2 * deriv f x) /
        (2 * h ^ 2) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_one_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- The `(2,0)` confluent entry is the same centered second-difference expression. -/
lemma symmThreePointConfluentMatrix_apply_two_zero
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 2 0 =
      (leftSecant f x h + rightSecant f x h - 2 * deriv f x) /
        (2 * h ^ 2) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- The `(1,1)` confluent entry combines endpoint derivatives and the central secant. -/
lemma symmThreePointConfluentMatrix_apply_one_one
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 1 1 =
      (deriv f (x - h) + deriv f (x + h) -
        2 * centralSecant f x h) / (4 * h ^ 2) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- The `(1,2)` confluent entry is the odd third-order finite-difference form. -/
lemma symmThreePointConfluentMatrix_apply_one_two
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 1 2 =
      (deriv f (x + h) - deriv f (x - h) +
        2 * (leftSecant f x h - rightSecant f x h)) /
          (4 * h ^ 3) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_zero_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- The `(2,1)` confluent entry is the same odd third-order finite-difference form. -/
lemma symmThreePointConfluentMatrix_apply_two_one
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 2 1 =
      (deriv f (x + h) - deriv f (x - h) +
        2 * (leftSecant f x h - rightSecant f x h)) /
          (4 * h ^ 3) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_zero_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- The `(2,2)` confluent entry is the even fourth-order finite-difference form. -/
lemma symmThreePointConfluentMatrix_apply_two_two
    {f : ℝ → ℝ} {x h : ℝ} (hh : h ≠ 0) :
    symmThreePointConfluentMatrix f x h 2 2 =
      (deriv f (x - h) + deriv f (x + h) + 4 * deriv f x +
        2 * centralSecant f x h -
          4 * leftSecant f x h -
            4 * rightSecant f x h) / (4 * h ^ 4) := by
  simp [symmThreePointConfluentMatrix,
    symmThreePointConfluentTransform, Matrix.mul_apply, Fin.sum_univ_three,
    symmThreePointLoewnerMatrix_apply_zero_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_zero_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_zero (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_one_two (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_two_one (f := f) (x := x) (h := h) hh,
    symmThreePointLoewnerMatrix_apply_self, symmThreePointNodes]
  field_simp [hh]
  ring

/-- Small positive symmetric steps keep all three nodes inside `(-1,1)`. -/
lemma symmThreePointNodes_mem_Ioo_of_pos_lt_min
    {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h < min (x + 1) (1 - x)) :
    ∀ i, symmThreePointNodes x h i ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases hx with ⟨hxleft, hxright⟩
  have hhleft : h < x + 1 := lt_of_lt_of_le hhsmall (min_le_left _ _)
  have hhright : h < 1 - x := lt_of_lt_of_le hhsmall (min_le_right _ _)
  intro i
  fin_cases i <;>
    simp [symmThreePointNodes] <;> constructor <;> linarith

/-- For a positive step, the symmetric three-point nodes are pairwise distinct. -/
lemma symmThreePointNodes_injective
    {x h : ℝ} (hhpos : 0 < h) :
    Function.Injective (symmThreePointNodes x h) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [symmThreePointNodes] at hij ⊢ <;> linarith

/--
Principal symmetric three-point determinant nonnegativity, specialized to the
nodes `x - h`, `x`, `x + h`.
-/
theorem loewnerKernel_threePoint_symm_det_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h < min (x + 1) (1 - x)) :
    0 ≤ (symmThreePointLoewnerMatrix f x h).det := by
  simpa [symmThreePointLoewnerMatrix] using
    loewnerKernel_threePoint_real_det_nonneg_of_loewnerPosOnUnitInterval
      (f := f) hpos
      (symmThreePointNodes_mem_Ioo_of_pos_lt_min hx hhpos hhsmall)
      (symmThreePointNodes_injective (x := x) hhpos)

/-- Principal symmetric three-point PSD, specialized to the nodes `x - h`, `x`, `x + h`. -/
theorem loewnerKernel_threePoint_symm_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h < min (x + 1) (1 - x)) :
    (symmThreePointLoewnerMatrix f x h).PosSemidef := by
  simpa [symmThreePointLoewnerMatrix] using
    loewnerKernel_threePoint_real_posSemidef_of_loewnerPosOnUnitInterval
      (f := f) hpos
      (symmThreePointNodes_mem_Ioo_of_pos_lt_min hx hhpos hhsmall)
      (symmThreePointNodes_injective (x := x) hhpos)

/--
The finite confluent matrix is PSD because it is the symmetric three-point
Löwner matrix conjugated by the finite-difference transform.
-/
theorem symmThreePointConfluentMatrix_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x h : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hhpos : 0 < h) (hhsmall : h < min (x + 1) (1 - x)) :
    (symmThreePointConfluentMatrix f x h).PosSemidef := by
  have hL :=
    loewnerKernel_threePoint_symm_posSemidef_of_loewnerPosOnUnitInterval
      (f := f) hpos hx hhpos hhsmall
  have hconj :=
    hL.conjTranspose_mul_mul_same
      (symmThreePointConfluentTransform h)
  simpa [symmThreePointConfluentMatrix] using hconj

/--
The symmetric three-point determinant remains nonnegative after the `h^6`
scaling used in the confluent determinant limit.
-/
theorem
    loewnerKernel_threePoint_symm_det_scaled_eventually_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      0 ≤ threePointSymmScaledDet f x h := by
  have hmargin : 0 < min (x + 1) (1 - x) := by
    exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have hsmall :
      ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min (x + 1) (1 - x) :=
    (eventually_lt_nhds hmargin).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hhpos hhsmall
  exact div_nonneg
    (loewnerKernel_threePoint_symm_det_nonneg_of_loewnerPosOnUnitInterval
      (f := f) hpos hx hhpos hhsmall)
    (pow_nonneg (le_of_lt hhpos) 6)


/--
Bridge from the symmetric determinant limit to nonnegativity of the confluent
Hankel determinant.  The convergence input holds for `C⁵` functions by
`threePoint_det_scaled_tendsto_C5` (`ConfluentHankelC5.lean`).
-/
theorem hankel3_det_nonneg_of_threePoint_symm_det_scaled_tendsto
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hlim :
      Tendsto (fun h : ℝ => threePointSymmScaledDet f x h)
        (𝓝[>] (0 : ℝ))
        (𝓝 (4 * (confluentLoewnerHankel3 f x).det))) :
    0 ≤ (confluentLoewnerHankel3 f x).det := by
  have hfour :
      0 ≤ 4 * (confluentLoewnerHankel3 f x).det :=
    ge_of_tendsto hlim
      (loewnerKernel_threePoint_symm_det_scaled_eventually_nonneg_of_loewnerPosOnUnitInterval
        (f := f) hpos hx)
  nlinarith

/--
Quadratic-test form of the principal three-point public Löwner matrix.  This
keeps the C² pilot on genuine principal PSD data rather than non-principal
cross-minors.
-/
theorem loewnerKernel_threePoint_quadratic_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 3 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (w : Fin 3 → ℂ) :
    0 ≤
      dotProduct (star w)
        (Matrix.mulVec
          (Matrix.of
            (fun i j : Fin 3 => (loewnerKernel f (x i) (x j) : ℂ))) w) :=
  (loewnerKernel_threePoint_posSemidef_of_loewnerPosOnUnitInterval
    hpos hx hinj).dotProduct_mulVec_nonneg w

/-- Principal four-point public Löwner PSD, used only through one quadratic test. -/
theorem loewnerKernel_fourPoint_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    (Matrix.of
      (fun i j : Fin 4 => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef :=
  hpos.posSemidef 4 x hx hinj

/-- Real-valued PSD form of the principal four-point public Löwner matrix. -/
theorem loewnerKernel_fourPoint_real_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    (Matrix.of
      (fun i j : Fin 4 => loewnerKernel f (x i) (x j))).PosSemidef := by
  have hpsdC :=
    loewnerKernel_fourPoint_posSemidef_of_loewnerPosOnUnitInterval
      (f := f) hpos hx hinj
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.of_apply,
      loewnerKernel_symm]
  · intro w
    have hquadC :=
      hpsdC.dotProduct_mulVec_nonneg (fun i : Fin 4 => (w i : ℂ))
    have hquadC' :
        0 ≤
          ((star w ⬝ᵥ
            (Matrix.mulVec
              (Matrix.of
                (fun i j : Fin 4 => loewnerKernel f (x i) (x j))) w) : ℝ) : ℂ) := by
      simpa [Matrix.mulVec, dotProduct, Matrix.of_apply,
        Complex.ofReal_sum, Complex.ofReal_mul] using hquadC
    exact (RCLike.ofReal_nonneg (K := ℂ)).1 hquadC'

end

end Quantum.TraceInequality.Loewner
