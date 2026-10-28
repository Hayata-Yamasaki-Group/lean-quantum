import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.TwoByTwoRegularity
import Quantum.Analysis.Calculus.SharedSecantFilter

/-!
# Chapter 3 two-point order-ray interfaces

This file contains the two-point order-ray spectral variation interfaces and
raw divided-difference reductions before the concrete three-point order-ray
calculation.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/-- Two nodes used by the future `2×2` order-ray spectral-variation argument. -/
def twoPointNodes (x y : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then x else y

/-- If both scalar nodes are in the interval, the two-point node family is too. -/
lemma twoPointNodes_mem_Ioo {x y : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ i : Fin 2, twoPointNodes x y i ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro i
  fin_cases i <;> simp [twoPointNodes, hx, hy]

/-- Distinct scalar nodes give an injective two-point node family. -/
lemma twoPointNodes_injective_of_ne {x y : ℝ} (hxy : x ≠ y) :
    Function.Injective (twoPointNodes x y) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    exact hxy (by simpa [twoPointNodes] using hij)
  · exfalso
    exact hxy (by simpa [twoPointNodes] using hij.symm)
  · rfl

/--
Raw off-diagonal divided difference, in the orientation naturally used by
punctured secant slopes.
-/
def twoPointRawDividedDifference (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (f y - f x) / (y - x)

/-- Off the diagonal, the raw divided difference is the Lowner kernel. -/
theorem twoPointRawDividedDifference_eq_loewnerKernel_of_ne
    (f : ℝ → ℝ) {x y : ℝ} (hyx : y ≠ x) :
    twoPointRawDividedDifference f x y = loewnerKernel f x y := by
  rw [twoPointRawDividedDifference,
    loewnerKernel_eq_div (f := f) (x := x) (y := y) hyx.symm]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hyx.symm]
  ring

/--
Second divided difference around the fixed center `x`.

This is the scalar three-point quantity that can supply the complementary
control missing from the purely two-point order-ray diagnostics.
-/
def threePointSecondDividedDifference
    (f : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (twoPointRawDividedDifference f x y -
    twoPointRawDividedDifference f x z) / (y - z)

/--
The difference of two raw divided differences is the second divided
difference times the separation of the moving nodes.
-/
theorem twoPointRawDividedDifference_sub_eq_secondDividedDifference_mul
    (f : ℝ → ℝ) (x : ℝ) {y z : ℝ} (hyz : y ≠ z) :
    twoPointRawDividedDifference f x y -
        twoPointRawDividedDifference f x z =
      threePointSecondDividedDifference f x y z * (y - z) := by
  have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
  rw [threePointSecondDividedDifference]
  field_simp [hyz']
end

end Quantum.TraceInequality.Loewner
