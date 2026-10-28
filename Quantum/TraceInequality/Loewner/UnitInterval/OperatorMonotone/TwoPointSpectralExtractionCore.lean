import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.ThreePointOrderRay

/-!
# Chapter 3 two-point spectral extraction

This file contains the two-point order-ray spectral extraction layer, from raw
centered divided-difference estimates through the concrete two-point CFC
comparison and signed-entry-bound wrappers.
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

/--
Concrete `2×2` diagonal order-ray matrix used by the future scalar comparison.

The base nodes are `(x,y)` and the positive direction is the rank-one all-ones
direction.  This definition is only the matrix skeleton for the next proof
node; the scalar comparison itself remains an explicit producer input below.
-/
def twoPointOrderRayMatrix (x y ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalPerturbation (twoPointNodes x y) (fun _ => (1 : ℂ)) ε

/--
Scalar quotient attached to the two-point order-ray nodes.

This is the concrete scalar quantity that the future `2×2` CFC/order-ray
comparison will bound from below and above.
-/
def twoPointOrderRayQuotient (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (f (twoPointNodes x y 1) - f (twoPointNodes x y 0)) /
    (twoPointNodes x y 1 - twoPointNodes x y 0)

/-- Center value used by the two-point order-ray scalar comparison. -/
def twoPointOrderRayCenter (_f : ℝ → ℝ) (_x D : ℝ) : ℝ :=
  D

/--
The concrete two-point order-ray quotient is the existing raw divided
difference.
-/
theorem twoPointOrderRayQuotient_eq_rawDividedDifference
    (f : ℝ → ℝ) (x y : ℝ) :
    twoPointOrderRayQuotient f x y =
      twoPointRawDividedDifference f x y := by
  simp [twoPointOrderRayQuotient, twoPointRawDividedDifference,
    twoPointNodes]

/--
Concrete `2×2` CStarMatrix order ray used by the scalar comparison core.

This is the C*-algebra copy of `twoPointOrderRayMatrix`.
-/
def twoPointCStarOrderRayMatrix (x y ε : ℝ) :
    CStarMatrix (Fin 2) (Fin 2) ℂ :=
  cStarDiagonalPerturbation (twoPointNodes x y)
    (fun _ : Fin 2 => (1 : ℂ)) ε

/-- The concrete two-point CStar order ray stays in the CFC interval domain. -/
lemma twoPointCStarOrderRay_mem_domain_eventually
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      twoPointCStarOrderRayMatrix x y ε ∈
        cStarFiniteMatrixDomain 2 := by
  simpa [twoPointCStarOrderRayMatrix] using
    (cStarDiagonalPerturbation_mem_domain_eventually
      (twoPointNodes x y) (twoPointNodes_mem_Ioo hx hy)
      (fun _ : Fin 2 => (1 : ℂ)))

/--
The two-point CStar order ray is above its diagonal base point for
nonnegative parameters.
-/
lemma twoPointCStarOrderRay_le_of_nonneg
    (x y : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    cStarDiagonalMatrix (twoPointNodes x y) ≤
      twoPointCStarOrderRayMatrix x y ε := by
  simpa [twoPointCStarOrderRayMatrix] using
    (cStarDiagonalMatrix_le_perturbation_of_nonneg
      (twoPointNodes x y) (fun _ : Fin 2 => (1 : ℂ)) hε)

/--
Finite matrix monotonicity gives the concrete `2×2` CFC order-ray comparison.

This closes the monotonicity-to-CFC-order part of the future scalar comparison.
Extracting lower/upper scalar quotient bounds from this matrix inequality is
left to the next node.
-/
theorem twoPointCFCOrderRayComparison
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y)) ≤
        cfcₙ (fun t : ℝ => f t - f 0)
          (twoPointCStarOrderRayMatrix x y ε) := by
  filter_upwards [twoPointCStarOrderRay_mem_domain_eventually hx hy,
    self_mem_nhdsWithin] with ε hdom hεpos
  have hbase :
      cStarDiagonalMatrix (twoPointNodes x y) ∈
        cStarFiniteMatrixDomain 2 :=
    cStarDiagonalMatrix_mem_domain
      (twoPointNodes x y) (twoPointNodes_mem_Ioo hx hy)
  have hle_ray :
      cStarDiagonalMatrix (twoPointNodes x y) ≤
        twoPointCStarOrderRayMatrix x y ε :=
    twoPointCStarOrderRay_le_of_nonneg x y (le_of_lt hεpos)
  exact hfinite.cfc_monotone_matrix 2 hbase hdom hle_ray

/--
Difference matrix associated to the closed concrete `2×2` CFC order-ray
comparison.

The matrix is positive when finite matrix monotonicity is applied along the
order ray.  Scalar quotient extraction in the next node will use positivity
tests for this difference.
-/
def twoPointCFCOrderRayDifference
    (f : ℝ → ℝ) (x y ε : ℝ) : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  cfcₙ (fun t : ℝ => f t - f 0)
      (twoPointCStarOrderRayMatrix x y ε) -
    cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (twoPointNodes x y))
end

end Quantum.TraceInequality.Loewner
