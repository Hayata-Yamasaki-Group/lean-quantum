import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.TwoPointOrderRay

/-!
# Chapter 3 three-point order-ray calculation

This file contains the concrete three-point order-ray matrix calculation and the
conversion from bounded second divided differences to the two-point raw spectral
modulus input.
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

/-! ### Three-point nodes and order-ray comparison -/

/-- Three scalar nodes used by the `3×3` order-ray comparison
`threePointCFCOrderRayComparison`. -/
def threePointNodes (x y z : ℝ) : Fin 3 → ℝ :=
  fun i => if i = 0 then x else if i = 1 then y else z

/-- If the scalar nodes are in the interval, the three-point node family is too. -/
lemma threePointNodes_mem_Ioo {x y z : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ i : Fin 3, threePointNodes x y z i ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro i
  fin_cases i <;> simp [threePointNodes, hx, hy, hz]

/-- Distinct scalar nodes give an injective three-point node family. -/
lemma threePointNodes_injective_of_ne {x y z : ℝ}
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    Function.Injective (threePointNodes x y z) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    exact hyx (by simpa [threePointNodes] using hij.symm)
  · exfalso
    exact hzx (by simpa [threePointNodes] using hij.symm)
  · exfalso
    exact hyx (by simpa [threePointNodes] using hij)
  · rfl
  · exfalso
    exact hyz (by simpa [threePointNodes] using hij)
  · exfalso
    exact hzx (by simpa [threePointNodes] using hij)
  · exfalso
    exact hyz (by simpa [threePointNodes] using hij.symm)
  · rfl

/--
Concrete `3×3` diagonal order-ray matrix for the second divided-difference
frontier.

The base nodes are `(x,y,z)` and the positive direction is the rank-one
all-ones direction.
-/
def threePointOrderRayMatrix (x y z ε : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  diagonalPerturbation (threePointNodes x y z)
    (fun _ : Fin 3 => (1 : ℂ)) ε

/-- The `CStarMatrix` copy of `threePointOrderRayMatrix`. -/
def threePointCStarOrderRayMatrix (x y z ε : ℝ) :
    CStarMatrix (Fin 3) (Fin 3) ℂ :=
  cStarDiagonalPerturbation (threePointNodes x y z)
    (fun _ : Fin 3 => (1 : ℂ)) ε

/-- The concrete three-point CStar order ray stays in the CFC interval domain. -/
lemma threePointCStarOrderRay_mem_domain_eventually
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      threePointCStarOrderRayMatrix x y z ε ∈
        cStarFiniteMatrixDomain 3 := by
  simpa [threePointCStarOrderRayMatrix] using
    (cStarDiagonalPerturbation_mem_domain_eventually
      (threePointNodes x y z)
      (threePointNodes_mem_Ioo hx hy hz)
      (fun _ : Fin 3 => (1 : ℂ)))

/--
The three-point CStar order ray is above its diagonal base point for
nonnegative parameters.
-/
lemma threePointCStarOrderRay_le_of_nonneg
    (x y z : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    cStarDiagonalMatrix (threePointNodes x y z) ≤
      threePointCStarOrderRayMatrix x y z ε := by
  simpa [threePointCStarOrderRayMatrix] using
    (cStarDiagonalMatrix_le_perturbation_of_nonneg
      (threePointNodes x y z) (fun _ : Fin 3 => (1 : ℂ)) hε)

/--
Finite matrix monotonicity gives the concrete `3×3` CFC order-ray comparison.

This closes the monotonicity-to-CFC-order part of the three-point frontier.
Extracting a local second-divided-difference bound from this matrix inequality
remains the next scalar estimate.
-/
theorem threePointCFCOrderRayComparison
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z)) ≤
        cfcₙ (fun t : ℝ => f t - f 0)
          (threePointCStarOrderRayMatrix x y z ε) := by
  filter_upwards [threePointCStarOrderRay_mem_domain_eventually hx hy hz,
    self_mem_nhdsWithin] with ε hdom hεpos
  have hbase :
      cStarDiagonalMatrix (threePointNodes x y z) ∈
        cStarFiniteMatrixDomain 3 :=
    cStarDiagonalMatrix_mem_domain
      (threePointNodes x y z) (threePointNodes_mem_Ioo hx hy hz)
  have hle_ray :
      cStarDiagonalMatrix (threePointNodes x y z) ≤
        threePointCStarOrderRayMatrix x y z ε :=
    threePointCStarOrderRay_le_of_nonneg x y z (le_of_lt hεpos)
  exact hfinite.cfc_monotone_matrix 3 hbase hdom hle_ray

/-- Difference matrix associated to the concrete `3×3` CFC order-ray comparison. -/
def threePointCFCOrderRayDifference
    (f : ℝ → ℝ) (x y z ε : ℝ) : CStarMatrix (Fin 3) (Fin 3) ℂ :=
  cfcₙ (fun t : ℝ => f t - f 0)
      (threePointCStarOrderRayMatrix x y z ε) -
    cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (threePointNodes x y z))

/--
The concrete three-point CFC order-ray comparison is equivalently positivity of
the difference matrix, eventually for positive ray parameters.
-/
theorem threePointCFCOrderRayDifference_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ threePointCFCOrderRayDifference f x y z ε := by
  filter_upwards [threePointCFCOrderRayComparison hfinite hx hy hz]
    with ε hle
  simpa [threePointCFCOrderRayDifference] using sub_nonneg.mpr hle

/--
Positive three-point CFC difference matrices have nonnegative quadratic tests.
-/
theorem threePointCFCOrderRayDifference_testVector_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (c : Fin 3 → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ star c ⬝ᵥ
        ((CStarMatrix.ofMatrix.symm
          (threePointCFCOrderRayDifference f x y z ε)) *ᵥ c) := by
  filter_upwards
    [threePointCFCOrderRayDifference_nonneg_eventually hfinite hx hy hz]
    with ε hnonneg
  exact cStarMatrix_quadratic_nonneg_of_nonneg hnonneg c

/-! ### Barycentric second-difference tests -/

/--
Barycentric coefficients for the second divided difference at the nodes
`x,y,z`, in the node order used by `threePointNodes`.
-/
def threePointSecondDividedDifferenceCoeff
    (x y z : ℝ) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then (((y - x) * (z - x))⁻¹)
    else if i = 1 then (((y - x) * (y - z))⁻¹)
    else -(((z - x) * (y - z))⁻¹)

/--
The second divided difference is the barycentric linear combination of the
three scalar values at the nodes.
-/
theorem threePointSecondDividedDifference_barycentric_formula
    (f : ℝ → ℝ) {x y z : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    threePointSecondDividedDifference f x y z =
      ∑ i : Fin 3,
        threePointSecondDividedDifferenceCoeff x y z i *
          f (threePointNodes x y z i) := by
  simp [threePointSecondDividedDifference, twoPointRawDividedDifference,
    threePointSecondDividedDifferenceCoeff, threePointNodes,
    Fin.sum_univ_three]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hzx, sub_ne_zero.mpr hyz]
  ring_nf

/--
Complex coefficient vector used to test the three-point CFC positivity matrix
against the scalar second-divided-difference barycentric direction.
-/
def threePointSecondDifferenceBarycentricVector
    (x y z : ℝ) : Fin 3 → ℂ :=
  fun i => (threePointSecondDividedDifferenceCoeff x y z i : ℂ)

/--
Three-point CFC positivity specialized to the barycentric vector for the
second divided difference.

The remaining three-point order-ray scalar extraction problem is to turn this positive
quadratic test, together with an exact/asymptotic evaluation of the CFC
difference, into a uniform local bound on the scalar second divided difference.
-/
theorem
    threePointCFCOrderRayDifference_barycentricVector_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ star (threePointSecondDifferenceBarycentricVector x y z) ⬝ᵥ
        ((CStarMatrix.ofMatrix.symm
          (threePointCFCOrderRayDifference f x y z ε)) *ᵥ
            threePointSecondDifferenceBarycentricVector x y z) :=
  threePointCFCOrderRayDifference_testVector_nonneg_eventually
    hfinite hx hy hz (threePointSecondDifferenceBarycentricVector x y z)

/--
Entry of the concrete `3×3` CFC order-ray difference matrix.  This is just a
name for the matrix entry used by the barycentric quadratic expansion below.
-/
def threePointCFCOrderRayDifferenceEntryFormula
    (f : ℝ → ℝ) (x y z ε : ℝ) (i j : Fin 3) : ℂ :=
  (CStarMatrix.ofMatrix.symm
    (threePointCFCOrderRayDifference f x y z ε)) i j

/--
The barycentric quadratic CFC positivity test expanded entrywise.

This is still an algebraic normal form: it does not evaluate the `3×3` CFC
entries or extract a scalar bound for the second divided difference.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_entry_formula
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    star (threePointSecondDifferenceBarycentricVector x y z) ⬝ᵥ
        ((CStarMatrix.ofMatrix.symm
          (threePointCFCOrderRayDifference f x y z ε)) *ᵥ
            threePointSecondDifferenceBarycentricVector x y z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j := by
  simp [threePointCFCOrderRayDifferenceEntryFormula, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  ring_nf

/--
Three-point barycentric positivity written in the explicit entry normal form.

The remaining three-point order-ray blocker is the exact/asymptotic evaluation of these
`3×3` entries, not the positivity-to-entry expansion.
-/
theorem threePointCFCOrderRayDifference_entryFormula_barycentricQuadratic_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j := by
  filter_upwards
    [threePointCFCOrderRayDifference_barycentricVector_nonneg_eventually
      hfinite hx hy hz]
    with ε hnonneg
  simpa [threePointCFCOrderRayDifference_barycentricQuadratic_entry_formula]
    using hnonneg

/-! ### Abstract spectral branches for the three-point ray -/

/--
The concrete three-point order-ray matrix is Hermitian.  This allows the
following spectral normal form to use Mathlib's Hermitian eigenvalues rather
than an explicit cubic formula.
-/
lemma threePointOrderRayMatrix_isHermitian
    (x y z ε : ℝ) :
    (threePointOrderRayMatrix x y z ε).IsHermitian := by
  change IsSelfAdjoint (threePointOrderRayMatrix x y z ε)
  simpa [threePointOrderRayMatrix] using
    diagonalPerturbation_isSelfAdjoint
      (threePointNodes x y z) (fun _ : Fin 3 => (1 : ℂ)) ε

/--
Abstract Hermitian eigenvalue branches for the `3×3` order ray.

The order of these branches is intentionally not fixed.  The later local
asymptotic step is responsible for choosing usable branches or proving
coefficient bounds.
-/
noncomputable def threePointOrderRayEigenvalue
    (x y z ε : ℝ) : Fin 3 → ℝ :=
  (threePointOrderRayMatrix_isHermitian x y z ε).eigenvalues

/-- Each abstract Hermitian eigenvalue belongs to the real spectrum. -/
lemma threePointOrderRayEigenvalues_mem_spectrum
    (x y z ε : ℝ) (k : Fin 3) :
    threePointOrderRayEigenvalue x y z ε k ∈
      spectrum ℝ (threePointOrderRayMatrix x y z ε) := by
  simpa [threePointOrderRayEigenvalue] using
    (threePointOrderRayMatrix_isHermitian x y z ε).eigenvalues_mem_spectrum_real k

/-- The real spectrum of the Hermitian three-point order ray is its eigenvalue range. -/
lemma threePointOrderRayMatrix_spectrum_eq_range_eigenvalues
    (x y z ε : ℝ) :
    spectrum ℝ (threePointOrderRayMatrix x y z ε) =
      Set.range (threePointOrderRayEigenvalue x y z ε) := by
  simpa [threePointOrderRayEigenvalue] using
    (threePointOrderRayMatrix_isHermitian x y z ε).spectrum_real_eq_range_eigenvalues

/-- CStarMatrix-copy version of the abstract eigenvalue spectrum containment. -/
lemma threePointCStarOrderRayMatrix_spectrum_subset_eigenvalues
    (x y z ε : ℝ) :
    spectrum ℝ (threePointCStarOrderRayMatrix x y z ε) ⊆
      Set.range (threePointOrderRayEigenvalue x y z ε) := by
  intro t ht
  have ht' :
      t ∈ spectrum ℝ (threePointOrderRayMatrix x y z ε) := by
    simpa [threePointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      threePointOrderRayMatrix] using ht
  simpa [threePointOrderRayMatrix_spectrum_eq_range_eigenvalues x y z ε]
    using ht'

/-- The real quasispectrum of the concrete three-point CStar order ray is finite. -/
lemma threePointCStarOrderRayMatrix_quasispectrum_finite
    (x y z ε : ℝ) :
    (quasispectrum ℝ (threePointCStarOrderRayMatrix x y z ε)).Finite := by
  have hfinite :
      ({0} ∪ Set.range (threePointOrderRayEigenvalue x y z ε) : Set ℝ).Finite :=
    (Set.finite_singleton 0).union (Set.finite_range _)
  refine hfinite.subset ?_
  intro t ht
  have htq : t = 0 ∨ t ∈ spectrum ℝ (threePointCStarOrderRayMatrix x y z ε) :=
    (mem_quasispectrum_iff
      (a := threePointCStarOrderRayMatrix x y z ε) (x := t)).mp ht
  rcases htq with rfl | hs
  · left
    rfl
  · right
    exact threePointCStarOrderRayMatrix_spectrum_subset_eigenvalues x y z ε hs

/--
Arbitrary normalized scalar functions are continuous on the finite
three-point order-ray quasispectrum.
-/
lemma threePointCStarOrderRayMatrix_continuousOn_normalized
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    ContinuousOn (fun t : ℝ => f t - f 0)
      (quasispectrum ℝ (threePointCStarOrderRayMatrix x y z ε)) :=
  (threePointCStarOrderRayMatrix_quasispectrum_finite x y z ε).continuousOn
    (fun t : ℝ => f t - f 0)

/-! ### Quadratic spectral interpolant -/

/--
Quadratic Lagrange interpolating polynomial through the three abstract
Hermitian eigenvalues of the `3×3` order ray.
-/
noncomputable def threePointOrderRaySpectralQuadraticPolynomial
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℝ[X] :=
  ∑ k : Fin 3,
    Polynomial.C
        (f (threePointOrderRayEigenvalue x y z ε k) - f 0) *
      lagrangeBasis (threePointOrderRayEigenvalue x y z ε) k

/-- Scalar function associated with the quadratic spectral interpolating polynomial. -/
noncomputable def threePointOrderRaySpectralQuadratic
    (f : ℝ → ℝ) (x y z ε t : ℝ) : ℝ :=
  (threePointOrderRaySpectralQuadraticPolynomial f x y z ε).eval t

/-- The quadratic spectral interpolant matches `f - f 0` at each eigenvalue. -/
lemma threePointOrderRaySpectralQuadratic_eval_eigenvalue
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (k : Fin 3) :
    threePointOrderRaySpectralQuadratic f x y z ε
        (threePointOrderRayEigenvalue x y z ε k) =
      f (threePointOrderRayEigenvalue x y z ε k) - f 0 := by
  classical
  simp [threePointOrderRaySpectralQuadratic,
    threePointOrderRaySpectralQuadraticPolynomial,
    Polynomial.eval_finset_sum, Polynomial.eval_mul,
    lagrangeBasis_eval hinj]

/--
Matrix expression obtained by applying the quadratic spectral interpolating
polynomial to the three-point CStar order ray.
-/
noncomputable def threePointOrderRaySpectralQuadraticMatrix
    (f : ℝ → ℝ) (x y z ε : ℝ) : CStarMatrix (Fin 3) (Fin 3) ℂ :=
  Polynomial.aeval (threePointCStarOrderRayMatrix x y z ε)
    (threePointOrderRaySpectralQuadraticPolynomial f x y z ε)

/--
On the concrete three-point order-ray matrix, normalized CFC is equal to the
quadratic spectral interpolant evaluated by polynomial functional calculus.
-/
lemma threePointCStarOrderRayMatrix_cfcₙ_eq_spectralQuadraticMatrix
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε)) :
    cfcₙ (fun t : ℝ => f t - f 0)
        (threePointCStarOrderRayMatrix x y z ε) =
      threePointOrderRaySpectralQuadraticMatrix f x y z ε := by
  let M : CStarMatrix (Fin 3) (Fin 3) ℂ :=
    threePointCStarOrderRayMatrix x y z ε
  let p : ℝ[X] := threePointOrderRaySpectralQuadraticPolynomial f x y z ε
  have hnorm_cont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ M) := by
    simpa [M] using
      threePointCStarOrderRayMatrix_continuousOn_normalized f x y z ε
  have hspectrum :
      spectrum ℝ M ⊆
        Set.range (threePointOrderRayEigenvalue x y z ε) := by
    simpa [M] using
      threePointCStarOrderRayMatrix_spectrum_subset_eigenvalues x y z ε
  have hcongr :
      cfc (fun t : ℝ => f t - f 0) M = cfc p.eval M := by
    apply cfc_congr
    intro t ht
    rcases hspectrum ht with ⟨k, rfl⟩
    symm
    simpa [p, threePointOrderRaySpectralQuadratic] using
      threePointOrderRaySpectralQuadratic_eval_eigenvalue
        f x y z ε hinj k
  have hsa : IsSelfAdjoint M := by
    simpa [M, threePointCStarOrderRayMatrix] using
      cStarDiagonalPerturbation_isSelfAdjoint
        (threePointNodes x y z) (fun _ : Fin 3 => (1 : ℂ)) ε
  calc
    cfcₙ (fun t : ℝ => f t - f 0)
        (threePointCStarOrderRayMatrix x y z ε) =
        cfc (fun t : ℝ => f t - f 0) M := by
      simpa [M] using cfcₙ_eq_cfc (a := M) (hf := hnorm_cont) (hf0 := by simp)
    _ = cfc p.eval M := hcongr
    _ = threePointOrderRaySpectralQuadraticMatrix f x y z ε := by
      simpa [M, p, threePointOrderRaySpectralQuadraticMatrix] using
        (cfc_polynomial p M (ha := hsa))

/--
Entrywise spectral-quadratic normal form for normalized CFC on the concrete
three-point order-ray matrix.
-/
theorem threePointCStarOrderRayMatrix_cfcₙ_entry_spectralQuadraticFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (i j : Fin 3) :
    (cfcₙ (fun t : ℝ => f t - f 0)
        (threePointCStarOrderRayMatrix x y z ε)) i j =
      (threePointOrderRaySpectralQuadraticMatrix f x y z ε) i j := by
  have hmatrix :=
    threePointCStarOrderRayMatrix_cfcₙ_eq_spectralQuadraticMatrix
      f x y z ε hinj
  exact congrArg (fun M : CStarMatrix (Fin 3) (Fin 3) ℂ => M i j) hmatrix

/--
Entrywise spectral-quadratic normal form for the three-point CFC order-ray
difference.
-/
theorem threePointCFCOrderRayDifference_entry_spectralQuadraticFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (i j : Fin 3) :
    threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j =
      (threePointOrderRaySpectralQuadraticMatrix f x y z ε) i j -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z))) i j := by
  unfold threePointCFCOrderRayDifferenceEntryFormula
    threePointCFCOrderRayDifference
  change
    (cfcₙ (fun t : ℝ => f t - f 0)
        (threePointCStarOrderRayMatrix x y z ε) -
      cfcₙ (fun t : ℝ => f t - f 0)
        (cStarDiagonalMatrix (threePointNodes x y z))) i j =
      (threePointOrderRaySpectralQuadraticMatrix f x y z ε) i j -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z))) i j
  have hmatrix :=
    threePointCStarOrderRayMatrix_cfcₙ_eq_spectralQuadraticMatrix
      f x y z ε hinj
  have hdiff :
      cfcₙ (fun t : ℝ => f t - f 0)
          (threePointCStarOrderRayMatrix x y z ε) -
        cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z)) =
      threePointOrderRaySpectralQuadraticMatrix f x y z ε -
        cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z)) := by
    rw [hmatrix]
  exact congrArg (fun M : CStarMatrix (Fin 3) (Fin 3) ℂ => M i j) hdiff

/-! ### Spectral quadratic coefficient expansion -/

/--
Barycentric quadratic positivity in spectral-quadratic entry normal form.

This is still only an exact CFC-entry evaluation layer; extracting the local
second-divided-difference bound requires the next eigenvalue/coefficient
asymptotic step.
-/
theorem
    threePointCFCOrderRayDifference_barycentricQuadratic_spectralQuadraticFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          ((threePointOrderRaySpectralQuadraticMatrix f x y z ε) i j -
            (cfcₙ (fun t : ℝ => f t - f 0)
              (cStarDiagonalMatrix (threePointNodes x y z))) i j) *
            threePointSecondDifferenceBarycentricVector x y z j := by
  simp_rw [threePointCFCOrderRayDifference_entry_spectralQuadraticFormula
    (f := f) (x := x) (y := y) (z := z) (ε := ε) (hinj := hinj)]

/--
For three nodes, the Lagrange basis polynomial has degree at most two.
This keeps the spectral interpolant in an explicit quadratic coefficient
form.
-/
lemma threePointLagrangeBasis_natDegree_le
    (x : Fin 3 → ℝ) (k : Fin 3) :
    (lagrangeBasis x k).natDegree ≤ 2 := by
  classical
  unfold lagrangeBasis
  calc
    (∏ j ∈ Finset.univ.erase k,
        Polynomial.C ((x k - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))).natDegree
        ≤ ∑ j ∈ Finset.univ.erase k,
            (Polynomial.C ((x k - x j)⁻¹) *
              (Polynomial.X - Polynomial.C (x j))).natDegree := by
          exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase k, 1 := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            (Polynomial.natDegree_X_sub_C_le (x j))
    _ = 2 := by
          have hcard : (Finset.univ.erase k).card = 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
            simp
          simp [hcard]

/-- The three-point spectral interpolating polynomial is genuinely quadratic. -/
lemma threePointOrderRaySpectralQuadraticPolynomial_natDegree_le
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    (threePointOrderRaySpectralQuadraticPolynomial f x y z ε).natDegree ≤ 2 := by
  classical
  unfold threePointOrderRaySpectralQuadraticPolynomial
  exact Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ)
    (f := fun k : Fin 3 =>
      Polynomial.C
          (f (threePointOrderRayEigenvalue x y z ε k) - f 0) *
        lagrangeBasis (threePointOrderRayEigenvalue x y z ε) k)
    (n := 2)
    (by
      intro k _hk
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (threePointLagrangeBasis_natDegree_le
          (threePointOrderRayEigenvalue x y z ε) k))

/-- Coefficient of the three-point spectral quadratic polynomial. -/
noncomputable def threePointOrderRaySpectralQuadraticCoeff
    (f : ℝ → ℝ) (x y z ε : ℝ) (n : ℕ) : ℝ :=
  (threePointOrderRaySpectralQuadraticPolynomial f x y z ε).coeff n

/-- Constant coefficient of the three-point spectral quadratic polynomial. -/
noncomputable def threePointOrderRaySpectralQuadraticCoeff0
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℝ :=
  threePointOrderRaySpectralQuadraticCoeff f x y z ε 0

/-- Linear coefficient of the three-point spectral quadratic polynomial. -/
noncomputable def threePointOrderRaySpectralQuadraticCoeff1
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℝ :=
  threePointOrderRaySpectralQuadraticCoeff f x y z ε 1

/-- Quadratic coefficient of the three-point spectral quadratic polynomial. -/
noncomputable def threePointOrderRaySpectralQuadraticCoeff2
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℝ :=
  threePointOrderRaySpectralQuadraticCoeff f x y z ε 2

/--
The polynomial CFC matrix for the three-point spectral interpolant is the
explicit coefficient expression `c₀ 1 + c₁ M + c₂ M²`.
-/
theorem threePointOrderRaySpectralQuadraticMatrix_eq_coeffs
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    threePointOrderRaySpectralQuadraticMatrix f x y z ε =
      threePointOrderRaySpectralQuadraticCoeff0 f x y z ε •
          (1 : CStarMatrix (Fin 3) (Fin 3) ℂ) +
        threePointOrderRaySpectralQuadraticCoeff1 f x y z ε •
          threePointCStarOrderRayMatrix x y z ε +
        threePointOrderRaySpectralQuadraticCoeff2 f x y z ε •
          (threePointCStarOrderRayMatrix x y z ε) ^ 2 := by
  let M : CStarMatrix (Fin 3) (Fin 3) ℂ :=
    threePointCStarOrderRayMatrix x y z ε
  let p : ℝ[X] := threePointOrderRaySpectralQuadraticPolynomial f x y z ε
  have hdeg : p.natDegree < 3 := by
    exact Nat.lt_succ_of_le
      (by
        simpa [p] using
          threePointOrderRaySpectralQuadraticPolynomial_natDegree_le f x y z ε)
  have haeval :
      Polynomial.aeval M p =
        ∑ n ∈ Finset.range 3, p.coeff n • M ^ n := by
    simpa using Polynomial.aeval_eq_sum_range' (p := p) hdeg M
  rw [threePointOrderRaySpectralQuadraticMatrix]
  change Polynomial.aeval M p = _
  rw [haeval]
  simp [Finset.sum_range_succ, p, M, pow_two,
    threePointOrderRaySpectralQuadraticCoeff0,
    threePointOrderRaySpectralQuadraticCoeff1,
    threePointOrderRaySpectralQuadraticCoeff2,
    threePointOrderRaySpectralQuadraticCoeff]

/-- Entry form of the spectral quadratic coefficient expansion. -/
theorem threePointOrderRaySpectralQuadraticMatrix_entry_eq_coeffs
    (f : ℝ → ℝ) (x y z ε : ℝ) (i j : Fin 3) :
    (threePointOrderRaySpectralQuadraticMatrix f x y z ε) i j =
      (if i = j then
          (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
        else 0) +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          (threePointCStarOrderRayMatrix x y z ε) i j +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i j := by
  have hmatrix := threePointOrderRaySpectralQuadraticMatrix_eq_coeffs
    f x y z ε
  have hentry :=
    congrArg (fun M : CStarMatrix (Fin 3) (Fin 3) ℂ => M i j) hmatrix
  simpa [CStarMatrix.smul_apply, CStarMatrix.one_apply, mul_assoc] using hentry

/--
Entrywise CFC order-ray difference in spectral-quadratic coefficient form.
-/
theorem threePointCFCOrderRayDifference_entry_spectralQuadraticCoeffFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (i j : Fin 3) :
    threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j =
      ((if i = j then
          (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
        else 0) +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          (threePointCStarOrderRayMatrix x y z ε) i j +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i j) -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z))) i j := by
  rw [threePointCFCOrderRayDifference_entry_spectralQuadraticFormula
    (f := f) (x := x) (y := y) (z := z) (ε := ε) (hinj := hinj) (i := i) (j := j)]
  rw [threePointOrderRaySpectralQuadraticMatrix_entry_eq_coeffs]

/--
Barycentric quadratic positivity in spectral-quadratic coefficient form.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_spectralQuadraticCoeffFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (hinj : Function.Injective (threePointOrderRayEigenvalue x y z ε)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          (((if i = j then
              (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
            else 0) +
            (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
              (threePointCStarOrderRayMatrix x y z ε) i j +
            (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
              ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i j) -
            (cfcₙ (fun t : ℝ => f t - f 0)
              (cStarDiagonalMatrix (threePointNodes x y z))) i j) *
            threePointSecondDifferenceBarycentricVector x y z j := by
  simp_rw [threePointCFCOrderRayDifference_entry_spectralQuadraticCoeffFormula
    (f := f) (x := x) (y := y) (z := z) (ε := ε) (hinj := hinj)]

/-! ### Concrete matrix entry formulas -/

/-- Entry formula for the concrete three-point CStar order-ray matrix. -/
theorem threePointCStarOrderRayMatrix_entry_formula
    (x y z ε : ℝ) (i j : Fin 3) :
    (threePointCStarOrderRayMatrix x y z ε) i j =
      (if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
        (ε : ℂ) := by
  simp [threePointCStarOrderRayMatrix, cStarDiagonalPerturbation,
    diagonalPerturbation, diagonalMatrix, rankOnePerturbation,
    Matrix.vecMulVec, Matrix.diagonal_apply]

/-- Entry formula for the square of the concrete three-point CStar order ray. -/
theorem threePointCStarOrderRayMatrix_sq_entry_formula
    (x y z ε : ℝ) (i j : Fin 3) :
    ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i j =
      ∑ k : Fin 3,
        (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) *
          ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
            (ε : ℂ))) := by
  calc
    ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i j =
        ∑ k : Fin 3,
          (threePointCStarOrderRayMatrix x y z ε) i k *
            (threePointCStarOrderRayMatrix x y z ε) k j := by
      rw [pow_two]
      exact CStarMatrix.mul_apply
    _ = ∑ k : Fin 3,
        (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) *
          ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
            (ε : ℂ))) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      simp [threePointCStarOrderRayMatrix_entry_formula]

/-- Diagonal entry formula for the concrete three-point CStar order ray. -/
theorem threePointCStarOrderRayMatrix_diag_entry_formula
    (x y z ε : ℝ) (i : Fin 3) :
    (threePointCStarOrderRayMatrix x y z ε) i i =
      ((threePointNodes x y z i : ℝ) : ℂ) + (ε : ℂ) := by
  simp [threePointCStarOrderRayMatrix_entry_formula]

/-- Diagonal entry formula for the square of the concrete three-point CStar order ray. -/
theorem threePointCStarOrderRayMatrix_sq_diag_entry_formula
    (x y z ε : ℝ) (i : Fin 3) :
    ((threePointCStarOrderRayMatrix x y z ε) ^ 2) i i =
      ∑ k : Fin 3,
        (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) *
          ((if k = i then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
            (ε : ℂ))) := by
  simpa using
    threePointCStarOrderRayMatrix_sq_entry_formula x y z ε i i

/-! ### Diagonal node polynomial functional calculus -/

/-- Quadratic node interpolant for the diagonal base CFC. -/
noncomputable def threePointNodeInterpolatingPolynomial
    (f : ℝ → ℝ) (x y z : ℝ) : ℝ[X] :=
  ∑ k : Fin 3,
    Polynomial.C (f (threePointNodes x y z k) - f 0) *
      lagrangeBasis (threePointNodes x y z) k

/-- The node interpolant has degree at most two. -/
lemma threePointNodeInterpolatingPolynomial_natDegree_le
    (f : ℝ → ℝ) (x y z : ℝ) :
    (threePointNodeInterpolatingPolynomial f x y z).natDegree ≤ 2 := by
  classical
  unfold threePointNodeInterpolatingPolynomial
  exact Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ)
    (f := fun k : Fin 3 =>
      Polynomial.C (f (threePointNodes x y z k) - f 0) *
        lagrangeBasis (threePointNodes x y z) k)
    (n := 2)
    (by
      intro k _hk
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (threePointLagrangeBasis_natDegree_le
          (threePointNodes x y z) k))

/-- The node interpolant matches the normalized scalar function at each node. -/
lemma threePointNodeInterpolatingPolynomial_eval_node
    (f : ℝ → ℝ) (x y z : ℝ)
    (hnodes : Function.Injective (threePointNodes x y z))
    (k : Fin 3) :
    (threePointNodeInterpolatingPolynomial f x y z).eval
        (threePointNodes x y z k) =
      f (threePointNodes x y z k) - f 0 := by
  classical
  simp [threePointNodeInterpolatingPolynomial,
    Polynomial.eval_finset_sum, Polynomial.eval_mul,
    lagrangeBasis_eval hnodes]

/--
Polynomial functional calculus for a quadratic polynomial on a three-point
diagonal CStar matrix is entrywise diagonal.
-/
lemma threePointCStarDiagonalMatrix_quadratic_aeval_entry
    (p : ℝ[X]) {x y z : ℝ} (hdeg : p.natDegree ≤ 2) (i j : Fin 3) :
    (Polynomial.aeval (cStarDiagonalMatrix (threePointNodes x y z)) p) i j =
      if i = j then ((p.eval (threePointNodes x y z i) : ℝ) : ℂ)
      else 0 := by
  let D : CStarMatrix (Fin 3) (Fin 3) ℂ :=
    cStarDiagonalMatrix (threePointNodes x y z)
  have hdeglt : p.natDegree < 3 := Nat.lt_succ_of_le hdeg
  have haeval :
      Polynomial.aeval D p =
        ∑ n ∈ Finset.range 3, p.coeff n • D ^ n := by
    simpa using Polynomial.aeval_eq_sum_range' (p := p) hdeglt D
  have heval :
      p.eval (threePointNodes x y z i) =
        ∑ n ∈ Finset.range 3,
          p.coeff n * (threePointNodes x y z i) ^ n := by
    simpa using
      Polynomial.eval_eq_sum_range' (p := p) hdeglt
        (threePointNodes x y z i)
  rw [haeval]
  have hD0 :
      (1 : CStarMatrix (Fin 3) (Fin 3) ℂ) i j =
        if i = j then (1 : ℂ) else 0 := by
    simp [CStarMatrix.one_apply]
  have hD_entry :
      D i j =
        if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0 := by
    simp [D, cStarDiagonalMatrix, diagonalMatrix, Matrix.diagonal_apply]
  have hD2 :
      (D ^ 2) i j =
        if i = j then ((threePointNodes x y z i : ℝ) : ℂ) ^ 2 else 0 := by
    simpa [D, cStarDiagonalMatrix] using
      diagonalMatrix_pow_apply (threePointNodes x y z) 2 i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, heval]
    simp [Finset.sum_range_succ, hD0, hD_entry, hD2]
  · rw [if_neg hij]
    simp [Finset.sum_range_succ, hD0, hD_entry, hD2, hij]

/-- Exact entry formula for the three-point diagonal base CFC. -/
lemma threePointCStarDiagonalMatrix_cfcₙ_entry_formula
    (f : ℝ → ℝ) {x y z : ℝ}
    (hnodes : Function.Injective (threePointNodes x y z))
    (i j : Fin 3) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (threePointNodes x y z))) i j =
        if i = j then
          ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)
        else 0 := by
  let D : CStarMatrix (Fin 3) (Fin 3) ℂ :=
    cStarDiagonalMatrix (threePointNodes x y z)
  let p : ℝ[X] := threePointNodeInterpolatingPolynomial f x y z
  have hspectrum :
      spectrum ℝ D ⊆ Set.range (threePointNodes x y z) := by
    intro t ht
    change t ∈ spectrum ℝ
      (cStarDiagonalMatrix (threePointNodes x y z)) at ht
    rw [cStarDiagonalMatrix] at ht
    change t ∈ spectrum ℝ
      (diagonalMatrix (threePointNodes x y z)) at ht
    rw [← spectrum.preimage_algebraMap ℂ] at ht
    simp only [Set.mem_preimage] at ht
    change (t : ℂ) ∈ spectrum ℂ
      (diagonalMatrix (threePointNodes x y z)) at ht
    rw [diagonalMatrix, spectrum_diagonal] at ht
    rcases ht with ⟨k, hk⟩
    exact ⟨k, Complex.ofReal_injective hk⟩
  have hfinite : (quasispectrum ℝ D).Finite := by
    have hset :
        ({0} ∪ Set.range (threePointNodes x y z) : Set ℝ).Finite :=
      (Set.finite_singleton 0).union (Set.finite_range _)
    refine hset.subset ?_
    intro t ht
    have ht' : t = 0 ∨ t ∈ spectrum ℝ D :=
      (mem_quasispectrum_iff (a := D) (x := t)).mp ht
    rcases ht' with ht | ht
    · left
      simpa using ht
    · right
      exact hspectrum ht
  have hcont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ D) :=
    hfinite.continuousOn _
  have hsa : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint
      (threePointNodes x y z)).star_eq
    simpa [D, cStarDiagonalMatrix] using congrArg CStarMatrix.ofMatrix h
  have hmatch :
      Set.EqOn (fun t : ℝ => f t - f 0) p.eval (spectrum ℝ D) := by
    intro t ht
    rcases hspectrum ht with ⟨k, rfl⟩
    symm
    simpa [p] using
      threePointNodeInterpolatingPolynomial_eval_node f x y z hnodes k
  have hcfc :
      cfcₙ (fun t : ℝ => f t - f 0) D = Polynomial.aeval D p := by
    calc
      cfcₙ (fun t : ℝ => f t - f 0) D =
          cfc (fun t : ℝ => f t - f 0) D := by
        exact cfcₙ_eq_cfc (a := D) (hf := hcont) (hf0 := by simp)
      _ = cfc p.eval D := by
        exact cfc_congr hmatch
      _ = Polynomial.aeval D p := by
        simpa [p] using cfc_polynomial p D (ha := hsa)
  have hentry := congrArg (fun M : CStarMatrix (Fin 3) (Fin 3) ℂ => M i j) hcfc
  have hpoly_entry :
      (Polynomial.aeval D p) i j =
        if i = j then
          ((p.eval (threePointNodes x y z i) : ℝ) : ℂ)
        else 0 := by
    simpa [D, p] using
      threePointCStarDiagonalMatrix_quadratic_aeval_entry
        p (by
          simpa [p] using
            threePointNodeInterpolatingPolynomial_natDegree_le f x y z) i j
  have hentry' :
      (cfcₙ (fun t : ℝ => f t - f 0)
        (cStarDiagonalMatrix (threePointNodes x y z))) i j =
        (Polynomial.aeval D p) i j := by
    simpa [D] using hentry
  rw [hentry', hpoly_entry]
  by_cases hij : i = j
  · subst j
    have hpnode :
        p.eval (threePointNodes x y z i) =
          f (threePointNodes x y z i) - f 0 := by
      simpa [p] using
        threePointNodeInterpolatingPolynomial_eval_node f x y z hnodes i
    rw [hpnode]
  · simp [hij]

/-- The three-point diagonal base CFC has zero off-diagonal entries. -/
lemma threePointCStarDiagonalMatrix_cfcₙ_offdiag_zero
    (f : ℝ → ℝ) {x y z : ℝ}
    (hnodes : Function.Injective (threePointNodes x y z))
    {i j : Fin 3} (hij : i ≠ j) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (threePointNodes x y z))) i j = 0 := by
  simpa [hij] using
    threePointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hnodes i j

/-- The three-point diagonal base CFC has the expected diagonal entries. -/
lemma threePointCStarDiagonalMatrix_cfcₙ_diag_formula
    (f : ℝ → ℝ) {x y z : ℝ}
    (hnodes : Function.Injective (threePointNodes x y z))
    (i : Fin 3) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (threePointNodes x y z))) i i =
        ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ) := by
  simpa using
    threePointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hnodes i i

/-! ### Expanded CFC difference entry formulas -/

/--
Entrywise CFC order-ray difference with the order-ray entries and the diagonal
base CFC both expanded.
-/
theorem threePointCFCOrderRayDifference_entry_spectralQuadraticCoeffExpandedFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z))
    (i j : Fin 3) :
    threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j =
      ((if i = j then
          (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
        else 0) +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          ((if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          (∑ k : Fin 3,
            (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
                (ε : ℂ)) *
              ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
                (ε : ℂ))))) -
        (if i = j then
          ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)
        else 0) := by
  rw [threePointCFCOrderRayDifference_entry_spectralQuadraticCoeffFormula
    (f := f) (x := x) (y := y) (z := z) (ε := ε) (hinj := heig) (i := i) (j := j)]
  rw [threePointCStarOrderRayMatrix_entry_formula]
  rw [threePointCStarOrderRayMatrix_sq_entry_formula]
  rw [threePointCStarDiagonalMatrix_cfcₙ_entry_formula (f := f) hnodes i j]

/--
Fully expanded scalar entry expression for the three-point CFC order-ray
difference after spectral-quadratic coefficient expansion and diagonal
base cancellation.
-/
def threePointCFCOrderRayDifferenceExpandedEntry
    (f : ℝ → ℝ) (x y z ε : ℝ) (i j : Fin 3) : ℂ :=
  ((if i = j then
      (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
    else 0) +
    (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
      ((if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
        (ε : ℂ)) +
    (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
      (∑ k : Fin 3,
        (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) *
          ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
            (ε : ℂ))))) -
    (if i = j then
      ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)
    else 0)

/--
Barycentric quadratic CFC difference in the fully expanded scalar entry form.
-/
theorem
  threePointCFCOrderRayDifference_barycentricQuadratic_spectralQuadraticCoeffExpandedFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceExpandedEntry f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j := by
  simp_rw [
    threePointCFCOrderRayDifference_entry_spectralQuadraticCoeffExpandedFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes)]
  rfl

/--
The same expanded barycentric expression, with the diagonal base CFC
cancellation displayed as a single diagonal subtraction term.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_diagonalCancellationFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      (∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          (threePointCFCOrderRayDifferenceExpandedEntry f x y z ε i j +
            if i = j then
              ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)
            else 0) *
          threePointSecondDifferenceBarycentricVector x y z j) -
        ∑ i : Fin 3,
          star (threePointSecondDifferenceBarycentricVector x y z i) *
            ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ) *
              threePointSecondDifferenceBarycentricVector x y z i := by
  rw [
  threePointCFCOrderRayDifference_barycentricQuadratic_spectralQuadraticCoeffExpandedFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes)]
  simp [threePointCFCOrderRayDifferenceExpandedEntry, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_sub, sub_mul]

/-! ### Barycentric cancellations and contribution terms -/

/-- The barycentric coefficients annihilate constants. -/
theorem threePointSecondDividedDifferenceCoeff_sum_eq_zero
    {x y z : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i = 0 := by
  simp [threePointSecondDividedDifferenceCoeff, Fin.sum_univ_three]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hzx, sub_ne_zero.mpr hyz]
  ring

/-- The barycentric coefficients annihilate affine functions. -/
theorem threePointSecondDividedDifferenceCoeff_weighted_sum_eq_zero
    {x y z : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∑ i : Fin 3,
      threePointSecondDividedDifferenceCoeff x y z i *
        threePointNodes x y z i = 0 := by
  simp [threePointSecondDividedDifferenceCoeff, threePointNodes,
    Fin.sum_univ_three]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hzx, sub_ne_zero.mpr hyz]
  ring

/-- The barycentric coefficients evaluate the quadratic monomial to `1`. -/
theorem threePointSecondDividedDifferenceCoeff_weighted_sq_sum_eq_one
    {x y z : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∑ i : Fin 3,
      threePointSecondDividedDifferenceCoeff x y z i *
        (threePointNodes x y z i) ^ 2 = 1 := by
  simp [threePointSecondDividedDifferenceCoeff, threePointNodes,
    Fin.sum_univ_three]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hzx, sub_ne_zero.mpr hyz]
  ring

/-- Coefficient multiplying the constant spectral-quadratic term in the barycentric test. -/
def threePointBarycentricUnitCoeff (x y z : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      (if i = j then (1 : ℂ) else 0) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Coefficient multiplying the linear matrix term in the barycentric test. -/
def threePointBarycentricOrderRayCoeff
    (x y z ε : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      (((if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
        (ε : ℂ))) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Coefficient multiplying the quadratic matrix term in the barycentric test. -/
def threePointBarycentricOrderRaySqCoeff
    (x y z ε : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      (∑ k : Fin 3,
        (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
            (ε : ℂ)) *
          ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
            (ε : ℂ)))) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Diagonal base CFC contribution in the barycentric test. -/
def threePointBarycentricDiagonalBaseTerm
    (f : ℝ → ℝ) (x y z : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      (if i = j then
        ((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)
      else 0) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Constant spectral-coefficient contribution in the barycentric test. -/
def threePointBarycentricConstantContribution
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      (if i = j then
        (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ)
      else 0) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Linear spectral-coefficient contribution in the barycentric test. -/
def threePointBarycentricLinearContribution
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      ((threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
        (((if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
          (ε : ℂ)))) *
        threePointSecondDifferenceBarycentricVector x y z j

/-- Quadratic spectral-coefficient contribution in the barycentric test. -/
def threePointBarycentricQuadraticContribution
    (f : ℝ → ℝ) (x y z ε : ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    star (threePointSecondDifferenceBarycentricVector x y z i) *
      ((threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
        (∑ k : Fin 3,
          (((if i = k then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
              (ε : ℂ)) *
            ((if k = j then ((threePointNodes x y z k : ℝ) : ℂ) else 0) +
              (ε : ℂ))))) *
        threePointSecondDifferenceBarycentricVector x y z j

/-! ### Collected coefficient factorizations -/

/--
Collected coefficient form of the expanded barycentric quadratic CFC difference.

This isolates the scalar extraction still needed for the local
second-divided-difference bound: after this point the CFC side is reduced to
three explicit spectral-coefficient contributions and the diagonal base term.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_coeffCollectedFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      threePointBarycentricConstantContribution f x y z ε +
        threePointBarycentricLinearContribution f x y z ε +
        threePointBarycentricQuadraticContribution f x y z ε -
        threePointBarycentricDiagonalBaseTerm f x y z := by
  rw [
  threePointCFCOrderRayDifference_barycentricQuadratic_spectralQuadraticCoeffExpandedFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes)]
  simp [threePointCFCOrderRayDifferenceExpandedEntry,
    threePointBarycentricConstantContribution,
    threePointBarycentricLinearContribution,
    threePointBarycentricQuadraticContribution,
    threePointBarycentricDiagonalBaseTerm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, add_mul, mul_sub, sub_mul]

/-- The constant contribution is the zeroth spectral coefficient times its scalar weight. -/
theorem threePointBarycentricConstantContribution_eq_coeff_mul
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    threePointBarycentricConstantContribution f x y z ε =
      (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
        threePointBarycentricUnitCoeff x y z := by
  simp [threePointBarycentricConstantContribution,
    threePointBarycentricUnitCoeff, Fin.sum_univ_three]
  ring_nf

/-- The linear contribution is the first spectral coefficient times its scalar weight. -/
theorem threePointBarycentricLinearContribution_eq_coeff_mul
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    threePointBarycentricLinearContribution f x y z ε =
      (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
        threePointBarycentricOrderRayCoeff x y z ε := by
  simp [threePointBarycentricLinearContribution,
    threePointBarycentricOrderRayCoeff, Fin.sum_univ_three]
  ring_nf

/-- The quadratic contribution is the second spectral coefficient times its scalar weight. -/
theorem threePointBarycentricQuadraticContribution_eq_coeff_mul
    (f : ℝ → ℝ) (x y z ε : ℝ) :
    threePointBarycentricQuadraticContribution f x y z ε =
      (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
        threePointBarycentricOrderRaySqCoeff x y z ε := by
  simp [threePointBarycentricQuadraticContribution,
    threePointBarycentricOrderRaySqCoeff, Fin.sum_univ_three]
  ring_nf

/--
Collected coefficient form with all three spectral coefficients factored out.

The remaining scalar extraction can now focus separately on the three explicit
barycentric weights and the diagonal base term.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_coeffFactoredFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
          threePointBarycentricUnitCoeff x y z +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          threePointBarycentricOrderRayCoeff x y z ε +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          threePointBarycentricOrderRaySqCoeff x y z ε -
        threePointBarycentricDiagonalBaseTerm f x y z := by
  rw [
    threePointCFCOrderRayDifference_barycentricQuadratic_coeffCollectedFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes),
    threePointBarycentricConstantContribution_eq_coeff_mul,
    threePointBarycentricLinearContribution_eq_coeff_mul,
    threePointBarycentricQuadraticContribution_eq_coeff_mul]

/-! ### Explicit barycentric coefficient formulas -/

/-- Explicit scalar form of the barycentric coefficient of the constant term. -/
theorem threePointBarycentricUnitCoeff_explicit (x y z : ℝ) :
    threePointBarycentricUnitCoeff x y z =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 := by
  simp [threePointBarycentricUnitCoeff,
    threePointSecondDifferenceBarycentricVector]
  ring_nf

/--
Explicit scalar form of the barycentric coefficient of the linear order-ray
term.  The only `ε`-dependence is through the square of the sum of the
barycentric coefficients.
-/
theorem threePointBarycentricOrderRayCoeff_explicit
    (x y z ε : ℝ) :
    threePointBarycentricOrderRayCoeff x y z ε =
      (∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          ((threePointNodes x y z i : ℝ) : ℂ)) +
        (ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) ^ 2 := by
  simp [threePointBarycentricOrderRayCoeff,
    threePointSecondDifferenceBarycentricVector, Fin.sum_univ_three]
  ring_nf

/-- The linear barycentric weight has no `ε`-term at distinct nodes. -/
theorem threePointBarycentricOrderRayCoeff_distinct
    {x y z ε : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    threePointBarycentricOrderRayCoeff x y z ε =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          ((threePointNodes x y z i : ℝ) : ℂ) := by
  rw [threePointBarycentricOrderRayCoeff_explicit]
  have hsumC :
      (∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) = 0 := by
    exact_mod_cast
      threePointSecondDividedDifferenceCoeff_sum_eq_zero
        (x := x) (y := y) (z := z) hyx hzx hyz
  simp [hsumC]

/--
Explicit scalar form of the barycentric coefficient of the quadratic order-ray
term.  This separates the diagonal square contribution from the `ε` and
`ε²` ray contributions.
-/
theorem threePointBarycentricOrderRaySqCoeff_explicit
    (x y z ε : ℝ) :
    threePointBarycentricOrderRaySqCoeff x y z ε =
      (∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) +
        (2 : ℂ) * (ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) *
              ((threePointNodes x y z i : ℝ) : ℂ)) +
        (3 : ℂ) * (ε : ℂ) ^ 2 *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) ^ 2 := by
  simp [threePointBarycentricOrderRaySqCoeff,
    threePointSecondDifferenceBarycentricVector, Fin.sum_univ_three]
  ring_nf

/-- The quadratic barycentric weight has no ray-parameter terms at distinct nodes. -/
theorem threePointBarycentricOrderRaySqCoeff_distinct
    {x y z ε : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    threePointBarycentricOrderRaySqCoeff x y z ε =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          (((threePointNodes x y z i : ℝ) : ℂ) ^ 2) := by
  rw [threePointBarycentricOrderRaySqCoeff_explicit]
  have hsumC :
      (∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) = 0 := by
    exact_mod_cast
      threePointSecondDividedDifferenceCoeff_sum_eq_zero
        (x := x) (y := y) (z := z) hyx hzx hyz
  simp [hsumC]

/-- Explicit scalar form of the diagonal base contribution. -/
theorem threePointBarycentricDiagonalBaseTerm_explicit
    (f : ℝ → ℝ) (x y z : ℝ) :
    threePointBarycentricDiagonalBaseTerm f x y z =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  simp [threePointBarycentricDiagonalBaseTerm,
    threePointSecondDifferenceBarycentricVector, Fin.sum_univ_three]
  ring_nf

/-! ### Explicit scalar normal forms -/

/--
Factored coefficient form expanded into pure scalar barycentric weights.

This is the exact scalar normal form to be used for the remaining local-bound
extraction in the three-point order-ray diagnostic.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_explicitScalarFormula
    (f : ℝ → ℝ) (x y z ε : ℝ)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2) +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          ((∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
              ((threePointNodes x y z i : ℝ) : ℂ)) +
            (ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) ^ 2) +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          ((∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
              (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) +
            (2 : ℂ) * (ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) *
                  ((threePointNodes x y z i : ℝ) : ℂ)) +
            (3 : ℂ) * (ε : ℂ) ^ 2 *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ)) ^ 2) -
        ∑ i : Fin 3,
          (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
            (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  rw [
    threePointCFCOrderRayDifference_barycentricQuadratic_coeffFactoredFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes),
    threePointBarycentricUnitCoeff_explicit,
    threePointBarycentricOrderRayCoeff_explicit,
    threePointBarycentricOrderRaySqCoeff_explicit,
    threePointBarycentricDiagonalBaseTerm_explicit]

/--
At distinct nodes the explicit scalar formula has no remaining `ε`-dependence
in the barycentric weights; only the spectral coefficients still depend on
the order-ray parameter.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_distinctScalarFormula
    (f : ℝ → ℝ) {x y z ε : ℝ}
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z)
    (heig : Function.Injective (threePointOrderRayEigenvalue x y z ε))
    (hnodes : Function.Injective (threePointNodes x y z)) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (threePointSecondDifferenceBarycentricVector x y z i) *
          threePointCFCOrderRayDifferenceEntryFormula f x y z ε i j *
            threePointSecondDifferenceBarycentricVector x y z j =
      (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2) +
        (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
              ((threePointNodes x y z i : ℝ) : ℂ)) +
        (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
          (∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
              (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) -
        ∑ i : Fin 3,
          (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
            (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  rw [
    threePointCFCOrderRayDifference_barycentricQuadratic_coeffFactoredFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      (heig := heig) (hnodes := hnodes),
    threePointBarycentricUnitCoeff_explicit,
    threePointBarycentricOrderRayCoeff_distinct hyx hzx hyz,
    threePointBarycentricOrderRaySqCoeff_distinct hyx hzx hyz,
    threePointBarycentricDiagonalBaseTerm_explicit]

/-! ### Linear versus quadratic barycentric weights -/

/--
The target scalar second divided difference is the linear barycentric
combination of the normalized scalar values `f(node) - f 0`.

This is deliberately kept next to the quadratic positivity formula: it makes
explicit that the positivity test currently controls a quadratic-weight
diagonal base term, while the desired divided difference uses the first power
of the barycentric coefficients.
-/
theorem threePointSecondDividedDifference_linearBarycentricTerm
    (f : ℝ → ℝ) {x y z : ℝ} (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    (threePointSecondDividedDifference f x y z : ℂ) =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) *
          (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  have hreal :
      threePointSecondDividedDifference f x y z =
        ∑ i : Fin 3,
          threePointSecondDividedDifferenceCoeff x y z i *
            (f (threePointNodes x y z i) - f 0) := by
    rw [threePointSecondDividedDifference_barycentric_formula f hyx hzx hyz]
    have hsum0 :
        ∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i = 0 :=
      threePointSecondDividedDifferenceCoeff_sum_eq_zero
        (x := x) (y := y) (z := z) hyx hzx hyz
    have hshift :
        (∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i *
            (f (threePointNodes x y z i) - f 0)) =
          ∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i *
            f (threePointNodes x y z i) := by
      have hcomm :
          (∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i * f 0) =
            ∑ i : Fin 3, f 0 * threePointSecondDividedDifferenceCoeff x y z i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      calc
        (∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i *
            (f (threePointNodes x y z i) - f 0)) =
            (∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i *
              f (threePointNodes x y z i)) -
              f 0 * ∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i := by
              simp [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, hcomm]
        _ = ∑ i : Fin 3, threePointSecondDividedDifferenceCoeff x y z i *
            f (threePointNodes x y z i) := by
            simp [hsum0]
    simp [hshift]
  exact_mod_cast hreal

/--
The diagonal base term appearing in the barycentric quadratic positivity test
uses quadratic barycentric weights.
-/
theorem threePointBarycentricDiagonalBaseTerm_quadraticWeight
    (f : ℝ → ℝ) (x y z : ℝ) :
    threePointBarycentricDiagonalBaseTerm f x y z =
      ∑ i : Fin 3,
        (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
          (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  exact threePointBarycentricDiagonalBaseTerm_explicit f x y z

/-! ### Eventual scalar inequality from positivity -/

/--
Closed CFC positivity, combined with the distinct-node scalar normal form,
gives only the quadratic-weight scalar inequality.  The injectivity of the
three eigenvalue branches is kept as an eventual-side hypothesis; extracting a
local bound for the linear second divided difference is the remaining
three-point order-ray scalar problem.
-/
theorem threePointCFCOrderRayDifference_barycentricQuadratic_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (threePointOrderRayEigenvalue x y z ε) →
        0 ≤
          (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2) +
            (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                  ((threePointNodes x y z i : ℝ) : ℂ)) +
            (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                  (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) -
            ∑ i : Fin 3,
              (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  have hnodes : Function.Injective (threePointNodes x y z) :=
    threePointNodes_injective_of_ne hyx hzx hyz
  filter_upwards
    [threePointCFCOrderRayDifference_entryFormula_barycentricQuadratic_nonneg_eventually
      hfinite hx hy hz] with ε hnonneg heig
  have hformula :=
    threePointCFCOrderRayDifference_barycentricQuadratic_distinctScalarFormula
      (f := f) (x := x) (y := y) (z := z) (ε := ε)
      hyx hzx hyz heig hnodes
  have hineq :
      0 ≤
        (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
            (∑ i : Fin 3,
              (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2) +
          (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
            (∑ i : Fin 3,
              (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                ((threePointNodes x y z i : ℝ) : ℂ)) +
          (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
            (∑ i : Fin 3,
              (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) -
          ∑ i : Fin 3,
            (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
              (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
    exact hformula ▸ hnonneg
  simpa using hineq

/--
Semantic alias for the scalar inequality now obtained from the explicit
distinct-node formula and positivity.  The conclusion is intentionally this
quadratic-weight inequality, not the linear second-divided-difference bound.
-/
theorem threePointCFCOrderRayDifference_explicitScalarInequality_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (threePointOrderRayEigenvalue x y z ε) →
        0 ≤
          (threePointOrderRaySpectralQuadraticCoeff0 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2) +
            (threePointOrderRaySpectralQuadraticCoeff1 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                  ((threePointNodes x y z i : ℝ) : ℂ)) +
            (threePointOrderRaySpectralQuadraticCoeff2 f x y z ε : ℂ) *
              (∑ i : Fin 3,
                (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                  (((threePointNodes x y z i : ℝ) : ℂ) ^ 2)) -
            ∑ i : Fin 3,
              (threePointSecondDividedDifferenceCoeff x y z i : ℂ) ^ 2 *
                (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) :=
  threePointCFCOrderRayDifference_barycentricQuadratic_nonneg_eventually
    hfinite hx hy hz hyx hzx hyz


end

end Quantum.TraceInequality.Loewner
