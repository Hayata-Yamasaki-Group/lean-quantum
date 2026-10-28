import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.ThreePointOrderRayCore

/-!
# Chapter 3 weighted three-point order-ray diagnostics

This file contains the weighted and polarized three-point order-ray
diagnostic layer, plus the raw modulus producers built from local
three-point second-divided-difference bounds.
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
Three-point rank-one order ray with an arbitrary perturbation direction.

This is the polarized variant of the all-ones ray.  It is used only as a
diagnostic three-point order-ray layer: changing the positive rank-one direction separates
the perturbation vector from the test vector, but the diagonal base term of the
quadratic test still depends on the test vector through absolute-square
weights.
-/
def threePointWeightedOrderRayMatrix
    (x y z : ℝ) (u : Fin 3 → ℂ) (ε : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  diagonalPerturbation (threePointNodes x y z) u ε

/-- The `CStarMatrix` copy of the weighted three-point order ray. -/
def threePointWeightedCStarOrderRayMatrix
    (x y z : ℝ) (u : Fin 3 → ℂ) (ε : ℝ) :
    CStarMatrix (Fin 3) (Fin 3) ℂ :=
  cStarDiagonalPerturbation (threePointNodes x y z) u ε

/-- Weighted three-point order rays remain in the interval CFC domain near the base. -/
lemma threePointWeightedCStarOrderRay_mem_domain_eventually
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (u : Fin 3 → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      threePointWeightedCStarOrderRayMatrix x y z u ε ∈
        cStarFiniteMatrixDomain 3 := by
  simpa [threePointWeightedCStarOrderRayMatrix] using
    (cStarDiagonalPerturbation_mem_domain_eventually
      (threePointNodes x y z)
      (threePointNodes_mem_Ioo hx hy hz) u)

/-- The weighted three-point CStar order ray is above its diagonal base. -/
lemma threePointWeightedCStarOrderRay_le_of_nonneg
    (x y z : ℝ) (u : Fin 3 → ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    cStarDiagonalMatrix (threePointNodes x y z) ≤
      threePointWeightedCStarOrderRayMatrix x y z u ε := by
  simpa [threePointWeightedCStarOrderRayMatrix] using
    (cStarDiagonalMatrix_le_perturbation_of_nonneg
      (threePointNodes x y z) u hε)

/-- Finite matrix monotonicity gives the weighted three-point CFC comparison. -/
theorem threePointWeightedCFCOrderRayComparison
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (u : Fin 3 → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (threePointNodes x y z)) ≤
        cfcₙ (fun t : ℝ => f t - f 0)
          (threePointWeightedCStarOrderRayMatrix x y z u ε) := by
  filter_upwards
    [threePointWeightedCStarOrderRay_mem_domain_eventually hx hy hz u,
      self_mem_nhdsWithin] with ε hdom hεpos
  have hbase :
      cStarDiagonalMatrix (threePointNodes x y z) ∈
        cStarFiniteMatrixDomain 3 :=
    cStarDiagonalMatrix_mem_domain
      (threePointNodes x y z) (threePointNodes_mem_Ioo hx hy hz)
  have hle_ray :
      cStarDiagonalMatrix (threePointNodes x y z) ≤
        threePointWeightedCStarOrderRayMatrix x y z u ε :=
    threePointWeightedCStarOrderRay_le_of_nonneg x y z u (le_of_lt hεpos)
  exact hfinite.cfc_monotone_matrix 3 hbase hdom hle_ray

/-- CFC difference matrix for a weighted three-point rank-one order ray. -/
def threePointWeightedCFCOrderRayDifference
    (f : ℝ → ℝ) (x y z : ℝ) (u : Fin 3 → ℂ) (ε : ℝ) :
    CStarMatrix (Fin 3) (Fin 3) ℂ :=
  cfcₙ (fun t : ℝ => f t - f 0)
      (threePointWeightedCStarOrderRayMatrix x y z u ε) -
    cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (threePointNodes x y z))

/-- Weighted CFC comparison as eventual positivity of the difference matrix. -/
theorem threePointWeightedCFCOrderRayDifference_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (u : Fin 3 → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ threePointWeightedCFCOrderRayDifference f x y z u ε := by
  filter_upwards
    [threePointWeightedCFCOrderRayComparison hfinite hx hy hz u] with ε hle
  simpa [threePointWeightedCFCOrderRayDifference] using sub_nonneg.mpr hle

/-- Weighted positive CFC differences have nonnegative quadratic tests. -/
theorem threePointWeightedCFCOrderRayDifference_testVector_nonneg_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x y z : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (u c : Fin 3 → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ star c ⬝ᵥ
        ((CStarMatrix.ofMatrix.symm
          (threePointWeightedCFCOrderRayDifference f x y z u ε)) *ᵥ c) := by
  filter_upwards
    [threePointWeightedCFCOrderRayDifference_nonneg_eventually
      hfinite hx hy hz u] with ε hnonneg
  exact cStarMatrix_quadratic_nonneg_of_nonneg hnonneg c

/-- Entry of a weighted three-point CFC order-ray difference matrix. -/
def threePointWeightedCFCOrderRayDifferenceEntryFormula
    (f : ℝ → ℝ) (x y z : ℝ) (u : Fin 3 → ℂ) (ε : ℝ) (i j : Fin 3) : ℂ :=
  (CStarMatrix.ofMatrix.symm
    (threePointWeightedCFCOrderRayDifference f x y z u ε)) i j

/-- Weighted quadratic CFC positivity expanded entrywise. -/
theorem threePointWeightedCFCOrderRayDifference_testVector_entry_formula
    (f : ℝ → ℝ) (x y z : ℝ) (u c : Fin 3 → ℂ) (ε : ℝ) :
    star c ⬝ᵥ
        ((CStarMatrix.ofMatrix.symm
          (threePointWeightedCFCOrderRayDifference f x y z u ε)) *ᵥ c) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (c i) *
          threePointWeightedCFCOrderRayDifferenceEntryFormula f x y z u ε i j *
            c j := by
  simp [threePointWeightedCFCOrderRayDifferenceEntryFormula, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  ring_nf

/-- Quadratic test associated to a weighted three-point CFC order-ray difference. -/
def threePointWeightedCFCOrderRayQuadraticTest
    (f : ℝ → ℝ) (x y z : ℝ) (u c : Fin 3 → ℂ) (ε : ℝ) : ℂ :=
  star c ⬝ᵥ
    ((CStarMatrix.ofMatrix.symm
      (threePointWeightedCFCOrderRayDifference f x y z u ε)) *ᵥ c)

/-- Entrywise expansion of the weighted CFC order-ray quadratic test. -/
theorem threePointWeightedCFCOrderRayQuadraticTest_entry_formula
    (f : ℝ → ℝ) (x y z : ℝ) (u c : Fin 3 → ℂ) (ε : ℝ) :
    threePointWeightedCFCOrderRayQuadraticTest f x y z u c ε =
      ∑ i : Fin 3, ∑ j : Fin 3,
        star (c i) *
          threePointWeightedCFCOrderRayDifferenceEntryFormula f x y z u ε i j *
            c j := by
  simpa [threePointWeightedCFCOrderRayQuadraticTest] using
    threePointWeightedCFCOrderRayDifference_testVector_entry_formula f x y z u c ε

/--
Entry formula for the weighted rank-one ray itself.  The off-diagonal part is
controlled by the perturbation direction `u`, while the diagonal base remains
the original three nodes.
-/
theorem threePointWeightedCStarOrderRayMatrix_entry_formula
    (x y z : ℝ) (u : Fin 3 → ℂ) (ε : ℝ) (i j : Fin 3) :
    (threePointWeightedCStarOrderRayMatrix x y z u ε) i j =
      (if i = j then ((threePointNodes x y z i : ℝ) : ℂ) else 0) +
        (ε : ℂ) * u i * star (u j) := by
  simp [threePointWeightedCStarOrderRayMatrix, cStarDiagonalPerturbation,
    diagonalPerturbation, diagonalMatrix, rankOnePerturbation,
    Matrix.vecMulVec, Matrix.diagonal_apply]
  ring

/--
Product seen by first-order rank-one entries after testing with a vector `c`.
Because the quadratic form uses `star c` on the left, the natural product is
`star (c i) * u i`.
-/
def threePointPolarizedRankOneWeight
    (u c : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  star (c i) * u i

/-- Condition that a polarized test sees the barycentric coefficient vector. -/
def threePointPolarizedMatchesBarycentric
    (x y z : ℝ) (u c : Fin 3 → ℂ) : Prop :=
  ∀ i : Fin 3,
    threePointPolarizedRankOneWeight u c i =
      (threePointSecondDividedDifferenceCoeff x y z i : ℂ)

/--
If the polarized product `star c_i * u_i` matches the barycentric coefficients,
then the corresponding linear scalar term is exactly the second divided
difference.
-/
theorem threePointPolarizedLinearTerm_eq_secondDividedDifference
    (f : ℝ → ℝ) {x y z : ℝ} {u c : Fin 3 → ℂ}
    (hmatch : threePointPolarizedMatchesBarycentric x y z u c)
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∑ i : Fin 3,
        threePointPolarizedRankOneWeight u c i *
          (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) =
      (threePointSecondDividedDifference f x y z : ℂ) := by
  rw [threePointSecondDividedDifference_linearBarycentricTerm
    f hyx hzx hyz]
  apply Finset.sum_congr rfl
  intro i _
  rw [hmatch i]

/--
The rank-one first-order direction seen by a quadratic test factors through the
polarized products `star c_i * u_i`.
-/
theorem threePointWeightedRankOneTestContribution_formula
    (u c : Fin 3 → ℂ) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        star (c i) * (u i * star (u j)) * c j =
      ∑ i : Fin 3, ∑ j : Fin 3,
        threePointPolarizedRankOneWeight u c i *
          star (threePointPolarizedRankOneWeight u c j) := by
  simp [threePointPolarizedRankOneWeight, mul_comm, mul_left_comm]

/-- Diagonal base contribution of a weighted test vector. -/
def threePointWeightedDiagonalBaseTerm
    (f : ℝ → ℝ) (x y z : ℝ) (c : Fin 3 → ℂ) : ℂ :=
  ∑ i : Fin 3,
    star (c i) * (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) * c i

/--
The diagonal base contribution of any positive rank-one test is weighted by
`star c_i * c_i`.  Thus polarization of the perturbation direction does not by
itself turn the diagonal base term into the desired linear barycentric
combination.
-/
theorem threePointWeightedDiagonalBaseTerm_absoluteSquareWeight
    (f : ℝ → ℝ) (x y z : ℝ) (c : Fin 3 → ℂ) :
    threePointWeightedDiagonalBaseTerm f x y z c =
      ∑ i : Fin 3,
        (star (c i) * c i) *
          (((f (threePointNodes x y z i) - f 0 : ℝ) : ℂ)) := by
  simp [threePointWeightedDiagonalBaseTerm, sub_eq_add_neg,
    mul_comm, mul_left_comm]

/--
Scale the perturbation direction in the polarized weighted diagnostic.

The intended use is to increase the rank-one direction while shrinking the
test vector by the inverse scale.
-/
def threePointPolarizedScaledDirection
    (R : ℝ) (u : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => (R : ℂ) * u i

/-- The inverse-scaled test vector paired with `threePointPolarizedScaledDirection`. -/
def threePointPolarizedScaledTestVector
    (R : ℝ) (c : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => ((R : ℂ)⁻¹) * c i

/--
The scaled direction/test-vector pair preserves the polarized first-order
product `star c_i * u_i`.
-/
theorem threePointPolarizedRankOneWeight_scaled
    {R : ℝ} (hR : R ≠ 0) (u c : Fin 3 → ℂ) (i : Fin 3) :
    threePointPolarizedRankOneWeight
        (threePointPolarizedScaledDirection R u)
        (threePointPolarizedScaledTestVector R c) i =
      threePointPolarizedRankOneWeight u c i := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  simp [threePointPolarizedRankOneWeight,
    threePointPolarizedScaledDirection,
    threePointPolarizedScaledTestVector, hRc, mul_comm, mul_assoc]

/--
If the original polarized pair matches the barycentric coefficients, then the
scaled pair does as well.
-/
theorem threePointPolarizedMatchesBarycentric_scaled
    {R : ℝ} (hR : R ≠ 0) {x y z : ℝ} {u c : Fin 3 → ℂ}
    (hmatch : threePointPolarizedMatchesBarycentric x y z u c) :
    threePointPolarizedMatchesBarycentric x y z
      (threePointPolarizedScaledDirection R u)
      (threePointPolarizedScaledTestVector R c) := by
  intro i
  rw [threePointPolarizedRankOneWeight_scaled hR u c i, hmatch i]

/--
Scaling the perturbation direction by `R` is equivalent to replacing the ray
parameter by `ε * R^2`.
-/
theorem threePointWeightedCStarOrderRayMatrix_scaled
    (x y z R ε : ℝ) (u : Fin 3 → ℂ) :
    threePointWeightedCStarOrderRayMatrix x y z
        (threePointPolarizedScaledDirection R u) ε =
      threePointWeightedCStarOrderRayMatrix x y z u (ε * R ^ 2) := by
  ext i j
  simp [threePointWeightedCStarOrderRayMatrix_entry_formula,
    threePointPolarizedScaledDirection, pow_two]
  ring

/--
The corresponding CFC difference has the same scaling, but this reindexes the
positive ray parameter from `ε` to `ε * R^2`.
-/
theorem threePointWeightedCFCOrderRayDifference_scaled
    (f : ℝ → ℝ) (x y z R ε : ℝ) (u : Fin 3 → ℂ) :
    threePointWeightedCFCOrderRayDifference f x y z
        (threePointPolarizedScaledDirection R u) ε =
      threePointWeightedCFCOrderRayDifference f x y z u (ε * R ^ 2) := by
  simp [threePointWeightedCFCOrderRayDifference,
    threePointWeightedCStarOrderRayMatrix_scaled]

/--
The absolute-square weight of the inverse-scaled test vector is multiplied by
`1 / R^2`.
-/
theorem threePointWeightedDiagonalBaseTerm_scaled_absoluteSquareControl
    (R : ℝ) (c : Fin 3 → ℂ) (i : Fin 3) :
    star (threePointPolarizedScaledTestVector R c i) *
        threePointPolarizedScaledTestVector R c i =
      (((R ^ 2)⁻¹ : ℝ) : ℂ) * (star (c i) * c i) := by
  simp [threePointPolarizedScaledTestVector, pow_two, mul_comm,
    mul_left_comm, mul_assoc]

/--
Consequently, the diagonal base contribution of the inverse-scaled test vector
is the original diagonal base contribution multiplied by `1 / R^2`.
-/
theorem threePointWeightedDiagonalBaseTerm_scaled
    (f : ℝ → ℝ) (x y z R : ℝ) (c : Fin 3 → ℂ) :
    threePointWeightedDiagonalBaseTerm f x y z
        (threePointPolarizedScaledTestVector R c) =
      (((R ^ 2)⁻¹ : ℝ) : ℂ) *
        threePointWeightedDiagonalBaseTerm f x y z c := by
  simp [threePointWeightedDiagonalBaseTerm,
    threePointPolarizedScaledTestVector, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc, pow_two]

/--
Scaling the perturbation direction and inverse-scaling the test vector only
rescales the whole quadratic test, while the CFC ray parameter is reindexed
from `ε` to `ε * R^2`.
-/
theorem threePointWeightedCFCOrderRayQuadraticTest_scaled
    (f : ℝ → ℝ) (x y z R ε : ℝ) (u c : Fin 3 → ℂ) :
    threePointWeightedCFCOrderRayQuadraticTest f x y z
        (threePointPolarizedScaledDirection R u)
        (threePointPolarizedScaledTestVector R c) ε =
      (((R ^ 2)⁻¹ : ℝ) : ℂ) *
        threePointWeightedCFCOrderRayQuadraticTest f x y z u c (ε * R ^ 2) := by
  rw [threePointWeightedCFCOrderRayQuadraticTest_entry_formula,
    threePointWeightedCFCOrderRayQuadraticTest_entry_formula]
  simp [threePointWeightedCFCOrderRayDifferenceEntryFormula,
    threePointWeightedCFCOrderRayDifference_scaled,
    threePointPolarizedScaledTestVector, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc, pow_two]

/--
Positive-neighborhood events can be pulled back along the reindexing
`ε ↦ ε * R^2` when `R ≠ 0`.
-/
theorem eventually_nhdsWithin_pos_mul_sq
    {R : ℝ} (hR : R ≠ 0) {p : ℝ → Prop}
    (hp : ∀ᶠ η in 𝓝[>] (0 : ℝ), p η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p (ε * R ^ 2) := by
  have hpos : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  have htend :
      Filter.Tendsto (fun ε : ℝ => ε * R ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun ε : ℝ => ε * R ^ 2) (0 : ℝ) :=
        continuousAt_id.mul continuousAt_const
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using mul_pos hε hpos
  exact htend.eventually hp

/--
A local bound on the three-point second divided difference gives the pairwise
raw divided-difference modulus estimate.
-/
theorem twoPointRawDividedDifference_pairwise_modulus_of_threePointSecondDifferenceBound
    {f : ℝ → ℝ} {x : ℝ}
    (hbound :
      ∃ M > 0, ∃ ρ > 0,
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < ρ →
          ∀ z ∈ Set.Ioo (-1 : ℝ) 1, z ≠ x → dist z x < ρ →
            y ≠ z →
              |threePointSecondDividedDifference f x y z| ≤ M) :
    ∀ ε > 0,
      ∃ δ > 0,
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < δ →
          ∀ z ∈ Set.Ioo (-1 : ℝ) 1, z ≠ x → dist z x < δ →
            dist (twoPointRawDividedDifference f x y)
              (twoPointRawDividedDifference f x z) < ε := by
  intro ε hε
  rcases hbound with ⟨M, hM, ρ, hρ, hlocal⟩
  let δ : ℝ := min (ρ / 2) (ε / (4 * M))
  have hδ : 0 < δ := by
    have hρ2 : 0 < ρ / 2 := half_pos hρ
    have hεM : 0 < ε / (4 * M) := by
      positivity
    exact lt_min hρ2 hεM
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyx hydist z hz hzx hzdist
  by_cases hyz : y = z
  · subst z
    simpa using hε
  · have hδρ : δ < ρ := by
      have hδ_le : δ ≤ ρ / 2 := min_le_left _ _
      linarith
    have hyρ : dist y x < ρ := lt_trans hydist hδρ
    have hzρ : dist z x < ρ := lt_trans hzdist hδρ
    have hsecond := hlocal y hy hyx hyρ z hz hzx hzρ hyz
    have hsub :=
      twoPointRawDividedDifference_sub_eq_secondDividedDifference_mul
        f x hyz
    have hdist_yz : |y - z| < 2 * δ := by
      have htri : dist y z ≤ dist y x + dist z x := by
        calc
          dist y z ≤ dist y x + dist x z := dist_triangle y x z
          _ = dist y x + dist z x := by rw [dist_comm x z]
      have hsum : dist y x + dist z x < δ + δ := by
        linarith
      have hlt : dist y z < 2 * δ := by
        linarith
      simpa [Real.dist_eq] using hlt
    have hprod : M * |y - z| < ε := by
      have hδ_le : δ ≤ ε / (4 * M) := min_le_right _ _
      have hMdist : M * |y - z| < M * (2 * δ) :=
        mul_lt_mul_of_pos_left hdist_yz hM
      have hMδ : M * (2 * δ) ≤ ε / 2 := by
        calc
          M * (2 * δ) = 2 * M * δ := by ring
          _ ≤ 2 * M * (ε / (4 * M)) := by
            gcongr
          _ = ε / 2 := by
            field_simp [ne_of_gt hM]
            ring
      linarith
    have habs :
        |twoPointRawDividedDifference f x y -
            twoPointRawDividedDifference f x z| < ε := by
      rw [hsub, abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsecond (abs_nonneg _)) hprod
    simpa [Real.dist_eq] using habs
end

end Quantum.TraceInequality.Loewner
