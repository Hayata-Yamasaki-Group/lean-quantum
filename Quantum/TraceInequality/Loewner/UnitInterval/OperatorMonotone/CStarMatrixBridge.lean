import Quantum.Analysis.Matrix.UnitIntervalOrder
import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData
import Quantum.TraceInequality.Loewner.RealComplexOrder
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Quantum.TraceInequality.HiaiPetz.FinMatrixCStar

/-!
# Chapter 3 finite CStarMatrix bridge

This file contains the finite-dimensional matrix and `CStarMatrix` bridge used
at the start of the route from operator monotonicity to finite Loewner
positivity on the normalized interval.
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

open scoped FinMatrixCStar

theorem unitIntervalMatrixMonotone_of_finiteMatrixMonotone {f : ℝ → ℝ}
    (h : UnitIntervalFiniteMatrixMonotone.{0} f) : UnitIntervalMatrixMonotone f where
  cfc_monotone_matrix := by
    intro n
    exact @UnitIntervalFiniteMatrixMonotone.cfc_monotone_finite.{0} f h
      (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance CStarMatrix.instPartialOrder
      CStarMatrix.instStarOrderedRing (@instFinCStarMatrixFiniteDimensional n)

/--
The public operator-monotone predicate immediately restricts to finite
dimensions.
-/
theorem finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval {f : ℝ → ℝ}
    (h : OperatorMonotoneOnUnitInterval.{u} f) :
    UnitIntervalFiniteMatrixMonotone.{u} f where
  cfc_monotone_finite := by
    intro A _ _ _ _
    exact h.cfc_monotone

/-- The finite Löwner matrix is Hermitian. -/
lemma loewnerMatrix_isHermitian (f : ℝ → ℝ) (n : ℕ) (x : Fin n → ℝ) :
    (Matrix.of
      (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp [loewnerKernel_swap]

/--
Convert the nonnegativity of all complex quadratic forms into positive
semidefiniteness of the finite Löwner matrix.
-/
theorem loewnerMatrix_posSemidef_of_quadratic_nonneg
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hquad :
      ∀ c : Fin n → ℂ,
        0 ≤ star c ⬝ᵥ
          ((Matrix.of
            (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c)) :
    (Matrix.of
      (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (loewnerMatrix_isHermitian f n x) hquad

/-- The finite matrix domain used by the CFC monotonicity predicate. -/
def finiteMatrixDomain (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {a | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}

/-- Diagonal matrix with the interpolation nodes on the diagonal. -/
def diagonalMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (x i : ℂ)

/-- Rank-one positive direction used for the diagonal first variation. -/
def rankOnePerturbation {n : ℕ} (c : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec c (star c)

/-- The order ray through the diagonal matrix in the rank-one positive direction. -/
def diagonalPerturbation {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  diagonalMatrix x + ε • rankOnePerturbation c

/-- The rank-one perturbation direction is positive semidefinite. -/
lemma rankOnePerturbation_posSemidef {n : ℕ} (c : Fin n → ℂ) :
    (rankOnePerturbation c).PosSemidef := by
  simpa [rankOnePerturbation] using
    (Matrix.posSemidef_vecMulVec_self_star (R := ℂ) c)

/-- Moving in a nonnegative rank-one direction increases the diagonal matrix. -/
lemma diagonalMatrix_le_perturbation_of_nonneg
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    diagonalMatrix x ≤ diagonalPerturbation x c ε := by
  rw [Matrix.le_iff]
  have hdir : (ε • rankOnePerturbation c).PosSemidef :=
    (rankOnePerturbation_posSemidef c).smul hε
  simpa [diagonalPerturbation] using hdir

/-- The diagonal interpolation matrix is self-adjoint. -/
lemma diagonalMatrix_isSelfAdjoint {n : ℕ} (x : Fin n → ℝ) :
    IsSelfAdjoint (diagonalMatrix x) := by
  change (diagonalMatrix x).IsHermitian
  rw [diagonalMatrix, Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

/-- The diagonal interpolation matrix lies in the CFC interval domain. -/
lemma diagonalMatrix_mem_domain {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) :
    diagonalMatrix x ∈ finiteMatrixDomain n := by
  refine ⟨diagonalMatrix_isSelfAdjoint x, ?_⟩
  intro y hy
  have hyq : y = 0 ∨ y ∈ spectrum ℝ (diagonalMatrix x) :=
    (mem_quasispectrum_iff (a := diagonalMatrix x) (x := y)).mp hy
  rcases hyq with rfl | hy
  · simp
  · rw [← spectrum.preimage_algebraMap ℂ] at hy
    simp only [Set.mem_preimage] at hy
    rw [diagonalMatrix, spectrum_diagonal] at hy
    rcases hy with ⟨i, hi⟩
    have hyeq : y = x i := Complex.ofReal_injective hi.symm
    simpa [hyeq] using hx i

/-- The rank-one first-variation direction is self-adjoint. -/
lemma rankOnePerturbation_isSelfAdjoint {n : ℕ} (c : Fin n → ℂ) :
    IsSelfAdjoint (rankOnePerturbation c) := by
  rw [isSelfAdjoint_iff]
  ext i j
  simp [rankOnePerturbation, Matrix.vecMulVec, mul_comm]

/-- Every diagonal rank-one perturbation on the order ray is self-adjoint. -/
lemma diagonalPerturbation_isSelfAdjoint
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) :
    IsSelfAdjoint (diagonalPerturbation x c ε) := by
  exact (diagonalMatrix_isSelfAdjoint x).add
    ((IsSelfAdjoint.all ε).smul (rankOnePerturbation_isSelfAdjoint c))

/-- The diagonal perturbation tends back to the diagonal base point as `ε → 0`. -/
lemma diagonalPerturbation_tendsto_zero
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Filter.Tendsto (fun ε : ℝ => diagonalPerturbation x c ε)
      (𝓝 (0 : ℝ)) (𝓝 (diagonalMatrix x)) := by
  have hsmul : ContinuousAt (fun ε : ℝ => ε • rankOnePerturbation c) (0 : ℝ) :=
    continuousAt_id.smul continuousAt_const
  have hconst : ContinuousAt (fun _ : ℝ => diagonalMatrix x) (0 : ℝ) :=
    continuousAt_const
  have h : ContinuousAt
      (fun ε : ℝ => diagonalMatrix x + ε • rankOnePerturbation c)
      (0 : ℝ) := by
    simpa [Pi.add_apply] using hconst.add hsmul
  have hz :
      diagonalMatrix x + (0 : ℝ) • rankOnePerturbation c =
        diagonalMatrix x := by
    ext i j
    simp
  have ht := h.tendsto
  change Filter.Tendsto
    (fun ε : ℝ => diagonalMatrix x + ε • rankOnePerturbation c)
    (𝓝 (0 : ℝ))
    (𝓝 (diagonalMatrix x + (0 : ℝ) • rankOnePerturbation c)) at ht
  rw [hz] at ht
  simpa [diagonalPerturbation] using ht

/--
If a path tends to a point with real quasispectrum in `(-1,1)`, this holds eventually.
-/
lemma quasispectrum_subset_Ioo_eventually
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
    [IsScalarTower ℝ A A] [CompleteSpace A]
    {a₀ : A} {a : ℝ → A}
    (hbase : quasispectrum ℝ a₀ ⊆ Set.Ioo (-1 : ℝ) 1)
    (htend : Filter.Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 a₀)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      quasispectrum ℝ (a ε) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  have hupper := (upperHemicontinuous_quasispectrum ℝ A).upperHemicontinuousAt a₀
  rw [upperHemicontinuousAt_iff_forall_isOpen] at hupper
  have hnhds : ∀ᶠ b in 𝓝 a₀, quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1 :=
    hupper (Set.Ioo (-1 : ℝ) 1) isOpen_Ioo hbase
  exact htend.eventually hnhds

/--
Scalar difference quotient obtained by applying the normalized CFC map along the
rank-one order ray and testing against the same vector.
-/
def diagonalVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) : ℂ :=
  (ε⁻¹ : ℝ) •
    (star c ⬝ᵥ
      ((cfcₙ (fun t : ℝ => f t - f 0) (diagonalPerturbation x c ε) -
        cfcₙ (fun t : ℝ => f t - f 0) (diagonalMatrix x)) *ᵥ c))

/-- The same finite-dimensional CFC domain, viewed in Mathlib's `CStarMatrix` copy. -/
def cStarFiniteMatrixDomain (n : ℕ) :
    Set (CStarMatrix (Fin n) (Fin n) ℂ) :=
  {a | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}

/-- The diagonal matrix in the `CStarMatrix` copy used by the CFC order API. -/
def cStarDiagonalMatrix {n : ℕ} (x : Fin n → ℝ) :
    CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (diagonalMatrix x)

/-- The rank-one positive direction in the `CStarMatrix` copy. -/
def cStarRankOnePerturbation {n : ℕ} (c : Fin n → ℂ) :
    CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (rankOnePerturbation c)

/-- The diagonal order ray in the `CStarMatrix` copy. -/
def cStarDiagonalPerturbation
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) :
    CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (diagonalPerturbation x c ε)

/--
The same scalar difference quotient after applying finite-dimensional
monotonicity in the `CStarMatrix` C*-algebra copy.
-/
def cStarDiagonalVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) : ℂ :=
  (ε⁻¹ : ℝ) •
    (star c ⬝ᵥ
      (((CStarMatrix.ofMatrix.symm
          (cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalPerturbation x c ε))) -
        (CStarMatrix.ofMatrix.symm
          (cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalMatrix x)))) *ᵥ c))

/--
Testing a positive `CStarMatrix` against a vector gives a nonnegative complex
quadratic form on the underlying matrix.
-/
lemma cStarMatrix_quadratic_nonneg_of_nonneg
    {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) ℂ} (hM : 0 ≤ M)
    (c : Fin n → ℂ) :
    0 ≤ star c ⬝ᵥ ((CStarMatrix.ofMatrix.symm M) *ᵥ c) :=
  (cStarMatrix_posSemidef_of_nonneg hM).dotProduct_mulVec_nonneg c

/-- The `CStarMatrix` order ray increases in a nonnegative rank-one direction. -/
lemma cStarDiagonalMatrix_le_perturbation_of_nonneg
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    cStarDiagonalMatrix x ≤ cStarDiagonalPerturbation x c ε := by
  rw [← sub_nonneg]
  have hdir : (ε • rankOnePerturbation c).PosSemidef :=
    (rankOnePerturbation_posSemidef c).smul hε
  simpa [cStarDiagonalMatrix, cStarDiagonalPerturbation,
    diagonalPerturbation, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using cStarMatrix_nonneg_of_posSemidef hdir

/-- The `CStarMatrix` and plain-matrix scalar quotients have the same formula. -/
lemma diagonalVariationQuotient_eq_cstar
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) :
    diagonalVariationQuotient f x c ε =
      cStarDiagonalVariationQuotient f x c ε := by
  rfl

/-- The diagonal interpolation matrix lies in the CFC interval domain in `CStarMatrix`. -/
lemma cStarDiagonalMatrix_mem_domain {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) :
    cStarDiagonalMatrix x ∈ cStarFiniteMatrixDomain n := by
  refine ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint x).star_eq
    simpa [cStarDiagonalMatrix] using congrArg CStarMatrix.ofMatrix h
  · intro y hy
    have hyq : y = 0 ∨ y ∈ spectrum ℝ (cStarDiagonalMatrix x) :=
      (mem_quasispectrum_iff (a := cStarDiagonalMatrix x) (x := y)).mp hy
    rcases hyq with rfl | hy
    · simp
    · rw [cStarDiagonalMatrix] at hy
      change y ∈ spectrum ℝ (diagonalMatrix x) at hy
      rw [← spectrum.preimage_algebraMap ℂ] at hy
      simp only [Set.mem_preimage] at hy
      change (algebraMap ℝ ℂ) y ∈ spectrum ℂ (diagonalMatrix x) at hy
      rw [diagonalMatrix, spectrum_diagonal] at hy
      rcases hy with ⟨i, hi⟩
      have hyeq : y = x i := Complex.ofReal_injective hi.symm
      simpa [hyeq] using hx i

/-- The rank-one first-variation direction is self-adjoint in `CStarMatrix`. -/
lemma cStarRankOnePerturbation_isSelfAdjoint
    {n : ℕ} (c : Fin n → ℂ) :
    IsSelfAdjoint (cStarRankOnePerturbation c) := by
  rw [isSelfAdjoint_iff]
  have h := (rankOnePerturbation_isSelfAdjoint c).star_eq
  simpa [cStarRankOnePerturbation] using congrArg CStarMatrix.ofMatrix h

/-- Every diagonal rank-one perturbation is self-adjoint in `CStarMatrix`. -/
lemma cStarDiagonalPerturbation_isSelfAdjoint
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ε : ℝ) :
    IsSelfAdjoint (cStarDiagonalPerturbation x c ε) := by
  rw [cStarDiagonalPerturbation, isSelfAdjoint_iff]
  have h := (diagonalPerturbation_isSelfAdjoint x c ε).star_eq
  simpa using congrArg CStarMatrix.ofMatrix h

/-- The `CStarMatrix` diagonal perturbation tends back to the diagonal base point. -/
lemma cStarDiagonalPerturbation_tendsto_zero
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Filter.Tendsto (fun ε : ℝ => cStarDiagonalPerturbation x c ε)
      (𝓝 (0 : ℝ)) (𝓝 (cStarDiagonalMatrix x)) := by
  have hsmul :
      ContinuousAt (fun ε : ℝ => ε • cStarRankOnePerturbation c) (0 : ℝ) :=
    continuousAt_id.smul continuousAt_const
  have hconst :
      ContinuousAt (fun _ : ℝ => cStarDiagonalMatrix x) (0 : ℝ) :=
    continuousAt_const
  have h : ContinuousAt
      (fun ε : ℝ =>
        cStarDiagonalMatrix x + ε • cStarRankOnePerturbation c)
      (0 : ℝ) := by
    simpa [Pi.add_apply] using hconst.add hsmul
  have hz :
      cStarDiagonalMatrix x + (0 : ℝ) • cStarRankOnePerturbation c =
        cStarDiagonalMatrix x := by
    ext i j
    simp [cStarRankOnePerturbation]
  have ht := h.tendsto
  change Filter.Tendsto
    (fun ε : ℝ => cStarDiagonalMatrix x + ε • cStarRankOnePerturbation c)
    (𝓝 (0 : ℝ))
    (𝓝 (cStarDiagonalMatrix x +
      (0 : ℝ) • cStarRankOnePerturbation c)) at ht
  rw [hz] at ht
  simpa [cStarDiagonalPerturbation, cStarDiagonalMatrix,
    diagonalPerturbation, cStarRankOnePerturbation] using ht

/-- Small positive diagonal rank-one perturbations stay in the finite `CStarMatrix` domain. -/
lemma cStarDiagonalPerturbation_mem_domain_eventually
    {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) (c : Fin n → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      cStarDiagonalPerturbation x c ε ∈ cStarFiniteMatrixDomain n := by
  have hbase := cStarDiagonalMatrix_mem_domain x hx
  have htend :
      Filter.Tendsto (fun ε : ℝ => cStarDiagonalPerturbation x c ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (cStarDiagonalMatrix x)) :=
    (cStarDiagonalPerturbation_tendsto_zero x c).mono_left nhdsWithin_le_nhds
  have hqs_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        quasispectrum ℝ (cStarDiagonalPerturbation x c ε) ⊆
          Set.Ioo (-1 : ℝ) 1 :=
    quasispectrum_subset_Ioo_eventually
      (A := CStarMatrix (Fin n) (Fin n) ℂ) hbase.2 htend
  filter_upwards [hqs_eventually] with ε hqs
  exact ⟨cStarDiagonalPerturbation_isSelfAdjoint x c ε, hqs⟩

/-- Transfer the CFC interval domain from `CStarMatrix` back to the plain matrix copy. -/
lemma finiteMatrixDomain_of_cstar_domain
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : (CStarMatrix.ofMatrix M : CStarMatrix (Fin n) (Fin n) ℂ) ∈
      cStarFiniteMatrixDomain n) :
    M ∈ finiteMatrixDomain n := by
  refine ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    have h := hM.1.star_eq
    have h' := congrArg CStarMatrix.ofMatrix.symm h
    simpa using h'
  · intro y hy
    have hyq : y = 0 ∨ y ∈ spectrum ℝ M :=
      (mem_quasispectrum_iff (a := M) (x := y)).mp hy
    apply hM.2
    apply
      (mem_quasispectrum_iff
        (a := (CStarMatrix.ofMatrix M : CStarMatrix (Fin n) (Fin n) ℂ))
        (x := y)).mpr
    rcases hyq with rfl | hy
    · left
      rfl
    · right
      have hyc : (algebraMap ℝ ℂ) y ∈ spectrum ℂ M :=
        spectrum.algebraMap_mem ℂ hy
      change (algebraMap ℝ ℂ) y ∈ spectrum ℂ (CStarMatrix.ofMatrix M)
      change (algebraMap ℝ ℂ) y ∈ spectrum ℂ M at hyc
      exact hyc

/-- Small positive diagonal rank-one perturbations stay in the plain matrix domain. -/
lemma diagonalPerturbation_mem_domain_eventually
    {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) (c : Fin n → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      diagonalPerturbation x c ε ∈ finiteMatrixDomain n := by
  filter_upwards [cStarDiagonalPerturbation_mem_domain_eventually x hx c] with ε hε
  exact finiteMatrixDomain_of_cstar_domain hε

end

end Quantum.TraceInequality.Loewner
