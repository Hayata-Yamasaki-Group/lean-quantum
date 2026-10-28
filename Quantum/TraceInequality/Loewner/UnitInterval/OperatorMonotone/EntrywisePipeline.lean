import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HermiteApproximation

/-!
# Chapter 3 entrywise pipeline wrappers

This file contains the wrapper pipeline that turns polynomial-approximation,
raw, and separated entrywise CFC variation inputs into the quadratic-form input
for finite Loewner positivity. In `HiaiRegularity.lean`, differentiability
obtained from `twoByTwoRegularityInput_closed` is used to construct the Hermite
inputs of `HermiteApproximation.lean` before this pipeline is applied.
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
Entrywise convergence of all separated weighted CFC coefficient contributions
implies convergence of the separated quadratic-form quotient.
-/
theorem diagonalSeparatedVariationQuotient_tendsto_of_entrywise
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u v : Fin n → ℂ}
    (hentry :
      ∀ i j : Fin n,
        Filter.Tendsto
          (fun ε : ℝ =>
            diagonalCFCSeparatedEntrywiseVariationQuotient f x u v ε i j)
          (𝓝[>] (0 : ℝ))
          (𝓝 (separatedLoewnerDerivativeEntry f x u v i j))) :
    Filter.Tendsto (fun ε : ℝ =>
        diagonalSeparatedVariationQuotient f x u v ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (separatedLoewnerQuadraticForm f x u v)) := by
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∑ i : Fin n, ∑ j : Fin n,
            diagonalCFCSeparatedEntrywiseVariationQuotient f x u v ε i j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ i : Fin n, ∑ j : Fin n,
            separatedLoewnerDerivativeEntry f x u v i j)) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro i _hi
    refine tendsto_finset_sum Finset.univ ?_
    intro j _hj
    exact hentry i j
  simpa [diagonalSeparatedVariationQuotient_eq_sum_entries,
    separatedLoewnerQuadraticForm_eq_sum_entries] using hsum

/--
Finite-dimensional monotonicity on the separated order ray makes the separated
quotient eventually nonnegative.
-/
theorem diagonalSeparatedVariationQuotient_nonneg_eventually_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hmatrix : UnitIntervalMatrixMonotone f)
    (n : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) (u v : Fin n → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ diagonalSeparatedVariationQuotient f x u v ε := by
  filter_upwards [cStarDiagonalPerturbation_mem_domain_eventually x hx u,
    self_mem_nhdsWithin] with ε hpert hεpos
  have hbase : cStarDiagonalMatrix x ∈ cStarFiniteMatrixDomain n :=
    cStarDiagonalMatrix_mem_domain x hx
  have hle_ray :
      cStarDiagonalMatrix x ≤ cStarDiagonalPerturbation x u ε :=
    cStarDiagonalMatrix_le_perturbation_of_nonneg x u (le_of_lt hεpos)
  have hle_cfc :
      cfcₙ (fun t : ℝ => f t - f 0) (cStarDiagonalMatrix x) ≤
        cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalPerturbation x u ε) := by
    exact hmatrix.cfc_monotone_matrix n hbase hpert hle_ray
  have hdiff_nonneg :
      0 ≤
        cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalPerturbation x u ε) -
          cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalMatrix x) := by
    exact sub_nonneg.mpr hle_cfc
  have hquad :
      0 ≤ star v ⬝ᵥ
        (((CStarMatrix.ofMatrix.symm
            (cfcₙ (fun t : ℝ => f t - f 0)
              (cStarDiagonalPerturbation x u ε))) -
          (CStarMatrix.ofMatrix.symm
            (cfcₙ (fun t : ℝ => f t - f 0)
              (cStarDiagonalMatrix x)))) *ᵥ v) := by
    simpa using
      (cStarMatrix_quadratic_nonneg_of_nonneg hdiff_nonneg v)
  have hεinv : 0 ≤ (ε⁻¹ : ℝ) := inv_nonneg.mpr (le_of_lt hεpos)
  have hscaled :
      0 ≤ (ε⁻¹ : ℝ) •
        (star v ⬝ᵥ
          (((CStarMatrix.ofMatrix.symm
              (cfcₙ (fun t : ℝ => f t - f 0)
                (cStarDiagonalPerturbation x u ε))) -
            (CStarMatrix.ofMatrix.symm
              (cfcₙ (fun t : ℝ => f t - f 0)
                (cStarDiagonalMatrix x)))) *ᵥ v)) := by
    exact smul_nonneg hεinv hquad
  simpa [diagonalSeparatedVariationQuotient_eq_cstar,
    cStarDiagonalSeparatedVariationQuotient] using hscaled

/--
Corrected entrywise first-variation input with perturbation vector and test
vector separated.

Specializing the perturbation vector to the constant-one vector gives the
Löwner quadratic form without double-counting the test coefficients.
-/
structure DiagonalCFCSeparatedEntrywiseVariationInput (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  entrywise_tendsto :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
        Function.Injective x →
          ∀ u v : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCSeparatedEntrywiseVariationQuotient
                    f x u v ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 (separatedLoewnerDerivativeEntry f x u v i j))

/--
Raw matrix-coefficient first-variation input.

This is the unweighted coefficient form after the weighted entrywise reduction.  It is the
input expected from the finite-dimensional divided-difference/Hermite
interpolation CFC calculation.
-/
structure DiagonalCFCRawEntrywiseVariationInput (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  raw_entrywise_tendsto :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
        Function.Injective x →
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient f x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 (rawLoewnerDerivativeEntry f x u i j))

/--
Polynomial approximation plus a zero first-order remainder supplies the raw
matrix-coefficient CFC first-variation input.
-/
theorem rawEntrywiseVariationInput_of_polynomialApproximationInput
    {f : ℝ → ℝ}
    (input : DiagonalCFCRawEntrywisePolynomialApproximationInput f) :
    DiagonalCFCRawEntrywiseVariationInput f where
  differentiable := input.differentiable
  raw_entrywise_tendsto := by
    intro n x hx hinj u i j
    let p := input.polynomial n x hx hinj u
    have hpoly :
        Filter.Tendsto
          (fun ε : ℝ => polynomialRawEntrywiseVariationQuotient p x u ε i j)
          (𝓝[>] (0 : ℝ))
          (𝓝 (polynomialRawLoewnerDerivativeEntry p x u i j)) :=
      polynomialRawEntrywiseVariation_tendsto
    have hrem :
        Filter.Tendsto
          (fun ε : ℝ =>
            diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
              polynomialRawEntrywiseVariationQuotient p x u ε i j)
          (𝓝[>] (0 : ℝ))
          (𝓝 0) :=
      input.remainder_tendsto_zero n x hx hinj u i j
    have hsum := hrem.add hpoly
    have hmatch :
        polynomialRawLoewnerDerivativeEntry p x u i j =
          rawLoewnerDerivativeEntry f x u i j :=
      input.polynomial_matches_loewner n x hx hinj u i j
    simpa [p, hmatch, sub_add_cancel] using hsum

/-- Raw coefficient first variation supplies the separated entrywise input. -/
theorem separatedEntrywiseVariationInput_of_rawEntrywiseVariationInput
    {f : ℝ → ℝ} (input : DiagonalCFCRawEntrywiseVariationInput f) :
    DiagonalCFCSeparatedEntrywiseVariationInput f where
  differentiable := input.differentiable
  entrywise_tendsto := by
    intro n x hx hinj u v i j
    exact separatedEntrywise_tendsto_of_rawEntrywise
      (input.raw_entrywise_tendsto n x hx hinj u i j)

/--
The separated entrywise input supplies the corrected quadratic-form input.  The
positive order direction is the constant-one rank-one matrix, while the
quadratic form is tested against the arbitrary vector `c`.
-/
theorem quadraticFormInput_of_separatedEntrywiseVariationInput
    {f : ℝ → ℝ} (input : DiagonalCFCSeparatedEntrywiseVariationInput f) :
    LoewnerQuadraticFormFromFiniteMatrixMonotoneInput.{0} f where
  differentiable := input.differentiable
  quadratic_nonneg_of_finiteMatrixMonotone := by
    intro hfinite n x hx hinj c
    let one : Fin n → ℂ := fun _ => 1
    have hnonneg :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          0 ≤ diagonalSeparatedVariationQuotient f x one c ε := by
      exact diagonalSeparatedVariationQuotient_nonneg_eventually_of_finiteMatrixMonotone
        (unitIntervalMatrixMonotone_of_finiteMatrixMonotone hfinite) n x hx one c
    have hmem :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          diagonalSeparatedVariationQuotient f x one c ε ∈ Set.Ici (0 : ℂ) :=
      hnonneg
    change (star c ⬝ᵥ
        ((Matrix.of
          (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c)) ∈
      Set.Ici (0 : ℂ)
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => diagonalSeparatedVariationQuotient f x one c ε)
          (𝓝[>] (0 : ℝ))
          (𝓝 (star c ⬝ᵥ
            ((Matrix.of
              (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c))) := by
      have hsep :=
        diagonalSeparatedVariationQuotient_tendsto_of_entrywise
          (input.entrywise_tendsto n x hx hinj one c)
      simpa [one, separatedLoewnerQuadraticForm_one_eq] using hsep
    exact IsClosed.mem_of_tendsto (isClosed_Ici : IsClosed {z : ℂ | 0 ≤ z})
      htend hmem

theorem quadraticFormMatrixInput_of_separatedEntrywiseVariationInput
    {f : ℝ → ℝ} (input : DiagonalCFCSeparatedEntrywiseVariationInput f) :
    LoewnerQuadraticFormFromMatrixMonotoneInput f where
  differentiable := input.differentiable
  quadratic_nonneg_of_matrixMonotone := by
    intro hmatrix n x hx hinj c
    let one : Fin n → ℂ := fun _ => 1
    have hnonneg :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          0 ≤ diagonalSeparatedVariationQuotient f x one c ε := by
      exact diagonalSeparatedVariationQuotient_nonneg_eventually_of_finiteMatrixMonotone
        hmatrix n x hx one c
    have hmem :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          diagonalSeparatedVariationQuotient f x one c ε ∈ Set.Ici (0 : ℂ) :=
      hnonneg
    change (star c ⬝ᵥ
        ((Matrix.of
          (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c)) ∈
      Set.Ici (0 : ℂ)
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => diagonalSeparatedVariationQuotient f x one c ε)
          (𝓝[>] (0 : ℝ))
          (𝓝 (star c ⬝ᵥ
            ((Matrix.of
              (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c))) := by
      have hsep :=
        diagonalSeparatedVariationQuotient_tendsto_of_entrywise
          (input.entrywise_tendsto n x hx hinj one c)
      simpa [one, separatedLoewnerQuadraticForm_one_eq] using hsep
    exact IsClosed.mem_of_tendsto (isClosed_Ici : IsClosed {z : ℂ | 0 ≤ z})
      htend hmem

/--
Explicit producer interface for the one-variable regularity statement that
operator monotone functions are differentiable on the open interval.

The Hiai regularity module supplies the closed producer used by the public route.
-/
structure OperatorMonotoneDifferentiabilityInput : Prop where
  differentiable :
    ∀ {f : ℝ → ℝ},
      OperatorMonotoneOnUnitInterval.{0} f →
        DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)

end

end Quantum.TraceInequality.Loewner
