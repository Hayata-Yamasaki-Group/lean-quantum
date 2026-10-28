import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.CStarMatrixBridge

/-!
# Chapter 3 diagonal first-variation interface

This file contains the diagonal CFC order-ray and first-variation interfaces
that convert finite-dimensional operator monotonicity into Loewner matrix
positivity, conditional on entrywise variation data.
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
Explicit input for the first-variation quadratic-form step.

The book proof first derives nonnegativity of the quadratic form associated with
the Löwner matrix.  This structure records exactly that intermediate output
from finite-dimensional matrix monotonicity, keeping the analytic first
variation and differentiability supply separate from the algebraic
`PosSemidef` conversion.
-/
structure LoewnerQuadraticFormFromFiniteMatrixMonotoneInput.{v}
    (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  quadratic_nonneg_of_finiteMatrixMonotone :
    UnitIntervalFiniteMatrixMonotone.{v} f →
      ∀ n : ℕ, ∀ x : Fin n → ℝ,
        (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
          Function.Injective x →
            ∀ c : Fin n → ℂ,
              0 ≤ star c ⬝ᵥ
                ((Matrix.of
                  (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c)

/-- W version: quadratic-form first-variation input from the matrix-level predicate. -/
structure LoewnerQuadraticFormFromMatrixMonotoneInput (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  quadratic_nonneg_of_matrixMonotone :
    UnitIntervalMatrixMonotone f →
      ∀ n : ℕ, ∀ x : Fin n → ℝ,
        (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
          Function.Injective x →
            ∀ c : Fin n → ℂ,
              0 ≤ star c ⬝ᵥ
                ((Matrix.of
                  (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ c)

/--
Explicit input for the finite-dimensional first-variation step.

The book proof differentiates matrix monotonicity at diagonal matrices and
identifies the resulting quadratic form with the Löwner matrix.  This structure
records that analytic/matrix-calculus step as an input, without deriving
differentiability from operator monotonicity in this node.  The step itself is
completed by the raw entrywise route in `loewnerPosOnUnitInterval_of_finiteMatrixMonotone`
(`HiaiRegularity.lean`).
-/
structure LoewnerMatrixFromFiniteMatrixMonotoneInput
    (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  posSemidef_of_finiteMatrixMonotone :
    UnitIntervalFiniteMatrixMonotone.{u} f →
      ∀ n : ℕ, ∀ x : Fin n → ℝ,
        (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
          Function.Injective x →
            (Matrix.of
              (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef

/-- W version: Löwner-matrix input from the matrix-level predicate. -/
structure LoewnerMatrixFromMatrixMonotoneInput (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  posSemidef_of_matrixMonotone :
    UnitIntervalMatrixMonotone f →
      ∀ n : ℕ, ∀ x : Fin n → ℝ,
        (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
          Function.Injective x →
            (Matrix.of
              (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef

/--
The quadratic-form first-variation input implies the existing Löwner-matrix
input by the finite `PosSemidef` characterization.
-/
theorem loewnerMatrixFromFiniteMatrixMonotoneInput_of_quadraticFormInput
    {f : ℝ → ℝ}
    (input : LoewnerQuadraticFormFromFiniteMatrixMonotoneInput.{u} f) :
    LoewnerMatrixFromFiniteMatrixMonotoneInput.{u} f where
  differentiable := input.differentiable
  posSemidef_of_finiteMatrixMonotone := by
    intro hfinite n x hx hinj
    exact loewnerMatrix_posSemidef_of_quadratic_nonneg
      (input.quadratic_nonneg_of_finiteMatrixMonotone hfinite n x hx hinj)

/-- W version of the quadratic→matrix conversion (introduced as a public lemma, rather than a
direct construction inside the theorem, so as to be symmetric with the old counterpart
loewnerMatrixFromFiniteMatrixMonotoneInput_of_quadraticFormInput). -/
theorem loewnerMatrixFromMatrixMonotoneInput_of_quadraticFormInput
    {f : ℝ → ℝ}
    (input : LoewnerQuadraticFormFromMatrixMonotoneInput f) :
    LoewnerMatrixFromMatrixMonotoneInput f where
  differentiable := input.differentiable
  posSemidef_of_matrixMonotone := by
    intro hmatrix n x hx hinj
    exact loewnerMatrix_posSemidef_of_quadratic_nonneg
      (input.quadratic_nonneg_of_matrixMonotone hmatrix n x hx hinj)

/-- Assemble the public finite Löwner positivity predicate from the explicit
finite-dimensional first-variation input. -/
theorem loewnerPosOnUnitInterval_of_finiteMatrixMonotone_of_loewnerMatrixInput
    {f : ℝ → ℝ} (hfinite : UnitIntervalFiniteMatrixMonotone.{u} f)
    (input : LoewnerMatrixFromFiniteMatrixMonotoneInput.{u} f) :
    LoewnerPosOnUnitInterval f where
  differentiable := input.differentiable
  posSemidef := input.posSemidef_of_finiteMatrixMonotone hfinite

/-- Assemble `LoewnerPosOnUnitInterval` from finite matrix monotonicity and the
quadratic-form first-variation input. -/
theorem loewnerPosOnUnitInterval_of_finiteMatrixMonotone_of_quadraticFormInput
    {f : ℝ → ℝ} (hfinite : UnitIntervalFiniteMatrixMonotone.{u} f)
    (input : LoewnerQuadraticFormFromFiniteMatrixMonotoneInput.{u} f) :
    LoewnerPosOnUnitInterval f :=
  loewnerPosOnUnitInterval_of_finiteMatrixMonotone_of_loewnerMatrixInput hfinite
    (loewnerMatrixFromFiniteMatrixMonotoneInput_of_quadraticFormInput input)

end

end Quantum.TraceInequality.Loewner
