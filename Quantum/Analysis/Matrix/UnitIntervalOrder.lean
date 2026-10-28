import Quantum.TraceInequality.Loewner.RealComplexOrder
import Quantum.QuantumEntropy.Common.RealComplexOrder
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

private noncomputable instance instFinMatrixFiniteDimensional {n : ℕ} :
    FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.finiteDimensional

/-- The finite `CStarMatrix` wrapper is finite-dimensional over `ℂ`. -/
noncomputable instance instFinCStarMatrixFiniteDimensional {n : ℕ} :
    FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) := by
  change FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ)
  infer_instance

private instance instFinMatrixContinuousSMulReal {n : ℕ} :
    ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ) where
  continuous_smul := by
    change Continuous fun p : ℝ × Matrix (Fin n) (Fin n) ℂ => ((p.1 : ℂ) • p.2)
    exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd

private noncomputable instance instFinMatrixNonUnitalCFC {n : ℕ} :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix (Fin n) (Fin n) ℂ) IsSelfAdjoint := by
  exact (@IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
    (Matrix (Fin n) (Fin n) ℂ) inferInstance).toNonUnitalContinuousFunctionalCalculus

private noncomputable instance instFinMatrixNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instNonnegSpectrumClass

private instance instFinCStarMatrixContinuousSMulReal {n : ℕ} :
    ContinuousSMul ℝ (CStarMatrix (Fin n) (Fin n) ℂ) where
  continuous_smul := by
    change Continuous fun p : ℝ × CStarMatrix (Fin n) (Fin n) ℂ => ((p.1 : ℂ) • p.2)
    exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd

private noncomputable instance instFinCStarMatrixNonUnitalCFC {n : ℕ} :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint := by
  exact (@IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
    (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance).toNonUnitalContinuousFunctionalCalculus

-- Keep this bridge because Mathlib's real CFC does not synthesize from the standard algebra.
private noncomputable instance instFinCStarMatrixCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint := by
  exact @IsSelfAdjoint.instContinuousFunctionalCalculus
    (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance inferInstance inferInstance inferInstance
    inferInstance

private noncomputable instance instFinCStarMatrixNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) := by
  exact @CStarAlgebra.instNonnegSpectrumClass' (CStarMatrix (Fin n) (Fin n) ℂ)
    inferInstance inferInstance CStarMatrix.instStarOrderedRing

private noncomputable instance instFinCStarMatrixIsTopologicalRing {n : ℕ} :
    IsTopologicalRing (CStarMatrix (Fin n) (Fin n) ℂ) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance

private theorem matrix_nonneg_iff_eq_star_mul_self {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℂ} :
    0 ≤ M ↔ ∃ B, M = star B * B :=
  @CStarAlgebra.nonneg_iff_eq_star_mul_self (Matrix (Fin n) (Fin n) ℂ)
    inferInstance inferInstance inferInstance Matrix.instStarRing
    inferInstance inferInstance inferInstance
    Matrix.instStarOrderedRing inferInstance inferInstance inferInstance inferInstance M

private theorem cstarMatrix_nonneg_iff_eq_star_mul_self {n : ℕ}
    {M : CStarMatrix (Fin n) (Fin n) ℂ} :
    0 ≤ M ↔ ∃ B, M = star B * B :=
  @CStarAlgebra.nonneg_iff_eq_star_mul_self (CStarMatrix (Fin n) (Fin n) ℂ)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    CStarMatrix.instStarOrderedRing inferInstance inferInstance inferInstance inferInstance M

/--
Finite-dimensional version of operator monotonicity on the normalized interval.

This is a direct finite-dimensional restriction of
`OperatorMonotoneOnUnitInterval`: the same normalized non-unital CFC map
`x ↦ f x - f 0` is monotone on self-adjoint elements whose real quasispectrum
lies in `(-1,1)`.
-/
structure UnitIntervalFiniteMatrixMonotone (f : ℝ → ℝ) : Prop where
  cfc_monotone_finite :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      [FiniteDimensional ℂ A],
      MonotoneOn (fun a : A => cfcₙ (fun x : ℝ => f x - f 0) a)
        {a : A | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}

/-- Operator monotonicity predicate stated at the matrix level (the matrix case of the
C*-algebra predicate above). No universe variables. -/
structure UnitIntervalMatrixMonotone (f : ℝ → ℝ) : Prop where
  cfc_monotone_matrix :
    ∀ n : ℕ,
      MonotoneOn (fun a : CStarMatrix (Fin n) (Fin n) ℂ => cfcₙ (fun x : ℝ => f x - f 0) a)
        {a : CStarMatrix (Fin n) (Fin n) ℂ |
          IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}

/-- Positivity of a plain matrix direction can be used in the `CStarMatrix` copy. -/
lemma cStarMatrix_nonneg_of_posSemidef
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    0 ≤ (CStarMatrix.ofMatrix M : CStarMatrix (Fin n) (Fin n) ℂ) := by
  rw [cstarMatrix_nonneg_iff_eq_star_mul_self]
  have hM_nonneg : 0 ≤ (M : Matrix (Fin n) (Fin n) ℂ) := hM.nonneg
  rw [matrix_nonneg_iff_eq_star_mul_self] at hM_nonneg
  rcases hM_nonneg with ⟨B, hB⟩
  refine ⟨CStarMatrix.ofMatrix B, ?_⟩
  ext i j
  simp [CStarMatrix.star_eq_conjTranspose, CStarMatrix.mul_apply,
    CStarMatrix.conjTranspose_apply, Matrix.mul_apply, hB]

/-- Positivity in `CStarMatrix` gives the usual positive-semidefinite matrix. -/
lemma cStarMatrix_posSemidef_of_nonneg
    {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) ℂ} (hM : 0 ≤ M) :
    (CStarMatrix.ofMatrix.symm M).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  rw [matrix_nonneg_iff_eq_star_mul_self]
  rw [cstarMatrix_nonneg_iff_eq_star_mul_self] at hM
  rcases hM with ⟨B, hB⟩
  refine ⟨CStarMatrix.ofMatrix.symm B, ?_⟩
  ext i j
  simp [CStarMatrix.star_eq_conjTranspose, CStarMatrix.mul_apply,
    CStarMatrix.conjTranspose_apply, Matrix.mul_apply, hB]

end

end Quantum.TraceInequality.Loewner
