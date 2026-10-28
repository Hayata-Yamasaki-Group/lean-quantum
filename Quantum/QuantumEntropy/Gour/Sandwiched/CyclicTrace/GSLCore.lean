import Quantum.QuantumEntropy.YoungInequalityLMCompat.GSLCore
import Quantum.QuantumEntropy.Gour.Sandwiched.EndpointClassification.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.SandwichedRenyiBase.Tensor.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)


/-! # Singular cyclic trace identity -/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel TensorProduct OPT
open scoped ComplexOrder ENNReal NNReal
open scoped MatrixOrder


universe u v

/-! ## singular `CC†` / `C†C` trace identity -/

/-- The traces of positive real powers of `C†C` and `CC†` agree without any
invertibility assumption on `C`.  The proof compares their Hermitian
eigenvalue multisets through the common characteristic polynomial. -/
private theorem traceRpow_star_mul_eq_mul_star
    {H : Type u} [Qudit H] (C : L H) {q : ℝ} (hq : 0 ≤ q) :
    Tr (CFC.rpow (star C * C) q) =
      Tr (CFC.rpow (C * star C) q) := by
  have h1Nonneg : (0 : L H) ≤ 1 :=
    (LinearMap.nonneg_iff_isPositive 1).mpr LinearMap.isPositive_one
  have hStarMulNonneg : (0 : L H) ≤ star C * C := by
    have h := star_left_conjugate_nonneg h1Nonneg C
    rwa [mul_one] at h
  have hMulStarNonneg : (0 : L H) ≤ C * star C := by
    have h := star_left_conjugate_nonneg h1Nonneg (star C)
    rwa [star_star, mul_one] at h
  have hStarMulPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hStarMulNonneg
  have hMulStarPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hMulStarNonneg
  let b := stdOrthonormalBasis ℂ H
  set M := LinearMap.toMatrixOrthonormal b C
  have hHermitian₁ : (star M * M).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self M
  have hHermitian₂ : (M * star M).IsHermitian :=
    Matrix.isHermitian_mul_conjTranspose_self M
  have hNonneg₁ : 0 ≤ star M * M :=
    (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hNonneg₂ : 0 ≤ M * star M :=
    (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have hMatrix₁ :
      LinearMap.toMatrixOrthonormal b (star C * C) = star M * M := by
    rw [map_mul, map_star]
  have hMatrix₂ :
      LinearMap.toMatrixOrthonormal b (C * star C) = M * star M := by
    rw [map_mul, map_star]
  have hEigenvalues : hHermitian₁.eigenvalues = hHermitian₂.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  -- Pass to matrices and compare eigenvalues. The operator and matrix powers in the transport
  -- lemma and in the eigenvalue formula carry instance terms that agree with the ones here only
  -- after unfolding, so these steps rewrite up to definitional unfolding.
  rw [tr_eq_matrix_trace_orthonormal b, tr_eq_matrix_trace_orthonormal b]
  erw [toMatrixOrthonormal_rpow_lm b _ hStarMulPositive q hq,
    toMatrixOrthonormal_rpow_lm b _ hMulStarPositive q hq]
  rw [hMatrix₁, hMatrix₂]
  erw [matrix_trace_rpow_eq_sum_eigenvalues _ hHermitian₁ hNonneg₁ q,
    matrix_trace_rpow_eq_sum_eigenvalues _ hHermitian₂ hNonneg₂ q]
  rw [hEigenvalues]

private lemma b3SpectrumRealFinite
    {H : Type u} [Qudit H] [Nontrivial H] (A : L H) :
    (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private lemma b3Rpow_eq_cfc
    {H : Type u} [Qudit H] [Nontrivial H]
    {A : L H} (hA : 0 ≤ A) (p : ℝ) :
    CFC.rpow A p = cfc (fun x : ℝ ↦ x ^ p) A := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hA

private lemma b3Rpow_mul_rpow_cfc
    {H : Type u} [Qudit H] [Nontrivial H]
    {A : L H} (hA : 0 ≤ A) (p q : ℝ) :
    CFC.rpow A p * CFC.rpow A q =
      cfc (fun x : ℝ ↦ x ^ p * x ^ q) A := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) :=
    fun f ↦ (b3SpectrumRealFinite A).continuousOn f
  rw [b3Rpow_eq_cfc hA p, b3Rpow_eq_cfc hA q]
  exact (cfc_mul _ _ A (hcont _) (hcont _)).symm

private lemma b3Rpow_mul_self
    {H : Type u} [Qudit H] [Nontrivial H]
    {A : L H} (hA : 0 ≤ A) (p : ℝ) :
    CFC.rpow A p * CFC.rpow A p = CFC.rpow A (p + p) := by
  rw [b3Rpow_mul_rpow_cfc hA, b3Rpow_eq_cfc hA]
  apply cfc_congr
  intro x hx
  have hxNonneg : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  by_cases hp : p = 0
  · simp [hp]
  · exact (Real.rpow_add' hxNonneg (by intro h; apply hp; linarith)).symm


/-- Exercise 6.40 for arbitrary, possibly singular density operators.  The
formal order domain is the full half-line `alpha > 0`, including `alpha = 1`;
no `IsUnit` assumption is imposed on either density or the auxiliary matrix. -/
theorem gourSandwichedTraceCyclicEquivalence
    {H : Type u} [Qudit H] [Nontrivial H]
    {alpha : ℝ} (halpha : 0 < alpha)
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    Tr (CFC.rpow
        (CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
          CFC.rpow sigma ((1 - alpha) / (2 * alpha))) alpha) =
      Tr (CFC.rpow
        (CFC.rpow rho (1 / 2) *
          CFC.rpow sigma ((1 - alpha) / alpha) *
          CFC.rpow rho (1 / 2)) alpha) := by
  let c : ℝ := (1 - alpha) / (2 * alpha)
  let P : L H := CFC.rpow sigma c
  let Q : L H := CFC.rpow rho (1 / 2)
  let C : L H := P * Q
  have hrhoNonneg : (0 : L H) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive _).mpr hrho.1
  have hsigmaNonneg : (0 : L H) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive _).mpr hsigma.1
  have hPstar : star P = P := (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hQstar : star Q = Q := (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hQsq : Q * Q = rho := by
    change CFC.rpow rho (1 / 2) * CFC.rpow rho (1 / 2) = rho
    rw [b3Rpow_mul_self hrhoNonneg]
    norm_num [CFC.rpow_one rho hrhoNonneg]
  have hPsq : P * P = CFC.rpow sigma ((1 - alpha) / alpha) := by
    change CFC.rpow sigma c * CFC.rpow sigma c = _
    rw [b3Rpow_mul_self hsigmaNonneg]
    congr 1
    dsimp only [c]
    field_simp [halpha.ne']
    ring
  have hCstar : star C = Q * P := by
    change star (P * Q) = Q * P
    rw [star_mul, hPstar, hQstar]
  have hMulStar : C * star C = P * rho * P := by
    rw [hCstar]
    change P * Q * (Q * P) = P * rho * P
    rw [← mul_assoc (P * Q) Q P, mul_assoc P Q Q, hQsq]
  have hStarMul : star C * C =
      Q * CFC.rpow sigma ((1 - alpha) / alpha) * Q := by
    rw [hCstar]
    change Q * P * (P * Q) = _
    rw [← mul_assoc (Q * P) P Q, mul_assoc Q P P, hPsq]
  change Tr (CFC.rpow (P * rho * P) alpha) =
    Tr (CFC.rpow
      (Q * CFC.rpow sigma ((1 - alpha) / alpha) * Q) alpha)
  rw [← hMulStar, ← hStarMul]
  exact (traceRpow_star_mul_eq_mul_star C halpha.le).symm

end SandwichedRenyiRelativeEntropy
