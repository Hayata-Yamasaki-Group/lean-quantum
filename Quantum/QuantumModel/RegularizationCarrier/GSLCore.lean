/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.Channel.Representations
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumModel.CategoryInstances.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCore
import Quantum.QuantumModel.Purification.GSLCore
import Quantum.QuantumModel.Skeleton.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore
import Quantum.QuantumModel.TensorCalculus.GSLCore
import Quantum.QuantumModel.UnitTrace.GSLCore
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Geometry.Convex.Cone.TensorProduct
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Logic.Equiv.Bool
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Carrier and tensor seam for measured-relative-entropy regularization

This module supplies the flat `Fin` systems for finitely many identical
copies, density-matrix tensor products, the standard-basis transport to
right-associated Hilbert tensor products, and support transport.

The target is **the Hiai–Petz regularization (1991, measured type) — a theorem distinct from the
Hiai–Petz type matrix inequality (trace powers)**.  No regularization limit or trace-power matrix
inequality is asserted here.
-/

noncomputable section

namespace QuantumModel

open QuantumState
open TensorProduct
open scoped TensorProduct

/-! ## Flat systems and density tensor products -/

/-- The right-associated system of `n` copies.  Its Hilbert carrier remains
the native flat `Fin` carrier of the quantum-model skeleton. -/
def systemPow (A : Sys) : ℕ → Sys
  | 0 => tensorUnitSystem
  | n + 1 => tensorSystem A (systemPow A n)

private theorem matrix_trace_reindex
    {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (M : Matrix m m ℂ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  change (∑ i : n, M (e.symm i) (e.symm i)) = ∑ i : m, M i i
  exact Equiv.sum_comp e.symm (fun i : m => M i i)

/-- Trace is multiplicative in the native Kronecker operator coordinates. -/
theorem trace_operatorTensorEquiv_tmul {A B : Sys}
    (X : Operator A) (Y : Operator B) :
    Tr (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y)) = Tr X * Tr Y := by
  rw [LinearMap.trace_eq_matrix_trace
      (R := ℂ) (b := spaceBasis (tensorSystem A B)),
    LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A),
    LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis B)]
  change Matrix.trace
      (operatorEquivMatrix (tensorSystem A B)
        (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y))) =
    Matrix.trace (operatorEquivMatrix A X) *
      Matrix.trace (operatorEquivMatrix B Y)
  rw [operatorTensorEquiv_matrix_tmul]
  change Matrix.trace
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kronecker (operatorEquivMatrix A X)
          (operatorEquivMatrix B Y))) = _
  rw [matrix_trace_reindex]
  change Matrix.trace
      (Matrix.kroneckerMap (fun x y : ℂ => x * y)
        (operatorEquivMatrix A X) (operatorEquivMatrix B Y)) = _
  exact Matrix.trace_kronecker _ _

/-- The unique density matrix on the tensor unit. -/
noncomputable def tensorUnitDensity : DensityMatrix tensorUnitSystem where
  operator := LinearMap.id
  nonneg := (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_id
  trace_one := by
    rw [← operatorUnitEquiv_one, trace_operatorUnitEquiv]

/-- Binary tensor product of native density matrices. -/
noncomputable def densityTensor {A B : Sys}
    (rho : DensityMatrix A) (sigma : DensityMatrix B) :
    DensityMatrix (tensorSystem A B) where
  operator := operatorTensorEquiv A B (rho.operator ⊗ₜ[ℂ] sigma.operator)
  nonneg := operatorTensorEquiv_tmul_nonneg rho.nonneg sigma.nonneg
  trace_one := by
    rw [trace_operatorTensorEquiv_tmul, rho.trace_one, sigma.trace_one, mul_one]

@[simp] theorem densityTensor_operator {A B : Sys}
    (rho : DensityMatrix A) (sigma : DensityMatrix B) :
    (densityTensor rho sigma).operator =
      operatorTensorEquiv A B (rho.operator ⊗ₜ[ℂ] sigma.operator) :=
  rfl

/-- The right-associated tensor power of a density matrix. -/
noncomputable def densityTensorPow {A : Sys} (rho : DensityMatrix A) :
    (n : ℕ) → DensityMatrix (systemPow A n)
  | 0 => tensorUnitDensity
  | n + 1 => densityTensor rho (densityTensorPow rho n)

/-! ## Native flat carrier versus Hilbert tensor carrier -/

/-- Native flat binary carrier to the Mathlib Hilbert tensor carrier. -/
noncomputable def nativeTensorEquiv (A B : Sys) :
    Space (tensorSystem A B) ≃ₗᵢ[ℂ] (Space A ⊗[ℂ] Space B) :=
  (jointSpaceEquiv A B).symm

/-- Transport a native binary-system operator to the Hilbert tensor carrier. -/
noncomputable def nativeTensorOperatorTransport (A B : Sys) :
    Operator (tensorSystem A B) →ₗ[ℂ] L (Space A ⊗[ℂ] Space B) :=
  QuantumChannel.conjugateEnd (nativeTensorEquiv A B).toLinearEquiv

/-- The Hilbert tensor operator associated to `X ⊗ Y` is the ordinary
tensor map on vectors. -/
theorem hilbertTensorOperator_eq_map
    {E F : Type*} [Qudit E] [Qudit F] (X : L E) (Y : L F) :
    (QuantumChannel.l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
        (X ⊗ₜ[ℂ] Y) = TensorProduct.map X Y := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul,
      TensorProduct.map_tmul]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-! ## Support tensor lemmas -/

namespace DensityMatrix

/-- A density operator is nonzero because its trace is one. -/
theorem operator_ne_zero {A : Sys} (rho : DensityMatrix A) :
    rho.operator ≠ 0 := by
  intro hzero
  have h := rho.trace_one
  rw [hzero] at h
  simp at h

end DensityMatrix

end QuantumModel
