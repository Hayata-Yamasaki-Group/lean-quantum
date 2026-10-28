/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.LinearMap
import Quantum.TraceInequality.HiaiPetz.Core.Basic

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section MatrixScopedInstances

variable {n m : ℕ}

/-- The Hilbert-Schmidt adjoint of the identity map is the identity map.
Sanity lemma: the identity channel is self-adjoint for the Hilbert-Schmidt
inner product. -/
@[simp] theorem hsAdjoint_id :
    hsAdjoint (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) =
      (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) := by
  dsimp [hsAdjoint]
  exact
    @ContinuousLinearMap.adjoint_id ℂ (Mₙ n)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))

/-- Left multiplication by the identity is the identity operator.
Source: Hiai, Definition 6.1 left multiplication. -/
@[simp] theorem leftMul_one :
    leftMul (1 : Mₙ n) = (1 : HSOp n) := by
  ext X i j
  simp [leftMul_apply]

/-- Left multiplication turns matrix multiplication into operator multiplication.
Source: Hiai, Definition 6.1 left multiplication. -/
@[simp] theorem leftMul_mul (A B : Mₙ n) :
    leftMul (A * B) = leftMul A * leftMul B := by
  ext X i j
  simp [leftMul_apply, Matrix.mul_assoc]

/-- Right multiplication reverses matrix multiplication under operator multiplication.
Source: Hiai, Definition 6.1 right multiplication. -/
@[simp] theorem rightMul_mul (A B : Mₙ n) :
    rightMul (A * B) = rightMul B * rightMul A := by
  ext X i j
  simp [rightMul_apply, Matrix.mul_assoc]

/-- Left multiplication is additive in the multiplying matrix.
Source: Hiai, Definition 6.1 left multiplication. -/
@[simp] theorem leftMul_add (A B : Mₙ n) :
    leftMul (A + B) = leftMul A + leftMul B := by
  ext X i j
  simp [leftMul_apply, Matrix.add_mul]

/-- Right multiplication is additive in the multiplying matrix.
Source: Hiai, Definition 6.1 right multiplication. -/
@[simp] theorem rightMul_add (A B : Mₙ n) :
    rightMul (A + B) = rightMul A + rightMul B := by
  ext X i j
  simp [rightMul_apply, Matrix.mul_add]

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.Core

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The self-composition `Φ ∘ hsAdjoint Φ` is a positive continuous linear map
on the codomain Hilbert-Schmidt space. -/
theorem self_comp_hsAdjoint_isPositive
    {n m : ℕ} (Φ : HSMap n m) :
    @ContinuousLinearMap.IsPositive ℂ (Mₙ m)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := m))
      (instMatrixInnerProductSpace (n := m))
      ((Φ.comp (hsAdjoint Φ) : HSOp m)) := by
  simpa [hsAdjoint] using
    (@ContinuousLinearMap.isPositive_self_comp_adjoint ℂ (Mₙ n) (Mₙ m)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixNormedAddCommGroup (n := m))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixInnerProductSpace (n := m))
      (instMatrixCompleteSpace (n := n))
      (instMatrixCompleteSpace (n := m))
      Φ)

end

end HiaiPetz.Core

namespace HiaiPetz.Core

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- A Hilbert–Schmidt map out of the zero-dimensional space sends the identity to
`0`, since `(1 : Mₙ 0) = 0`. -/
theorem image_one_zeroDomain_eq_zero {m : ℕ} (Φ : HSMap 0 m) :
    Φ (1 : Mₙ 0) = 0 := by
  have hone : (1 : Mₙ 0) = 0 := by
    ext i j
    exact Fin.elim0 i
  rw [hone, Φ.map_zero]

end

end HiaiPetz.Core

namespace HiaiPetz.Core

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- Every Hilbert–Schmidt map into the zero-dimensional space is the zero map. -/
theorem hsMap_eq_zero_of_zeroCodomain {n : ℕ} (Φ : HSMap n 0) :
    Φ = 0 := by
  ext X i j
  exact Fin.elim0 j

end

end HiaiPetz.Core
