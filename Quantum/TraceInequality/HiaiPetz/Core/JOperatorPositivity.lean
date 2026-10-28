/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core.Basic

/-!
# Positive and invertible J-operator core

This file proves the basic positivity and strict-invertibility properties of
the Hiai-Petz operator `J_f(A,B)`. The proofs reduce `J_f(A,B)` to functional
calculus of the positive Hilbert-Schmidt operator `L_A R_{B^{-1}}` and use
commutation with right multiplication to build the explicit inverse model.

## Main results

* `jArg_isSelfAdjoint` and `jArg_nonneg`: self-adjointness and positivity of
  `L_A R_{B^{-1}}`.
* `jOperator_mul_jOperatorInv_of_posDef` and
  `jOperatorInv_mul_jOperator_of_posDef`: the strict positive-definite inverse
  identities for `J_f(A,B)`.
* `jOperator_nonneg`, `jOperatorInv_nonneg`, `jOperator_strict_pos`, and
  `jOperatorInv_strict_pos`: positivity and strict positivity of `J_f(A,B)` and
  its inverse model.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, Definition 6.1 and Theorem 6.2 setup.
-/

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section MatrixScopedInstances

variable {n m : ℕ}

/-- Positive definiteness of a matrix is preserved by inversion in the strict regime. -/
theorem posInv_posDef {B : Mₙ n} :
    Matrix.PosDef B → Matrix.PosDef (B⁻¹) := by
  intro hB
  simpa using hB.inv

/-- If `A` is self-adjoint and `B` is positive definite, then
`L_A R_{B^{-1}}` is self-adjoint for the Hilbert-Schmidt adjoint. -/
theorem jArg_isSelfAdjoint {A B : Mₙ n} :
    IsSelfAdjoint A → Matrix.PosDef B → hsAdjoint (jArg A B) = jArg A B := by
  intro hA hB
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  have hBinv : IsSelfAdjoint (B⁻¹) := (posInv_posDef hB).1
  calc
    hsAdjoint (jArg A B)
        = hsAdjoint ((rightMul (B⁻¹)).comp (leftMul A)) := by rfl
    _ = (hsAdjoint (leftMul A)).comp (hsAdjoint (rightMul (B⁻¹))) := by
          dsimp [hsAdjoint]
          exact
            (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ n) (Mₙ n)
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixCompleteSpace (n := n))
              (instMatrixCompleteSpace (n := n))
              (instMatrixCompleteSpace (n := n))
              (rightMul (B⁻¹)) (leftMul A))
    _ = (leftMul A).comp (rightMul (B⁻¹)) := by
          rw [leftMul_isSelfAdjoint hA, rightMul_isSelfAdjoint hBinv]
    _ = (rightMul (B⁻¹)).comp (leftMul A) := by
          rw [leftMul_comm_rightMul]
    _ = jArg A B := by rfl

/-- If `A` is nonnegative and `B` is positive definite, then the argument
`L_A R_{B^{-1}}` of `J_f(A,B)` is nonnegative in Mathlib's Loewner order. -/
theorem jArg_nonneg {A B : Mₙ n} :
    0 ≤ A → Matrix.PosDef B → 0 ≤ jArg A B := by
  intro hA hB
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  have hleft_nonneg : 0 ≤ leftMul A := leftMul_nonneg hA
  have hright_nonneg : 0 ≤ rightMul (B⁻¹) :=
    rightMul_nonneg (Matrix.PosDef.nonneg (posInv_posDef hB))
  have hcomm : Commute (rightMul (B⁻¹)) (leftMul A) := by
    simpa using leftMul_comm_rightMul A (B⁻¹)
  rw [jArg]
  exact (commute_iff_mul_nonneg hright_nonneg hleft_nonneg).mp hcomm

private theorem jArg_mul_rightMul {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    jArg A B * rightMul B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

private theorem rightMul_mul_jArg {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * jArg A B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

private theorem commute_jArg_rightMul {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (jArg A B) (rightMul B) := by
  change jArg A B * rightMul B = rightMul B * jArg A B
  rw [jArg_mul_rightMul hB, rightMul_mul_jArg hB]

private theorem commute_cfc_jArg_rightMul {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (hsCfcR f (jArg A B)) (rightMul B) := by
  exact (commute_jArg_rightMul (A := A) hB).cfc_real f

/-- For positive-definite `B`, the `J`-operator is self-adjoint for every
real-valued scalar function used by the real continuous functional calculus. -/
theorem jOperator_isSelfAdjoint {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    IsSelfAdjoint (jOperator f A B) := by
  have hcfc : IsSelfAdjoint (hsCfcR f (jArg A B)) := by
    simp [hsCfcR]
  have hright : IsSelfAdjoint (rightMul B) :=
    rightMul_isSelfAdjoint hB.isSelfAdjoint
  have hcomm := commute_cfc_jArg_rightMul (f := f) (A := A) hB
  rw [jOperator]
  calc
    star (hsCfcR f (jArg A B) * rightMul B) =
        star (rightMul B) * star (hsCfcR f (jArg A B)) := star_mul _ _
    _ = rightMul B * hsCfcR f (jArg A B) := by rw [hright.star_eq, hcfc.star_eq]
    _ = hsCfcR f (jArg A B) * rightMul B := hcomm.eq.symm

end MatrixScopedInstances

end HiaiPetz
