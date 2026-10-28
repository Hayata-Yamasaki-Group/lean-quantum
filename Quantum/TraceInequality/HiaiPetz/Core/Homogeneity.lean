/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Homogeneity aliases for core operators

This file records how the strict inverse, left and right multiplication, the
argument `L_A R_{B^{-1}}`, and the Hiai-Petz operator `J_f(A,B)` behave under a
common positive real scaling of the matrix inputs. These identities are used to
normalize quasi-entropy expressions without changing their `jArg` component.

## Main results

* `posInv_smul`, `leftMul_smul`, and `rightMul_smul`: scalar rules for the
  algebraic building blocks.
* `jArg_smul`: simultaneous positive scaling of `A` and `B` leaves
  `L_A R_{B^{-1}}` unchanged.
* `jOperator_homogeneous`, `jOperatorInv_homogeneous`, and
  `quasiEntropy_homogeneous`: homogeneity of `J_f`, its inverse model, and the
  associated quasi-entropy.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, Definition 6.1.
-/

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder


noncomputable section MatrixScopedInstances

variable {n m : ℕ}

/-- The strict inverse of a positive real scalar multiple is the inverse scalar
multiple of the strict inverse. -/
theorem posInv_smul {B : Mₙ n} {r : ℝ} (hr : 0 < r) :
    ((r • B)⁻¹) = (r⁻¹) • B⁻¹ := by
  by_cases hB : IsUnit B.det
  · letI : Invertible (r : ℂ) := invertibleOfNonzero (by exact_mod_cast hr.ne')
    change ((r : ℂ) • B)⁻¹ = (((r⁻¹ : ℝ) : ℂ) • B⁻¹)
    simpa using Matrix.inv_smul (A := B) (k := (r : ℂ)) hB
  · have hsmul : ¬ IsUnit (Matrix.det (r • B)) := by
      have hdetB : Matrix.det B = 0 := by
        simpa [isUnit_iff_ne_zero] using hB
      have hdetSmul : Matrix.det (r • B) = 0 := by
        change Matrix.det (((r : ℂ)) • B) = 0
        rw [Matrix.det_smul B (r : ℂ), hdetB]
        simp
      simp [isUnit_iff_ne_zero, hdetSmul]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hsmul,
      Matrix.nonsing_inv_apply_not_isUnit _ hB]
    ext i j
    simp

/-- Left multiplication is homogeneous for real scalar multiplication of the
left matrix. -/
theorem leftMul_smul {A : Mₙ n} {r : ℝ} :
    leftMul (r • A) = (r : ℂ) • leftMul A := by
  ext X i j
  change (((r : ℂ) • A) * X) i j = ((r : ℂ) • (A * X)) i j
  rw [smul_mul_assoc]

/-- Right multiplication is homogeneous for real scalar multiplication of the
right matrix. -/
theorem rightMul_smul {B : Mₙ n} {r : ℝ} :
    rightMul (r • B) = (r : ℂ) • rightMul B := by
  ext X i j
  change ∑ x, X i x * (((r : ℂ) * B x j)) = (r : ℂ) * ∑ x, X i x * B x j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  ring

/-- Simultaneously scaling `A` and `B` by a positive real scalar leaves
`L_A R_{B^{-1}}` unchanged. -/
theorem jArg_smul {A B : Mₙ n} {r : ℝ} (hr : 0 < r) :
    jArg (r • A) (r • B) = jArg A B := by
  ext X
  rw [jArg_apply, jArg_apply, posInv_smul hr]
  simp [Matrix.mul_assoc, hr.ne']

/-- `J_f(A,B)` is homogeneous of degree one under simultaneous positive real
scaling of `A` and `B`.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem jOperator_homogeneous {f : ℝ → ℝ} {A B : Mₙ n} {r : ℝ} :
    0 < r →
    jOperator f (r • A) (r • B) = r • jOperator f A B := by
  intro hr
  rw [jOperator, jOperator, jArg_smul hr, rightMul_smul]
  ext X
  simp

/-- The explicit inverse model of `J_f(A,B)` is homogeneous of degree `-1`
under simultaneous positive real scaling of `A` and `B`. -/
theorem jOperatorInv_homogeneous {f : ℝ → ℝ} {A B : Mₙ n} {r : ℝ} :
    0 < r →
    jOperatorInv f (r • A) (r • B) = r⁻¹ • jOperatorInv f A B := by
  intro hr
  rw [jOperatorInv, jArg_smul hr, posInv_smul hr, rightMul_smul]
  change
    hsCfcR (fun x => (f x)⁻¹) (jArg A B) * ((((r⁻¹ : ℝ) : ℂ)) • rightMul (B⁻¹)) =
      (((r⁻¹ : ℝ) : ℂ)) •
        (hsCfcR (fun x => (f x)⁻¹) (jArg A B) * rightMul (B⁻¹))
  rw [mul_smul_comm]

/-- Hiai-Petz quasi-entropy is homogeneous of degree one in the two positive
matrix arguments under simultaneous positive real scaling. -/
theorem quasiEntropy_homogeneous {f : ℝ → ℝ} {A B X : Mₙ n} {r : ℝ} :
    0 < r →
    quasiEntropy f (r • A) (r • B) X = r * quasiEntropy f A B X := by
  intro hr
  rw [quasiEntropy, quasiEntropy, jOperator_homogeneous (f := f) (A := A) (B := B) hr]
  change
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (((r : ℂ) • jOperator f A B) X))) =
      r * Complex.re (Matrix.trace (Matrix.conjTranspose X * jOperator f A B X))
  rw [ContinuousLinearMap.smul_apply]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  change
    Complex.re (((r : ℂ) * (Matrix.conjTranspose X * jOperator f A B X).trace)) =
      r * Complex.re ((Matrix.conjTranspose X * jOperator f A B X).trace)
  rw [Complex.mul_re]
  simp

end MatrixScopedInstances

end HiaiPetz
