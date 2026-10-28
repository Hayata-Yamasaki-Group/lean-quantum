/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.InnerProduct

/-!
# Contractivity of Hilbert-Schmidt adjoints

This file proves the elementary Hilbert-Schmidt facts needed to transfer
contractive estimates through the adjoint map. The argument rewrites
quadratic forms of `Φ ∘ hsAdjoint Φ` as squared norms and combines positivity
with the assumed norm contraction of `Φ`.

## Main results

* `hsAdjoint_contract_of_contract`: a contractive Hilbert-Schmidt map has a
  contractive Hilbert-Schmidt adjoint.
* `self_comp_hsAdjoint_isPositive`: the operator `Φ ∘ hsAdjoint Φ` is
  positive on the output Hilbert-Schmidt space.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 Hilbert-Schmidt adjoints.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- If a Hilbert-Schmidt map is norm-contractive, then its Hilbert-Schmidt
adjoint is norm-contractive with respect to the Frobenius norm. -/
theorem hsAdjoint_contract_of_contract
    {n m : ℕ} (Φ : HSMap n m)
    (hΦ : ∀ x : Mₙ n, ‖Φ x‖ ≤ ‖x‖) (y : Mₙ m) :
    ‖hsAdjoint Φ y‖ ≤ ‖y‖ := by
  let T : HSOp m := Φ.comp (hsAdjoint Φ)
  have hsq :
      ‖hsAdjoint Φ y‖ ^ 2 =
        Complex.re (Matrix.trace (Matrix.conjTranspose y * (T y))) := by
    simpa [T] using (HiaiPetz.AmbientSubmodule.hsQForm_comp_hsAdjoint_eq_norm_sq Φ y).symm
  have htrace_inner :
      Complex.re (Matrix.trace (Matrix.conjTranspose y * (T y))) =
        Complex.re (inner ℂ (T y) y) := by
    simpa [T] using (hsQForm_real_eq_inner_real (T := T) y)
  have hmid :
      Complex.re (inner ℂ (T y) y) ≤ ‖Φ ((hsAdjoint Φ) y)‖ * ‖y‖ := by
    have hTy : T y = Φ ((hsAdjoint Φ) y) := by
      rfl
    calc
      Complex.re (inner ℂ (T y) y)
          ≤ ‖T y‖ * ‖y‖ := by
              change RCLike.re (inner ℂ (T y) y) ≤ ‖T y‖ * ‖y‖
              -- Explicit instances: the statement's norm elaborates under the
              -- Frobenius scope while the inner product carries the unified
              -- `instMatrix*` index; `exact` bridges the defeq indices.
              exact @re_inner_le_norm ℂ (Mₙ m) _
                (instMatrixNormedAddCommGroup (n := m)).toSeminormedAddCommGroup
                (instMatrixInnerProductSpace (n := m)) (T y) y
      _ = ‖Φ ((hsAdjoint Φ) y)‖ * ‖y‖ := by
            rw [hTy]
  have hcontract := hΦ ((hsAdjoint Φ) y)
  have hsq_le : ‖hsAdjoint Φ y‖ ^ 2 ≤ ‖hsAdjoint Φ y‖ * ‖y‖ := by
    calc
      ‖hsAdjoint Φ y‖ ^ 2
          = Complex.re (Matrix.trace (Matrix.conjTranspose y * (T y))) := hsq
      _ = Complex.re (inner ℂ (T y) y) := htrace_inner
      _ ≤ ‖Φ ((hsAdjoint Φ) y)‖ * ‖y‖ := hmid
      _ ≤ ‖hsAdjoint Φ y‖ * ‖y‖ := by
            exact mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)
  nlinarith [norm_nonneg (hsAdjoint Φ y), norm_nonneg y, hsq_le]

end MatrixScopedInstances

end HiaiPetz
