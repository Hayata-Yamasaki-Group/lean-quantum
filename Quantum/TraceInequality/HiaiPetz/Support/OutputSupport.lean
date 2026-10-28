/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport

/-!
# Namespaced API for the output support projection

Convenience re-exports for `outputSupportProj Φ`, the orthogonal projection onto
the support of `Φ(1)` for a Hilbert–Schmidt map `Φ`.  Each result specializes the
corresponding `MatrixSupportProj` lemma to the matrix `Φ (1 : Mₙ n)`, gathering
them under the `OutputSupportProj` namespace for short dotted access downstream.

## Main results

* `OutputSupportProj.isProj` / `idempotent` / `isSelfAdjoint`: the output support
  projection is a self-adjoint idempotent.
* `OutputSupportProj.mulVec_eq_self_iff`: fixed vectors are exactly the elements
  of the output support subspace.
* `OutputSupportProj.left_mul_eq_self_of_mem` / `right_mul_eq_self_of_mem` /
  `mem_corner_iff`: characterizations of the corner subalgebra cut out by the
  projection.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

/- Namespaced API for the projection onto the output support of `Φ(1)`. -/
namespace OutputSupportProj

/-- The output support projection `outputSupportProj Φ` is a matrix projection
(a self-adjoint idempotent). -/
theorem isProj {n m : ℕ} (Φ : HSMap n m) :
    IsMatrixProj (outputSupportProj Φ) :=
  MatrixSupportProj.isProj (Φ (1 : Mₙ n))

/-- The output support projection is idempotent. -/
theorem idempotent {n m : ℕ} (Φ : HSMap n m) :
    outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
  (isProj Φ).1

/-- The output support projection is self-adjoint. -/
theorem isSelfAdjoint {n m : ℕ} (Φ : HSMap n m) :
    IsSelfAdjoint (outputSupportProj Φ) :=
  (isProj Φ).2

/-- A vector is fixed by the output support projection if and only if it lies in
the output support subspace of `Φ`. -/
theorem mulVec_eq_self_iff {n m : ℕ} (Φ : HSMap n m) (x : Fin m → ℂ) :
    (outputSupportProj Φ).mulVec x = x ↔ x ∈ outputSupportSubspace Φ :=
  MatrixSupportProj.mulVec_eq_self_iff (Φ (1 : Mₙ n)) x

/-- Left multiplication by the output support projection fixes every element of
the corner subalgebra it determines. -/
theorem left_mul_eq_self_of_mem {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m}
    (hX : X ∈ matrixCornerSubmodule (outputSupportProj Φ)) :
    outputSupportProj Φ * X = X :=
  MatrixSupportProj.left_mul_eq_self_of_mem (C := Φ (1 : Mₙ n)) hX

/-- Right multiplication by the output support projection fixes every element of
the corner subalgebra it determines. -/
theorem right_mul_eq_self_of_mem {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m}
    (hX : X ∈ matrixCornerSubmodule (outputSupportProj Φ)) :
    X * outputSupportProj Φ = X :=
  MatrixSupportProj.right_mul_eq_self_of_mem (C := Φ (1 : Mₙ n)) hX

/-- Membership in the corner subalgebra of the output support projection is
equivalent to being fixed by the two-sided compression `P * X * P = X`. -/
theorem mem_corner_iff {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m} :
    X ∈ matrixCornerSubmodule (outputSupportProj Φ) ↔
      outputSupportProj Φ * X * outputSupportProj Φ = X :=
  MatrixSupportProj.mem_corner_iff (C := Φ (1 : Mₙ n))

end OutputSupportProj

end HiaiPetz
