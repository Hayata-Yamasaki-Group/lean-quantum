/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Support.Corner

/-!
# Namespaced API for the matrix support projection

Convenience re-exports for `matrixSupportProj C`, the orthogonal projection onto
the support subspace of a matrix `C`.  The underlying facts are proved in
`HiaiPetz/Support/Corner.lean`; this module only gathers them under the
`MatrixSupportProj` namespace so downstream files can refer to the projection's
properties by short dotted names (`MatrixSupportProj.isProj`, `.idempotent`, …).

## Main results

* `MatrixSupportProj.isProj` / `idempotent` / `isSelfAdjoint`: the projection is
  a self-adjoint idempotent.
* `MatrixSupportProj.mulVec_eq_self_iff`: fixed vectors of the projection are
  exactly the elements of the support subspace.
* `MatrixSupportProj.left_mul_eq_self_of_mem` / `right_mul_eq_self_of_mem` /
  `mem_corner_iff`: characterizations of the corner subalgebra cut out by the
  projection.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

/- Namespaced API for the projection onto the matrix support subspace. -/
namespace MatrixSupportProj

/-- The matrix support projection `matrixSupportProj C` is a matrix projection
(a self-adjoint idempotent). -/
theorem isProj {n : ℕ} (C : Mₙ n) :
    IsMatrixProj (matrixSupportProj C) :=
  matrixSupportProj_isProj C

/-- The matrix support projection is idempotent. -/
theorem idempotent {n : ℕ} (C : Mₙ n) :
    matrixSupportProj C * matrixSupportProj C = matrixSupportProj C :=
  (isProj C).1

/-- The matrix support projection is self-adjoint. -/
theorem isSelfAdjoint {n : ℕ} (C : Mₙ n) :
    IsSelfAdjoint (matrixSupportProj C) :=
  (isProj C).2

/-- A vector is fixed by the matrix support projection if and only if it lies in
the support subspace of `C`. -/
theorem mulVec_eq_self_iff {n : ℕ} (C : Mₙ n) (x : Fin n → ℂ) :
    (matrixSupportProj C).mulVec x = x ↔ x ∈ matrixSupportSubspace C :=
  matrixSupportProj_mulVec_eq_self_iff C x

/-- Left multiplication by the support projection fixes every element of the
corner subalgebra it determines. -/
theorem left_mul_eq_self_of_mem {n : ℕ} {C X : Mₙ n}
    (hX : X ∈ matrixCornerSubmodule (matrixSupportProj C)) :
    matrixSupportProj C * X = X :=
  matrixCornerSubmodule.left_fix (isProj C) hX

/-- Right multiplication by the support projection fixes every element of the
corner subalgebra it determines. -/
theorem right_mul_eq_self_of_mem {n : ℕ} {C X : Mₙ n}
    (hX : X ∈ matrixCornerSubmodule (matrixSupportProj C)) :
    X * matrixSupportProj C = X :=
  matrixCornerSubmodule.right_fix (isProj C) hX

/-- Membership in the corner subalgebra of the support projection is equivalent
to being fixed by the two-sided compression `P * X * P = X`. -/
theorem mem_corner_iff {n : ℕ} {C X : Mₙ n} :
    X ∈ matrixCornerSubmodule (matrixSupportProj C) ↔
      matrixSupportProj C * X * matrixSupportProj C = X :=
  mem_matrixCornerSubmodule_iff

end MatrixSupportProj

end HiaiPetz
