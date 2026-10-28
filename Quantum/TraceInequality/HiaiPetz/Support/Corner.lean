/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Support

/-!
# Matrix corner submodule

Foundation-level definitions for the corner cut out by a matrix `P`.  The
submodule contains the matrices `X` satisfying `P * X * P = X`, and
`matrixCornerProj P` is the cornering map `X ↦ P * X * P`.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

/-- The corner submodule cut out by a matrix `P`, consisting of matrices satisfying `PXP = X`. -/
def matrixCornerSubmodule {m : ℕ} (P : Mₙ m) : Submodule ℂ (Mₙ m) where
  carrier := {X | P * X * P = X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    calc
      P * (X + Y) * P = P * X * P + P * Y * P := by
        simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = X + Y := by rw [hX, hY]
  smul_mem' := by
    intro a X hX
    calc
      P * (a • X) * P = a • (P * X * P) := by
        simp [Matrix.mul_assoc]
      _ = a • X := by rw [hX]

/-- Membership in `matrixCornerSubmodule P` unfolds to the corner equation `P * X * P = X`. -/
@[simp] theorem mem_matrixCornerSubmodule_iff {m : ℕ} {P X : Mₙ m} :
    X ∈ matrixCornerSubmodule P ↔ P * X * P = X := Iff.rfl

/-- The raw cornering map `X ↦ PXP` on matrices. -/
noncomputable def matrixCornerProj {m : ℕ} (P : Mₙ m) : HSOp m :=
  leftMul P * rightMul P

/-- Evaluate the cornering map: `matrixCornerProj P X = P * X * P`. -/
@[simp] theorem matrixCornerProj_apply {m : ℕ} (P X : Mₙ m) :
    matrixCornerProj P X = P * X * P := by
  simp [matrixCornerProj, leftMul_apply, rightMul_apply, Matrix.mul_assoc]

private theorem matrixCornerSubmodule_left_fix_of_isIdempotentElem
    {m : ℕ} {P X : Mₙ m} (hP : IsIdempotentElem P)
    (hX : X ∈ matrixCornerSubmodule P) :
    P * X = X := by
  rw [mem_matrixCornerSubmodule_iff] at hX
  calc
    P * X = P * (P * X * P) := by rw [hX]
    _ = (P * P) * X * P := by simp [Matrix.mul_assoc]
    _ = P * X * P := by rw [hP.eq]
    _ = X := hX

private theorem matrixCornerSubmodule_right_fix_of_isIdempotentElem
    {m : ℕ} {P X : Mₙ m} (hP : IsIdempotentElem P)
    (hX : X ∈ matrixCornerSubmodule P) :
    X * P = X := by
  rw [mem_matrixCornerSubmodule_iff] at hX
  calc
    X * P = (P * X * P) * P := by rw [hX]
    _ = P * X * (P * P) := by simp [Matrix.mul_assoc]
    _ = P * X * P := by rw [hP.eq]
    _ = X := hX

/-- When `P` is a projection, a corner element is fixed on the left: `P * X = X`. -/
theorem matrixCornerSubmodule.left_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    P * X = X :=
  matrixCornerSubmodule_left_fix_of_isIdempotentElem hP.isIdempotentElem hX

/-- When `P` is a projection, a corner element is fixed on the right: `X * P = X`. -/
theorem matrixCornerSubmodule.right_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    X * P = X :=
  matrixCornerSubmodule_right_fix_of_isIdempotentElem hP.isIdempotentElem hX

end HiaiPetz
