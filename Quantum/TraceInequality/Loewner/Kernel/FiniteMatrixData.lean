/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Order

/-!
# Finite Löwner matrix data

This module contains the lightweight finite-point data shared by the public
Löwner statements and the Korányi finite construction.
-/

namespace Quantum.TraceInequality

noncomputable section

section Kernel

variable (f : ℝ → ℝ)

/-- The divided-difference Loewner kernel, with the diagonal defined by `deriv f`. -/
def loewnerKernel (x y : ℝ) : ℝ :=
  if x = y then deriv f x else (f x - f y) / (x - y)

end Kernel

section Matrix

variable {n : ℕ} (f : ℝ → ℝ) (y : Fin (n + 1) → ℝ)

/-- The finite Loewner matrix associated to a point family. -/
def loewnerMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => (loewnerKernel f (y i) (y j) : ℂ)

end Matrix

section Points

variable {n : ℕ}

/-- Point hypotheses for the finite Koranyi construction on `(-1,1)` with base point `0`. -/
def pointsHyp (y : Fin (n + 1) → ℝ) : Prop :=
  y 0 = 0 ∧
    Function.Injective y ∧
      (∀ i, y i ∈ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ i, i ≠ 0 → y i ≠ 0)

end Points

end

end Quantum.TraceInequality

namespace Quantum.TraceInequality.Loewner

noncomputable section

/-! ### Kernel preliminaries -/
section Kernel

variable (f : ℝ → ℝ)

/-- On the diagonal, the Loewner kernel is the derivative of `f`. -/
@[simp] lemma loewnerKernel_self (x : ℝ) : loewnerKernel f x x = deriv f x := by
  simp [loewnerKernel]

/-- Off the diagonal, the Loewner kernel is the usual divided difference. -/
lemma loewnerKernel_eq_div {x y : ℝ} (h : x ≠ y) :
    loewnerKernel f x y = (f x - f y) / (x - y) := by
  simp [loewnerKernel, h]

/-! ### Zero-anchor kernel formulas -/
/-- At the right base point `0`, the kernel is `(f x - f 0) / x`. -/
lemma loewnerKernel_zero_right {x : ℝ} (h : x ≠ 0) :
    loewnerKernel f x 0 = (f x - f 0) / x := by
  simpa [sub_eq_add_neg] using (loewnerKernel_eq_div (f := f) (x := x) (y := 0) h)

/-- At the left base point `0`, the symmetric kernel is `(f y - f 0) / y`. -/
lemma loewnerKernel_zero_left {y : ℝ} (h : y ≠ 0) :
    loewnerKernel f 0 y = (f y - f 0) / y := by
  have h0y : (0 : ℝ) ≠ y := by simpa using h.symm
  -- Convert `(f 0 - f y)/(0-y)` into `(f y - f 0)/y`.
  calc
    loewnerKernel f 0 y = (f 0 - f y) / (0 - y) := by
      simpa using (loewnerKernel_eq_div (f := f) (x := 0) (y := y) h0y)
    _ = (-(f 0 - f y)) / (-(0 - y)) := by
      simpa using (neg_div_neg_eq (f 0 - f y) (0 - y)).symm
    _ = (f y - f 0) / y := by
      simp [sub_eq_add_neg, add_comm]

/-! ### Koranyi kernel identities -/
/-- The finite Koranyi identity relating the two zero-anchored divided differences. -/
lemma koranyi_identity {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    (loewnerKernel f x y - loewnerKernel f 0 y) / x =
      (loewnerKernel f x y - loewnerKernel f x 0) / y := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  -- Reduce to a purely rational identity.
  simp [loewnerKernel_eq_div (f := f) (x := x) (y := y) hxy,
    loewnerKernel_zero_left (f := f) (y := y) hy,
    loewnerKernel_zero_right (f := f) (x := x) hx]
  field_simp [hx, hy, hxy']
  ring

/-- The Loewner kernel is symmetric in its two real arguments. -/
lemma loewnerKernel_swap (x y : ℝ) : loewnerKernel f x y = loewnerKernel f y x := by
  by_cases hxy : x = y
  · subst hxy
    simp
  · -- Reduce to the standard `(-a)/(-b) = a/b` trick.
    have hyx : y ≠ x := by simpa [eq_comm] using hxy
    calc
      loewnerKernel f x y = (f x - f y) / (x - y) := by
        simp [loewnerKernel, hxy]
      _ = (-(f x - f y)) / (-(x - y)) := by
        simpa using (neg_div_neg_eq (f x - f y) (x - y)).symm
      _ = (f y - f x) / (y - x) := by
        simp [sub_eq_add_neg]
      _ = loewnerKernel f y x := by
        simp [loewnerKernel, hyx]

end Kernel

end

end Quantum.TraceInequality.Loewner
