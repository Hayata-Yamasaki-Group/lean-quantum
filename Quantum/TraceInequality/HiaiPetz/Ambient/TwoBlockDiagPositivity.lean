/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.BlockDiagonal
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Positive-definiteness helpers for two-block diagonal matrices

This module records the elementary positivity facts needed to build block
diagonal positive inputs for the ambient Hiai-Petz operators.  The proofs
reduce scalar multiples and two-block diagonals to the defining quadratic
forms of `Matrix.PosDef`.

## Main results

* `matrixPosDef_smul`: positive scalar multiples preserve matrix positive
  definiteness.
* `twoBlockDiag_posDef`: a block diagonal matrix is positive definite when
  both diagonal blocks are positive definite.

## References

* Internal finite-dimensional linear algebra used in the Hiai-Petz
  two-block construction.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section MatrixScopedInstances

/-- Positive scalar multiplication preserves matrix positive definiteness:
if `A` is positive definite and `r > 0`, then `r • A` is positive definite. -/
theorem matrixPosDef_smul {n : ℕ} {A : Mₙ n} {r : ℝ} :
    Matrix.PosDef A → 0 < r → Matrix.PosDef (r • A) := by
  intro hA hr
  exact hA.smul hr

/-- Positive definiteness is preserved by forming a two-block diagonal matrix:
the quadratic form splits into the sum of the two block quadratic forms. -/
theorem twoBlockDiag_posDef {n : ℕ} {A₁ A₂ : Mₙ n} :
    Matrix.PosDef A₁ → Matrix.PosDef A₂ → Matrix.PosDef (twoBlockDiag A₁ A₂) := by
  intro hA₁ hA₂
  have hHerm : Matrix.IsHermitian (twoBlockDiag A₁ A₂) := by
    change Matrix.conjTranspose (twoBlockDiag A₁ A₂) = twoBlockDiag A₁ A₂
    rw [conjTranspose_twoBlockDiag]
    exact congrArg₂ twoBlockDiag hA₁.isHermitian hA₂.isHermitian
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro x hx
  refine RCLike.pos_iff.mpr ⟨?_, ?_⟩
  · let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
      (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
    let y : Fin n ⊕ Fin n → ℂ := x ∘ e.symm
    let x₁ : Fin n → ℂ := y ∘ Sum.inl
    let x₂ : Fin n → ℂ := y ∘ Sum.inr
    have hy_comp_explicit :
        y ∘ finSumFinEquiv.symm ∘ finCongr (by simp [two_mul]) = x := by
      ext i
      simp [y, e]
    have hreindex_mul :
        (reindexToBlockMatrix n (twoBlockDiag A₁ A₂)).mulVec y =
          (twoBlockDiag A₁ A₂).mulVec x ∘ e.symm := by
      simpa [reindexToBlockMatrix, reindexToBlockEquiv, e, hy_comp_explicit] using
        (Matrix.submatrix_mulVec_equiv (M := twoBlockDiag A₁ A₂) (v := y)
          (e₁ := e.symm) (e₂ := e.symm))
    have hy_mul :
        (Matrix.fromBlocks A₁ 0 0 A₂).mulVec y =
          Sum.elim (A₁.mulVec x₁) (A₂.mulVec x₂) := by
      simpa [y, x₁, x₂] using Matrix.fromBlocks_mulVec A₁ 0 0 A₂ y
    have hreindex_mul' :
        (twoBlockDiag A₁ A₂).mulVec x ∘ e.symm =
          Sum.elim (A₁.mulVec x₁) (A₂.mulVec x₂) := by
      calc
        (twoBlockDiag A₁ A₂).mulVec x ∘ e.symm =
            (reindexToBlockMatrix n (twoBlockDiag A₁ A₂)).mulVec y := by
              exact hreindex_mul.symm
        _ = Sum.elim (A₁.mulVec x₁) (A₂.mulVec x₂) := by
              rw [reindexToBlockMatrix_twoBlockDiag]
              exact hy_mul
    have hstar_split : star y = Sum.elim (star x₁) (star x₂) := by
      ext i
      cases i <;> rfl
    have hsum :
        dotProduct (star y) (Sum.elim (A₁.mulVec x₁) (A₂.mulVec x₂)) =
          dotProduct (star x₁) (A₁.mulVec x₁) +
            dotProduct (star x₂) (A₂.mulVec x₂) := by
      rw [hstar_split]
      simp
    have hdot :
        dotProduct (star y) ((twoBlockDiag A₁ A₂).mulVec x ∘ e.symm) =
          dotProduct (star x) ((twoBlockDiag A₁ A₂).mulVec x) := by
      simpa [y, dotProduct] using
        (comp_equiv_dotProduct_comp_equiv (x := star x)
          (y := (twoBlockDiag A₁ A₂).mulVec x) e.symm)
    have hx_split : x₁ ≠ 0 ∨ x₂ ≠ 0 := by
      by_contra hsplit
      push_neg at hsplit
      have hy_zero : y = 0 := by
        ext i
        cases i with
        | inl j => simpa [x₁] using congrArg (fun f => f j) hsplit.1
        | inr j => simpa [x₂] using congrArg (fun f => f j) hsplit.2
      have hx_zero : x = 0 := by
        ext i
        have hi := congrArg (fun f => f (e i)) hy_zero
        simpa [y] using hi
      exact hx hx_zero
    have hq₁_nonneg : 0 ≤ Complex.re (dotProduct (star x₁) (A₁.mulVec x₁)) := by
      by_cases hx₁ : x₁ = 0
      · simp [hx₁]
      · exact le_of_lt (hA₁.re_dotProduct_pos hx₁)
    have hq₂_nonneg : 0 ≤ Complex.re (dotProduct (star x₂) (A₂.mulVec x₂)) := by
      by_cases hx₂ : x₂ = 0
      · simp [hx₂]
      · exact le_of_lt (hA₂.re_dotProduct_pos hx₂)
    have hq_pos :
        0 < Complex.re (dotProduct (star x₁) (A₁.mulVec x₁)) +
          Complex.re (dotProduct (star x₂) (A₂.mulVec x₂)) := by
      cases hx_split with
      | inl hx₁ => exact add_pos_of_pos_of_nonneg (hA₁.re_dotProduct_pos hx₁) hq₂_nonneg
      | inr hx₂ => exact add_pos_of_nonneg_of_pos hq₁_nonneg (hA₂.re_dotProduct_pos hx₂)
    have hq_pos' :
        0 <
          Complex.re
            (dotProduct (star x₁) (A₁.mulVec x₁) +
              dotProduct (star x₂) (A₂.mulVec x₂)) := by
      simpa [Complex.add_re] using hq_pos
    calc
      0 < Complex.re (dotProduct (star y) (Sum.elim (A₁.mulVec x₁) (A₂.mulVec x₂))) := by
        rw [hsum]
        exact hq_pos'
      _ = Complex.re (dotProduct (star y) ((twoBlockDiag A₁ A₂).mulVec x ∘ e.symm)) := by
            rw [hreindex_mul']
      _ = Complex.re (dotProduct (star x) ((twoBlockDiag A₁ A₂).mulVec x)) := by
            rw [hdot]
  · simpa using hHerm.im_star_dotProduct_mulVec_self x

end MatrixScopedInstances

end HiaiPetz
