/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.AdjointHelpers
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.AdjointHelpers

/-!
# Block positivity and adjoint two-positivity
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section

/-! ### Block Positivity and Adjoint Inverse-Form DPI -/
private def twoBlockMatrixUnflatten {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix (Fin 2) (Fin 2) (Mₙ n) :=
  ![![F.toBlocks₁₁, F.toBlocks₁₂], ![F.toBlocks₂₁, F.toBlocks₂₂]]

private theorem twoBlockMatrixFlatten_unflatten {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    twoBlockMatrixFlatten (twoBlockMatrixUnflatten F) = F := by
  simp [twoBlockMatrixFlatten, twoBlockMatrixUnflatten, Matrix.fromBlocks_toBlocks]

private theorem trace_fromBlocks {n : ℕ} (A B C D : Mₙ n) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  classical
  simp [Matrix.trace, Matrix.fromBlocks]

private theorem trace_twoBlockMatrixFlatten_mul {n : ℕ}
    (M N : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    Matrix.trace (twoBlockMatrixFlatten M * twoBlockMatrixFlatten N) =
      (Matrix.trace (M 0 0 * N 0 0) + Matrix.trace (M 0 1 * N 1 0)) +
        (Matrix.trace (M 1 0 * N 0 1) + Matrix.trace (M 1 1 * N 1 1)) := by
  classical
  rw [show twoBlockMatrixFlatten M * twoBlockMatrixFlatten N =
      Matrix.fromBlocks
        (M 0 0 * N 0 0 + M 0 1 * N 1 0)
        (M 0 0 * N 0 1 + M 0 1 * N 1 1)
        (M 1 0 * N 0 0 + M 1 1 * N 1 0)
        (M 1 0 * N 0 1 + M 1 1 * N 1 1) by
    simp [twoBlockMatrixFlatten, Matrix.fromBlocks_multiply]]
  rw [trace_fromBlocks]
  simp [Matrix.trace_add]

private theorem block_entry_conjTranspose_eq_of_flatten_isHermitian {n : ℕ}
    {M : Matrix (Fin 2) (Fin 2) (Mₙ n)}
    (hM : (twoBlockMatrixFlatten M).IsHermitian) (i j : Fin 2) :
    Matrix.conjTranspose (M j i) = M i j := by
  ext a b
  fin_cases i <;> fin_cases j
  · simpa [twoBlockMatrixFlatten] using hM.apply (Sum.inl a) (Sum.inl b)
  · simpa [twoBlockMatrixFlatten] using hM.apply (Sum.inl a) (Sum.inr b)
  · simpa [twoBlockMatrixFlatten] using hM.apply (Sum.inr a) (Sum.inl b)
  · simpa [twoBlockMatrixFlatten] using hM.apply (Sum.inr a) (Sum.inr b)

private theorem trace_block_hsAdjoint_eq {n m : ℕ} (Ψ : HSMap n m)
    {M : Matrix (Fin 2) (Fin 2) (Mₙ n)}
    (N : Matrix (Fin 2) (Fin 2) (Mₙ m))
    (hM : (twoBlockMatrixFlatten M).IsHermitian)
    (hP : (twoBlockMatrixFlatten (M.map Ψ)).IsHermitian) :
    Matrix.trace (twoBlockMatrixFlatten M * twoBlockMatrixFlatten (N.map (hsAdjoint Ψ))) =
      Matrix.trace (twoBlockMatrixFlatten (M.map Ψ) * twoBlockMatrixFlatten N) := by
  classical
  rw [trace_twoBlockMatrixFlatten_mul M (N.map (hsAdjoint Ψ))]
  rw [trace_twoBlockMatrixFlatten_mul (M.map Ψ) N]
  have h00 : Matrix.trace (M 0 0 * hsAdjoint Ψ (N 0 0)) =
      Matrix.trace (Ψ (M 0 0) * N 0 0) := by
    have hM00 : Matrix.conjTranspose (M 0 0) = M 0 0 := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hM 0 0
    have hP00 : Matrix.conjTranspose (Ψ (M 0 0)) = Ψ (M 0 0) := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hP 0 0
    calc
      Matrix.trace (M 0 0 * hsAdjoint Ψ (N 0 0)) =
          Matrix.trace (Matrix.conjTranspose (M 0 0) * hsAdjoint Ψ (N 0 0)) := by
        rw [hM00]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ (M 0 0)) * N 0 0) :=
        trace_hsAdjoint_eq Ψ (M 0 0) (N 0 0)
      _ = Matrix.trace (Ψ (M 0 0) * N 0 0) := by
        rw [hP00]
  have h01 : Matrix.trace (M 0 1 * hsAdjoint Ψ (N 1 0)) =
      Matrix.trace (Ψ (M 0 1) * N 1 0) := by
    have hM10 : Matrix.conjTranspose (M 1 0) = M 0 1 := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hM 0 1
    have hP10 : Matrix.conjTranspose (Ψ (M 1 0)) = Ψ (M 0 1) := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hP 0 1
    calc
      Matrix.trace (M 0 1 * hsAdjoint Ψ (N 1 0)) =
          Matrix.trace (Matrix.conjTranspose (M 1 0) * hsAdjoint Ψ (N 1 0)) := by
        rw [hM10]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ (M 1 0)) * N 1 0) :=
        trace_hsAdjoint_eq Ψ (M 1 0) (N 1 0)
      _ = Matrix.trace (Ψ (M 0 1) * N 1 0) := by
        rw [hP10]
  have h10 : Matrix.trace (M 1 0 * hsAdjoint Ψ (N 0 1)) =
      Matrix.trace (Ψ (M 1 0) * N 0 1) := by
    have hM01 : Matrix.conjTranspose (M 0 1) = M 1 0 := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hM 1 0
    have hP01 : Matrix.conjTranspose (Ψ (M 0 1)) = Ψ (M 1 0) := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hP 1 0
    calc
      Matrix.trace (M 1 0 * hsAdjoint Ψ (N 0 1)) =
          Matrix.trace (Matrix.conjTranspose (M 0 1) * hsAdjoint Ψ (N 0 1)) := by
        rw [hM01]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ (M 0 1)) * N 0 1) :=
        trace_hsAdjoint_eq Ψ (M 0 1) (N 0 1)
      _ = Matrix.trace (Ψ (M 1 0) * N 0 1) := by
        rw [hP01]
  have h11 : Matrix.trace (M 1 1 * hsAdjoint Ψ (N 1 1)) =
      Matrix.trace (Ψ (M 1 1) * N 1 1) := by
    have hM11 : Matrix.conjTranspose (M 1 1) = M 1 1 := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hM 1 1
    have hP11 : Matrix.conjTranspose (Ψ (M 1 1)) = Ψ (M 1 1) := by
      simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hP 1 1
    calc
      Matrix.trace (M 1 1 * hsAdjoint Ψ (N 1 1)) =
          Matrix.trace (Matrix.conjTranspose (M 1 1) * hsAdjoint Ψ (N 1 1)) := by
        rw [hM11]
      _ = Matrix.trace (Matrix.conjTranspose (Ψ (M 1 1)) * N 1 1) :=
        trace_hsAdjoint_eq Ψ (M 1 1) (N 1 1)
      _ = Matrix.trace (Ψ (M 1 1) * N 1 1) := by
        rw [hP11]
  simpa using (by rw [h00, h01, h10, h11])

private theorem trace_mul_hsAdjoint_conjTranspose {n m : ℕ} (Ψ : HSMap n m)
    (X : Mₙ n) (Y : Mₙ m) :
    Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Ψ Y)) =
      Matrix.trace (Ψ X * Matrix.conjTranspose Y) := by
  calc
    Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Ψ Y)) =
        Matrix.trace (Matrix.conjTranspose
          (Matrix.conjTranspose (X * Matrix.conjTranspose (hsAdjoint Ψ Y)))) := by
      simp
    _ = star (Matrix.trace
        (Matrix.conjTranspose (X * Matrix.conjTranspose (hsAdjoint Ψ Y)))) := by
      rw [Matrix.trace_conjTranspose]
    _ = star (Matrix.trace (hsAdjoint Ψ Y * Matrix.conjTranspose X)) := by
      simp [Matrix.conjTranspose_mul]
    _ = star (Matrix.trace (Matrix.conjTranspose X * hsAdjoint Ψ Y)) := by
      rw [Matrix.trace_mul_comm]
    _ = star (Matrix.trace (Matrix.conjTranspose (Ψ X) * Y)) := by
      rw [trace_hsAdjoint_eq Ψ X Y]
    _ = Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose (Ψ X) * Y)) := by
      rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (Matrix.conjTranspose Y * Ψ X) := by
      simp [Matrix.conjTranspose_mul]
    _ = Matrix.trace (Ψ X * Matrix.conjTranspose Y) := by
      rw [Matrix.trace_mul_comm]

private theorem hsAdjoint_map_conjTranspose_of_isTwoPositiveMap {n m : ℕ}
    {Ψ : HSMap n m} (hΨ : IsTwoPositiveMap Ψ) (Y : Mₙ m) :
    hsAdjoint Ψ (Matrix.conjTranspose Y) = Matrix.conjTranspose (hsAdjoint Ψ Y) := by
  classical
  rw [Matrix.ext_iff_trace_mul_left]
  intro X
  calc
    Matrix.trace (X * hsAdjoint Ψ (Matrix.conjTranspose Y)) =
        Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose X) *
          hsAdjoint Ψ (Matrix.conjTranspose Y)) := by
      simp
    _ = Matrix.trace (Matrix.conjTranspose (Ψ (Matrix.conjTranspose X)) *
          Matrix.conjTranspose Y) :=
      trace_hsAdjoint_eq Ψ (Matrix.conjTranspose X) (Matrix.conjTranspose Y)
    _ = Matrix.trace (Ψ X * Matrix.conjTranspose Y) := by
      rw [map_conjTranspose_of_isTwoPositiveMap hΨ X]
      simp
    _ = Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Ψ Y)) :=
      (trace_mul_hsAdjoint_conjTranspose Ψ X Y).symm

private theorem trace_rankOne_mul_eq_dot {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (O : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.vecMulVec v (star v) * O) =
      dotProduct (star v) (O.mulVec v) := by
  classical
  suffices
      (∑ x, ∑ y, v x * star (v y) * O y x) =
        ∑ x, star (v x) * ∑ y, O x y * v y by
    simpa [Matrix.trace, Matrix.vecMulVec_apply, Matrix.mul_apply, dotProduct,
      Matrix.mulVec] using this
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
The Hilbert--Schmidt adjoint of a two-positive finite-dimensional map is again
two-positive.
-/
theorem isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap {n m : ℕ} {Ψ : HSMap n m}
    (hΨ : IsTwoPositiveMap Ψ) :
    IsTwoPositiveMap (hsAdjoint Ψ) := by
  intro N hN
  change (twoBlockMatrixFlatten (N.map (hsAdjoint Ψ))).PosSemidef
  have hOherm : (twoBlockMatrixFlatten (N.map (hsAdjoint Ψ))).IsHermitian := by
    refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
    · have hN00 : Matrix.conjTranspose (N 0 0) = N 0 0 := by
        simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hN.1 0 0
      have h := hsAdjoint_map_conjTranspose_of_isTwoPositiveMap hΨ (N 0 0)
      rw [hN00] at h
      exact h.symm
    · have hN01 : Matrix.conjTranspose (N 0 1) = N 1 0 := by
        simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hN.1 1 0
      have h := hsAdjoint_map_conjTranspose_of_isTwoPositiveMap hΨ (N 0 1)
      rw [hN01] at h
      exact h.symm
    · have hN11 : Matrix.conjTranspose (N 1 1) = N 1 1 := by
        simpa using block_entry_conjTranspose_eq_of_flatten_isHermitian hN.1 1 1
      have h := hsAdjoint_map_conjTranspose_of_isTwoPositiveMap hΨ (N 1 1)
      rw [hN11] at h
      exact h.symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hOherm ?_
  intro v
  let O : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    twoBlockMatrixFlatten (N.map (hsAdjoint Ψ))
  let R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.vecMulVec v (star v)
  let M : Matrix (Fin 2) (Fin 2) (Mₙ n) := twoBlockMatrixUnflatten R
  have hMpos : BlockMatrixPosSemidef M := by
    simpa [BlockMatrixPosSemidef, M, R, twoBlockMatrixFlatten_unflatten] using
      (Matrix.posSemidef_vecMulVec_self_star (R := ℂ) v)
  have hPpos : BlockMatrixPosSemidef (M.map Ψ) := hΨ M hMpos
  have htrace := trace_block_hsAdjoint_eq Ψ (M := M) N hMpos.1 hPpos.1
  have hPpos' : (twoBlockMatrixFlatten (M.map Ψ)).PosSemidef := hPpos
  have hN' : (twoBlockMatrixFlatten N).PosSemidef := hN
  have hprod :
      0 ≤ Matrix.trace (twoBlockMatrixFlatten (M.map Ψ) * twoBlockMatrixFlatten N) :=
    matrix_trace_mul_nonneg_of_posSemidef hPpos' hN'
  have hrank : Matrix.trace (R * O) = dotProduct (star v) (O.mulVec v) := by
    simpa [O, R] using trace_rankOne_mul_eq_dot v O
  rw [← hrank]
  have hleft : Matrix.trace (R * O) =
      Matrix.trace (twoBlockMatrixFlatten (M.map Ψ) * twoBlockMatrixFlatten N) := by
    simpa [M, R, O, twoBlockMatrixFlatten_unflatten] using htrace
  rw [hleft]
  exact hprod

end

end Quantum.TraceInequality.Loewner.HiaiPetz
