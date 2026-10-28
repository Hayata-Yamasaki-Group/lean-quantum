/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.PaperSupport
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.InverseTermReductionRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.AdjointHelpers
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.BlockPositivity
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone

/-!
# Carlen 2022 Theorem 1.46 boundary-support infrastructure

This module contains the boundary-support infrastructure stage for Carlen 2022,
Theorem 1.46: Hilbert--Schmidt operator instances, positivity from
two-positivity, support-corner transport, common adjoint support, and the
reduced input map used by the paper-support specialization.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder Matrix.Norms.Frobenius

noncomputable section

/-! ### HS-Operator Instances and Positivity from Two-Positivity -/
attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance carlenBoundaryHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance carlenBoundaryHSOpStarRing {n : ℕ} : StarRing (HSOp n) :=
  (carlenBoundaryHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- `HSOp n` is a complex algebra. -/
noncomputable local instance carlenBoundaryHSOpComplexAlgebra {n : ℕ} :
    Algebra ℂ (HSOp n) :=
  ContinuousLinearMap.algebra

/-- `HSOp n` is a complex normed algebra. -/
noncomputable local instance carlenBoundaryHSOpNormedAlgebra {n : ℕ} :
    NormedAlgebra ℂ (HSOp n) :=
  ContinuousLinearMap.toNormedAlgebra

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance carlenBoundaryHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance carlenBoundaryHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance
      (carlenBoundaryHSOpPartialOrder (n := n))
      (carlenBoundaryHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance carlenBoundaryHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (carlenBoundaryHSOpCStarAlgebra (n := n))
    (carlenBoundaryHSOpPartialOrder (n := n))
    (carlenBoundaryHSOpStarOrderedRing (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance carlenBoundaryHSOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance carlenBoundaryHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- A two-positive finite-dimensional map is positive on positive semidefinite matrices. -/
theorem isPositiveMap_of_isTwoPositiveMap {n m : ℕ} {Ψ : HSMap n m}
    (hΨ : IsTwoPositiveMap Ψ) :
    IsPositiveMap Ψ := by
  intro A hA
  rw [Matrix.nonneg_iff_posSemidef] at hA ⊢
  let M : Matrix (Fin 2) (Fin 2) (Mₙ n) :=
    ![![A, 0], ![(0 : Mₙ n), 0]]
  have hM : BlockMatrixPosSemidef M := by
    change (twoBlockMatrixFlatten M).PosSemidef
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · have hzero :
          ((0 : Mₙ n) - Matrix.conjTranspose (0 : Mₙ n) * A⁻¹ *
              (0 : Mₙ n)).IsHermitian := by
          simp
      have h :=
        (Matrix.IsHermitian.fromBlocks₁₁ (B := (0 : Mₙ n)) (D := (0 : Mₙ n))
          hA.1).2 hzero
      simpa [M, twoBlockMatrixFlatten] using h
    · intro x
      have hx := Matrix.PosSemidef.dotProduct_mulVec_nonneg hA (fun i => x (Sum.inl i))
      simpa [M, twoBlockMatrixFlatten, dotProduct, Matrix.mulVec] using hx
  have hMapped : BlockMatrixPosSemidef (M.map Ψ) := hΨ M hM
  have h00 :
      ((twoBlockMatrixFlatten (M.map Ψ)).submatrix Sum.inl Sum.inl).PosSemidef :=
    Matrix.PosSemidef.submatrix hMapped Sum.inl
  simpa [M, twoBlockMatrixFlatten] using h00

/-- The Hilbert--Schmidt adjoint of a two-positive map is positive. -/
theorem isPositiveMap_hsAdjoint_of_isTwoPositiveMap {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsTwoPositiveMap Φ) :
    IsPositiveMap (hsAdjoint Φ) :=
  isPositiveMap_of_isTwoPositiveMap (isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap hΦ)

/-- A unital two-positive map has a positive Hilbert--Schmidt adjoint. -/
theorem isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsUnitalTwoPositiveMap Φ) :
    IsPositiveMap (hsAdjoint Φ) :=
  isPositiveMap_hsAdjoint_of_isTwoPositiveMap hΦ.2

/-! ### Corner Two-Block Matrix Transport -/
private theorem MatrixCornerModel.toMat_symm_adjoint {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y : Mₙ model.dim) :
    (model.toMat.symm (star Y)).1 = star ((model.toMat.symm Y).1) := by
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  let Ystar : matrixCornerSubmodule P :=
    ⟨star Ycorner.1, model.adjoint_mem_corner Ycorner⟩
  have hYstar : model.toMat Ystar = star Y := by
    calc
      model.toMat Ystar = star (model.toMat Ycorner) := model.preservesAdjoint Ycorner
      _ = star Y := by simp [Ycorner]
  have hsub : model.toMat.symm (star Y) = Ystar := by
    apply model.toMat.injective
    simp [hYstar]
  simpa [Ycorner, Ystar] using congrArg Subtype.val hsub

private theorem MatrixCornerModel.toMat_symm_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y Z : Mₙ model.dim) :
    (model.toMat.symm (Y * Z)).1 =
      (model.toMat.symm Y).1 * (model.toMat.symm Z).1 := by
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  let Zcorner : matrixCornerSubmodule P := model.toMat.symm Z
  let YZcorner : matrixCornerSubmodule P :=
    ⟨Ycorner.1 * Zcorner.1, model.mul_mem_corner Ycorner Zcorner⟩
  have hYZ : model.toMat YZcorner = Y * Z := by
    calc
      model.toMat YZcorner = model.toMat Ycorner * model.toMat Zcorner :=
        model.map_mul Ycorner Zcorner
      _ = Y * Z := by simp [Ycorner, Zcorner]
  have hsub : model.toMat.symm (Y * Z) = YZcorner := by
    apply model.toMat.injective
    simp [hYZ]
  simpa [Ycorner, Zcorner, YZcorner] using congrArg Subtype.val hsub

private theorem MatrixCornerModel.toMat_star_of_eq {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) {X Y : Mₙ m}
    (hX : X ∈ matrixCornerSubmodule P) (hY : Y ∈ matrixCornerSubmodule P)
    (hXY : star X = Y) :
    star (model.toMat ⟨X, hX⟩) = model.toMat ⟨Y, hY⟩ := by
  calc
    star (model.toMat ⟨X, hX⟩) =
        model.toMat ⟨star X, model.adjoint_mem_corner ⟨X, hX⟩⟩ :=
      (model.preservesAdjoint ⟨X, hX⟩).symm
    _ = model.toMat ⟨Y, hY⟩ := by
      simp [hXY]

private noncomputable def twoBlockMatrixUnflattenLocal {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix (Fin 2) (Fin 2) (Mₙ n) :=
  ![![F.toBlocks₁₁, F.toBlocks₁₂], ![F.toBlocks₂₁, F.toBlocks₂₂]]

private theorem twoBlockMatrixFlatten_unflattenLocal {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    twoBlockMatrixFlatten (twoBlockMatrixUnflattenLocal F) = F := by
  simp [twoBlockMatrixFlatten, twoBlockMatrixUnflattenLocal, Matrix.fromBlocks_toBlocks]

private theorem twoBlockMatrixUnflattenLocal_flatten {n : ℕ}
    (K : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    twoBlockMatrixUnflattenLocal (twoBlockMatrixFlatten K) = K := by
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    simp [twoBlockMatrixUnflattenLocal, twoBlockMatrixFlatten]

private theorem twoBlockMatrixFlatten_star {n : ℕ}
    (K : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    twoBlockMatrixFlatten (star K) = Matrix.conjTranspose (twoBlockMatrixFlatten K) := by
  ext i j
  cases i <;> cases j <;> simp [twoBlockMatrixFlatten]

private theorem twoBlockMatrixFlatten_mul {n : ℕ}
    (K L : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    twoBlockMatrixFlatten (K * L) = twoBlockMatrixFlatten K * twoBlockMatrixFlatten L := by
  ext i j
  cases i <;> cases j <;>
    simp [twoBlockMatrixFlatten, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def matrixCornerTwoBlockToMatSymm {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (K : Matrix (Fin 2) (Fin 2) (Mₙ model.dim)) :
    Matrix (Fin 2) (Fin 2) (Mₙ m) :=
  fun i j => (model.toMat.symm (K i j)).1

private noncomputable def matrixCornerTwoBlockToMat {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (K : Matrix (Fin 2) (Fin 2) (Mₙ m))
    (hK : ∀ i j, K i j ∈ matrixCornerSubmodule P) :
    Matrix (Fin 2) (Fin 2) (Mₙ model.dim) :=
  fun i j => model.toMat ⟨K i j, hK i j⟩

private theorem matrixCornerTwoBlockToMatSymm_star {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (K : Matrix (Fin 2) (Fin 2) (Mₙ model.dim)) :
    matrixCornerTwoBlockToMatSymm model (star K) =
      star (matrixCornerTwoBlockToMatSymm model K) := by
  ext i j a b
  simp [matrixCornerTwoBlockToMatSymm, MatrixCornerModel.toMat_symm_adjoint]

private theorem matrixCornerTwoBlockToMatSymm_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (K L : Matrix (Fin 2) (Fin 2) (Mₙ model.dim)) :
    matrixCornerTwoBlockToMatSymm model (K * L) =
      matrixCornerTwoBlockToMatSymm model K * matrixCornerTwoBlockToMatSymm model L := by
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    simp [matrixCornerTwoBlockToMatSymm, Matrix.mul_apply, Fin.sum_univ_two,
      MatrixCornerModel.toMat_symm_mul]

private theorem matrixPosSemidef_eq_conjTranspose_mul_self_local {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    ∃ Y : Matrix ι ι ℂ, C = Matrix.conjTranspose Y * Y :=
  matrixPosSemidef_eq_conjTranspose_mul_self hC

private theorem matrix_trace_mul_nonneg_of_posSemidef_local {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self_local hB
  rw [hY]
  have htrace :
      Matrix.trace (A * (Matrix.conjTranspose Y * Y)) =
        Matrix.trace (Y * A * Matrix.conjTranspose Y) := by
    calc
      Matrix.trace (A * (Matrix.conjTranspose Y * Y)) =
          Matrix.trace ((A * Matrix.conjTranspose Y) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Matrix.conjTranspose Y)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Matrix.conjTranspose Y) := by
        simp [Matrix.mul_assoc]
  rw [htrace]
  exact (hA.mul_mul_conjTranspose_same Y).trace_nonneg

private theorem trace_rankOne_mul_eq_dot_local {ι : Type*} [Fintype ι]
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
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem matrixCornerTwoBlockToMatSymm_posSemidef {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {K : Matrix (Fin 2) (Fin 2) (Mₙ model.dim)}
    (hK : BlockMatrixPosSemidef K) :
    BlockMatrixPosSemidef (matrixCornerTwoBlockToMatSymm model K) := by
  classical
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self_local hK
  let L : Matrix (Fin 2) (Fin 2) (Mₙ model.dim) :=
    twoBlockMatrixUnflattenLocal Y
  have hLY : twoBlockMatrixFlatten (star L * L) = Matrix.conjTranspose Y * Y := by
    simp [L, twoBlockMatrixFlatten_mul, twoBlockMatrixFlatten_star,
      twoBlockMatrixFlatten_unflattenLocal]
  have hK_eq : K = star L * L := by
    have hflat : twoBlockMatrixFlatten K = twoBlockMatrixFlatten (star L * L) :=
      hY.trans hLY.symm
    have h := congrArg twoBlockMatrixUnflattenLocal hflat
    simpa [twoBlockMatrixUnflattenLocal_flatten] using h
  rw [hK_eq, matrixCornerTwoBlockToMatSymm_mul, matrixCornerTwoBlockToMatSymm_star]
  change (twoBlockMatrixFlatten (star (matrixCornerTwoBlockToMatSymm model L) *
    matrixCornerTwoBlockToMatSymm model L)).PosSemidef
  rw [twoBlockMatrixFlatten_mul, twoBlockMatrixFlatten_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

private theorem trace_twoBlockMatrixFlatten_mul_local {n : ℕ}
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
  have htrace_fromBlocks : ∀ (A B C D : Mₙ n),
      Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
    intro A B C D
    simp [Matrix.trace, Matrix.fromBlocks]
  rw [htrace_fromBlocks]
  simp [Matrix.trace_add]

private theorem block_entry_star_eq_of_flatten_isHermitian {n : ℕ}
    {M : Matrix (Fin 2) (Fin 2) (Mₙ n)}
    (hM : (twoBlockMatrixFlatten M).IsHermitian) (i j : Fin 2) :
    star (M j i) = M i j := by
  ext a b
  fin_cases i <;> fin_cases j
  · simpa [twoBlockMatrixFlatten, Matrix.star_eq_conjTranspose] using
      hM.apply (Sum.inl a) (Sum.inl b)
  · simpa [twoBlockMatrixFlatten, Matrix.star_eq_conjTranspose] using
      hM.apply (Sum.inl a) (Sum.inr b)
  · simpa [twoBlockMatrixFlatten, Matrix.star_eq_conjTranspose] using
      hM.apply (Sum.inr a) (Sum.inl b)
  · simpa [twoBlockMatrixFlatten, Matrix.star_eq_conjTranspose] using
      hM.apply (Sum.inr a) (Sum.inr b)

private theorem trace_corner_pair {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {Aij Aji : Mₙ model.dim} {Bji : Mₙ m}
    (hA : star Aji = Aij)
    (hB : Bji ∈ matrixCornerSubmodule P) :
    Matrix.trace ((model.toMat.symm Aij).1 * Bji) =
      Matrix.trace (Aij * model.toMat ⟨Bji, hB⟩) := by
  let X : matrixCornerSubmodule P := model.toMat.symm Aji
  let Y : matrixCornerSubmodule P := ⟨Bji, hB⟩
  have hsymm : (model.toMat.symm Aij).1 = star X.1 := by
    calc
      (model.toMat.symm Aij).1 = (model.toMat.symm (star Aji)).1 := by rw [← hA]
      _ = star X.1 := by simp [X, MatrixCornerModel.toMat_symm_adjoint]
  have hpres := model.preservesTraceMul X Y
  calc
    Matrix.trace ((model.toMat.symm Aij).1 * Bji)
        = Matrix.trace (star X.1 * Y.1) := by simp [hsymm, Y]
    _ = Matrix.trace (star (model.toMat X) * model.toMat Y) := hpres.symm
    _ = Matrix.trace (Aij * model.toMat ⟨Bji, hB⟩) := by
      simp [X, Y, hA]

private theorem trace_twoBlockToMatSymm_mul_twoBlockToMat {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (A : Matrix (Fin 2) (Fin 2) (Mₙ model.dim))
    (B : Matrix (Fin 2) (Fin 2) (Mₙ m))
    (hA : (twoBlockMatrixFlatten A).IsHermitian)
    (hB : ∀ i j, B i j ∈ matrixCornerSubmodule P) :
    Matrix.trace (twoBlockMatrixFlatten (matrixCornerTwoBlockToMatSymm model A) *
        twoBlockMatrixFlatten B) =
      Matrix.trace (twoBlockMatrixFlatten A *
        twoBlockMatrixFlatten (matrixCornerTwoBlockToMat model B hB)) := by
  rw [trace_twoBlockMatrixFlatten_mul_local]
  rw [trace_twoBlockMatrixFlatten_mul_local]
  have h00 := trace_corner_pair model
    (block_entry_star_eq_of_flatten_isHermitian hA 0 0) (hB 0 0)
  have h01 := trace_corner_pair model
    (block_entry_star_eq_of_flatten_isHermitian hA 0 1) (hB 1 0)
  have h10 := trace_corner_pair model
    (block_entry_star_eq_of_flatten_isHermitian hA 1 0) (hB 0 1)
  have h11 := trace_corner_pair model
    (block_entry_star_eq_of_flatten_isHermitian hA 1 1) (hB 1 1)
  simpa [matrixCornerTwoBlockToMatSymm, matrixCornerTwoBlockToMat] using
    (by rw [h00, h01, h10, h11])

private theorem matrixCornerTwoBlockToMat_isHermitian {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    (B : Matrix (Fin 2) (Fin 2) (Mₙ m))
    (hBcorner : ∀ i j, B i j ∈ matrixCornerSubmodule P)
    (hBherm : (twoBlockMatrixFlatten B).IsHermitian) :
    (twoBlockMatrixFlatten (matrixCornerTwoBlockToMat model B hBcorner)).IsHermitian := by
  refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
  · simpa [Matrix.star_eq_conjTranspose] using
      MatrixCornerModel.toMat_star_of_eq model (hBcorner 0 0) (hBcorner 0 0)
        (block_entry_star_eq_of_flatten_isHermitian hBherm 0 0)
  · simpa [Matrix.star_eq_conjTranspose] using
      MatrixCornerModel.toMat_star_of_eq model (hBcorner 0 1) (hBcorner 1 0)
        (block_entry_star_eq_of_flatten_isHermitian hBherm 1 0)
  · simpa [Matrix.star_eq_conjTranspose] using
      MatrixCornerModel.toMat_star_of_eq model (hBcorner 1 1) (hBcorner 1 1)
        (block_entry_star_eq_of_flatten_isHermitian hBherm 1 1)

private theorem matrixCornerTwoBlockToMat_posSemidef_of_posSemidef {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P)
    {B : Matrix (Fin 2) (Fin 2) (Mₙ m)}
    (hBcorner : ∀ i j, B i j ∈ matrixCornerSubmodule P)
    (hB : BlockMatrixPosSemidef B) :
    BlockMatrixPosSemidef (matrixCornerTwoBlockToMat model B hBcorner) := by
  classical
  let R : Matrix (Fin 2) (Fin 2) (Mₙ model.dim) :=
    matrixCornerTwoBlockToMat model B hBcorner
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [R] using matrixCornerTwoBlockToMat_isHermitian model B hBcorner hB.1
  · intro v
    let O : Matrix (Fin model.dim ⊕ Fin model.dim) (Fin model.dim ⊕ Fin model.dim) ℂ :=
      twoBlockMatrixFlatten R
    let rank : Matrix (Fin model.dim ⊕ Fin model.dim) (Fin model.dim ⊕ Fin model.dim) ℂ :=
      Matrix.vecMulVec v (star v)
    let A : Matrix (Fin 2) (Fin 2) (Mₙ model.dim) :=
      twoBlockMatrixUnflattenLocal rank
    have hApos : BlockMatrixPosSemidef A := by
      simpa [BlockMatrixPosSemidef, A, rank, twoBlockMatrixFlatten_unflattenLocal] using
        (Matrix.posSemidef_vecMulVec_self_star (R := ℂ) v)
    have hSpos : BlockMatrixPosSemidef (matrixCornerTwoBlockToMatSymm model A) :=
      matrixCornerTwoBlockToMatSymm_posSemidef model hApos
    have hprod :
        0 ≤ Matrix.trace (twoBlockMatrixFlatten (matrixCornerTwoBlockToMatSymm model A) *
          twoBlockMatrixFlatten B) :=
      matrix_trace_mul_nonneg_of_posSemidef_local hSpos hB
    have htrace := trace_twoBlockToMatSymm_mul_twoBlockToMat model A B hApos.1 hBcorner
    have hrank : Matrix.trace (rank * O) = dotProduct (star v) (O.mulVec v) := by
      simpa [O, rank] using trace_rankOne_mul_eq_dot_local v O
    rw [← hrank]
    have hright : Matrix.trace (rank * O) =
        Matrix.trace (twoBlockMatrixFlatten (matrixCornerTwoBlockToMatSymm model A) *
          twoBlockMatrixFlatten B) := by
      calc
        Matrix.trace (rank * O) =
            Matrix.trace (twoBlockMatrixFlatten A *
              twoBlockMatrixFlatten (matrixCornerTwoBlockToMat model B hBcorner)) := by
          simp [A, rank, O, R, twoBlockMatrixFlatten_unflattenLocal]
        _ = Matrix.trace (twoBlockMatrixFlatten (matrixCornerTwoBlockToMatSymm model A) *
              twoBlockMatrixFlatten B) := htrace.symm
    rw [hright]
    exact hprod

/-! ### Output-Support Two-Positivity for C3 -/
/-- Two-positivity survives the canonical output-support reduction. -/
theorem outputSupportReducedMap_twoPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTwo : IsTwoPositiveMap Φ) :
    IsTwoPositiveMap (outputSupportReducedMap Φ hPos) := by
  intro M hM
  let B : Matrix (Fin 2) (Fin 2) (Mₙ m) := M.map Φ
  let model := outputSupportMatrixCornerModel Φ
  have hBcorner : ∀ i j, B i j ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
    intro i j
    simpa [B] using phi_image_mem_outputCorner Φ hPos (M i j)
  have hBpos : BlockMatrixPosSemidef B := hTwo M hM
  have hred :
      BlockMatrixPosSemidef (matrixCornerTwoBlockToMat model B hBcorner) :=
    matrixCornerTwoBlockToMat_posSemidef_of_posSemidef model hBcorner hBpos
  simpa [B, model, matrixCornerTwoBlockToMat, outputSupportReducedMap] using hred

/-- Short API synonym: the canonical reduced Hilbert--Schmidt map is two-positive. -/
theorem outputSupportReducedHSMap_twoPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTwo : IsTwoPositiveMap Φ) :
    IsTwoPositiveMap (outputSupportReducedHSMap Φ hPos) := by
  simpa [outputSupportReducedHSMap] using
    outputSupportReducedMap_twoPositive Φ hPos hTwo

/-! ### Carlen Adjoint-Support G Surface -/
/-- Carlen's adjoint support projection, i.e. the support of `hsAdjoint Φ 1`. -/
noncomputable def carlenAdjointSupportProj {n m : ℕ} (Φ : HSMap n m) : Mₙ n :=
  outputSupportProj (hsAdjoint Φ)

/-- Matrix model for the support corner cut out by `hsAdjoint Φ 1`. -/
noncomputable def carlenAdjointSupportMatrixCornerModel {n m : ℕ} (Φ : HSMap n m) :
    MatrixCornerModel (carlenAdjointSupportProj Φ) :=
  outputSupportMatrixCornerModel (hsAdjoint Φ)

/-- Raw Carlen support-corner `G_f`, acting on the actual support corner of
`hsAdjoint Φ 1`. -/
noncomputable def carlenSupportGOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X Y : Mₙ m) :
    matrixCornerSubmodule (carlenAdjointSupportProj Φ) →L[ℂ]
      matrixCornerSubmodule (carlenAdjointSupportProj Φ) :=
  (carlenAdjointSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap.comp
    ((gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
      (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y)).comp
      (carlenAdjointSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Raw Carlen support-corner inverse `G_f`, acting on the actual support corner of
`hsAdjoint Φ 1`. -/
noncomputable def carlenSupportGOperatorInv {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X Y : Mₙ m) :
    matrixCornerSubmodule (carlenAdjointSupportProj Φ) →L[ℂ]
      matrixCornerSubmodule (carlenAdjointSupportProj Φ) :=
  (carlenAdjointSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap.comp
    ((gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
      (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y)).comp
      (carlenAdjointSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinate form of the raw support-corner `G_f`. -/
noncomputable def carlenSupportGOperatorModelConj {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X Y : Mₙ m) :
    HSOp (carlenAdjointSupportMatrixCornerModel Φ).dim :=
  (carlenAdjointSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((carlenSupportGOperator f Φ hAdjPos X Y).comp
      (carlenAdjointSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap)

/-- Coordinate form of the raw support-corner inverse `G_f`. -/
noncomputable def carlenSupportGOperatorInvModelConj {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X Y : Mₙ m) :
    HSOp (carlenAdjointSupportMatrixCornerModel Φ).dim :=
  (carlenAdjointSupportMatrixCornerModel Φ).toMat.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((carlenSupportGOperatorInv f Φ hAdjPos X Y).comp
      (carlenAdjointSupportMatrixCornerModel Φ).toMat.symm.toContinuousLinearMap)

/-- Transporting the raw support-corner `G_f` to coordinates gives the reduced-map `G_f`. -/
theorem carlenSupportGOperator_conj_eq_reducedMap_gOperator {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X Y : Mₙ m) :
    carlenSupportGOperatorModelConj f Φ hAdjPos X Y =
      gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
        (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) := by
  ext Z i j
  dsimp [carlenSupportGOperatorModelConj, carlenSupportGOperator]
  change ((carlenAdjointSupportMatrixCornerModel Φ).toMat
      ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm
        ((gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y))
          ((carlenAdjointSupportMatrixCornerModel Φ).toMat
            ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm Z))))) i j =
    ((gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
      (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y)) Z) i j
  simp

/-- Transporting the raw support-corner inverse `G_f` to coordinates gives the reduced-map
inverse `G_f`. -/
theorem carlenSupportGOperatorInv_conj_eq_reducedMap_gOperatorInv {n m : ℕ}
    (f : ℝ → ℝ) (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (X Y : Mₙ m) :
    carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y =
      gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
        (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) := by
  ext Z i j
  dsimp [carlenSupportGOperatorInvModelConj, carlenSupportGOperatorInv]
  change ((carlenAdjointSupportMatrixCornerModel Φ).toMat
      ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm
        ((gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y))
          ((carlenAdjointSupportMatrixCornerModel Φ).toMat
            ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm Z))))) i j =
    ((gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
      (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y)) Z) i j
  simp

/-! ### Common Adjoint Support and Reduced Input Map -/
/-- The adjoint image lies in the support corner of `hsAdjoint Φ 1`. -/
theorem hsAdjoint_image_mem_adjointSupportCorner {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X : Mₙ m) :
    hsAdjoint Φ X ∈ matrixCornerSubmodule (carlenAdjointSupportProj Φ) := by
  simpa [carlenAdjointSupportProj] using
    phi_image_mem_outputCorner (hsAdjoint Φ) hAdjPos X

/-- Positive-definite ambient inputs have adjoint images with the common Carlen adjoint
support projection. -/
theorem hsAdjoint_image_supportProj_eq_adjointSupportProj {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) {X : Mₙ m} (hX : MatrixPosDef X) :
    matrixSupportProj (hsAdjoint Φ X) = carlenAdjointSupportProj Φ := by
  simpa [carlenAdjointSupportProj] using
    phi_image_supportProj_eq_outputSupportProj_of_matrixPosDef
      (hsAdjoint Φ) hAdjPos hX

/-- The Carlen adjoint image of a positive-definite input is positive semidefinite. -/
theorem hsAdjoint_image_nonneg_of_matrixPosDef {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) {X : Mₙ m} (hX : MatrixPosDef X) :
    0 ≤ hsAdjoint Φ X := by
  exact hAdjPos ((Matrix.nonneg_iff_posSemidef).2 (matrixPosDef_posDef hX).posSemidef)

/-- Two positive-definite ambient inputs have a common adjoint support projection. -/
theorem hsAdjoint_images_common_supportProj {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) {X Y : Mₙ m}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    matrixSupportProj (hsAdjoint Φ X) = carlenAdjointSupportProj Φ ∧
      matrixSupportProj (hsAdjoint Φ Y) = carlenAdjointSupportProj Φ ∧
      matrixSupportProj (hsAdjoint Φ X) = matrixSupportProj (hsAdjoint Φ Y) := by
  have hXeq := hsAdjoint_image_supportProj_eq_adjointSupportProj Φ hAdjPos hX
  have hYeq := hsAdjoint_image_supportProj_eq_adjointSupportProj Φ hAdjPos hY
  exact ⟨hXeq, hYeq, hXeq.trans hYeq.symm⟩

/-- Unital two-positive maps supply the positive adjoint hypothesis needed for the Carlen
common-support statement. -/
theorem hsAdjoint_images_common_supportProj_of_unitalTwoPositive {n m : ℕ} (Φ : HSMap n m)
    (hΦ : IsUnitalTwoPositiveMap Φ) {X Y : Mₙ m}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    matrixSupportProj (hsAdjoint Φ X) = carlenAdjointSupportProj Φ ∧
      matrixSupportProj (hsAdjoint Φ Y) = carlenAdjointSupportProj Φ ∧
      matrixSupportProj (hsAdjoint Φ X) = matrixSupportProj (hsAdjoint Φ Y) :=
  hsAdjoint_images_common_supportProj Φ
    (isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ) hX hY

/-- The support-corner model sends adjoint images of positive-definite matrices to
positive-definite matrices. -/
theorem hsAdjoint_image_posDef_on_adjointSupport {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) {X : Mₙ m} (hX : MatrixPosDef X) :
    MatrixPosDef
      (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X) := by
  have hredPos :
      IsPositiveMap (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos) := by
    simpa [outputSupportReducedHSMap] using
      outputSupportReducedMap_isPositiveMap (hsAdjoint Φ) hAdjPos
  have hredOne :
      MatrixPosDef (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos (1 : Mₙ m)) := by
    simpa [outputSupportReducedHSMap] using
      outputSupportReducedMap_one_posDef (hsAdjoint Φ) hAdjPos
  exact isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
    (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos) hredPos hredOne hX

/-- The input-support reduced Carlen map: restrict the codomain of `hsAdjoint Φ`
to its output support, then take the Hilbert--Schmidt adjoint. -/
noncomputable def carlenInputSupportReducedMap {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) :
    HSMap (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim m :=
  hsAdjoint (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos)

/-- The Hilbert--Schmidt adjoint of the reduced Carlen map is the reduced adjoint image map. -/
theorem carlenInputSupportReducedMap_hsAdjoint_apply {n m : ℕ} (Φ : HSMap n m)
    (hAdjPos : IsPositiveMap (hsAdjoint Φ)) (X : Mₙ m) :
    hsAdjoint (carlenInputSupportReducedMap Φ hAdjPos) X =
      outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X := by
  simp [carlenInputSupportReducedMap, hsAdjoint_hsAdjoint]

/-- The input-support reduced Carlen map is unital when the original map is unital. -/
theorem carlenInputSupportReducedMap_unital {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsUnitalTwoPositiveMap Φ) :
    IsUnitalMap
      (carlenInputSupportReducedMap Φ
        (isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ)) := by
  let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
  have hAdjTrace : _root_.HiaiPetz.TracePreserving (hsAdjoint Φ) :=
    hsAdjoint_tracePreserving_of_isUnitalMap hΦ.1
  have hTraceReduced :
      _root_.HiaiPetz.TracePreserving (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos) := by
    simpa [outputSupportReducedHSMap] using
      outputSupportReducedMap_tracePreserving (hsAdjoint Φ) hAdjPos hAdjTrace
  simpa [carlenInputSupportReducedMap, hAdjPos] using
    isUnitalMap_hsAdjoint_of_tracePreserving hTraceReduced

/-- The input-support reduced Carlen map is two-positive when the original map is unital
two-positive. -/
theorem carlenInputSupportReducedMap_twoPositive {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsUnitalTwoPositiveMap Φ) :
    IsTwoPositiveMap
      (carlenInputSupportReducedMap Φ
        (isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ)) := by
  let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
  have hAdjTwo : IsTwoPositiveMap (hsAdjoint Φ) :=
    isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap hΦ.2
  have hRedTwo :
      IsTwoPositiveMap (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos) :=
    outputSupportReducedHSMap_twoPositive (hsAdjoint Φ) hAdjPos hAdjTwo
  simpa [carlenInputSupportReducedMap, outputSupportReducedHSMap, hAdjPos] using
    isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap hRedTwo

/-- Bundled C3 readiness: the input-support reduced Carlen map is unital two-positive. -/
theorem carlenInputSupportReducedMap_unitalTwoPositive {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsUnitalTwoPositiveMap Φ) :
    IsUnitalTwoPositiveMap
      (carlenInputSupportReducedMap Φ
        (isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ)) :=
  ⟨carlenInputSupportReducedMap_unital hΦ, carlenInputSupportReducedMap_twoPositive hΦ⟩

/-- Positive-definite ambient inputs become positive-definite adjoint inputs for the
input-support reduced Carlen map. -/
theorem carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    {X : Mₙ m} (hX : MatrixPosDef X) :
    MatrixPosDef (hsAdjoint (carlenInputSupportReducedMap Φ hAdjPos) X) := by
  simpa [carlenInputSupportReducedMap_hsAdjoint_apply Φ hAdjPos X] using
    hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hX

end

end Quantum.TraceInequality.Loewner.HiaiPetz
