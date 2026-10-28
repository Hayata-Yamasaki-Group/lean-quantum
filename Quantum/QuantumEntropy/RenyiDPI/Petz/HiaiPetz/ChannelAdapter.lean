/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Equivalence
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.YoungInequality
import Quantum.TraceInequality.HiaiPetz.Interface
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.BlockPositivity
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# CPTP channels as Hilbert--Schmidt matrix maps

This module transports a finite-dimensional CPTP channel to the concrete
Hilbert--Schmidt matrix model used by the Hiai--Petz ProofNet interface.  The
coordinates are fixed throughout to `stdOrthonormalBasis`.

The two-positivity proof includes the order bridge between positive
`CStarMatrix` block matrices of operators and the positive-semidefinite
flattened `2 × 2` block matrices used by `IsTwoPositiveMap`.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy
open Quantum.TraceInequality.Loewner.HiaiPetz
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Frobenius

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

universe u v

variable {ℋ : Type u} {𝒦 : Type v} [Qudit ℋ] [Qudit 𝒦]

/-! ## The standard-coordinate adapter -/

/-- A CPTP channel in the standard orthonormal Hilbert--Schmidt coordinates. -/
noncomputable def hsMapOfCPTP (E : CPTP ℋ 𝒦) :
    _root_.HiaiPetz.HSMap (Module.finrank ℂ ℋ) (Module.finrank ℂ 𝒦) :=
  ({ toFun := fun A =>
       LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ 𝒦)
         (E.toFun
           ((LinearMap.toMatrixOrthonormal
             (stdOrthonormalBasis ℂ ℋ)).symm A))
     map_add' := by
       intro A B
       simp
     map_smul' := by
       intro z A
       simp } :
      Mₙ (Module.finrank ℂ ℋ) →ₗ[ℂ] Mₙ (Module.finrank ℂ
        𝒦)).toContinuousLinearMap

/-- Pointwise form of `hsMapOfCPTP`. -/
@[simp]
theorem hsMapOfCPTP_apply (E : CPTP ℋ 𝒦)
    (A : Mₙ (Module.finrank ℂ ℋ)) :
    hsMapOfCPTP E A =
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ 𝒦)
        (E.toFun
          ((LinearMap.toMatrixOrthonormal
            (stdOrthonormalBasis ℂ ℋ)).symm A)) :=
  rfl

/-- The standard-coordinate adapter commutes with the operator/matrix models. -/
@[simp]
theorem hsMapOfCPTP_toMatrixOrthonormal (E : CPTP ℋ 𝒦) (A : L ℋ) :
    LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ 𝒦) (E.toFun A) =
      hsMapOfCPTP E
        (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ) A) := by
  simp

/-- The matrix adapter of a CPTP channel is positive. -/
theorem hsMapOfCPTP_isPositiveMap (E : CPTP ℋ 𝒦) :
    _root_.HiaiPetz.IsPositiveMap (hsMapOfCPTP E) := by
  intro A hA
  let eℋ := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ)
  let e𝒦 := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ 𝒦)
  have hpre : 0 ≤ eℋ.symm A :=
    starAlgEquiv_nonneg eℋ.symm hA
  have himage : 0 ≤ E.toFun (eℋ.symm A) :=
    map_nonneg E.toCompletelyPositiveMap hpre
  change 0 ≤ e𝒦 (E.toFun (eℋ.symm A))
  exact starAlgEquiv_nonneg e𝒦 himage

/-- The matrix adapter of a CPTP channel preserves the matrix trace. -/
theorem hsMapOfCPTP_tracePreserving (E : CPTP ℋ 𝒦) :
    _root_.HiaiPetz.TracePreserving (hsMapOfCPTP E) := by
  intro A
  let eℋ := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ)
  let e𝒦 := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ 𝒦)
  let X : L ℋ := eℋ.symm A
  calc
    Matrix.trace (hsMapOfCPTP E A) = Tr (E.toFun X) := by
      rw [tr_eq_matrix_trace_orthonormal]
      rfl
    _ = Tr X := (E.trace_map X).symm
    _ = Matrix.trace A := by
      simp [X, eℋ]

/-! ## The `2 × 2` block-order bridge -/

/-- The product indexing used by `Matrix.comp` in the two-block sum order. -/
private noncomputable def finTwoProdEquivSum (n : ℕ) :
    Fin 2 × Fin n ≃ Fin n ⊕ Fin n :=
  (finTwoEquiv.prodCongr (Equiv.refl (Fin n))).trans
    (Equiv.boolProdEquivSum (Fin n))

/-- Flatten nested `2 × 2` matrices while preserving multiplication and star. -/
private noncomputable def compStarAlgEquiv (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (Mₙ n) ≃⋆ₐ[ℂ]
      Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    (Matrix.compAlgEquiv (Fin 2) (Fin n) ℂ ℂ) (by
      intro M
      rfl)

/-- Reindex the product coordinates as the left/right block sum. -/
private noncomputable def reindexStarAlgEquiv (n : ℕ) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    (Matrix.reindexAlgEquiv ℂ ℂ (finTwoProdEquivSum n)) (by
      intro M
      rfl)

/-- The star-algebra equivalence underlying `twoBlockMatrixFlatten`. -/
private noncomputable def blockFlattenStarAlgEquiv (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (Mₙ n) ≃⋆ₐ[ℂ]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (compStarAlgEquiv n).trans (reindexStarAlgEquiv n)

@[simp]
private theorem blockFlattenStarAlgEquiv_apply (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    blockFlattenStarAlgEquiv n M = twoBlockMatrixFlatten M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockFlattenStarAlgEquiv, reindexStarAlgEquiv,
      compStarAlgEquiv, finTwoProdEquivSum, twoBlockMatrixFlatten,
      Matrix.reindex_apply, finTwoEquiv]

/-- Apply an orthonormal-basis matrix model to every outer block. -/
private noncomputable def outerBasisStarAlgEquiv
    {n : ℕ} {H : Type*} [Qudit H]
    (b : OrthonormalBasis (Fin n) ℂ H) :
    CStarMatrix (Fin 2) (Fin 2) (L H) ≃⋆ₐ[ℂ]
      Matrix (Fin 2) (Fin 2) (Mₙ n) :=
  (CStarMatrix.ofMatrixStarAlgEquiv (A := L H) (n := Fin 2)).symm.trans
    (StarAlgEquiv.ofAlgEquiv
      (LinearMap.toMatrixOrthonormal b).toAlgEquiv.mapMatrix (by
        intro M
        ext i j k l
        simpa using congrArg (fun X : Mₙ n => X k l)
          (map_star (LinearMap.toMatrixOrthonormal b) (M j i))))

/-- The complete basis-and-block star-algebra equivalence. -/
private noncomputable def blockOrderStarAlgEquiv
    {n : ℕ} {H : Type*} [Qudit H]
    (b : OrthonormalBasis (Fin n) ℂ H) :
    CStarMatrix (Fin 2) (Fin 2) (L H) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  ((outerBasisStarAlgEquiv b).trans (blockFlattenStarAlgEquiv n)).trans
    (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin n ⊕ Fin n))

private noncomputable def cstarBlockOfMatrix
    {n : ℕ} {H : Type*} [Qudit H]
    (b : OrthonormalBasis (Fin n) ℂ H)
    (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    CStarMatrix (Fin 2) (Fin 2) (L H) :=
  CStarMatrix.ofMatrix
    (M.map (LinearMap.toMatrixOrthonormal b).symm)

@[simp]
private theorem blockOrderStarAlgEquiv_cstarBlockOfMatrix
    {n : ℕ} {H : Type*} [Qudit H]
    (b : OrthonormalBasis (Fin n) ℂ H)
    (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    blockOrderStarAlgEquiv b (cstarBlockOfMatrix b M) =
      CStarMatrix.ofMatrix (twoBlockMatrixFlatten M) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    change (LinearMap.toMatrixOrthonormal b)
      ((LinearMap.toMatrixOrthonormal b).symm (M _ _)) i j =
        M _ _ i j <;>
    simp [finTwoProdEquivSum, finTwoEquiv]

private lemma scalarCStarMatrix_nonneg_of_posSemidef
    {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    0 ≤ (CStarMatrix.ofMatrix M : CStarMatrix ι ι ℂ) := by
  classical
  exact (starAlgEquiv_nonneg_iff
    (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := ι))).2 hM.nonneg

private lemma scalarCStarMatrix_posSemidef_of_nonneg
    {ι : Type*} [Fintype ι]
    {M : CStarMatrix ι ι ℂ} (hM : 0 ≤ M) :
    (CStarMatrix.ofMatrix.symm M).PosSemidef := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  exact starAlgEquiv_nonneg
    (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := ι)).symm hM

/--
The explicit basis transport between `CStarMatrix` block positivity and the
flattened block order used by `BlockMatrixPosSemidef`.
-/
theorem blockMatrixPosSemidef_iff_cstarMatrix_nonneg_toMatrixOrthonormal
    {n : ℕ} {H : Type*} [Qudit H]
    (b : OrthonormalBasis (Fin n) ℂ H)
    (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    BlockMatrixPosSemidef M ↔
      0 ≤ (CStarMatrix.ofMatrix
        (M.map (LinearMap.toMatrixOrthonormal b).symm) :
          CStarMatrix (Fin 2) (Fin 2) (L H)) := by
  let e := blockOrderStarAlgEquiv b
  have he : e (cstarBlockOfMatrix b M) =
      CStarMatrix.ofMatrix (twoBlockMatrixFlatten M) :=
    blockOrderStarAlgEquiv_cstarBlockOfMatrix b M
  constructor
  · intro hM
    have hout : 0 ≤ e (cstarBlockOfMatrix b M) := by
      rw [he]
      exact scalarCStarMatrix_nonneg_of_posSemidef hM
    exact (starAlgEquiv_nonneg_iff e).1 hout
  · intro hM
    have hM' : 0 ≤ cstarBlockOfMatrix b M := hM
    have hout : 0 ≤ e (cstarBlockOfMatrix b M) :=
      starAlgEquiv_nonneg e hM'
    rw [he] at hout
    simpa using scalarCStarMatrix_posSemidef_of_nonneg hout

/-! ## Complete positivity and Schwarz -/

/-- Complete positivity of a CPTP channel gives two-positivity of its adapter. -/
theorem hsMapOfCPTP_isTwoPositiveMap (E : CPTP ℋ 𝒦) :
    IsTwoPositiveMap (hsMapOfCPTP E) := by
  intro M hM
  let bℋ := stdOrthonormalBasis ℂ ℋ
  let b𝒦 := stdOrthonormalBasis ℂ 𝒦
  let N := cstarBlockOfMatrix bℋ M
  have hN : 0 ≤ N :=
    (blockMatrixPosSemidef_iff_cstarMatrix_nonneg_toMatrixOrthonormal
      bℋ M).1 hM
  have hcp : IsCompletelyPositive E.toCompletelyPositiveMap.toLinearMap :=
    ⟨E.toCompletelyPositiveMap, rfl⟩
  have hEN : 0 ≤ N.map E.toCompletelyPositiveMap :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg
      E.toCompletelyPositiveMap.toLinearMap).1 hcp 2 N hN
  have hblocks :
      cstarBlockOfMatrix b𝒦 (M.map (hsMapOfCPTP E)) =
        N.map E.toCompletelyPositiveMap := by
    ext i j
    simp [N, cstarBlockOfMatrix, bℋ, b𝒦]
    rfl
  apply (blockMatrixPosSemidef_iff_cstarMatrix_nonneg_toMatrixOrthonormal
    b𝒦 (M.map (hsMapOfCPTP E))).2
  change 0 ≤ cstarBlockOfMatrix b𝒦 (M.map (hsMapOfCPTP E))
  rw [hblocks]
  exact hEN

/--
The adjoint of the CPTP adapter satisfies Schwarz.  The proof follows the
fixed path: adjoint two-positivity, adjoint unitality, then Kadison--Choi.
-/
theorem hsMapOfCPTP_hsAdjointSchwarz (E : CPTP ℋ 𝒦) :
    _root_.HiaiPetz.HSAdjointSchwarz (hsMapOfCPTP E) := by
  have htwo : IsTwoPositiveMap (hsMapOfCPTP E) :=
    hsMapOfCPTP_isTwoPositiveMap E
  have hadjTwo : IsTwoPositiveMap (hsAdjoint (hsMapOfCPTP E)) :=
    isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap htwo
  have hadjUnital : IsUnitalMap (hsAdjoint (hsMapOfCPTP E)) :=
    isUnitalMap_hsAdjoint_of_tracePreserving
      (hsMapOfCPTP_tracePreserving E)
  intro X
  have hschwarz :=
    kadisonChoi_schwarz_of_isUnitalTwoPositiveMap
      (⟨hadjUnital, hadjTwo⟩ :
        IsUnitalTwoPositiveMap (hsAdjoint (hsMapOfCPTP E))) X
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef]
  simpa [Matrix.star_eq_conjTranspose] using hschwarz

/-! ## Strict positivity bridges -/

/--
Membership in `pdSetLM` is exactly positive definiteness of the standard
orthonormal-basis matrix.
-/
theorem pdSetLM_iff_toMatrixOrthonormal_posDef (A : L ℋ) :
    A ∈ pdSetLM (ℋ := ℋ) ↔
      Matrix.PosDef
        (LinearMap.toMatrixOrthonormal
          (stdOrthonormalBasis ℂ ℋ) A) := by
  let e := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ)
  rw [pdSetLM_strictPositivity_certificate]
  rw [← Matrix.isStrictlyPositive_iff_posDef]
  rw [IsStrictlyPositive.iff_of_unital, IsStrictlyPositive.iff_of_unital]
  exact and_congr
    (starAlgEquiv_nonneg_iff e).symm
    (isUnit_map_iff e A).symm

/-- Every positive-semidefinite matrix is bounded above by its trace times one. -/
private theorem posSemidef_le_trace_smul_one
    {n : ℕ} {A : Mₙ n} (hA : A.PosSemidef) :
    A ≤ A.trace.re • (1 : Mₙ n) := by
  classical
  by_cases hn : Nonempty (Fin n)
  · letI := hn
    let β : ℝ := A.trace.re
    have hβge : ∀ i : Fin n, hA.1.eigenvalues i ≤ β := by
      intro i
      have hi : hA.1.eigenvalues i ≤
          ∑ j : Fin n, hA.1.eigenvalues j := by
        simpa using Finset.single_le_sum
          (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
      simpa [β, hA.1.trace_eq_sum_eigenvalues] using hi
    have hdiag :
        (Matrix.diagonal
          (fun i => Complex.ofReal (β - hA.1.eigenvalues i)) :
            Mₙ n).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (hβge i)
    have hone :
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
            (β • (1 : Mₙ n)) =
          β • (1 : Mₙ n) := by
      calc
        Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
            (β • (1 : Mₙ n)) =
            β • (Unitary.conjStarAlgAut ℂ (Mₙ n)
              hA.1.eigenvectorUnitary (1 : Mₙ n)) := by
                let ψ := (Unitary.conjStarAlgAut ℂ (Mₙ n)
                  hA.1.eigenvectorUnitary).toAlgEquiv
                let φ := ψ.toLinearEquiv.toLinearMap
                exact φ.map_smul_of_tower β (1 : Mₙ n)
        _ = β • (1 : Mₙ n) := by simp
    rw [← sub_nonneg]
    refine (Matrix.nonneg_iff_posSemidef).2 ?_
    have hstep :
        β • (1 : Mₙ n) - A =
          Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
            (β • (1 : Mₙ n) -
              Matrix.diagonal
                (Complex.ofReal ∘ hA.1.eigenvalues)) := by
      calc
        β • (1 : Mₙ n) - A =
            β • (1 : Mₙ n) -
              Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
                (Matrix.diagonal
                  (Complex.ofReal ∘ hA.1.eigenvalues)) := by
                    exact congrArg
                      (fun M : Mₙ n => β • (1 : Mₙ n) - M)
                      hA.1.spectral_theorem
        _ = Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
              (β • (1 : Mₙ n)) -
            Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
              (Matrix.diagonal
                (Complex.ofReal ∘ hA.1.eigenvalues)) := by
                  rw [hone]
        _ = _ := by rw [← map_sub]
    rw [hstep]
    refine (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe
        (U := hA.1.eigenvectorUnitary))).2 ?_
    convert hdiag using 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    exact le_of_eq (Subsingleton.elim _ _)

/--
If a positive map sends one positive-definite input to a positive-definite
output, then its image of the identity is positive definite.
-/
theorem posMap_one_posDef_of_posDef_image
    {n m : ℕ} (Φ : _root_.HiaiPetz.HSMap n m)
    (hPos : _root_.HiaiPetz.IsPositiveMap Φ)
    {A : Mₙ n} (hA : Matrix.PosDef A)
    (hΦA : Matrix.PosDef (Φ A)) :
    Matrix.PosDef (Φ (1 : Mₙ n)) := by
  let β : ℝ := A.trace.re
  have hAupper : A ≤ β • (1 : Mₙ n) := by
    simpa [β] using
      posSemidef_le_trace_smul_one hA.posSemidef
  have hmapDiff : 0 ≤ Φ (β • (1 : Mₙ n) - A) :=
    hPos (sub_nonneg.mpr hAupper)
  have hupper : Φ A ≤ (β : ℂ) • Φ (1 : Mₙ n) := by
    rw [Φ.map_sub, Φ.map_smul_of_tower] at hmapDiff
    simpa [sub_nonneg] using hmapDiff
  have hΦ1nonneg : 0 ≤ Φ (1 : Mₙ n) := hPos zero_le_one
  have hΦ1psd : (Φ (1 : Mₙ n)).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef).1 hΦ1nonneg
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hΦ1psd.isHermitian ?_
  intro x hx
  have hdiffNonneg :
      0 ≤ (β : ℂ) • Φ (1 : Mₙ n) - Φ A :=
    sub_nonneg.mpr hupper
  have hdiffPsd :
      ((β : ℂ) • Φ (1 : Mₙ n) - Φ A).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef).1 hdiffNonneg
  have hrest :
      0 ≤ Complex.re
        (dotProduct (star x)
          (Matrix.mulVec
            ((β : ℂ) • Φ (1 : Mₙ n) - Φ A) x)) :=
    hdiffPsd.re_dotProduct_nonneg x
  have himage :
      0 < Complex.re
        (dotProduct (star x) (Matrix.mulVec (Φ A) x)) :=
    hΦA.re_dotProduct_pos hx
  have hscalar :
      Complex.re
        (dotProduct (star x)
          (Matrix.mulVec ((β : ℂ) • Φ (1 : Mₙ n)) x)) =
        β * Complex.re
          (dotProduct (star x)
            (Matrix.mulVec (Φ (1 : Mₙ n)) x)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp [smul_eq_mul]
  have hdecomp :
      dotProduct (star x)
          (Matrix.mulVec ((β : ℂ) • Φ (1 : Mₙ n)) x) =
        dotProduct (star x)
            (Matrix.mulVec
              ((β : ℂ) • Φ (1 : Mₙ n) - Φ A) x) +
          dotProduct (star x) (Matrix.mulVec (Φ A) x) := by
    calc
      dotProduct (star x)
          (Matrix.mulVec ((β : ℂ) • Φ (1 : Mₙ n)) x) =
          dotProduct (star x)
            (Matrix.mulVec
              (((β : ℂ) • Φ (1 : Mₙ n) - Φ A) + Φ A) x) := by
                congr 1
                simp
      _ = dotProduct (star x)
            (Matrix.mulVec
                ((β : ℂ) • Φ (1 : Mₙ n) - Φ A) x +
              Matrix.mulVec (Φ A) x) := by
                simpa using congrArg (dotProduct (star x))
                  (Matrix.add_mulVec
                    ((β : ℂ) • Φ (1 : Mₙ n) - Φ A) (Φ A) x)
      _ = _ := by simp [dotProduct_add]
  refine RCLike.pos_iff.mpr ⟨?_, ?_⟩
  · have hscaledPos :
        0 < Complex.re
          (dotProduct (star x)
            (Matrix.mulVec ((β : ℂ) • Φ (1 : Mₙ n)) x)) := by
      rw [hdecomp]
      exact add_pos_of_nonneg_of_pos hrest himage
    rw [hscalar] at hscaledPos
    have hβnonneg : 0 ≤ β := by
      exact (RCLike.nonneg_iff.mp hA.posSemidef.trace_nonneg).1
    by_contra hq
    have hqnonpos :
        Complex.re
          (dotProduct (star x)
            (Matrix.mulVec (Φ (1 : Mₙ n)) x)) ≤ 0 :=
      le_of_not_gt hq
    exact (not_lt_of_ge
      (mul_nonpos_of_nonneg_of_nonpos hβnonneg hqnonpos)) hscaledPos
  · simpa using
      hΦ1psd.isHermitian.im_star_dotProduct_mulVec_self x

end

end UmegakiDPI
