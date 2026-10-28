/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.AH1
import Quantum.TraceInequality.Loewner.HalfLine.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic

/-!
# Carlen's `opmontI` conditions: local structure and weighted blocks

This module contains the first stage of Carlen 2022 Theorem 1.46 in the
`opmontI` route: local analytic structure, the two-block duplication map,
and weighted block positivity.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

/-! ### Local analytic structure and Carlen conditions -/
attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C\*-algebra. -/
noncomputable local instance instOpMontIBaseHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a complex algebra. -/
noncomputable local instance instOpMontIBaseHSOpComplexAlgebra {n : ℕ} :
    Algebra ℂ (HSOp n) :=
  ContinuousLinearMap.algebra

/-- The complex matrices `Mₙ n` form a real module by restriction of scalars. -/
noncomputable local instance instOpMontIBaseMatrixRealModule {n : ℕ} : Module ℝ (Mₙ n) :=
  Module.complexToReal (Mₙ n)

/-- The real and complex scalar actions on `Mₙ n` form a scalar tower. -/
noncomputable local instance instOpMontIBaseMatrixRealScalarTower {n : ℕ} :
    IsScalarTower ℝ ℂ (Mₙ n) :=
  RestrictScalars.isScalarTower ℝ ℂ (Mₙ n)

/-- `Mₙ n` is a real normed space by restriction of scalars. -/
noncomputable local instance instOpMontIBaseMatrixRealNormedSpace {n : ℕ} :
    NormedSpace ℝ (Mₙ n) :=
  NormedSpace.complexToReal

/-- `Mₙ n` is finite-dimensional over `ℝ`. -/
noncomputable local instance instOpMontIBaseMatrixRealFiniteDimensional {n : ℕ} :
    FiniteDimensional ℝ (Mₙ n) :=
  FiniteDimensional.complexToReal (Mₙ n)

/-- `HSOp n` is a real algebra via the `ℝ → ℂ` scalar map. -/
noncomputable local instance instOpMontIBaseHSOpRealAlgebra {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  Algebra.compHom (HSOp n) (algebraMap ℝ ℂ)

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance instOpMontIBaseHSOpStarRing {n : ℕ} : StarRing (HSOp n) :=
  (instOpMontIBaseHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance instOpMontIBaseHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance instOpMontIBaseHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance (instOpMontIBaseHSOpPartialOrder (n := n))
      (instOpMontIBaseHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance instOpMontIBaseHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (instOpMontIBaseHSOpCStarAlgebra (n := n))
    (instOpMontIBaseHSOpPartialOrder (n := n))
    (instOpMontIBaseHSOpStarOrderedRing (n := n))

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance instOpMontIBaseHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The opposite matrix algebra `(Mₙ n)ᵐᵒᵖ` has a real continuous functional calculus
for self-adjoint elements. -/
local instance instOpMontIBaseMatrixOppRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ ((Mₙ n)ᵐᵒᵖ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The product `HSOp n × HSOp n` is a C⋆-algebra. -/
noncomputable local instance instOpMontIBaseHSOpProdCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n × HSOp n) :=
  inferInstance

/-- The product `HSOp n × HSOp n` has a real continuous functional calculus for
self-adjoint elements. -/
local instance instOpMontIBaseHSOpProdRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n × HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The four-fold product `(HSOp n × HSOp n) × (HSOp n × HSOp n)` is a C⋆-algebra. -/
noncomputable local instance instOpMontIBaseHSOpProdProdCStarAlgebra {n : ℕ} :
    CStarAlgebra ((HSOp n × HSOp n) × (HSOp n × HSOp n)) :=
  inferInstance

/-- The four-fold product `(HSOp n × HSOp n) × (HSOp n × HSOp n)` has a real continuous
functional calculus for self-adjoint elements. -/
local instance instOpMontIBaseHSOpProdProdRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      ((HSOp n × HSOp n) × (HSOp n × HSOp n)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable section

/-- Function hypothesis in Carlen's `opmontI` theorem: positivity and continuity on `(0,∞)`. -/
def CarlenOpMontIFunctionHypothesis (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) ∧
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x

/-- Condition (1): `f` is operator monotone on the positive half-line. -/
def CarlenOpMontICondition1 (f : ℝ → ℝ) : Prop :=
  OperatorMonotoneOnPositive.{u} f

/-- Real convex combination of complex matrices. -/
def matrixConvexCombo {n : ℕ} (θ : ℝ) (A B : Mₙ n) : Mₙ n :=
  (θ : ℂ) • A + ((1 - θ : ℝ) : ℂ) • B

/-! ### Two-block duplication map and two-positivity -/
/--
Reindex a `2 × 2` block matrix with two `n × n` diagonal blocks as an ordinary
matrix indexed by `Fin (n + n)`.
-/
noncomputable def twoBlockReindex {n : ℕ} :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ ≃ₐ[ℂ] Mₙ (n + n) :=
  Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := n) (n := n))

/--
The block-diagonal duplication map `A ↦ diag(A,A)`, viewed as a Hilbert--Schmidt
linear map `Mₙ n → Mₙ (n+n)`.
-/
noncomputable def blockDiagDuplicateMap {n : ℕ} : HSMap n (n + n) :=
  ({ toFun := fun X => twoBlockReindex (Matrix.fromBlocks X 0 0 X)
     map_add' := by
       intro X Y
       have hblocks :
           Matrix.fromBlocks (X + Y) 0 0 (X + Y) =
             Matrix.fromBlocks X 0 0 X + Matrix.fromBlocks Y 0 0 Y := by
         rw [Matrix.fromBlocks_add]
         simp
       simp [hblocks, map_add]
     map_smul' := by
       intro c X
       have hblocks :
           Matrix.fromBlocks (c • X) 0 0 (c • X) =
             c • Matrix.fromBlocks X 0 0 X := by
         rw [Matrix.fromBlocks_smul]
         simp
       simp [hblocks, map_smul] } : Mₙ n →ₗ[ℂ] Mₙ (n + n)).toContinuousLinearMap

/-- Pointwise form of the block-diagonal duplication map. -/
theorem blockDiagDuplicateMap_apply {n : ℕ} (X : Mₙ n) :
    blockDiagDuplicateMap (n := n) X =
      twoBlockReindex (n := n) (Matrix.fromBlocks X 0 0 X) :=
  rfl

/-- Entrywise form of the block-diagonal duplication map. -/
theorem blockDiagDuplicateMap_apply_entry {n : ℕ} (X : Mₙ n)
    (i j : Fin (n + n)) :
    blockDiagDuplicateMap (n := n) X i j =
      Matrix.fromBlocks X 0 0 X
        ((finSumFinEquiv (m := n) (n := n)).symm i)
        ((finSumFinEquiv (m := n) (n := n)).symm j) := by
  change (twoBlockReindex (n := n) (Matrix.fromBlocks X 0 0 X)) i j =
    Matrix.fromBlocks X 0 0 X
      ((finSumFinEquiv (m := n) (n := n)).symm i)
      ((finSumFinEquiv (m := n) (n := n)).symm j)
  simp [twoBlockReindex, Matrix.reindex_apply]

/-- Reindexing a two-block matrix preserves and reflects positive semidefiniteness. -/
theorem twoBlockReindex_posSemidef_iff {n : ℕ}
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} :
    (twoBlockReindex (n := n) A).PosSemidef ↔ A.PosSemidef := by
  simp [twoBlockReindex, Matrix.reindex_apply,
    Matrix.posSemidef_submatrix_equiv (M := A)
      (e := (finSumFinEquiv (m := n) (n := n)).symm)]

/-- Reindexing a two-block matrix preserves positive semidefiniteness. -/
theorem twoBlockReindex_posSemidef {n : ℕ}
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hA : A.PosSemidef) :
    (twoBlockReindex (n := n) A).PosSemidef :=
  (twoBlockReindex_posSemidef_iff (n := n) (A := A)).2 hA

/-- Reindexing by an equivalence preserves positive semidefiniteness. -/
theorem reindexAlgEquiv_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) :
    (Matrix.reindexAlgEquiv ℂ ℂ e A).PosSemidef := by
  simpa [Matrix.reindexAlgEquiv, Matrix.reindex_apply] using
    (Matrix.posSemidef_submatrix_equiv (M := A) (e := e.symm)).2 hA

/-- Reindexing by an equivalence preserves positive definiteness. -/
theorem reindexAlgEquiv_posDef {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) {A : Matrix ι ι ℂ}
    (hA : A.PosDef) :
    (Matrix.reindexAlgEquiv ℂ ℂ e A).PosDef := by
  have hpsd :
      (Matrix.reindexAlgEquiv ℂ ℂ e A).PosSemidef :=
    reindexAlgEquiv_posSemidef e hA.posSemidef
  refine (Matrix.PosSemidef.posDef_iff_isUnit hpsd).2 ?_
  simpa [Matrix.reindexAlgEquiv, Matrix.reindex_apply] using
    (Matrix.isUnit_submatrix_equiv (A := A) e.symm e.symm).2 hA.isUnit

/--
Duplicating a positive semidefinite matrix on the block diagonal is positive
semidefinite, for any finite index type.
-/
theorem fromBlocks_duplicate_posSemidef' {ι : Type*} [Finite ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) :
    (Matrix.fromBlocks A 0 0 A).PosSemidef := by
  classical
  letI := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa using hA.1.apply i j
    · simp
    · simp
    · simpa using hA.1.apply i j
  · intro x
    have hleft :
        0 ≤ dotProduct (star (x ∘ Sum.inl)) (A.mulVec (x ∘ Sum.inl)) := by
      simpa [Matrix.mulVec] using hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have hright :
        0 ≤ dotProduct (star (x ∘ Sum.inr)) (A.mulVec (x ∘ Sum.inr)) := by
      simpa [Matrix.mulVec] using hA.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    have hsum : 0 ≤
        dotProduct (star (x ∘ Sum.inl)) (A.mulVec (x ∘ Sum.inl)) +
          dotProduct (star (x ∘ Sum.inr)) (A.mulVec (x ∘ Sum.inr)) :=
      add_nonneg hleft hright
    rw [Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
    simpa [Matrix.mulVec] using hsum

/-- Duplicating a positive semidefinite matrix on the block diagonal is positive semidefinite. -/
theorem fromBlocks_duplicate_posSemidef {n : ℕ} {A : Mₙ n}
    (hA : A.PosSemidef) :
    (Matrix.fromBlocks A 0 0 A).PosSemidef :=
  fromBlocks_duplicate_posSemidef' hA

/-- The block-diagonal duplication map preserves positive semidefiniteness. -/
theorem blockDiagDuplicateMap_posSemidef {n : ℕ} {A : Mₙ n}
    (hA : A.PosSemidef) :
    (blockDiagDuplicateMap (n := n) A).PosSemidef := by
  change (twoBlockReindex (n := n) (Matrix.fromBlocks A 0 0 A)).PosSemidef
  exact twoBlockReindex_posSemidef (n := n)
    (fromBlocks_duplicate_posSemidef hA)

/-- Interchange the middle two summands in a fourfold sum. -/
def sumInterchange {α β γ δ : Type*} :
    ((α ⊕ β) ⊕ (γ ⊕ δ)) ≃ ((α ⊕ γ) ⊕ (β ⊕ δ)) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inl c)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv := by
    intro x
    rcases x with (_ | _) | (_ | _) <;> rfl
  right_inv := by
    intro x
    rcases x with (_ | _) | (_ | _) <;> rfl

/--
Index equivalence identifying the `2 × 2` block amplification of the
block-diagonal duplication map with two copies of the original flattened
`2 × 2` block matrix.
-/
noncomputable def duplicateAmplificationIndexEquiv {n : ℕ} :
    ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) ≃ (Fin (n + n) ⊕ Fin (n + n)) :=
  (sumInterchange.trans
    (Equiv.sumCongr
      (finSumFinEquiv (m := n) (n := n))
      (finSumFinEquiv (m := n) (n := n))))

/-- Reindexing a two-block matrix does not change the trace. -/
theorem trace_twoBlockReindex {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix.trace (twoBlockReindex (n := n) F) = Matrix.trace F := by
  classical
  let e := finSumFinEquiv (m := n) (n := n)
  change (∑ x : Fin (n + n), F (e.symm x) (e.symm x)) =
    ∑ y : Fin n ⊕ Fin n, F y y
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

/-- Reindexing a two-block matrix commutes with conjugate transpose. -/
theorem conjTranspose_twoBlockReindex {n : ℕ}
    (F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix.conjTranspose (twoBlockReindex (n := n) F) =
      twoBlockReindex (n := n) (Matrix.conjTranspose F) := by
  ext i j
  simp [twoBlockReindex, Matrix.reindex_apply]

/--
The Hilbert--Schmidt trace pairing is unchanged by the two-block reindexing.
-/
theorem trace_twoBlockReindex_mul_conjTranspose {n : ℕ}
    (F G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Matrix.trace
        (twoBlockReindex (n := n) G *
          Matrix.conjTranspose (twoBlockReindex (n := n) F)) =
      Matrix.trace (G * Matrix.conjTranspose F) := by
  rw [conjTranspose_twoBlockReindex]
  have hmul :
      twoBlockReindex (n := n) G *
          twoBlockReindex (n := n) (Matrix.conjTranspose F) =
        twoBlockReindex (n := n) (G * Matrix.conjTranspose F) := by
    simp
  rw [hmul]
  exact trace_twoBlockReindex (n := n) (G * Matrix.conjTranspose F)

/-- The trace of a `2 × 2` block matrix is the sum of the diagonal traces. -/
theorem trace_fromBlocks_diagonal {n : ℕ} (A B C D : Mₙ n) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  classical
  simp [Matrix.trace, Matrix.fromBlocks]

/--
The Hilbert--Schmidt adjoint of the block-diagonal duplication map adds the two
diagonal blocks.
-/
theorem hsAdjoint_blockDiagDuplicateMap_fromBlocks {n : ℕ}
    (A B C D : Mₙ n) :
    hsAdjoint (blockDiagDuplicateMap (n := n))
        (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D)) =
      A + D := by
  classical
  refine @ext_inner_right ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)) _ _ fun X => ?_
  have hAdj :=
    @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ (n + n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixNormedAddCommGroup (n := n + n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixInnerProductSpace (n := n + n))
      (instMatrixCompleteSpace (n := n))
      (instMatrixCompleteSpace (n := n + n))
      (blockDiagDuplicateMap (n := n))
      X
      (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D))
  rw [show inner ℂ
        (hsAdjoint (blockDiagDuplicateMap (n := n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D))) X =
        inner ℂ
          (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D))
          (blockDiagDuplicateMap (n := n) X) by
      simpa [hsAdjoint] using hAdj]
  change Matrix.trace
      (twoBlockReindex (n := n) (Matrix.fromBlocks X 0 0 X) *
        Matrix.conjTranspose (twoBlockReindex (n := n) (Matrix.fromBlocks A B C D))) =
    Matrix.trace (X * Matrix.conjTranspose (A + D))
  rw [trace_twoBlockReindex_mul_conjTranspose]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    trace_fromBlocks_diagonal, Matrix.mul_add, Matrix.trace_add]

/--
For a weighted block-diagonal input, the adjoint of the duplication map returns
the corresponding real convex combination.
-/
theorem hsAdjoint_blockDiagDuplicateMap_weighted_fromBlocks {n : ℕ}
    (θ : ℝ) (A B : Mₙ n) :
    hsAdjoint (blockDiagDuplicateMap (n := n))
        (twoBlockReindex (n := n)
          (Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 - θ : ℝ) : ℂ) • B))) =
      matrixConvexCombo θ A B := by
  simpa [matrixConvexCombo] using
    hsAdjoint_blockDiagDuplicateMap_fromBlocks
      (n := n) ((θ : ℂ) • A) 0 0 (((1 - θ : ℝ) : ℂ) • B)

/--
The weighted block-diagonal input used to apply condition (2) to the
block-diagonal duplication map.
-/
noncomputable def weightedBlockDiag {n : ℕ} (θ : ℝ) (A B : Mₙ n) :
    Mₙ (n + n) :=
  twoBlockReindex (n := n)
    (Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 - θ : ℝ) : ℂ) • B))

/--
The adjoint of the duplication map sends the weighted block-diagonal input to
the corresponding convex combination.
-/
theorem hsAdjoint_blockDiagDuplicateMap_weightedBlockDiag {n : ℕ}
    (θ : ℝ) (A B : Mₙ n) :
    hsAdjoint (blockDiagDuplicateMap (n := n)) (weightedBlockDiag θ A B) =
      matrixConvexCombo θ A B := by
  simpa [weightedBlockDiag] using
    hsAdjoint_blockDiagDuplicateMap_weighted_fromBlocks
      (n := n) θ A B

/-! ### Weighted block positivity -/
/-- Mathlib positive definiteness implies the theorem-facing predicate used in this file. -/
theorem matrixPosDef_of_posDef {n : ℕ} {A : Mₙ n} (hA : A.PosDef) :
    MatrixPosDef A := by
  refine ⟨hA.isHermitian.isSelfAdjoint, ?_⟩
  intro x hx
  have hdot := (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 (x := x) hx
  exact (RCLike.pos_iff.mp hdot).1

/--
For an interior weight, the weighted block-diagonal matrix built from two
positive-definite blocks is positive definite.
-/
theorem fromBlocks_weighted_posDef {n : ℕ} {θ : ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 : ℂ) - (θ : ℂ)) • B)).PosDef := by
  classical
  let Aθ : Mₙ n := (θ : ℂ) • A
  let Bθ : Mₙ n := (((1 : ℂ) - (θ : ℂ)) • B)
  have hAθ : Aθ.PosDef := by
    have hr : Aθ = (θ • A : Mₙ n) := by
      ext i j
      change θ • A i j = (θ : ℂ) * A i j
      rw [Complex.real_smul]
    rw [hr]
    exact (matrixPosDef_posDef hA).smul hθ0
  have hBθ : Bθ.PosDef := by
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
    have hscalar : ((1 : ℂ) - (θ : ℂ)) = ((1 - θ : ℝ) : ℂ) := by
      norm_num
    have hr : Bθ = ((1 - θ : ℝ) • B : Mₙ n) := by
      ext i j
      change ((1 : ℂ) - (θ : ℂ)) * B i j = (1 - θ : ℝ) • B i j
      rw [hscalar, Complex.real_smul]
    rw [hr]
    exact (matrixPosDef_posDef hB).smul h1θ
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Aθ, Bθ] using
      (Matrix.IsHermitian.fromBlocks₁₁ (B := (0 : Matrix (Fin n) (Fin n) ℂ))
        (D := Bθ) hAθ.1).2 (by simpa using hBθ.1)
  · intro x hx
    have hxsplit : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      ext i
      cases i with
      | inl i =>
          have hi := congrFun h.1 i
          simpa using hi
      | inr i =>
          have hi := congrFun h.2 i
          simpa using hi
    have hleft_nonneg :
        0 ≤ dotProduct (star (x ∘ Sum.inl)) (Aθ.mulVec (x ∘ Sum.inl)) := by
      by_cases hxl : x ∘ Sum.inl = 0
      · simp [hxl]
      · exact le_of_lt (hAθ.dotProduct_mulVec_pos hxl)
    have hright_nonneg :
        0 ≤ dotProduct (star (x ∘ Sum.inr)) (Bθ.mulVec (x ∘ Sum.inr)) := by
      by_cases hxr : x ∘ Sum.inr = 0
      · simp [hxr]
      · exact le_of_lt (hBθ.dotProduct_mulVec_pos hxr)
    have hsum_pos :
        0 <
          dotProduct (star (x ∘ Sum.inl)) (Aθ.mulVec (x ∘ Sum.inl)) +
            dotProduct (star (x ∘ Sum.inr)) (Bθ.mulVec (x ∘ Sum.inr)) := by
      rcases hxsplit with hxl | hxr
      · exact add_pos_of_pos_of_nonneg (hAθ.dotProduct_mulVec_pos hxl) hright_nonneg
      · exact add_pos_of_nonneg_of_pos hleft_nonneg (hBθ.dotProduct_mulVec_pos hxr)
    rw [Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
    simpa [Aθ, Bθ, Matrix.mulVec] using hsum_pos

/--
For an interior weight, the ordinary `Fin (n+n)` reindexing of the weighted
block-diagonal matrix is positive definite.
-/
theorem twoBlockReindex_fromBlocks_weighted_matrixPosDef {n : ℕ} {θ : ℝ}
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    MatrixPosDef
      (twoBlockReindex (n := n)
        (Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 : ℂ) - (θ : ℂ)) • B))) :=
  matrixPosDef_of_posDef <|
    reindexAlgEquiv_posDef (finSumFinEquiv (m := n) (n := n))
      (fromBlocks_weighted_posDef hA hB hθ0 hθ1)

/--
Variant of the weighted block positive-definiteness statement using the real
scalar `(1 - θ)` cast to `ℂ`.
-/
theorem twoBlockReindex_fromBlocks_weighted_real_matrixPosDef {n : ℕ} {θ : ℝ}
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    MatrixPosDef
      (twoBlockReindex (n := n)
        (Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 - θ : ℝ) : ℂ) • B))) := by
  have hscalar : ((1 : ℂ) - (θ : ℂ)) = ((1 - θ : ℝ) : ℂ) := by
    norm_num
  have hblocks :
      Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 - θ : ℝ) : ℂ) • B) =
        Matrix.fromBlocks ((θ : ℂ) • A) 0 0 (((1 : ℂ) - (θ : ℂ)) • B) := by
    rw [← hscalar]
  rw [hblocks]
  exact twoBlockReindex_fromBlocks_weighted_matrixPosDef
    (n := n) (θ := θ) hA hB hθ0 hθ1

/--
For an interior weight, the named weighted block-diagonal input is positive
definite.
-/
theorem weightedBlockDiag_matrixPosDef {n : ℕ} {θ : ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    MatrixPosDef (weightedBlockDiag θ A B) := by
  simpa [weightedBlockDiag] using
    twoBlockReindex_fromBlocks_weighted_real_matrixPosDef
      (n := n) (θ := θ) hA hB hθ0 hθ1

end

end Quantum.TraceInequality.Loewner.HiaiPetz
