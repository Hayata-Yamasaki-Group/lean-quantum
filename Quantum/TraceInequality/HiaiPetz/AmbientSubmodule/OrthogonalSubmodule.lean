/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Projections

/-!
# Orthogonal block submodules

Submodules, star projections, decompositions, and equivalences for the
diagonal block subspace and its orthogonal complement.

## Main results

* `twoBlockDiagSubmodule` and `offDiagSubmodule`: diagonal and off-diagonal
  block subspaces of `M_{2n}`.
* `twoBlockDiagOrthogonalDecomposition`: orthogonal decomposition of the
  ambient Hilbert-Schmidt space into diagonal and orthogonal components.
* `offDiagSubmodule_eq_orthogonal` and `offDiagOrthogonalEquiv`: identification
  of the off-diagonal block subspace with the orthogonal complement.

## References

* Hiai, block-matrix decomposition used in the off-diagonal
  CFC/Schur-complement reduction.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

/-- The diagonal block subspace of `M_{2n}`. -/
noncomputable def twoBlockDiagSubmodule (n : ℕ) :
    @Submodule ℂ (Mₙ (2 * n)) Complex.instSemiring
      (instMatrixNormedAddCommGroup (n := 2 * n)).toENormedAddCommMonoid.toAddCommMonoid
      (instMatrixInnerProductSpace (n := 2 * n)).toNormedSpace.toModule := by
  exact LinearMap.range (twoBlockDiagProj n).toLinearMap

/-- The diagonal block submodule has the orthogonal projection supplied by the
symmetric projection `twoBlockDiagProj`. -/
theorem twoBlockDiagSubmodule_hasOrthogonalProjection (n : ℕ) :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    ((twoBlockDiagProj n).toLinearMap)
    (twoBlockDiagProj_isSymmetricProjection n)

/-- Orthogonal star projection onto the two-block diagonal submodule. -/
noncomputable def twoBlockDiagStarProj (n : ℕ) : HSOp (2 * n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @Submodule.starProjection ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    (twoBlockDiagSubmodule n)
    (twoBlockDiagSubmodule_hasOrthogonalProjection n)

/-- Orthogonal complement of the two-block diagonal submodule in `M_{2n}`. -/
noncomputable def twoBlockDiagOrthogonalSubmodule (n : ℕ) :
    @Submodule ℂ (Mₙ (2 * n)) Complex.instSemiring
      (instMatrixNormedAddCommGroup (n := 2 * n)).toENormedAddCommMonoid.toAddCommMonoid
      (instMatrixInnerProductSpace (n := 2 * n)).toNormedSpace.toModule := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @Submodule.orthogonal ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    (twoBlockDiagSubmodule n)

/-- Orthogonal projection from the ambient matrix space onto the two-block
diagonal submodule. -/
noncomputable def twoBlockDiagOrthogonalProjection (n : ℕ) :
    Mₙ (2 * n) →L[ℂ] twoBlockDiagSubmodule n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @Submodule.orthogonalProjection ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    (twoBlockDiagSubmodule n)
    (twoBlockDiagSubmodule_hasOrthogonalProjection n)

/-- The concrete block projection `twoBlockDiagProj` agrees with the Hilbert
space star projection onto the diagonal submodule. -/
theorem twoBlockDiagProj_eq_starProjection (n : ℕ) :
    twoBlockDiagProj n = twoBlockDiagStarProj n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) :=
    twoBlockDiagSubmodule_hasOrthogonalProjection n
  rcases
      (@LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        ((twoBlockDiagProj n).toLinearMap)).mp (twoBlockDiagProj_isSymmetricProjection n) with
    ⟨_, hproj⟩
  exact ContinuousLinearMap.ext fun X => by
    simpa [twoBlockDiagStarProj, twoBlockDiagSubmodule] using
      congrArg (fun T : Mₙ (2 * n) →ₗ[ℂ] Mₙ (2 * n) => T X) hproj

/-- Membership in the diagonal submodule is equivalent to being fixed by
`twoBlockDiagProj`. -/
theorem mem_twoBlockDiagSubmodule_iff {n : ℕ} {X : Mₙ (2 * n)} :
    X ∈ twoBlockDiagSubmodule n ↔ twoBlockDiagProj n X = X := by
  constructor
  · rintro ⟨Y, rfl⟩
    simp
  · intro hX
    exact ⟨X, hX⟩

/-- A two-block diagonal matrix belongs to the diagonal block submodule. -/
theorem twoBlockDiag_mem_submodule {n : ℕ} (X₁ X₂ : Mₙ n) :
    twoBlockDiag X₁ X₂ ∈ twoBlockDiagSubmodule n := by
  rw [mem_twoBlockDiagSubmodule_iff, twoBlockDiagProj_twoBlockDiag]

/-- The off-diagonal block subspace of `M_{2n}`. -/
noncomputable def offDiagSubmodule (n : ℕ) :
    @Submodule ℂ (Mₙ (2 * n)) Complex.instSemiring
      (instMatrixNormedAddCommGroup (n := 2 * n)).toENormedAddCommMonoid.toAddCommMonoid
      (instMatrixInnerProductSpace (n := 2 * n)).toNormedSpace.toModule := by
  exact LinearMap.range (offDiagProj n).toLinearMap

/-- The off-diagonal submodule has the orthogonal projection supplied by the
symmetric projection `offDiagProj`. -/
theorem offDiagSubmodule_hasOrthogonalProjection (n : ℕ) :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (offDiagSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @LinearMap.IsSymmetricProjection.hasOrthogonalProjection_range ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    ((offDiagProj n).toLinearMap)
    (offDiagProj_isSymmetricProjection n)

/-- Local orthogonal-projection instance for the off-diagonal submodule. -/
noncomputable local instance instOffDiagSubmoduleHasOrthogonalProjection {n : ℕ} :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (offDiagSubmodule n) :=
  offDiagSubmodule_hasOrthogonalProjection n

/-- Local completeness instance for the off-diagonal submodule. -/
noncomputable local instance instOffDiagSubmoduleCompleteSpace {n : ℕ} :
    CompleteSpace (offDiagSubmodule n) :=
  by
    letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
    infer_instance

/-- Local completeness instance for the subtype carrier of the off-diagonal
submodule. -/
noncomputable local instance instOffDiagSubtypeCompleteSpace {n : ℕ} :
    CompleteSpace ↥(offDiagSubmodule n) :=
  instOffDiagSubmoduleCompleteSpace (n := n)

/-- Orthogonal star projection onto the off-diagonal submodule. -/
noncomputable def offDiagStarProj (n : ℕ) : HSOp (2 * n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @Submodule.starProjection ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    (offDiagSubmodule n)
    (offDiagSubmodule_hasOrthogonalProjection n)

/-- The orthogonal complement of the diagonal submodule has an orthogonal
projection. -/
theorem twoBlockDiagOrthogonalSubmodule_hasOrthogonalProjection (n : ℕ) :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagOrthogonalSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) :=
    twoBlockDiagSubmodule_hasOrthogonalProjection n
  infer_instance

/-- Local orthogonal-projection instance for the diagonal submodule. -/
noncomputable local instance instTwoBlockDiagSubmoduleHasOrthogonalProjection {n : ℕ} :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n) :=
  twoBlockDiagSubmodule_hasOrthogonalProjection n

/-- Local orthogonal-projection instance for the orthogonal complement of the
diagonal submodule. -/
noncomputable local instance instTwoBlockDiagOrthogonalSubmoduleHasOrthogonalProjection {n : ℕ} :
    @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagOrthogonalSubmodule n) :=
  twoBlockDiagOrthogonalSubmodule_hasOrthogonalProjection n

/-- Local completeness instance for the diagonal submodule. -/
noncomputable local instance instTwoBlockDiagSubmoduleCompleteSpace {n : ℕ} :
    CompleteSpace (twoBlockDiagSubmodule n) :=
  by
    letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
    infer_instance

/-- Local completeness instance for the subtype carrier of the diagonal
submodule. -/
noncomputable local instance instTwoBlockDiagSubtypeCompleteSpace {n : ℕ} :
    CompleteSpace ↥(twoBlockDiagSubmodule n) :=
  instTwoBlockDiagSubmoduleCompleteSpace (n := n)

/-- Local completeness instance for the orthogonal complement of the diagonal
submodule. -/
noncomputable local instance instTwoBlockDiagOrthogonalSubmoduleCompleteSpace {n : ℕ} :
    CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
  by
    letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
    infer_instance

/-- Local completeness instance for the subtype carrier of the orthogonal
complement. -/
noncomputable local instance instTwoBlockDiagOrthogonalSubtypeCompleteSpace {n : ℕ} :
    CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
  instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)

/-- Local completeness instance for the `WithLp` product of the diagonal
submodule and its orthogonal complement. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairCompleteSpace {n : ℕ} :
    CompleteSpace (WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) := by
  infer_instance

/-- Local normed additive group instance for the `WithLp` product of the
diagonal submodule and its orthogonal complement. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup
      (WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) := by
  infer_instance

/-- Local complex normed-space instance for the `WithLp` product of the
diagonal submodule and its orthogonal complement. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairNormedSpace {n : ℕ} :
    NormedSpace ℂ (WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) := by
  infer_instance

/-- Local inner-product-space instance for the `WithLp` product of the diagonal
submodule and its orthogonal complement. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ
      (WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) := by
  infer_instance

/-- Type synonym for the `WithLp` product of the diagonal block submodule and
its orthogonal complement. -/
noncomputable def twoBlockDiagOrthogonalPairSpace (n : ℕ) : Type :=
  WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)

/-- Local normed additive group instance for `twoBlockDiagOrthogonalPairSpace`. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n) := by
  unfold twoBlockDiagOrthogonalPairSpace
  exact instTwoBlockDiagOrthogonalPairNormedAddCommGroup (n := n)

/-- Local complex normed-space instance for `twoBlockDiagOrthogonalPairSpace`. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairSpaceNormedSpace {n : ℕ} :
    NormedSpace ℂ (twoBlockDiagOrthogonalPairSpace n) := by
  unfold twoBlockDiagOrthogonalPairSpace
  exact instTwoBlockDiagOrthogonalPairNormedSpace (n := n)

/-- Local inner-product-space instance for `twoBlockDiagOrthogonalPairSpace`. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairSpaceInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n) := by
  unfold twoBlockDiagOrthogonalPairSpace
  exact instTwoBlockDiagOrthogonalPairInnerProductSpace (n := n)

/-- Local completeness instance for `twoBlockDiagOrthogonalPairSpace`. -/
noncomputable local instance instTwoBlockDiagOrthogonalPairSpaceCompleteSpace {n : ℕ} :
    CompleteSpace (twoBlockDiagOrthogonalPairSpace n) := by
  unfold twoBlockDiagOrthogonalPairSpace
  exact instTwoBlockDiagOrthogonalPairCompleteSpace (n := n)

/-- Orthogonal projection from the ambient matrix space onto the complement of
the two-block diagonal submodule. -/
noncomputable def twoBlockDiagOrthogonalComplementProjection (n : ℕ) :
    Mₙ (2 * n) →L[ℂ] twoBlockDiagOrthogonalSubmodule n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact @Submodule.orthogonalProjection ℂ (Mₙ (2 * n))
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := 2 * n))
    (instMatrixInnerProductSpace (n := 2 * n))
    (twoBlockDiagOrthogonalSubmodule n)
    (twoBlockDiagOrthogonalSubmodule_hasOrthogonalProjection n)

/-- Hilbert-space orthogonal decomposition of `M_{2n}` into the diagonal
submodule and its orthogonal complement. -/
noncomputable def twoBlockDiagOrthogonalDecomposition (n : ℕ) :
    Mₙ (2 * n) ≃ₗᵢ[ℂ]
      WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  let hRaw :=
    @Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
  simpa [twoBlockDiagOrthogonalSubmodule] using
    hRaw

/-- Continuous linear map underlying the orthogonal decomposition into diagonal
and orthogonal components. -/
noncomputable def twoBlockDiagOrthogonalDecompositionCLM (n : ℕ) :
    Mₙ (2 * n) →L[ℂ]
      WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  exact
    (((WithLp.prodContinuousLinearEquiv 2 ℂ
        (twoBlockDiagSubmodule n) (twoBlockDiagOrthogonalSubmodule n)).symm :
      (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) →L[ℂ]
        WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n))) ∘L
      (twoBlockDiagOrthogonalProjection n).prod
        (twoBlockDiagOrthogonalComplementProjection n)

/-- The first component of the orthogonal decomposition is the projection onto
the diagonal submodule. -/
@[simp] theorem twoBlockDiagOrthogonalDecomposition_fst {n : ℕ} (X : Mₙ (2 * n)) :
    ((twoBlockDiagOrthogonalDecomposition n) X).fst = twoBlockDiagOrthogonalProjection n X := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  change ((@Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      X).fst) = twoBlockDiagOrthogonalProjection n X
  exact
    (@Submodule.fst_orthogonalDecomposition_apply ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      X).trans rfl

/-- The second component of the orthogonal decomposition is the projection onto
the orthogonal complement. -/
@[simp] theorem twoBlockDiagOrthogonalDecomposition_snd {n : ℕ} (X : Mₙ (2 * n)) :
    ((twoBlockDiagOrthogonalDecomposition n) X).snd =
      twoBlockDiagOrthogonalComplementProjection n X := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  change ((@Submodule.orthogonalDecomposition ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      X).snd) = twoBlockDiagOrthogonalComplementProjection n X
  exact
    (@Submodule.snd_orthogonalDecomposition_apply ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (twoBlockDiagSubmodule n)
      (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n))
      X).trans rfl

/-- The continuous-linear decomposition has `ofLp` pair equal to the two
orthogonal projections. -/
@[simp] theorem twoBlockDiagOrthogonalDecompositionCLM_ofLp {n : ℕ} (X : Mₙ (2 * n)) :
    ((twoBlockDiagOrthogonalDecompositionCLM n) X).ofLp =
      (twoBlockDiagOrthogonalProjection n X, twoBlockDiagOrthogonalComplementProjection n X) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  rfl

/-- Continuous linear map that reconstructs an ambient matrix from its diagonal
and orthogonal components. -/
noncomputable def twoBlockDiagOrthogonalDecompositionSymmCLM (n : ℕ) :
    WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) →L[ℂ]
      Mₙ (2 * n) := by
  exact
    (twoBlockDiagSubmodule n).subtypeL.coprod
        (twoBlockDiagOrthogonalSubmodule n).subtypeL ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ
        (twoBlockDiagSubmodule n) (twoBlockDiagOrthogonalSubmodule n))

/-- Conjugation of an endomorphism on the decomposition space back to an
ambient Hilbert-Schmidt operator on `M_{2n}`. -/
noncomputable def twoBlockDiagOrthogonalConjStarAlgEquiv (n : ℕ) :
    ((WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) →L[ℂ]
        WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n)) →
      HSOp (2 * n) := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  exact fun T =>
    twoBlockDiagOrthogonalDecompositionSymmCLM n ∘L T ∘L
      twoBlockDiagOrthogonalDecompositionCLM n

/-- Membership in the off-diagonal submodule is equivalent to being fixed by
`offDiagProj`. -/
theorem mem_offDiagSubmodule_iff {n : ℕ} {X : Mₙ (2 * n)} :
    X ∈ offDiagSubmodule n ↔ offDiagProj n X = X := by
  constructor
  · intro hX
    rcases hX with ⟨Y, rfl⟩
    exact congrArg (fun T : HSOp (2 * n) => T Y) (offDiagProj_idempotent n)
  · intro hX
    exact ⟨X, hX⟩

/-- The concrete block projection `offDiagProj` agrees with the Hilbert-space
star projection onto the off-diagonal submodule. -/
theorem offDiagProj_eq_starProjection (n : ℕ) :
    offDiagProj n = offDiagStarProj n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : @Submodule.HasOrthogonalProjection ℂ (Mₙ (2 * n))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (offDiagSubmodule n) :=
    offDiagSubmodule_hasOrthogonalProjection n
  rcases
      (@LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        ((offDiagProj n).toLinearMap)).mp (offDiagProj_isSymmetricProjection n) with
    ⟨_, hproj⟩
  exact ContinuousLinearMap.ext fun X => by
    simpa [offDiagStarProj, offDiagSubmodule] using
      congrArg (fun T : Mₙ (2 * n) →ₗ[ℂ] Mₙ (2 * n) => T X) hproj

/-- Coercing the orthogonal projection onto the diagonal submodule recovers the
concrete block projection `twoBlockDiagProj`. -/
@[simp] theorem coe_twoBlockDiagSubmodule_orthogonalProjection_apply {n : ℕ} (X : Mₙ (2 * n)) :
    ((twoBlockDiagOrthogonalProjection n X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) =
      twoBlockDiagProj n X := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  simpa [twoBlockDiagOrthogonalProjection, twoBlockDiagStarProj,
    Submodule.coe_orthogonalProjection_apply] using
    (congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_eq_starProjection n)).symm

/-- An off-diagonal four-block matrix belongs to the off-diagonal submodule. -/
theorem offDiag_mem_submodule {n : ℕ} (X₁₂ X₂₁ : Mₙ n) :
    fourBlockMatrix 0 X₁₂ X₂₁ 0 ∈ offDiagSubmodule n := by
  rw [mem_offDiagSubmodule_iff, offDiagProj_fourBlockMatrix]

/-- The off-diagonal block submodule is exactly the orthogonal complement of
the two-block diagonal submodule. -/
theorem offDiagSubmodule_eq_orthogonal (n : ℕ) :
    offDiagSubmodule n = twoBlockDiagOrthogonalSubmodule n := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  ext X
  constructor
  · intro hX
    rw [mem_offDiagSubmodule_iff] at hX
    have hsum :=
      congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
    have hsum' : twoBlockDiagProj n X + offDiagProj n X = X := by
      simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] using hsum
    have hzero : twoBlockDiagProj n X = 0 := by
      simpa [hX] using hsum'
    have hproj0 : twoBlockDiagOrthogonalProjection n X = 0 := by
      apply Subtype.ext
      simpa [coe_twoBlockDiagSubmodule_orthogonalProjection_apply] using hzero
    have horth0 :=
      @Submodule.orthogonalProjection_eq_zero_iff ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (twoBlockDiagSubmodule_hasOrthogonalProjection n)
        X
    simpa [twoBlockDiagOrthogonalSubmodule] using
      horth0.1 hproj0
  · intro hX
    have horth0 :=
      @Submodule.orthogonalProjection_eq_zero_iff ℂ (Mₙ (2 * n))
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (twoBlockDiagSubmodule n)
        (twoBlockDiagSubmodule_hasOrthogonalProjection n)
        X
    have hproj0 : twoBlockDiagOrthogonalProjection n X = 0 := by
      exact horth0.2 (by simpa [twoBlockDiagOrthogonalSubmodule] using hX)
    have hzero : twoBlockDiagProj n X = 0 := by
      simpa [coe_twoBlockDiagSubmodule_orthogonalProjection_apply] using
        congrArg (fun Z : twoBlockDiagSubmodule n => (Z : Mₙ (2 * n))) hproj0
    rw [mem_offDiagSubmodule_iff]
    have hsum :=
      congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
    have hsum' : twoBlockDiagProj n X + offDiagProj n X = X := by
      simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] using hsum
    simpa [hzero] using hsum'

/-- Coercing the projection onto the orthogonal complement recovers the
concrete off-diagonal block projection. -/
@[simp] theorem coe_twoBlockDiagOrthogonalProjection_apply {n : ℕ} (X : Mₙ (2 * n)) :
    ((twoBlockDiagOrthogonalComplementProjection n X : twoBlockDiagOrthogonalSubmodule n) :
        Mₙ (2 * n)) =
      offDiagProj n X := by
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  have horth :
      (@Submodule.starProjection ℂ (Mₙ (2 * n))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (twoBlockDiagOrthogonalSubmodule n)
          (twoBlockDiagOrthogonalSubmodule_hasOrthogonalProjection n) X : Mₙ (2 * n)) =
        X -
          @Submodule.starProjection ℂ (Mₙ (2 * n))
            (inferInstance : RCLike ℂ)
            (instMatrixNormedAddCommGroup (n := 2 * n))
            (instMatrixInnerProductSpace (n := 2 * n))
            (twoBlockDiagSubmodule n)
            (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n)) X := by
    simp [twoBlockDiagOrthogonalSubmodule]
  calc
    ((twoBlockDiagOrthogonalComplementProjection n X : twoBlockDiagOrthogonalSubmodule n) :
        Mₙ (2 * n)) =
      X -
        @Submodule.starProjection ℂ (Mₙ (2 * n))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := 2 * n))
          (instMatrixInnerProductSpace (n := 2 * n))
          (twoBlockDiagSubmodule n)
          (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n)) X := by
        simpa [twoBlockDiagOrthogonalComplementProjection] using horth
    _ = offDiagProj n X := by
      have hoff :
          offDiagStarProj n X =
            X -
              @Submodule.starProjection ℂ (Mₙ (2 * n))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := 2 * n))
                (instMatrixInnerProductSpace (n := 2 * n))
                (twoBlockDiagSubmodule n)
                (instTwoBlockDiagSubmoduleHasOrthogonalProjection (n := n)) X := by
        simp [offDiagStarProj, offDiagSubmodule_eq_orthogonal, twoBlockDiagOrthogonalSubmodule]
      simpa [hoff] using
        (congrArg (fun T : HSOp (2 * n) => T X) (offDiagProj_eq_starProjection n)).symm

/-- Reconstruction after applying the continuous-linear orthogonal
decomposition is the identity on the ambient matrix space. -/
@[simp] theorem twoBlockDiagOrthogonalDecomposition_cancel {n : ℕ} (X : Mₙ (2 * n)) :
    twoBlockDiagOrthogonalDecompositionSymmCLM n
      ((twoBlockDiagOrthogonalDecompositionCLM n) X) = X := by
  have hcoprod :
      ((twoBlockDiagSubmodule n).subtypeL.coprod (twoBlockDiagOrthogonalSubmodule n).subtypeL)
          (twoBlockDiagOrthogonalProjection n X, twoBlockDiagOrthogonalComplementProjection n X) =
        ((twoBlockDiagOrthogonalProjection n X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
          ((twoBlockDiagOrthogonalComplementProjection n X : twoBlockDiagOrthogonalSubmodule n) :
            Mₙ (2 * n)) := by
    simp
  have hsum :=
    congrArg (fun T : HSOp (2 * n) => T X) (twoBlockDiagProj_add_offDiagProj (n := n))
  have hsum' : twoBlockDiagProj n X + offDiagProj n X = X := by
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] using hsum
  have hdecomp :
      twoBlockDiagOrthogonalDecompositionSymmCLM n ((twoBlockDiagOrthogonalDecompositionCLM n) X) =
        ((twoBlockDiagOrthogonalProjection n X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
          ((twoBlockDiagOrthogonalComplementProjection n X : twoBlockDiagOrthogonalSubmodule n) :
            Mₙ (2 * n)) := by
    have h0 :
        twoBlockDiagOrthogonalDecompositionSymmCLM n
            ((twoBlockDiagOrthogonalDecompositionCLM n) X) =
          ((twoBlockDiagSubmodule n).subtypeL.coprod (twoBlockDiagOrthogonalSubmodule n).subtypeL)
            (twoBlockDiagOrthogonalProjection n X,
              twoBlockDiagOrthogonalComplementProjection n X) := by
      change
        ((twoBlockDiagSubmodule n).subtypeL.coprod (twoBlockDiagOrthogonalSubmodule n).subtypeL)
            (((twoBlockDiagOrthogonalDecompositionCLM n) X).ofLp) =
          ((twoBlockDiagSubmodule n).subtypeL.coprod (twoBlockDiagOrthogonalSubmodule n).subtypeL)
            (twoBlockDiagOrthogonalProjection n X, twoBlockDiagOrthogonalComplementProjection n X)
      rw [twoBlockDiagOrthogonalDecompositionCLM_ofLp]
    exact h0.trans hcoprod
  calc
    twoBlockDiagOrthogonalDecompositionSymmCLM n ((twoBlockDiagOrthogonalDecompositionCLM n) X)
        = ((twoBlockDiagOrthogonalProjection n X : twoBlockDiagSubmodule n) : Mₙ (2 * n)) +
          ((twoBlockDiagOrthogonalComplementProjection n X : twoBlockDiagOrthogonalSubmodule n) :
            Mₙ (2 * n)) := hdecomp
    _ = X := by
          simpa [twoBlockDiagProj, offDiagProj,
            coe_twoBlockDiagSubmodule_orthogonalProjection_apply,
            coe_twoBlockDiagOrthogonalProjection_apply] using hsum'

/-- Identify the off-diagonal block subspace with the orthogonal complement of the
diagonal block subspace. -/
noncomputable def offDiagOrthogonalEquiv (n : ℕ) :
    offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
  by
    letI := instMatrixNormedAddCommGroup (n := 2 * n)
    letI := instMatrixNormedSpace (n := 2 * n)
    letI := instMatrixInnerProductSpace (n := 2 * n)
    exact LinearIsometryEquiv.ofEq _ _ (offDiagSubmodule_eq_orthogonal n)

/-- Coercing the off-diagonal/orthogonal-complement equivalence leaves the
ambient matrix representative unchanged. -/
@[simp] theorem coe_offDiagOrthogonalEquiv_apply {n : ℕ} (X : offDiagSubmodule n) :
    (((offDiagOrthogonalEquiv n) X : twoBlockDiagOrthogonalSubmodule n) : Mₙ (2 * n)) =
      X.1 := rfl

/-- Coercing the inverse off-diagonal/orthogonal-complement equivalence leaves
the ambient matrix representative unchanged. -/
@[simp] theorem coe_offDiagOrthogonalEquiv_symm_apply {n : ℕ}
    (X : twoBlockDiagOrthogonalSubmodule n) :
    (((offDiagOrthogonalEquiv n).symm X : offDiagSubmodule n) : Mₙ (2 * n)) =
      X.1 := rfl

end MatrixScopedInstances

end HiaiPetz
