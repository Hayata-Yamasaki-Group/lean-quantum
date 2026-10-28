/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Support.OutputSupport
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Matrix model of the output-support corner (linear layer)

For a bounded map `Φ : HSMap n m` let `P = outputSupportProj Φ` be the orthogonal
projection onto the output support of `Φ(1)` and `outputSupportSubspace Φ` its range.
This file identifies the corner `P Mₘ P` (`matrixCornerSubmodule P`) with the
endomorphism algebra of the support subspace. It also transports the picture to the Euclidean
realization `outputSupportEuclideanSubspace Φ`, where inner products and adjoints are available.

## Main definitions

* `outputCornerSubspaceLinearEquiv`: corner `P Mₘ P ≃ₗ End (outputSupportSubspace Φ)`.
* `outputSupportEuclideanSubspace`: the support subspace inside `EuclideanSpace ℂ (Fin m)`.
* `outputCornerToEuclideanEndLinearEquiv`: corner `≃ₗ End` of the Euclidean support subspace.

## Main results

* `outputCorner_mul_mem` / `outputCorner_star_mem`: the corner is closed under
  matrix multiplication and adjoint.
* `outputCornerSubspaceLinearEquiv_mul` / `_proj` and their Euclidean analogues:
  the equivalences preserve products and send `P` to the identity.
* `outputSupportProj_eq_one_of_posDef`: `P = 1` when `Φ(1)` is positive definite.
* `outputCornerToEuclideanEndLinearEquiv_star_inner`: adjoint compatibility.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

section ExistingOwner

local notation "outputSupportProj_toEuclideanLin" => matrixSupportProj_toEuclideanLin

/-- The linear map `(Fin m → ℂ) →ₗ[ℂ] outputSupportSubspace Φ` sending `x` to `P x`,
the matrix-vector product with the output-support projection `P = outputSupportProj Φ`.
The image lands in the support subspace because `P` projects onto it. -/
noncomputable def outputSupportProjToSubspace {n m : ℕ} (Φ : HSMap n m) :
    (Fin m → ℂ) →ₗ[ℂ] outputSupportSubspace Φ where
  toFun := fun x =>
    ⟨(outputSupportProj Φ).mulVec x, by
      have hPidem : outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
        OutputSupportProj.idempotent Φ
      refine (OutputSupportProj.mulVec_eq_self_iff Φ ((outputSupportProj Φ).mulVec x)).1 ?_
      simpa [Matrix.mulVec_mulVec] using congrArg (fun M : Mₙ m => M.mulVec x) hPidem⟩
  map_add' := by
    intro x y
    ext i
    simp [Matrix.mulVec, dotProduct_add]
  map_smul' := by
    intro a x
    ext i
    simp [Matrix.mulVec, dotProduct_smul]

/-- On the support subspace, `outputSupportProjToSubspace Φ` acts as the identity:
`P x = x` for every `x ∈ outputSupportSubspace Φ`. -/
@[simp] theorem outputSupportProjToSubspace_apply_coe {n m : ℕ} (Φ : HSMap n m)
    (x : outputSupportSubspace Φ) :
    outputSupportProjToSubspace Φ x = x := by
  ext i
  have hx :
      (outputSupportProj Φ).mulVec x.1 = x.1 :=
    (OutputSupportProj.mulVec_eq_self_iff Φ x.1).2 x.2
  simpa using congrArg (fun v : Fin m → ℂ => v i) hx

/-- Applying `outputSupportProjToSubspace Φ` to `P x` gives the same result as applying
it to `x`, since the projection `P = outputSupportProj Φ` is idempotent. -/
@[simp] theorem outputSupportProjToSubspace_apply_proj {n m : ℕ} (Φ : HSMap n m)
    (x : Fin m → ℂ) :
    outputSupportProjToSubspace Φ ((outputSupportProj Φ).mulVec x) =
      outputSupportProjToSubspace Φ x := by
  have hPidem : outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
    OutputSupportProj.idempotent Φ
  ext i
  simpa [outputSupportProjToSubspace, Matrix.mulVec_mulVec] using
    congrArg (fun M : Mₙ m => M.mulVec x i) hPidem

/-- The linear map sending a corner matrix `X ∈ P Mₘ P` to the endomorphism `u ↦ X u`
of the support subspace `outputSupportSubspace Φ`. The image lands in the subspace
because `P * X = X` for corner elements. -/
noncomputable def outputCornerToSubspaceMap {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) →ₗ[ℂ]
      (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) where
  toFun := fun X =>
    { toFun := fun u =>
        ⟨X.1.mulVec u.1, by
          have hleft :
              outputSupportProj Φ * X.1 = X.1 :=
            OutputSupportProj.left_mul_eq_self_of_mem (Φ := Φ) X.2
          refine (OutputSupportProj.mulVec_eq_self_iff Φ (X.1.mulVec u.1)).1 ?_
          simpa [Matrix.mulVec_mulVec] using congrArg (fun M : Mₙ m => M.mulVec u.1) hleft⟩
      map_add' := by
        intro u v
        ext i
        change (fun j => X.1 i j) ⬝ᵥ (u.1 + v.1) =
          (fun j => X.1 i j) ⬝ᵥ u.1 + (fun j => X.1 i j) ⬝ᵥ v.1
        exact dotProduct_add _ _ _
      map_smul' := by
        intro a u
        ext i
        change (fun j => X.1 i j) ⬝ᵥ (a • u.1) = a * ((fun j => X.1 i j) ⬝ᵥ u.1)
        exact dotProduct_smul _ _ _ }
  map_add' := by
    intro X Y
    ext u i
    change (fun j => X.1 i j + Y.1 i j) ⬝ᵥ u.1 =
      (fun j => X.1 i j) ⬝ᵥ u.1 + (fun j => Y.1 i j) ⬝ᵥ u.1
    exact add_dotProduct _ _ _
  map_smul' := by
    intro a X
    ext u i
    change (a • fun j => X.1 i j) ⬝ᵥ u.1 = a * ((fun j => X.1 i j) ⬝ᵥ u.1)
    exact smul_dotProduct a (fun j => X.1 i j) u.1

/-- The linear map sending an endomorphism `T` of the support subspace back to a corner
matrix, namely the matrix of the composite `(Fin m → ℂ) → subspace → subspace → (Fin
  m → ℂ)`
built from the projection, `T`, and the inclusion. The result lies in the corner `P Mₘ P`. -/
noncomputable def subspaceMapToOutputCorner {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) →ₗ[ℂ]
      matrixCornerSubmodule (outputSupportProj Φ) where
  toFun := fun T =>
    let f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
      (outputSupportSubspace Φ).subtype.comp (T.comp (outputSupportProjToSubspace Φ))
    ⟨LinearMap.toMatrix' f, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      apply LinearMap.ext
      intro x
      funext i
      simp only [f, LinearMap.comp_apply]
      have hproj :
          outputSupportProjToSubspace Φ ((Matrix.toLin' (outputSupportProj Φ)) x) =
            outputSupportProjToSubspace Φ x := by
        simp [Matrix.toLin'_apply, outputSupportProjToSubspace_apply_proj Φ x]
      rw [hproj]
      have hfix :
          (outputSupportProj Φ).mulVec
              (((T (outputSupportProjToSubspace Φ x) : outputSupportSubspace Φ) : Fin m →
                ℂ)) =
            ((T (outputSupportProjToSubspace Φ x) : outputSupportSubspace Φ) : Fin m → ℂ) :=
        (OutputSupportProj.mulVec_eq_self_iff Φ
          ((T (outputSupportProjToSubspace Φ x) : outputSupportSubspace Φ) : Fin m → ℂ)).2
          (T (outputSupportProjToSubspace Φ x)).2
      simpa using congrArg (fun v : Fin m → ℂ => v i) hfix⟩
  map_add' := by
    intro T S
    apply Subtype.ext
    change
      LinearMap.toMatrix'
          ((outputSupportSubspace Φ).subtype.comp ((T + S).comp (outputSupportProjToSubspace
            Φ))) =
        LinearMap.toMatrix'
            ((outputSupportSubspace Φ).subtype.comp (T.comp (outputSupportProjToSubspace Φ))) +
          LinearMap.toMatrix'
            ((outputSupportSubspace Φ).subtype.comp (S.comp (outputSupportProjToSubspace Φ)))
    rw [show (T + S).comp (outputSupportProjToSubspace Φ) =
        T.comp (outputSupportProjToSubspace Φ) + S.comp (outputSupportProjToSubspace Φ) by
          ext x i; simp]
    rw [LinearMap.comp_add, LinearMap.toMatrix'.map_add]
  map_smul' := by
    intro a T
    apply Subtype.ext
    change
      LinearMap.toMatrix'
          ((outputSupportSubspace Φ).subtype.comp ((a • T).comp (outputSupportProjToSubspace
            Φ))) =
        a •
          LinearMap.toMatrix'
            ((outputSupportSubspace Φ).subtype.comp (T.comp (outputSupportProjToSubspace Φ)))
    rw [show (a • T).comp (outputSupportProjToSubspace Φ) =
        a • (T.comp (outputSupportProjToSubspace Φ)) by
          ext x i; simp]
    rw [LinearMap.comp_smul, LinearMap.toMatrix'.map_smul]

/-- The linear equivalence between the corner submodule `P Mₘ P` and the endomorphism
algebra of the support subspace, with `outputCornerToSubspaceMap Φ` and
`subspaceMapToOutputCorner Φ` as mutually inverse maps. -/
noncomputable def outputCornerSubspaceLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) where
  toFun := outputCornerToSubspaceMap Φ
  invFun := subspaceMapToOutputCorner Φ
  map_add' := (outputCornerToSubspaceMap Φ).map_add
  map_smul' := (outputCornerToSubspaceMap Φ).map_smul
  left_inv := by
    intro X
    apply Subtype.ext
    apply Matrix.toLin'.injective
    change Matrix.toLin' (LinearMap.toMatrix'
      ((outputSupportSubspace Φ).subtype.comp
        ((outputCornerToSubspaceMap Φ X).comp (outputSupportProjToSubspace Φ)))) =
      Matrix.toLin' X.1
    rw [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    funext i
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, Matrix.toLin'_apply]
    have hright : X.1 * outputSupportProj Φ = X.1 := by
      exact OutputSupportProj.right_mul_eq_self_of_mem (Φ := Φ) X.2
    change (X.1.mulVec ((outputSupportProj Φ).mulVec x)) i = X.1.mulVec x i
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M : Mₙ m => M.mulVec x i) hright
  right_inv := by
    intro T
    ext u i
    simp [outputCornerToSubspaceMap, subspaceMapToOutputCorner]

/-- The projection `P = outputSupportProj Φ` itself lies in its own corner submodule
`P Mₘ P`, since `P * P * P = P`. -/
theorem outputSupportProj_mem_outputCorner {n m : ℕ} (Φ : HSMap n m) :
    outputSupportProj Φ ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [OutputSupportProj.mem_corner_iff]
  have hPidem : outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
    OutputSupportProj.idempotent Φ
  calc
    outputSupportProj Φ * outputSupportProj Φ * outputSupportProj Φ
        = outputSupportProj Φ * outputSupportProj Φ := by
            simpa [Matrix.mul_assoc] using congrArg (fun M : Mₙ m => outputSupportProj Φ *
              M) hPidem
    _ = outputSupportProj Φ := hPidem

/-- `outputCornerSubspaceLinearEquiv Φ` sends the projection `P` (as a corner element)
to the identity endomorphism of the support subspace. -/
theorem outputCornerSubspaceLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerSubspaceLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ =
      LinearMap.id := by
  ext u i
  have hu :
      (outputSupportProj Φ).mulVec u.1 = u.1 :=
    (OutputSupportProj.mulVec_eq_self_iff Φ u.1).2 u.2
  simpa [outputCornerSubspaceLinearEquiv, outputCornerToSubspaceMap] using
    congrArg (fun v : Fin m → ℂ => v i) hu

/-- The corner submodule `P Mₘ P` is closed under matrix multiplication: if `X` and `Y`
lie in it then so does `X * Y`. -/
theorem outputCorner_mul_mem {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    X.1 * Y.1 ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  have hPX : outputSupportProj Φ * X.1 = X.1 := by
    exact OutputSupportProj.left_mul_eq_self_of_mem (Φ := Φ) X.2
  have hYP : Y.1 * outputSupportProj Φ = Y.1 := by
    exact OutputSupportProj.right_mul_eq_self_of_mem (Φ := Φ) Y.2
  calc
    outputSupportProj Φ * (X.1 * Y.1) * outputSupportProj Φ
        = (outputSupportProj Φ * X.1) * (Y.1 * outputSupportProj Φ) := by
            simp [Matrix.mul_assoc]
    _ = X.1 * Y.1 := by rw [hPX, hYP]

/-- The corner submodule `P Mₘ P` is closed under the adjoint (conjugate transpose):
if `X` lies in it then so does `star X`, using that `P` is self-adjoint. -/
theorem outputCorner_star_mem {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    star X.1 ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  have hPsa : Matrix.conjTranspose (outputSupportProj Φ) = outputSupportProj Φ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (OutputSupportProj.isSelfAdjoint Φ).star_eq
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc, hPsa] using
    congrArg star X.property

/-- `outputCornerSubspaceLinearEquiv Φ` is multiplicative: it sends a product `X * Y`
of corner elements to the composition of the corresponding subspace endomorphisms. -/
theorem outputCornerSubspaceLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerSubspaceLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      (outputCornerSubspaceLinearEquiv Φ X) * (outputCornerSubspaceLinearEquiv Φ Y) := by
  ext u i
  simp [outputCornerSubspaceLinearEquiv, outputCornerToSubspaceMap, Matrix.mulVec_mulVec]

/-- The output support subspace realized inside `EuclideanSpace ℂ (Fin m)` rather than
the bare function space `Fin m → ℂ`, obtained by transporting `outputSupportSubspace Φ`
along the isometric identification. This carries the inner-product structure needed for
adjoints and orthonormal bases. -/
noncomputable def outputSupportEuclideanSubspace {n m : ℕ} (Φ : HSMap n m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  (outputSupportSubspace Φ).map (EuclideanSpace.equiv (Fin m) ℂ).symm.toLinearMap

/-- A corner matrix `X ∈ P Mₘ P` annihilates the orthogonal complement of the support
subspace: `X u = 0` for every `u ∈ (outputSupportEuclideanSubspace Φ)ᗮ`, since `X * P = X`. -/
theorem outputCornerToEuclideanLin_apply_eq_zero_of_mem_orthogonal {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ))
    (u : (outputSupportEuclideanSubspace Φ)ᗮ) :
    Matrix.toEuclideanLin X.1 u.1 = 0 := by
  have huProj :
      (outputSupportEuclideanSubspace Φ).orthogonalProjection u.1 = 0 :=
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero u.2
  have huStar :
      (Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin m))
        (outputSupportEuclideanSubspace Φ)) u.1 = 0 := by
    rw [Submodule.starProjection, ContinuousLinearMap.comp_apply, huProj]
    simp
  have hPu : Matrix.toEuclideanLin (outputSupportProj Φ) u.1 = 0 := by
    simpa [outputSupportProj_toEuclideanLin] using huStar
  have hPuVec : (outputSupportProj Φ).mulVec (WithLp.ofLp u.1) = 0 := by
    have hPuLp : WithLp.toLp 2 ((outputSupportProj Φ).mulVec (WithLp.ofLp u.1)) = 0 := by
      rw [← Matrix.toLpLin_apply]
      exact hPu
    simpa using congrArg WithLp.ofLp hPuLp
  have hXP : X.1 * outputSupportProj Φ = X.1 := by
    exact OutputSupportProj.right_mul_eq_self_of_mem (Φ := Φ) X.2
  have hXu : X.1.mulVec (WithLp.ofLp u.1) = 0 := by
    have hfix := congrArg (fun M : Mₙ m => M.mulVec (WithLp.ofLp u.1)) hXP.symm
    have hfix' :
        X.1.mulVec (WithLp.ofLp u.1) =
          X.1.mulVec ((outputSupportProj Φ).mulVec (WithLp.ofLp u.1)) := by
      simpa [Matrix.mulVec_mulVec] using hfix
    rw [hPuVec] at hfix'
    simpa using hfix'
  simpa [Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) hXu

/-- The linear equivalence between the Euclidean support subspace
`outputSupportEuclideanSubspace Φ` and the bare support subspace `outputSupportSubspace Φ`,
induced by the identification `EuclideanSpace ℂ (Fin m) ≃ (Fin m → ℂ)`. -/
noncomputable def outputSupportEuclideanSubspaceLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEuclideanSubspace Φ ≃ₗ[ℂ] outputSupportSubspace Φ where
  toFun := fun u =>
    ⟨EuclideanSpace.equiv (Fin m) ℂ u.1, by
      rcases u.2 with ⟨v, hv, hvu⟩
      have : EuclideanSpace.equiv (Fin m) ℂ u.1 = v := by
        rw [← hvu]
        exact (EuclideanSpace.equiv (Fin m) ℂ).apply_symm_apply v
      simpa [this] using hv⟩
  invFun := fun u =>
    ⟨(EuclideanSpace.equiv (Fin m) ℂ).symm u.1, ⟨u.1, u.2, by
      simp⟩⟩
  left_inv := by
    intro u
    ext i
    rfl
  right_inv := by
    intro u
    ext i
    rfl
  map_add' := by
    intro u v
    ext i
    rfl
  map_smul' := by
    intro a u
    ext i
    rfl

/-- The linear equivalence between endomorphisms of the bare support subspace and
endomorphisms of the Euclidean support subspace, obtained by conjugating with
`outputSupportEuclideanSubspaceLinearEquiv Φ`. -/
noncomputable def outputSupportEndToEuclideanEndLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :=
  (outputSupportEuclideanSubspaceLinearEquiv Φ).symm.conj

/-- Evaluation formula: `outputSupportEndToEuclideanEndLinearEquiv Φ T` sends `u` to the
transport of `T` applied to the transported `u`, via `outputSupportEuclideanSubspaceLinearEquiv Φ`
and its inverse. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (T : outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ)
    (u : outputSupportEuclideanSubspace Φ) :
    outputSupportEndToEuclideanEndLinearEquiv Φ T u =
      (outputSupportEuclideanSubspaceLinearEquiv Φ).symm
        (T ((outputSupportEuclideanSubspaceLinearEquiv Φ) u)) := by
  rfl

/-- `outputSupportEndToEuclideanEndLinearEquiv Φ` is multiplicative: it sends a composition
of endomorphisms to the composition of their transports. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (T S : outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) :
    outputSupportEndToEuclideanEndLinearEquiv Φ (T * S) =
      outputSupportEndToEuclideanEndLinearEquiv Φ T *
        outputSupportEndToEuclideanEndLinearEquiv Φ S := by
  simpa [Module.End.mul_eq_comp] using
    LinearEquiv.conj_comp (outputSupportEuclideanSubspaceLinearEquiv Φ).symm S T

/-- `outputSupportEndToEuclideanEndLinearEquiv Φ` sends the identity endomorphism to the
identity. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_id {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEndToEuclideanEndLinearEquiv Φ LinearMap.id = LinearMap.id := by
  ext u i
  simp [outputSupportEndToEuclideanEndLinearEquiv_apply]

/-- The linear equivalence from the corner `P Mₘ P` to the endomorphism algebra of the
Euclidean support subspace, composing `outputCornerSubspaceLinearEquiv Φ` with
`outputSupportEndToEuclideanEndLinearEquiv Φ`. -/
noncomputable def outputCornerToEuclideanEndLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :=
  (outputCornerSubspaceLinearEquiv Φ).trans (outputSupportEndToEuclideanEndLinearEquiv Φ)

/-- At the level of ambient vectors, the endomorphism `outputCornerToEuclideanEndLinearEquiv Φ X`
acts exactly as the Euclidean linear map of the matrix `X`: its value on `u` has underlying
vector `X u`. -/
@[simp] theorem outputCornerToEuclideanEndLinearEquiv_apply_coe {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) (u : outputSupportEuclideanSubspace Φ) :
    ((outputCornerToEuclideanEndLinearEquiv Φ X u : outputSupportEuclideanSubspace Φ) :
        EuclideanSpace ℂ (Fin m)) =
      Matrix.toEuclideanLin X.1 u.1 := by
  ext i
  rfl

/-- Adjoint compatibility: the endomorphism attached to `star X` is the adjoint of the one
attached to `X`, expressed as `⟪(star X) u, v⟫ = ⟪u, X v⟫` on the Euclidean support
  subspace. -/
theorem outputCornerToEuclideanEndLinearEquiv_star_inner {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    ∀ u v : outputSupportEuclideanSubspace Φ,
      inner ℂ
          (((outputCornerToEuclideanEndLinearEquiv Φ
              ⟨star X.1, outputCorner_star_mem Φ X⟩) u :
                outputSupportEuclideanSubspace Φ) :
              EuclideanSpace ℂ (Fin m))
          v.1 =
        inner ℂ u.1
          (((outputCornerToEuclideanEndLinearEquiv Φ X) v :
                outputSupportEuclideanSubspace Φ) :
              EuclideanSpace ℂ (Fin m)) := by
  intro u v
  have hAdj :
      Matrix.toEuclideanLin (star X.1) = (Matrix.toEuclideanLin X.1).adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := X.1)
  calc
    inner ℂ
        (((outputCornerToEuclideanEndLinearEquiv Φ
            ⟨star X.1, outputCorner_star_mem Φ X⟩) u :
              outputSupportEuclideanSubspace Φ) :
            EuclideanSpace ℂ (Fin m))
        v.1
        = inner ℂ (Matrix.toEuclideanLin (star X.1) u.1) v.1 := by
            simp [outputCornerToEuclideanEndLinearEquiv_apply_coe]
    _ = inner ℂ ((Matrix.toEuclideanLin X.1).adjoint u.1) v.1 := by rw [hAdj]
    _ = inner ℂ u.1 (Matrix.toEuclideanLin X.1 v.1) := by
          simpa using
            (LinearMap.adjoint_inner_left (A := Matrix.toEuclideanLin X.1) (x := v.1) (y := u.1))
    _ = inner ℂ u.1
        (((outputCornerToEuclideanEndLinearEquiv Φ X) v :
              outputSupportEuclideanSubspace Φ) :
            EuclideanSpace ℂ (Fin m)) := by
          simp [outputCornerToEuclideanEndLinearEquiv_apply_coe]

/-- `outputCornerToEuclideanEndLinearEquiv Φ` is multiplicative: it sends `X * Y` to the
composition of the corresponding Euclidean endomorphisms. -/
theorem outputCornerToEuclideanEndLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToEuclideanEndLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToEuclideanEndLinearEquiv Φ X *
        outputCornerToEuclideanEndLinearEquiv Φ Y := by
  simp [outputCornerToEuclideanEndLinearEquiv, outputCornerSubspaceLinearEquiv_mul,
    outputSupportEndToEuclideanEndLinearEquiv_mul]

/-- `outputCornerToEuclideanEndLinearEquiv Φ` sends the projection `P` (as a corner element)
to the identity endomorphism. -/
theorem outputCornerToEuclideanEndLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToEuclideanEndLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = LinearMap.id := by
  simp [outputCornerToEuclideanEndLinearEquiv, outputCornerSubspaceLinearEquiv_proj,
    outputSupportEndToEuclideanEndLinearEquiv_id]

end ExistingOwner

/-- The Euclidean linear map of the projection matrix `P = outputSupportProj Φ` equals
the orthogonal (star) projection onto the Euclidean support subspace
`outputSupportEuclideanSubspace Φ`. -/
@[simp] theorem outputSupportProj_toEuclideanLin {n m : ℕ} (Φ : HSMap n m) :
    Matrix.toEuclideanLin (outputSupportProj Φ) =
      (Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin m))
        (outputSupportEuclideanSubspace Φ)).toLinearMap := by
  simp [outputSupportProj, outputSupportEuclideanSubspace, outputSupportSubspace]

end HiaiPetz
