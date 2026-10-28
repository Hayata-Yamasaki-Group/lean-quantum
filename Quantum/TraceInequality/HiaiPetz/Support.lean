/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Matrix support projections

Support subspaces and orthogonal support projections for finite matrices.  The
file packages the range of the matrix action, its projection matrix, and the
output-support notation used when reducing Hiai--Petz data-processing
statements to a support corner.

## Main results

* `matrixSupportProj`: the orthogonal projection onto the range of a matrix.
* `matrixSupportProj_isProj`: idempotence and self-adjointness of that
  projection.
* `matrixSupportProj_mulVec_eq_self_iff`: the projection fixes exactly the
  vectors in the matrix support.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Section 6.1.
-/

namespace HiaiPetz

open scoped ComplexOrder

/-- The support subspace of a matrix, viewed as the range of its action on vectors. -/
noncomputable def matrixSupportSubspace {n : ℕ} (C : Mₙ n) : Submodule ℂ (Fin n → ℂ) :=
  LinearMap.range C.mulVecLin

/-- The zero matrix has trivial support subspace, because its range is `⊥`. -/
@[simp] theorem matrixSupportSubspace_zero {n : ℕ} :
    matrixSupportSubspace (0 : Mₙ n) = ⊥ := by
  ext x
  simp [matrixSupportSubspace]

/-- A matrix projection for the general-output support-corner layer.
This book-facing name is a compatibility abbreviation for Mathlib's standard
star-projection predicate. -/
abbrev IsMatrixProj {m : ℕ} (P : Mₙ m) : Prop :=
  IsStarProjection P

/-- The ambient linear map whose matrix is `matrixSupportProj`. -/
private noncomputable def matrixSupportProjLin {n : ℕ} (C : Mₙ n) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  e.toLinearMap.comp (p.toLinearMap.comp e.symm.toLinearMap)

/-- The matrix of the orthogonal projection onto the support subspace of `C`. -/
noncomputable def matrixSupportProj {n : ℕ} (C : Mₙ n) : Mₙ n :=
  LinearMap.toMatrix' (matrixSupportProjLin C)

private theorem matrixSupportProjLin_idempotent {n : ℕ} (C : Mₙ n) :
    matrixSupportProjLin C * matrixSupportProjLin C = matrixSupportProjLin C := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  have hp : ∀ x, p (p x) = p x := by
    intro x
    simpa [Module.End.mul_eq_comp] using
      congrArg (fun f : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => f x)
        (U.isIdempotentElem_starProjection : p * p = p)
  apply LinearMap.ext
  intro x
  ext i
  change (e (p (e.symm (e (p (e.symm x)))))) i = (e (p (e.symm x))) i
  simp [hp]

/-- Transport identity identifying `matrixSupportProj` with the Hilbert-space
orthogonal projection onto the Euclidean image of `matrixSupportSubspace`. -/
@[simp] theorem matrixSupportProj_toEuclideanLin {n : ℕ} (C : Mₙ n) :
    Matrix.toEuclideanLin (matrixSupportProj C) =
      (Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
        ((matrixSupportSubspace C).map
          (EuclideanSpace.equiv (Fin n) ℂ).symm.toLinearMap)).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective
  simp [matrixSupportProj, matrixSupportProjLin, EuclideanSpace.equiv,
    PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv]

private theorem matrixSupportProj_isSelfAdjoint_aux {n : ℕ} (C : Mₙ n) :
    IsSelfAdjoint (matrixSupportProj C) := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  rw [← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_iff_isSymmetric]
  simpa [e, U, p] using (Submodule.starProjection_isSymmetric U)

/-- `matrixSupportProj` is an idempotent self-adjoint matrix projection. -/
theorem matrixSupportProj_isProj {n : ℕ} (C : Mₙ n) :
    IsMatrixProj (matrixSupportProj C) := by
  constructor
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul]
    unfold matrixSupportProj
    simpa [Module.End.mul_eq_comp] using matrixSupportProjLin_idempotent C
  · exact matrixSupportProj_isSelfAdjoint_aux C

/-- A vector is fixed by the support projection exactly when it lies in the
range of the original matrix action. -/
@[simp] theorem matrixSupportProj_mulVec_eq_self_iff {n : ℕ} (C : Mₙ n) (x : Fin n → ℂ) :
    (matrixSupportProj C).mulVec x = x ↔ x ∈ matrixSupportSubspace C := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  have hproj : Matrix.toEuclideanLin (matrixSupportProj C) = p.toLinearMap := by
    simp [e, U, p, matrixSupportProj_toEuclideanLin C]
  constructor
  · intro hx
    have hx' : p (e.symm x) = e.symm x := by
      have hxEuclid : Matrix.toEuclideanLin (matrixSupportProj C) (e.symm x) = e.symm x := by
        change Matrix.toEuclideanLin (matrixSupportProj C) (WithLp.toLp 2 x) = WithLp.toLp 2 x
        simpa only [Matrix.toLpLin_toLp] using congrArg (WithLp.toLp 2) hx
      simpa [hproj] using hxEuclid
    have hxU : e.symm x ∈ U := (Submodule.starProjection_eq_self_iff (K := U)).1 hx'
    simpa [e, U] using hxU
  · intro hx
    have hxU : e.symm x ∈ U := by
      simpa [e, U] using hx
    have hx' : p (e.symm x) = e.symm x :=
      (Submodule.starProjection_eq_self_iff (K := U)).2 hxU
    have hxEuclid : Matrix.toEuclideanLin (matrixSupportProj C) (e.symm x) = e.symm x := by
      simpa [hproj] using hx'
    have hxFunc : WithLp.toLp 2 ((matrixSupportProj C).mulVec x) = WithLp.toLp 2 x := by
      have hxEuclid' : Matrix.toEuclideanLin (matrixSupportProj C) (WithLp.toLp 2 x) =
          WithLp.toLp 2 x := by
        simpa [e] using hxEuclid
      simpa only [Matrix.toLpLin_toLp] using hxEuclid'
    simpa using congrArg WithLp.ofLp hxFunc

/-- The output-support subspace associated with `Φ(I)`. -/
noncomputable abbrev outputSupportSubspace {n m : ℕ} (Φ : HSMap n m) :
    Submodule ℂ (Fin m → ℂ) :=
  matrixSupportSubspace (Φ (1 : Mₙ n))

/-- The named output-support projection associated with `Φ(I)`. -/
noncomputable abbrev outputSupportProj {n m : ℕ} (Φ : HSMap n m) : Mₙ m :=
  matrixSupportProj (Φ (1 : Mₙ n))

end HiaiPetz
