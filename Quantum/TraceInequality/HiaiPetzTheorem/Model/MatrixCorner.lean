/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner

/-!
# Matrix model of the output-support corner (orthonormal layer and bundled model)

Continuing `…OutputSupport.Model.Basic`, this file identifies the corner `P Mₘ P`
(`P = outputSupportProj Φ`) with `d × d` matrices using an *orthonormal* basis of the
Euclidean support subspace, so that the resulting matrix model preserves adjoints,
positive semidefiniteness, units and trace. These compatibilities are
then bundled into the structure `MatrixCornerModel`, and the output-support corner is
exhibited as such a model via `outputSupportMatrixCornerModel`.

## Main definitions

* `outputSupportEuclideanOrthonormalBasis`: orthonormal basis of the Euclidean support subspace.
* `outputCornerToOrthonormalMatrixLinearEquiv`: corner `≃ₗ` `d × d` matrices (orthonormal
  model).
* `MatrixCornerModel`: a bundled matrix model of a corner, preserving trace, adjoint, product, unit.
* `outputSupportMatrixCornerModel`: the output-support corner as a `MatrixCornerModel`.
* `MatrixCornerModel.transportMap`: transport of an `HSMap` landing in the corner to `HSMap n dim`.

## Main results

* `outputCornerToOrthonormalMatrixLinearEquiv_star` / `_trace` / `_mul` / `_proj`:
  the orthonormal model preserves adjoint, trace, product and the projection.
* `..._posSemidef_iff` / `..._isUnit_iff`: positivity and invertibility are preserved.
* `MatrixCornerModel.inner_toMat_eq`: the model map is a Hilbert–Schmidt isometry.
* `MatrixCornerModel.hsAdjoint_transportMap_apply`: the transport commutes with the adjoint.
-/

namespace HiaiPetz
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The matrix image is positive semidefinite iff the endomorphism `T` is positive (as a
self-adjoint operator on the Euclidean support subspace). -/
theorem outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff {n m : ℕ}
    (Φ : HSMap n m) (T : outputSupportEuclideanSubspace Φ →ₗ[ℂ]
      outputSupportEuclideanSubspace Φ) :
    (outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ T).PosSemidef ↔
      @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _ T := by
  simp [outputSupportEuclideanToOrthonormalMatrixLinearEquiv,
    LinearMap.posSemidef_toMatrix_iff]

/-- The matrix image is a unit (invertible) iff the endomorphism `T` is a unit. -/
theorem outputSupportEuclideanToOrthonormalMatrixLinearEquiv_isUnit_iff {n m : ℕ}
    (Φ : HSMap n m) (T : outputSupportEuclideanSubspace Φ →ₗ[ℂ]
      outputSupportEuclideanSubspace Φ) :
    IsUnit (outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ T) ↔ IsUnit T := by
  simp [outputSupportEuclideanToOrthonormalMatrixLinearEquiv,
    LinearMap.isUnit_toMatrix_iff]

/-- Compatibility of the inverse model map with `star Y * Y`: `toMat.symm (star Y * Y)`
equals the corner element `star (toMat.symm Y) * (toMat.symm Y)`. -/
theorem MatrixCornerModel.toMat_symm_star_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y : Mₙ model.dim) :
    model.toMat.symm (star Y * Y) =
      ⟨star ((model.toMat.symm Y).1) * (model.toMat.symm Y).1,
        model.mul_mem_corner
          ⟨star ((model.toMat.symm Y).1), model.adjoint_mem_corner (model.toMat.symm Y)⟩
          (model.toMat.symm Y)⟩ := by
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  let Ystar : matrixCornerSubmodule P := ⟨star Ycorner.1, model.adjoint_mem_corner Ycorner⟩
  apply model.toMat.injective
  calc
    model.toMat (model.toMat.symm (star Y * Y)) = star Y * Y := by
      simp
    _ = star (model.toMat Ycorner) * model.toMat Ycorner := by
      simp [Ycorner]
    _ = model.toMat Ystar * model.toMat Ycorner := by
      rw [model.preservesAdjoint Ycorner]
    _ = model.toMat
          ⟨star Ycorner.1 * Ycorner.1, model.mul_mem_corner Ystar Ycorner⟩ := by
            rw [model.map_mul Ystar Ycorner]
    _ = model.toMat
          ⟨star ((model.toMat.symm Y).1) * (model.toMat.symm Y).1,
            model.mul_mem_corner
              ⟨star ((model.toMat.symm Y).1), model.adjoint_mem_corner (model.toMat.symm Y)⟩
              (model.toMat.symm Y)⟩ := by
                simp [Ycorner]

/-- Evaluation of the transported map: `transportMap Ψ hΨ X = toMat ⟨Ψ X, hΨ X⟩`. -/
@[simp] theorem MatrixCornerModel.transportMap_apply {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) :
    model.transportMap Ψ hΨ X = model.toMat ⟨Ψ X, hΨ X⟩ := by
  rfl

end HiaiPetz
