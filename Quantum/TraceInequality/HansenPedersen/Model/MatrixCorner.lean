/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetzTheorem.Model.MatrixCorner

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

/-- For a `MatrixCornerModel`, the model map `toMat` is an isometry for the Hilbert–Schmidt
inner product: `⟪toMat X, toMat Y⟫ = ⟪X, Y⟫`. -/
theorem MatrixCornerModel.inner_toMat_eq {m : ℕ} {P : Mₙ m} (model : MatrixCornerModel P)
    (X Y : matrixCornerSubmodule P) :
    inner ℂ (model.toMat X) (model.toMat Y) = inner ℂ X.1 Y.1 := by
  change Matrix.trace (model.toMat Y * Matrix.conjTranspose (model.toMat X)) =
    Matrix.trace (Y.1 * Matrix.conjTranspose X.1)
  calc
    Matrix.trace (model.toMat Y * Matrix.conjTranspose (model.toMat X))
        = Matrix.trace (Matrix.conjTranspose (model.toMat X) * model.toMat Y) := by
            exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (star (model.toMat X) * model.toMat Y) := by
          simp [Matrix.star_eq_conjTranspose]
    _ = Matrix.trace (star X.1 * Y.1) := model.preservesTraceMul X Y
    _ = Matrix.trace (Matrix.conjTranspose X.1 * Y.1) := by
          simp [Matrix.star_eq_conjTranspose]
    _ = Matrix.trace (Y.1 * Matrix.conjTranspose X.1) := by
          exact Matrix.trace_mul_comm _ _

/-- Compatibility of the inverse model map with multiplication. -/
theorem MatrixCornerModel.toMat_symm_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X Y : Mₙ model.dim) :
    model.toMat.symm (X * Y) =
      ⟨(model.toMat.symm X).1 * (model.toMat.symm Y).1,
        model.mul_mem_corner (model.toMat.symm X) (model.toMat.symm Y)⟩ := by
  let Xcorner : matrixCornerSubmodule P := model.toMat.symm X
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  apply model.toMat.injective
  calc
    model.toMat (model.toMat.symm (X * Y)) = X * Y := by simp
    _ = model.toMat Xcorner * model.toMat Ycorner := by simp [Xcorner, Ycorner]
    _ = model.toMat
          ⟨Xcorner.1 * Ycorner.1, model.mul_mem_corner Xcorner Ycorner⟩ := by
            rw [model.map_mul Xcorner Ycorner]
    _ = model.toMat
          ⟨(model.toMat.symm X).1 * (model.toMat.symm Y).1,
            model.mul_mem_corner (model.toMat.symm X) (model.toMat.symm Y)⟩ := by
              simp [Xcorner, Ycorner]

/-- Compatibility of the inverse model map with the adjoint. -/
theorem MatrixCornerModel.toMat_symm_star {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (X : Mₙ model.dim) :
    model.toMat.symm (star X) =
      ⟨star ((model.toMat.symm X).1), model.adjoint_mem_corner (model.toMat.symm X)⟩ := by
  let Xcorner : matrixCornerSubmodule P := model.toMat.symm X
  apply model.toMat.injective
  calc
    model.toMat (model.toMat.symm (star X)) = star X := by simp
    _ = star (model.toMat Xcorner) := by simp [Xcorner]
    _ = model.toMat ⟨star Xcorner.1, model.adjoint_mem_corner Xcorner⟩ := by
          rw [model.preservesAdjoint Xcorner]
    _ = model.toMat
          ⟨star ((model.toMat.symm X).1), model.adjoint_mem_corner (model.toMat.symm X)⟩ := by
            simp [Xcorner]

/-- Inner-product adjunction for the transported map:
`⟪transportMap Ψ hΨ X, Y⟫ = ⟪Ψ X, toMat.symm Y⟫`. -/
theorem MatrixCornerModel.inner_transportMap_apply {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) (Y : Mₙ model.dim) :
    inner ℂ (model.transportMap Ψ hΨ X) Y = inner ℂ (Ψ X) (model.toMat.symm Y).1 := by
  rw [MatrixCornerModel.transportMap_apply]
  simpa using model.inner_toMat_eq ⟨Ψ X, hΨ X⟩ (model.toMat.symm Y)

/-- The conjugate form of the inner-product adjunction:
`⟪Y, transportMap Ψ hΨ X⟫ = ⟪toMat.symm Y, Ψ X⟫`. -/
theorem MatrixCornerModel.inner_transportMap_apply_flip {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) (Y : Mₙ model.dim) :
    inner ℂ Y (model.transportMap Ψ hΨ X) = inner ℂ (model.toMat.symm Y).1 (Ψ X) := by
  have h :=
    congrArg star (model.inner_transportMap_apply Ψ hΨ X Y)
  simpa [inner_conj_symm] using h

/-- The Hilbert–Schmidt adjoint of the transported map is the transport of the adjoint:
`hsAdjoint (transportMap Ψ hΨ) Y = hsAdjoint Ψ (toMat.symm Y)`. -/
theorem MatrixCornerModel.hsAdjoint_transportMap_apply {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (Y : Mₙ model.dim) :
    hsAdjoint (model.transportMap Ψ hΨ) Y =
      hsAdjoint Ψ (model.toMat.symm Y).1 := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  letI := instMatrixNormedAddCommGroup (n := m)
  letI := instMatrixNormedSpace (n := m)
  letI := instMatrixInnerProductSpace (n := m)
  letI := instMatrixCompleteSpace (n := m)
  letI := instMatrixNormedAddCommGroup (n := model.dim)
  letI := instMatrixNormedSpace (n := model.dim)
  letI := instMatrixInnerProductSpace (n := model.dim)
  letI := instMatrixCompleteSpace (n := model.dim)
  let T : HSMap n model.dim := model.transportMap Ψ hΨ
  let Z : Mₙ m := (model.toMat.symm Y).1
  apply (@ext_inner_right ℂ (Mₙ n) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)))
  intro X
  have hAdjT :
      inner ℂ (hsAdjoint T Y) X = inner ℂ Y (T X) := by
    simpa [hsAdjoint, T] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ model.dim)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := model.dim))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := model.dim))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := model.dim))
        T X Y)
  have hAdjΨ :
      inner ℂ (hsAdjoint Ψ Z) X = inner ℂ Z (Ψ X) := by
    simpa [hsAdjoint, Z] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ m)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := m))
        Ψ X Z)
  exact hAdjT.trans <| (model.inner_transportMap_apply_flip Ψ hΨ X Y).trans hAdjΨ.symm

/-- Compatibility of the inverse model map with `Y * star Y`: `toMat.symm (Y * star Y)`
equals the corner element `(toMat.symm Y) * star (toMat.symm Y)`. -/
theorem MatrixCornerModel.toMat_symm_mul_star {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y : Mₙ model.dim) :
    model.toMat.symm (Y * star Y) =
      ⟨(model.toMat.symm Y).1 * star ((model.toMat.symm Y).1),
        model.mul_mem_corner (model.toMat.symm Y)
          ⟨star ((model.toMat.symm Y).1), model.adjoint_mem_corner (model.toMat.symm Y)⟩⟩
            := by
  let Ycorner : matrixCornerSubmodule P := model.toMat.symm Y
  let Ystar : matrixCornerSubmodule P := ⟨star Ycorner.1, model.adjoint_mem_corner Ycorner⟩
  apply model.toMat.injective
  calc
    model.toMat (model.toMat.symm (Y * star Y)) = Y * star Y := by simp
    _ = model.toMat Ycorner * star (model.toMat Ycorner) := by simp [Ycorner]
    _ = model.toMat Ycorner * model.toMat Ystar := by
          rw [model.preservesAdjoint Ycorner]
    _ = model.toMat
          ⟨Ycorner.1 * Ystar.1, model.mul_mem_corner Ycorner Ystar⟩ := by
            rw [model.map_mul Ycorner Ystar]
    _ = model.toMat
          ⟨(model.toMat.symm Y).1 * star ((model.toMat.symm Y).1),
            model.mul_mem_corner (model.toMat.symm Y)
              ⟨star ((model.toMat.symm Y).1), model.adjoint_mem_corner (model.toMat.symm
                Y)⟩⟩ := by
            simp [Ycorner, Ystar]

-- The theorem head re-triggers the same `InnerProductSpace` synthesis as the reduction layer.
-- The associated matrix-basis typeclass synthesis is also deterministic but heavy.
-- The unit transport theorem shares the same finite-dimensional elaboration hotspot.
-- The associated basis/typeclass synthesis needs the same local budget.

/-- The linear equivalence between algebraic endomorphisms and continuous linear
endomorphisms of the finite-dimensional Euclidean support subspace, via
`LinearMap.toContinuousLinearMap`. -/
noncomputable def outputSupportEuclideanEndToContinuousLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →L[ℂ] outputSupportEuclideanSubspace Φ) :=
  LinearMap.toContinuousLinearMap

/-- `outputSupportEuclideanEndToContinuousLinearEquiv Φ` is multiplicative (sends
composition to composition). -/
theorem outputSupportEuclideanEndToContinuousLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (T S : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :
    outputSupportEuclideanEndToContinuousLinearEquiv Φ (T * S) =
      outputSupportEuclideanEndToContinuousLinearEquiv Φ T *
        outputSupportEuclideanEndToContinuousLinearEquiv Φ S := by
  rfl

/-- The composite equivalence from the corner `P Mₘ P` to continuous linear endomorphisms
of the Euclidean support subspace. -/
noncomputable def outputCornerToEuclideanContinuousLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →L[ℂ] outputSupportEuclideanSubspace Φ) :=
  (outputCornerToEuclideanEndLinearEquiv Φ).trans
    (outputSupportEuclideanEndToContinuousLinearEquiv Φ)

/-- `outputCornerToEuclideanContinuousLinearEquiv Φ` is multiplicative: it sends `X * Y`
to the composition of the corresponding continuous endomorphisms. -/
theorem outputCornerToEuclideanContinuousLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToEuclideanContinuousLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToEuclideanContinuousLinearEquiv Φ X *
        outputCornerToEuclideanContinuousLinearEquiv Φ Y := by
  simp [outputCornerToEuclideanContinuousLinearEquiv, outputCornerToEuclideanEndLinearEquiv_mul,
    outputSupportEuclideanEndToContinuousLinearEquiv_mul]

end HiaiPetz
