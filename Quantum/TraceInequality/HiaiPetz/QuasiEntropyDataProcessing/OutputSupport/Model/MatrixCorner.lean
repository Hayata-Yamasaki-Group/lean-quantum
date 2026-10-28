/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic

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

/-- The standard orthonormal basis of the Euclidean support subspace, indexed by `Fin d`. -/
noncomputable def outputSupportEuclideanOrthonormalBasis {n m : ℕ} (Φ : HSMap n m) :
    OrthonormalBasis (Fin (Module.finrank ℂ (outputSupportEuclideanSubspace Φ))) ℂ
      (outputSupportEuclideanSubspace Φ) :=
  stdOrthonormalBasis ℂ (outputSupportEuclideanSubspace Φ)

/-- The linear equivalence between endomorphisms of the Euclidean support subspace and
`d × d` matrices, via `LinearMap.toMatrix` in the orthonormal basis
`outputSupportEuclideanOrthonormalBasis Φ`. Using an orthonormal basis makes it compatible
with adjoints and trace. -/
noncomputable def outputSupportEuclideanToOrthonormalMatrixLinearEquiv {n m : ℕ}
    (Φ : HSMap n m) :
    (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  LinearMap.toMatrix (outputSupportEuclideanOrthonormalBasis Φ).toBasis
    (outputSupportEuclideanOrthonormalBasis Φ).toBasis

/-- The composite equivalence from the corner `P Mₘ P` to `d × d` matrices through the
Euclidean endomorphisms, using the orthonormal basis. This is the model map that also
preserves adjoint and trace. -/
noncomputable def outputCornerToOrthonormalMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  (outputCornerToEuclideanEndLinearEquiv Φ).trans
    (outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ)

/-- `outputCornerToOrthonormalMatrixLinearEquiv Φ` is multiplicative: it sends `X * Y` to
the product of the corresponding matrices. -/
theorem outputCornerToOrthonormalMatrixLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToOrthonormalMatrixLinearEquiv Φ X *
        outputCornerToOrthonormalMatrixLinearEquiv Φ Y := by
  simp [outputCornerToOrthonormalMatrixLinearEquiv,
    outputSupportEuclideanToOrthonormalMatrixLinearEquiv,
    outputCornerToEuclideanEndLinearEquiv_mul, LinearMap.toMatrix_mul]

/-- `outputCornerToOrthonormalMatrixLinearEquiv Φ` sends the projection `P` (as a corner
element) to the identity matrix `1`. -/
theorem outputCornerToOrthonormalMatrixLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = 1 := by
  simpa [outputCornerToOrthonormalMatrixLinearEquiv,
    outputSupportEuclideanToOrthonormalMatrixLinearEquiv,
    outputCornerToEuclideanEndLinearEquiv_proj] using
    (outputSupportEuclideanOrthonormalBasis Φ).toBasis.toMatrix_self

/-- The orthonormal model map intertwines the matrix adjoint with the corner adjoint: it
sends `star X` to `star` of the matrix image of `X`. -/
theorem outputCornerToOrthonormalMatrixLinearEquiv_star {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨star X.1, outputCorner_star_mem Φ X⟩ =
      star (outputCornerToOrthonormalMatrixLinearEquiv Φ X) := by
  ext i j
  let b := outputSupportEuclideanOrthonormalBasis Φ
  have hinner := outputCornerToEuclideanEndLinearEquiv_star_inner Φ X (b j) (b i)
  calc
    outputCornerToOrthonormalMatrixLinearEquiv Φ
        ⟨star X.1, outputCorner_star_mem Φ X⟩ i j
        = inner ℂ
            ((b i : outputSupportEuclideanSubspace Φ) : EuclideanSpace ℂ (Fin m))
            ((((outputCornerToEuclideanEndLinearEquiv Φ
                ⟨star X.1, outputCorner_star_mem Φ X⟩) (b j) :
                  outputSupportEuclideanSubspace Φ) :
                EuclideanSpace ℂ (Fin m))) := by
            simp [outputCornerToOrthonormalMatrixLinearEquiv,
              outputSupportEuclideanToOrthonormalMatrixLinearEquiv, b,
              LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
              OrthonormalBasis.repr_apply_apply]
    _ = star
          (inner ℂ
            ((((outputCornerToEuclideanEndLinearEquiv Φ
                ⟨star X.1, outputCorner_star_mem Φ X⟩) (b j) :
                  outputSupportEuclideanSubspace Φ) :
                EuclideanSpace ℂ (Fin m)))
            ((b i : outputSupportEuclideanSubspace Φ) : EuclideanSpace ℂ (Fin m))) := by
          rw [← inner_conj_symm]
          rfl
    _ = star
          (inner ℂ
            ((b j : outputSupportEuclideanSubspace Φ) : EuclideanSpace ℂ (Fin m))
            ((((outputCornerToEuclideanEndLinearEquiv Φ X) (b i) :
                  outputSupportEuclideanSubspace Φ) :
                EuclideanSpace ℂ (Fin m)))) := by
          rw [hinner]
    _ = star (outputCornerToOrthonormalMatrixLinearEquiv Φ X j i) := by
          simp [outputCornerToOrthonormalMatrixLinearEquiv,
            outputSupportEuclideanToOrthonormalMatrixLinearEquiv, b,
            LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
            OrthonormalBasis.repr_apply_apply]
    _ = star (outputCornerToOrthonormalMatrixLinearEquiv Φ X) i j := by
          simp

/-- The operator trace of the Euclidean linear map of a matrix `A` equals the matrix
trace of `A`. -/
@[simp] theorem trace_toEuclideanLin_eq_matrix_trace {m : ℕ} (A : Mₙ m) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin m)) (Matrix.toEuclideanLin A) = Matrix.trace A
      := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- The orthonormal model map preserves trace: the matrix trace of the image equals the
matrix trace of the corner element `X`. -/
theorem outputCornerToOrthonormalMatrixLinearEquiv_trace {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    Matrix.trace (outputCornerToOrthonormalMatrixLinearEquiv Φ X) = Matrix.trace X.1 := by
  let U := outputSupportEuclideanSubspace Φ
  let A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin X.1
  let N : Bool → Submodule ℂ (EuclideanSpace ℂ (Fin m)) := fun b => cond b U Uᗮ
  have hInternal : DirectSum.IsInternal N := by
    have hBool : (Set.univ : Set Bool) = ({true, false} : Set Bool) := by
      ext b
      cases b <;> simp
    refine (DirectSum.isInternal_submodule_iff_isCompl N (by decide : true ≠ false) hBool).2 ?_
    simpa [N] using (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := U))
  have hMapsU : Set.MapsTo A (N true) (N true) := by
    intro u hu
    let uu : outputSupportEuclideanSubspace Φ := ⟨u, by simpa [N, U] using hu⟩
    simpa [A, N, U] using (outputCornerToEuclideanEndLinearEquiv Φ X uu).2
  have hMapsOrth : Set.MapsTo A (N false) (N false) := by
    intro u hu
    let uu : Uᗮ := ⟨u, by simpa [N, U] using hu⟩
    have huu : A u = 0 := by
      change Matrix.toEuclideanLin X.1 uu.1 = 0
      exact outputCornerToEuclideanLin_apply_eq_zero_of_mem_orthogonal Φ X uu
    simp [N, U, huu]
  have hRestrictU :
      A.restrict hMapsU = outputCornerToEuclideanEndLinearEquiv Φ X := by
    ext u
    rfl
  have hRestrictOrth : A.restrict hMapsOrth = 0 := by
    ext u i
    have huu : A u = 0 := by
      change Matrix.toEuclideanLin X.1 u.1 = 0
      exact outputCornerToEuclideanLin_apply_eq_zero_of_mem_orthogonal Φ X u
    simp [huu]
  have htrace :
      LinearMap.trace ℂ (EuclideanSpace ℂ (Fin m)) A =
        LinearMap.trace ℂ (N true) (A.restrict hMapsU) +
          LinearMap.trace ℂ (N false) (A.restrict hMapsOrth) := by
    simpa [N, Fintype.sum_bool] using
      (LinearMap.trace_eq_sum_trace_restrict (R := ℂ) (N := N) hInternal
        (fun b => by
          cases b
          · simpa [N] using hMapsOrth
          · simpa [N] using hMapsU) : _)
  calc
    Matrix.trace (outputCornerToOrthonormalMatrixLinearEquiv Φ X)
        = LinearMap.trace ℂ (outputSupportEuclideanSubspace Φ)
            (outputCornerToEuclideanEndLinearEquiv Φ X) := by
              simpa [outputCornerToOrthonormalMatrixLinearEquiv,
                outputSupportEuclideanToOrthonormalMatrixLinearEquiv] using
                (LinearMap.trace_eq_matrix_trace (R := ℂ)
                  (b := (outputSupportEuclideanOrthonormalBasis Φ).toBasis)
                  (f := outputCornerToEuclideanEndLinearEquiv Φ X)).symm
    _ = LinearMap.trace ℂ (N true) (A.restrict hMapsU) := by
          simpa [N, U] using
            congrArg (LinearMap.trace ℂ (N true)) hRestrictU.symm
    _ = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin m)) A := by
          symm
          rw [htrace, hRestrictOrth]
          simp
    _ = Matrix.trace X.1 := by simp [A]

/-- A concrete matrix model for a support corner `P M_m P`: a linear equivalence with the
matrix algebra of the corner's dimension, together with the compatibility fields making it a
Hilbert--Schmidt isometric realization (trace pairing, adjoints, products, and the unit). -/
structure MatrixCornerModel {m : ℕ} (P : Mₙ m) where
  dim : ℕ
  toMat : matrixCornerSubmodule P ≃ₗ[ℂ] Mₙ dim
  preservesTraceMul :
    ∀ X Y : matrixCornerSubmodule P,
      Matrix.trace (star (toMat X) * toMat Y) = Matrix.trace (star X.1 * Y.1)
  adjoint_mem_corner :
    ∀ X : matrixCornerSubmodule P, star X.1 ∈ matrixCornerSubmodule P
  preservesAdjoint :
    ∀ X : matrixCornerSubmodule P,
      toMat ⟨star X.1, adjoint_mem_corner X⟩ = star (toMat X)
  mul_mem_corner :
    ∀ X Y : matrixCornerSubmodule P, X.1 * Y.1 ∈ matrixCornerSubmodule P
  map_mul :
    ∀ X Y : matrixCornerSubmodule P,
      toMat ⟨X.1 * Y.1, mul_mem_corner X Y⟩ = toMat X * toMat Y
  proj_mem_corner :
    P ∈ matrixCornerSubmodule P
  map_proj :
    toMat ⟨P, proj_mem_corner⟩ = 1

/-- Transports a map `Ψ : HSMap n m` whose image lies in the corner `P Mₘ P` to a map
`HSMap n model.dim`, by post-composing with the model isomorphism `toMat`. -/
noncomputable def MatrixCornerModel.transportMap {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) :
    HSMap n model.dim :=
  (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (Ψ.codRestrict (matrixCornerSubmodule P) hΨ)

/-- The concrete `MatrixCornerModel` for the output-support corner of `Φ`, with
`dim = finrank ℂ (outputSupportEuclideanSubspace Φ)` and
`toMat = outputCornerToOrthonormalMatrixLinearEquiv Φ`, assembling the multiplicativity,
adjoint, trace and projection lemmas proved above. -/
noncomputable def outputSupportMatrixCornerModel {n m : ℕ} (Φ : HSMap n m) :
    MatrixCornerModel (outputSupportProj Φ) where
  dim := Module.finrank ℂ (outputSupportEuclideanSubspace Φ)
  toMat := outputCornerToOrthonormalMatrixLinearEquiv Φ
  preservesTraceMul := by
    intro X Y
    let Xstar : matrixCornerSubmodule (outputSupportProj Φ) :=
      ⟨star X.1, outputCorner_star_mem Φ X⟩
    calc
      Matrix.trace
          (star (outputCornerToOrthonormalMatrixLinearEquiv Φ X) *
            outputCornerToOrthonormalMatrixLinearEquiv Φ Y)
          = Matrix.trace
              (outputCornerToOrthonormalMatrixLinearEquiv Φ
                ⟨star X.1 * Y.1, outputCorner_mul_mem Φ Xstar Y⟩) := by
                  rw [← outputCornerToOrthonormalMatrixLinearEquiv_star Φ X,
                    ← outputCornerToOrthonormalMatrixLinearEquiv_mul Φ Xstar Y]
      _ = Matrix.trace (star X.1 * Y.1) := by
            simpa [Xstar] using
              outputCornerToOrthonormalMatrixLinearEquiv_trace Φ
                ⟨star X.1 * Y.1, outputCorner_mul_mem Φ Xstar Y⟩
  adjoint_mem_corner := outputCorner_star_mem Φ
  preservesAdjoint := outputCornerToOrthonormalMatrixLinearEquiv_star Φ
  mul_mem_corner := outputCorner_mul_mem Φ
  map_mul := outputCornerToOrthonormalMatrixLinearEquiv_mul Φ
  proj_mem_corner := outputSupportProj_mem_outputCorner Φ
  map_proj := outputCornerToOrthonormalMatrixLinearEquiv_proj Φ

end HiaiPetz
