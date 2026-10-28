/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.SupportCorners
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.Support.Corner
import Quantum.TraceInequality.HiaiPetzTheorem.Model.MatrixCorner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.SupportCorners

/-!
# Output-support corner models

This module contains the orthonormal Euclidean corner model and Hilbert--Schmidt
transport API for the output-support stage of Hiai--Petz 6.2.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOutputSupportHSOpCStarAlgebra
  instOutputSupportHSOpStarRing
  instOutputSupportHSOpComplexAlgebra
  instOutputSupportHSOpNormedAlgebra
  instOutputSupportHSOpPartialOrder
  instOutputSupportHSOpStarOrderedRing
  instOutputSupportHSOpNonnegSpectrumClass
  instOutputSupportHSOpComplexCFC
  instOutputSupportHSOpRealCFC
  outputSupportBridgeMatrixNormedAddCommGroup
  outputSupportBridgeMatrixNormedSpace
  outputSupportBridgeMatrixInnerProductSpace
  outputSupportBridgeMatrixCompleteSpace
  outputSupportBridgeMatrixFiniteDimensional

noncomputable section

/-! ### Orthonormal Euclidean Corner Model -/

noncomputable abbrev outputSupportEuclideanSubspace {n m : ℕ} (Φ : HSMap n m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  _root_.HiaiPetz.outputSupportEuclideanSubspace Φ

@[simp]
theorem outputSupportProj_toEuclideanLin {n m : ℕ} (Φ : HSMap n m) :
    Matrix.toEuclideanLin (outputSupportProj Φ) =
      (Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin m))
        (outputSupportEuclideanSubspace Φ)).toLinearMap := by
  exact _root_.HiaiPetz.outputSupportProj_toEuclideanLin Φ

/-- The Euclidean output-support subspace equals the range of the Euclidean linear map of the
output `Φ(1)`. -/
theorem outputSupportEuclideanSubspace_eq_range_toEuclideanLin {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEuclideanSubspace Φ = LinearMap.range (Matrix.toEuclideanLin (Φ (1 : Mₙ n))) := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, hv, hEq⟩
    rcases hv with ⟨x, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_⟩
    exact (Matrix.toLpLin_toLp (p := 2) (q := 2) (Φ (1 : Mₙ n)) x).trans hEq
  · rintro ⟨x, rfl⟩
    refine ⟨(Φ (1 : Mₙ n)).mulVec (WithLp.ofLp x), ?_, ?_⟩
    · exact ⟨WithLp.ofLp x, rfl⟩
    · simpa using (Matrix.toLpLin_apply (p := 2) (q := 2) (Φ (1 : Mₙ n)) x).symm

theorem outputSupportEuclideanSubspace_eq_top_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    outputSupportEuclideanSubspace Φ = ⊤ := by
  rw [outputSupportEuclideanSubspace_eq_range_toEuclideanLin]
  apply LinearMap.range_eq_top.2
  have hUnit : IsUnit (Φ (1 : Mₙ n)) := matrixPosDef_isUnit hΦ1
  exact LinearMap.injective_iff_surjective.mp <| by
    intro u v huv
    have huv' :
        (Φ (1 : Mₙ n)).mulVec (WithLp.ofLp u) = (Φ (1 : Mₙ n)).mulVec (WithLp.ofLp v) := by
      simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp huv
    have huv0 : WithLp.ofLp u = WithLp.ofLp v :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hUnit) huv'
    exact (WithLp.ofLp_injective (p := 2)) huv0

/-- A corner matrix supported on the output-support projection annihilates the orthogonal
complement of the Euclidean output-support subspace. -/
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
  have hXP : X.1 * outputSupportProj Φ = X.1 :=
    OutputSupportProj.right_mul_eq_self_of_mem (Φ := Φ) X.2
  have hXu : X.1.mulVec (WithLp.ofLp u.1) = 0 := by
    have hfix := congrArg (fun M : Mₙ m => M.mulVec (WithLp.ofLp u.1)) hXP.symm
    have hfix' :
        X.1.mulVec (WithLp.ofLp u.1) =
          X.1.mulVec ((outputSupportProj Φ).mulVec (WithLp.ofLp u.1)) := by
      simpa [Matrix.mulVec_mulVec] using hfix
    rw [hPuVec] at hfix'
    simpa using hfix'
  simpa [Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) hXu

/-- The linear equivalence between the Euclidean output-support subspace and the abstract
output-support subspace, via the coordinate identification of `EuclideanSpace ℂ (Fin m)`. -/
noncomputable abbrev outputSupportEuclideanSubspaceLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEuclideanSubspace Φ ≃ₗ[ℂ] outputSupportSubspace Φ :=
  _root_.HiaiPetz.outputSupportEuclideanSubspaceLinearEquiv Φ

/-- The conjugation equivalence between endomorphisms of the abstract output-support subspace and
endomorphisms of its Euclidean model. -/
noncomputable abbrev outputSupportEndToEuclideanEndLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :=
  _root_.HiaiPetz.outputSupportEndToEuclideanEndLinearEquiv Φ

/-- Pointwise value of the endomorphism transport equivalence. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (T : outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ)
    (u : outputSupportEuclideanSubspace Φ) :
    outputSupportEndToEuclideanEndLinearEquiv Φ T u =
      (outputSupportEuclideanSubspaceLinearEquiv Φ).symm
        (T ((outputSupportEuclideanSubspaceLinearEquiv Φ) u)) := by
  rfl

/-- The endomorphism transport equivalence is multiplicative. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (T S : outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) :
    outputSupportEndToEuclideanEndLinearEquiv Φ (T * S) =
      outputSupportEndToEuclideanEndLinearEquiv Φ T *
        outputSupportEndToEuclideanEndLinearEquiv Φ S := by
  simpa [Module.End.mul_eq_comp] using
    LinearEquiv.conj_comp (outputSupportEuclideanSubspaceLinearEquiv Φ).symm S T

/-- The endomorphism transport equivalence sends the identity to the identity. -/
theorem outputSupportEndToEuclideanEndLinearEquiv_id {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEndToEuclideanEndLinearEquiv Φ LinearMap.id = LinearMap.id := by
  ext u i
  simp [outputSupportEndToEuclideanEndLinearEquiv_apply]

noncomputable abbrev outputCornerToEuclideanEndLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :=
  _root_.HiaiPetz.outputCornerToEuclideanEndLinearEquiv Φ

/-- Pointwise value of the corner-to-Euclidean-endomorphism equivalence. -/
theorem outputCornerToEuclideanEndLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) (u : outputSupportEuclideanSubspace Φ) :
    outputCornerToEuclideanEndLinearEquiv Φ X u =
      (outputSupportEuclideanSubspaceLinearEquiv Φ).symm
        ((outputCornerSubspaceLinearEquiv Φ X)
          ((outputSupportEuclideanSubspaceLinearEquiv Φ) u)) := by
  rfl

@[simp] theorem outputCornerToEuclideanEndLinearEquiv_apply_coe {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) (u : outputSupportEuclideanSubspace Φ) :
    ((outputCornerToEuclideanEndLinearEquiv Φ X u : outputSupportEuclideanSubspace Φ) :
        EuclideanSpace ℂ (Fin m)) =
      Matrix.toEuclideanLin X.1 u.1 := by
  ext i
  rfl

/-- The corner-to-Euclidean-endomorphism equivalence intertwines the matrix star (conjugate
transpose) with the operator adjoint, expressed through the inner product. -/
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
  exact _root_.HiaiPetz.outputCornerToEuclideanEndLinearEquiv_star_inner Φ X

theorem outputCornerToEuclideanEndLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToEuclideanEndLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToEuclideanEndLinearEquiv Φ X *
        outputCornerToEuclideanEndLinearEquiv Φ Y := by
  exact _root_.HiaiPetz.outputCornerToEuclideanEndLinearEquiv_mul Φ X Y

theorem outputCornerToEuclideanEndLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToEuclideanEndLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = LinearMap.id := by
  exact _root_.HiaiPetz.outputCornerToEuclideanEndLinearEquiv_proj Φ

/-- A `Fin`-indexed linear basis of the Euclidean output-support subspace. -/
noncomputable def outputSupportEuclideanBasis {n m : ℕ} (Φ : HSMap n m) :
    Module.Basis (Fin (Module.finrank ℂ (outputSupportEuclideanSubspace Φ))) ℂ
      (outputSupportEuclideanSubspace Φ) :=
  let b := Module.Basis.ofVectorSpace ℂ (outputSupportEuclideanSubspace Φ)
  b.reindex (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm)

/-- The linear equivalence between endomorphisms of the Euclidean output-support subspace and
square matrices, via the chosen basis. -/
noncomputable def outputSupportEuclideanToMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  LinearMap.toMatrix (outputSupportEuclideanBasis Φ) (outputSupportEuclideanBasis Φ)

/-- The linear equivalence between the output-support corner algebra and a square-matrix algebra,
composing the corner-to-endomorphism and endomorphism-to-matrix equivalences. [hiai2025] -/
noncomputable def outputCornerToEuclideanMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  (outputCornerToEuclideanEndLinearEquiv Φ).trans (outputSupportEuclideanToMatrixLinearEquiv Φ)

/-- The corner-to-matrix equivalence is multiplicative. -/
theorem outputCornerToEuclideanMatrixLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToEuclideanMatrixLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToEuclideanMatrixLinearEquiv Φ X *
        outputCornerToEuclideanMatrixLinearEquiv Φ Y := by
  simp [outputCornerToEuclideanMatrixLinearEquiv, outputCornerToEuclideanEndLinearEquiv_mul,
    outputSupportEuclideanToMatrixLinearEquiv, LinearMap.toMatrix_mul]

/-- The corner-to-matrix equivalence sends the support projection to the identity matrix. -/
theorem outputCornerToEuclideanMatrixLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToEuclideanMatrixLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = 1 := by
  simp [outputCornerToEuclideanMatrixLinearEquiv, outputSupportEuclideanToMatrixLinearEquiv,
    outputCornerToEuclideanEndLinearEquiv_proj]

-- Building the finite-dimensional Hilbert basis representation is instance-heavy.
/-- The isometric identification of the Euclidean output-support subspace with a standard Euclidean
space of its dimension, via a standard orthonormal basis. -/
noncomputable def outputSupportEuclideanRepr {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEuclideanSubspace Φ ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ (outputSupportEuclideanSubspace Φ))) :=
  (stdOrthonormalBasis ℂ (outputSupportEuclideanSubspace Φ)).repr

noncomputable abbrev outputSupportEuclideanOrthonormalBasis {n m : ℕ} (Φ : HSMap n m) :
    OrthonormalBasis (Fin (Module.finrank ℂ (outputSupportEuclideanSubspace Φ))) ℂ
      (outputSupportEuclideanSubspace Φ) :=
  _root_.HiaiPetz.outputSupportEuclideanOrthonormalBasis Φ

/-- The linear equivalence between endomorphisms of the Euclidean output-support subspace and
square matrices via the standard orthonormal basis, so the matrix is the operator's matrix in an
orthonormal frame. -/
noncomputable abbrev outputSupportEuclideanToOrthonormalMatrixLinearEquiv {n m : ℕ}
    (Φ : HSMap n m) :
    (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  _root_.HiaiPetz.outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ

-- The theorem head re-triggers the same `InnerProductSpace` synthesis as the reduction layer.
-- The associated matrix-basis typeclass synthesis is also deterministic but heavy.
theorem outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff {n m : ℕ}
    (Φ : HSMap n m) (T : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :
    (outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ T).PosSemidef ↔
      @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _ T := by
  exact _root_.HiaiPetz.outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff Φ T

-- The unit transport theorem shares the same finite-dimensional elaboration hotspot.
-- The associated basis/typeclass synthesis needs the same local budget.
theorem outputSupportEuclideanToOrthonormalMatrixLinearEquiv_isUnit_iff {n m : ℕ}
    (Φ : HSMap n m) (T : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :
    IsUnit (outputSupportEuclideanToOrthonormalMatrixLinearEquiv Φ T) ↔ IsUnit T := by
  exact _root_.HiaiPetz.outputSupportEuclideanToOrthonormalMatrixLinearEquiv_isUnit_iff Φ T

noncomputable abbrev outputCornerToOrthonormalMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportEuclideanSubspace Φ)) :=
  _root_.HiaiPetz.outputCornerToOrthonormalMatrixLinearEquiv Φ

theorem outputCornerToOrthonormalMatrixLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToOrthonormalMatrixLinearEquiv Φ X *
        outputCornerToOrthonormalMatrixLinearEquiv Φ Y := by
  exact _root_.HiaiPetz.outputCornerToOrthonormalMatrixLinearEquiv_mul Φ X Y

theorem outputCornerToOrthonormalMatrixLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = 1 := by
  exact _root_.HiaiPetz.outputCornerToOrthonormalMatrixLinearEquiv_proj Φ

theorem outputCornerToOrthonormalMatrixLinearEquiv_star {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToOrthonormalMatrixLinearEquiv Φ
      ⟨star X.1, outputCorner_star_mem Φ X⟩ =
      star (outputCornerToOrthonormalMatrixLinearEquiv Φ X) := by
  exact _root_.HiaiPetz.outputCornerToOrthonormalMatrixLinearEquiv_star Φ X

@[simp] theorem trace_toEuclideanLin_eq_matrix_trace {m : ℕ} (A : Mₙ m) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin m)) (Matrix.toEuclideanLin A) = Matrix.trace A := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]

theorem outputCornerToOrthonormalMatrixLinearEquiv_trace {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    Matrix.trace (outputCornerToOrthonormalMatrixLinearEquiv Φ X) = Matrix.trace X.1 := by
  let U := outputSupportEuclideanSubspace Φ
  let A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := Matrix.toEuclideanLin X.1
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

/-- Loewner-surface compatibility name for the canonical matrix corner model.
The two former structures had field-for-field identical bodies.
Source: the Hiai--Petz matrix setup, `HiaiPetz.MatrixCornerModel`. -/
abbrev MatrixCornerModel {m : ℕ} (P : Mₙ m) :=
  _root_.HiaiPetz.MatrixCornerModel P

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

theorem MatrixCornerModel.toMat_symm_star_mul {m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Y : Mₙ model.dim) :
    model.toMat.symm (star Y * Y) =
      ⟨star ((model.toMat.symm Y).1) * (model.toMat.symm Y).1,
        model.mul_mem_corner
          ⟨star ((model.toMat.symm Y).1), model.adjoint_mem_corner (model.toMat.symm Y)⟩
          (model.toMat.symm Y)⟩ := by
  exact _root_.HiaiPetz.MatrixCornerModel.toMat_symm_star_mul model Y

noncomputable abbrev MatrixCornerModel.transportMap {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) :
    HSMap n model.dim :=
  _root_.HiaiPetz.MatrixCornerModel.transportMap model Ψ hΨ

@[simp]
theorem MatrixCornerModel.transportMap_apply {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) :
    model.transportMap Ψ hΨ X = model.toMat ⟨Ψ X, hΨ X⟩ := by
  rfl

theorem MatrixCornerModel.inner_transportMap_apply {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) (Y : Mₙ model.dim) :
    inner ℂ (model.transportMap Ψ hΨ X) Y = inner ℂ (Ψ X) (model.toMat.symm Y).1 := by
  rw [MatrixCornerModel.transportMap_apply]
  simpa using model.inner_toMat_eq ⟨Ψ X, hΨ X⟩ (model.toMat.symm Y)

theorem MatrixCornerModel.inner_transportMap_apply_flip {n m : ℕ} {P : Mₙ m}
    (model : MatrixCornerModel P) (Ψ : HSMap n m)
    (hΨ : ∀ X, Ψ X ∈ matrixCornerSubmodule P) (X : Mₙ n) (Y : Mₙ model.dim) :
    inner ℂ Y (model.transportMap Ψ hΨ X) = inner ℂ (model.toMat.symm Y).1 (Ψ X) := by
  have h :=
    congrArg star (model.inner_transportMap_apply Ψ hΨ X Y)
  simpa [inner_conj_symm] using h

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

noncomputable abbrev outputSupportMatrixCornerModel {n m : ℕ} (Φ : HSMap n m) :
    MatrixCornerModel (outputSupportProj Φ) :=
  _root_.HiaiPetz.outputSupportMatrixCornerModel Φ

end

end Quantum.TraceInequality.Loewner.HiaiPetz
