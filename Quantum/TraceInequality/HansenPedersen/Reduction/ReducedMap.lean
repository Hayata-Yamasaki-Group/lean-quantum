/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map
import Quantum.TraceInequality.HansenPedersen.MapVocabulary
import Quantum.TraceInequality.HansenPedersen.Model.Basic
import Quantum.TraceInequality.HansenPedersen.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetzTheorem.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap

namespace HiaiPetz
open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.L2Operator
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

private theorem outputSupportUnitToEuclideanEnd_ker_eq_bot {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    LinearMap.ker (outputSupportUnitToEuclideanEnd Φ hPos) = ⊥ := by
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  have hTsymm : T.IsSymmetric := hTpos.isSymmetric
  ext u
  constructor
  · intro hu
    have hu0 :
        outputSupportUnitToEuclideanEnd Φ hPos u = 0 := by
      simpa [outputSupportUnitToEuclideanEnd, LinearMap.mem_ker] using hu
    have huTzero : T u.1 = 0 := by
      have hu0' :
          (((outputSupportUnitToEuclideanEnd Φ hPos) u :
                outputSupportEuclideanSubspace Φ) :
              EuclideanSpace ℂ (Fin m)) = 0 := by
        simpa using congrArg Subtype.val hu0
      simpa [outputSupportUnitToEuclideanEnd, C, T,
        outputCornerToEuclideanEndLinearEquiv_apply_coe] using hu0'
    have huKer : u.1 ∈ LinearMap.ker T := by
      simpa [LinearMap.mem_ker, T] using huTzero
    have huRange : u.1 ∈ LinearMap.range T := by
      rcases u.2 with ⟨v, hv, hvu⟩
      rcases hv with ⟨x, rfl⟩
      refine ⟨WithLp.toLp 2 x, ?_⟩
      exact (Matrix.toLpLin_toLp (p := 2) (q := 2) C x).trans hvu
    have huOrth : u.1 ∈ (LinearMap.range T)ᗮ := by
      simpa [LinearMap.IsSymmetric.orthogonal_range hTsymm] using huKer
    have huZero : u.1 = 0 := by
      exact (Submodule.disjoint_def.mp (LinearMap.range T).orthogonal_disjoint) _ huRange huOrth
    have : u = 0 := Subtype.ext huZero
    simpa [Submodule.mem_bot] using this
  · intro hu
    rw [Submodule.mem_bot] at hu
    simp [hu]

private theorem outputSupportUnitToEuclideanEnd_isPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _
      (outputSupportUnitToEuclideanEnd Φ hPos) := by
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨?_, ?_⟩
  · intro u v
    change inner ℂ (T u.1) v.1 = inner ℂ u.1 (T v.1)
    simpa [outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.isSymmetric u.1 v.1
  · intro u
    change 0 ≤ RCLike.re (inner ℂ (T u.1) u.1)
    simpa [outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.re_inner_nonneg_left u.1

private theorem outputSupportImageToEuclideanEnd_isPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {A : Mₙ n} (hA : 0 ≤ A) :
    @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _
      (outputCornerToEuclideanEndLinearEquiv Φ
        ⟨Φ A, map_mem_outputCorner Φ hPos A⟩) := by
  let C : Mₙ m := Φ A
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by simpa [C] using hPos hA
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨?_, ?_⟩
  · intro u v
    change inner ℂ (T u.1) v.1 = inner ℂ u.1 (T v.1)
    simpa [C, T, outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.isSymmetric u.1 v.1
  · intro u
    change 0 ≤ RCLike.re (inner ℂ (T u.1) u.1)
    simpa [C, T, outputCornerToEuclideanEndLinearEquiv_apply_coe] using
      hTpos.re_inner_nonneg_left u.1

/-- The output-support reduction before transport to a concrete matrix model: `Φ` with codomain
restricted to the output corner cut out by `outputSupportProj Φ`. -/
noncomputable def outputSupportReducedMapToCorner {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    Mₙ n →L[ℂ] matrixCornerSubmodule (outputSupportProj Φ) :=
  Φ.codRestrict (matrixCornerSubmodule (outputSupportProj Φ))
    (map_mem_outputCorner Φ hPos)

/-- The reduced map sends the identity to a positive-definite matrix: on the output support `Φ 1`
induces a positive operator with trivial kernel, so its matrix model is positive definite. -/
theorem outputSupportReducedMap_one_posDef {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    Matrix.PosDef (outputSupportReducedMap Φ hPos (1 : Mₙ n)) := by
  let F : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ :=
    outputSupportUnitToEuclideanEnd Φ hPos
  have hFpos : @LinearMap.IsPositive ℂ ↥(outputSupportEuclideanSubspace Φ) _ _ _ F := by
    simpa [F] using outputSupportUnitToEuclideanEnd_isPositive Φ hPos
  have hFunit : IsUnit F := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    simpa [F] using outputSupportUnitToEuclideanEnd_ker_eq_bot Φ hPos
  have hMpsd : (outputSupportReducedMap Φ hPos (1 : Mₙ n)).PosSemidef := by
    rw [outputSupportReducedMap_apply]
    simpa [F] using
      (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff Φ F).2 hFpos
  have hMunit : IsUnit (outputSupportReducedMap Φ hPos (1 : Mₙ n)) := by
    rw [outputSupportReducedMap_apply]
    simpa [F] using
      (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_isUnit_iff Φ F).2 hFunit
  have hMposDef : (outputSupportReducedMap Φ hPos (1 : Mₙ n)).PosDef :=
    hMpsd.posDef_iff_isUnit.mpr hMunit
  exact hMposDef

/-- The reduced map is positive: it sends nonnegative matrices to nonnegative matrices. -/
theorem outputSupportReducedMap_isPositiveMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    IsPositiveMap (outputSupportReducedMap Φ hPos) := by
  intro A hA
  rw [Matrix.nonneg_iff_posSemidef, outputSupportReducedMap_apply]
  exact
    (outputSupportEuclideanToOrthonormalMatrixLinearEquiv_posSemidef_iff Φ
      (outputCornerToEuclideanEndLinearEquiv Φ
        ⟨Φ A, map_mem_outputCorner Φ hPos A⟩)).2
      (outputSupportImageToEuclideanEnd_isPositive Φ hPos hA)

/-- If `Φ` is trace preserving, so is the reduced map. -/
theorem outputSupportReducedMap_tracePreserving {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTrace : TracePreserving Φ) :
    TracePreserving (outputSupportReducedMap Φ hPos) := by
  intro X
  rw [outputSupportReducedMap_apply]
  exact
    (outputCornerToOrthonormalMatrixLinearEquiv_trace Φ
      ⟨Φ X, map_mem_outputCorner Φ hPos X⟩).trans (hTrace X)

/-- The Hilbert–Schmidt adjoint of the reduced map, evaluated at `Y`, equals `hsAdjoint Φ`
  applied
to the corner element that `Y` represents in the model. -/
theorem outputSupportReducedMap_hsAdjoint_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    hsAdjoint (outputSupportReducedMap Φ hPos) Y =
      hsAdjoint Φ ((outputSupportMatrixCornerModel Φ).toMat.symm Y).1 := by
  simpa [outputSupportReducedMap] using
    MatrixCornerModel.hsAdjoint_transportMap_apply (outputSupportMatrixCornerModel Φ)
      Φ (map_mem_outputCorner Φ hPos) Y

/-- If `Φ` satisfies the Hilbert–Schmidt adjoint Schwarz inequality, so does the reduced map. -/
theorem outputSupportReducedMap_hsAdjointSchwarz {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ) :
    HSAdjointSchwarz (outputSupportReducedMap Φ hPos) := by
  intro Y
  let model := outputSupportMatrixCornerModel Φ
  let Z : matrixCornerSubmodule (outputSupportProj Φ) := model.toMat.symm Y
  have hZ := hSch Z.1
  have hR :
      hsAdjoint (outputSupportReducedMap Φ hPos) (Matrix.conjTranspose Y * Y) =
        hsAdjoint Φ (Matrix.conjTranspose Z.1 * Z.1) := by
    rw [outputSupportReducedMap_hsAdjoint_apply]
    have hZY :
        ((model.toMat.symm (Matrix.conjTranspose Y * Y)).1) =
          Matrix.conjTranspose Z.1 * Z.1 := by
      simpa [model, Z, Matrix.star_eq_conjTranspose] using
        congrArg Subtype.val (MatrixCornerModel.toMat_symm_star_mul model Y)
    rw [hZY]
  calc
    Matrix.conjTranspose ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y) *
          ((hsAdjoint (outputSupportReducedMap Φ hPos)) Y)
        = Matrix.conjTranspose (hsAdjoint Φ Z.1) * hsAdjoint Φ Z.1 := by
            rw [outputSupportReducedMap_hsAdjoint_apply]
    _ ≤ hsAdjoint Φ (Matrix.conjTranspose Z.1 * Z.1) := hZ
    _ = hsAdjoint (outputSupportReducedMap Φ hPos) (Matrix.conjTranspose Y * Y) := hR.symm

/-- The corner-valued reduction agrees with `Φ`: forgetting the corner membership recovers the
matrix `Φ X`. -/
@[simp] theorem outputSupportReducedMapToCorner_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    ((outputSupportReducedMapToCorner Φ hPos) X : Mₙ m) = Φ X := by
  rfl

/-- Skeleton data for reducing a general-output map to a strict-output map on the output support. -/
structure OutputSupportReductionData {n m : ℕ} (Φ : HSMap n m) where
  proj : Mₙ m
  proj_isProj : IsMatrixProj proj
  model : MatrixCornerModel proj
  reducedMap : HSMap n model.dim
  image_in_corner : ∀ X, matrixCornerProj proj (Φ X) = Φ X
  adjoint_respects_corner : ∀ Y, hsAdjoint Φ (matrixCornerProj proj Y) = hsAdjoint Φ Y

/-- Package the already-proved output-support projection facts once a corner model and a reduced
map have been chosen. The model and the reduced map are `outputSupportMatrixCornerModel` and
`outputSupportReducedMap`, packaged in `outputSupportReductionData` below. -/
noncomputable def outputSupportReductionDataOfModel {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (model : MatrixCornerModel (outputSupportProj Φ))
    (reducedMap : HSMap n model.dim) : OutputSupportReductionData Φ where
  proj := outputSupportProj Φ
  proj_isProj := OutputSupportProj.isProj Φ
  model := model
  reducedMap := reducedMap
  image_in_corner := phi_image_eq_outputCornerProj Φ hPos
  adjoint_respects_corner := hsAdjoint_matrixCornerProj_eq Φ hPos

private theorem phi_image_mem_outputCorner_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (X : Mₙ n) :
    Φ X ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  simp [outputSupportProj_eq_one_of_posDef Φ hΦ1, mem_matrixCornerSubmodule_iff]

/-- Official full-support trivialization node: when `Φ(1)` is positive definite, the chosen
reduced map no longer needs a nontrivial support-corner witness. Because the fixed orthonormal
matrix realization of the support corner still represents the codomain in coordinates, the public
statement is the pointwise equality to that trivialized model transport of `Φ`. -/
theorem outputSupportReducedMap_eq_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (X : Mₙ n) :
    outputSupportReducedMap Φ hPos X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, phi_image_mem_outputCorner_of_posDef Φ hΦ1 X⟩ := by
  rw [outputSupportReducedMap_apply]

/-- The chosen output-support reduction datum packages the output-support projection, a fixed
orthonormal matrix realization of the support corner, and its associated reduced map. -/
noncomputable def outputSupportReductionData {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) : OutputSupportReductionData Φ :=
  outputSupportReductionDataOfModel Φ hPos
    (outputSupportMatrixCornerModel Φ) (outputSupportReducedMap Φ hPos)

/-- The canonical strict-output certificate for the chosen reduced map on the output support. -/
theorem outputSupportReducedHSMap_strictlyPositive {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTrace : TracePreserving Φ) (hSch : HSAdjointSchwarz Φ) :
    StrictlyPositiveSchwarzTracePreservingMap (outputSupportReducedHSMap Φ hPos) where
  toSchwarzTracePreservingMap := {
    positiveMap := by
      simpa [outputSupportReducedHSMap] using outputSupportReducedMap_isPositiveMap Φ hPos
    tracePreserving := by
      simpa [outputSupportReducedHSMap] using
        outputSupportReducedMap_tracePreserving Φ hPos hTrace
    adjointSchwarz := by
      simpa [outputSupportReducedHSMap] using
        outputSupportReducedMap_hsAdjointSchwarz Φ hPos hSch
  }
  outputPosDef := by
    simpa [outputSupportReducedHSMap] using outputSupportReducedMap_one_posDef Φ hPos

/-- On the output-support corner, the image of the unit induces a positive operator with trivial
kernel. This is the corner-level strict-positivity datum used before defining the reduced map. -/
theorem phi_image_posDef_on_outputCorner {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    let C : Mₙ m := Φ (1 : Mₙ n)
    let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
      Matrix.toEuclideanLin C
    T.IsPositive ∧ ∀ u, u ∈ outputSupportEuclideanSubspace Φ → T u = 0 → u = 0 := by
  dsimp
  let C : Mₙ m := Φ (1 : Mₙ n)
  let T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin C
  have hCnonneg : 0 ≤ C := by
    simpa [C] using hPos (show 0 ≤ (1 : Mₙ n) from
      (Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hCnonneg
  have hTpos : T.IsPositive := by
    simpa [T] using (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  refine ⟨hTpos, ?_⟩
  intro u hu huTzero
  let uu : outputSupportEuclideanSubspace Φ := ⟨u, hu⟩
  have huuZero :
      outputSupportUnitToEuclideanEnd Φ hPos uu = 0 := by
    apply Subtype.ext
    simpa [outputSupportUnitToEuclideanEnd, C, T,
      outputCornerToEuclideanEndLinearEquiv_apply_coe] using huTzero
  have huuKer : uu ∈ LinearMap.ker (outputSupportUnitToEuclideanEnd Φ hPos) := by
    simpa [LinearMap.mem_ker] using huuZero
  have huuBot : uu ∈ (⊥ : Submodule ℂ (outputSupportEuclideanSubspace Φ)) := by
    simpa [outputSupportUnitToEuclideanEnd_ker_eq_bot Φ hPos] using huuKer
  have huuEqZero : uu = 0 := by
    simpa using huuBot
  simpa [uu] using congrArg Subtype.val huuEqZero

end HiaiPetz
