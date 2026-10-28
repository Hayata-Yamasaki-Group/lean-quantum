/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.StrictOutputDPIViaLoewner
import Quantum.TraceInequality.HiaiPetz.Support
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic
import Quantum.TraceInequality.HiaiPetz.Support.Corner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic

/-!
# Output-support support corners

This module contains the support projections, corner endomorphism model, and
finite matrix-coordinate model for the output-support stage of Hiai--Petz 6.2.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance instOutputSupportHSOpCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance instOutputSupportHSOpStarRing {n : ℕ} : StarRing (HSOp n) :=
  (instOutputSupportHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- `HSOp n` is a complex algebra. -/
noncomputable local instance instOutputSupportHSOpComplexAlgebra {n : ℕ} :
    Algebra ℂ (HSOp n) :=
  ContinuousLinearMap.algebra

/-- `HSOp n` is a complex normed algebra. -/
noncomputable local instance instOutputSupportHSOpNormedAlgebra {n : ℕ} :
    NormedAlgebra ℂ (HSOp n) :=
  ContinuousLinearMap.toNormedAlgebra

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance instOutputSupportHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance instOutputSupportHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance (instOutputSupportHSOpPartialOrder (n := n))
      (instOutputSupportHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance instOutputSupportHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (instOutputSupportHSOpCStarAlgebra (n := n))
    (instOutputSupportHSOpPartialOrder (n := n))
    (instOutputSupportHSOpStarOrderedRing (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance instOutputSupportHSOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance instOutputSupportHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- `Mₙ n` is a normed additive commutative group. -/
noncomputable local instance outputSupportBridgeMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (Mₙ n) :=
  instMatrixNormedAddCommGroup (n := n)

/-- `Mₙ n` is a complex normed space. -/
noncomputable local instance outputSupportBridgeMatrixNormedSpace {n : ℕ} :
    NormedSpace ℂ (Mₙ n) :=
  instMatrixNormedSpace (n := n)

/-- `Mₙ n` is a complex inner product space under the Frobenius inner product. -/
noncomputable local instance outputSupportBridgeMatrixInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ (Mₙ n) :=
  instMatrixInnerProductSpace (n := n)

/-- `Mₙ n` is a complete metric space. -/
noncomputable local instance outputSupportBridgeMatrixCompleteSpace {n : ℕ} :
    CompleteSpace (Mₙ n) :=
  instMatrixCompleteSpace (n := n)

/-- `Mₙ n` is finite-dimensional over `ℂ`. -/
noncomputable local instance outputSupportBridgeMatrixFiniteDimensional {n : ℕ} :
    FiniteDimensional ℂ (Mₙ n) :=
  Matrix.finiteDimensional

/-! ### Support Projections and Matrix Corners -/

/-- The support subspace of a matrix, viewed as the range of its action on vectors. -/
noncomputable abbrev matrixSupportSubspace {n : ℕ} (C : Mₙ n) : Submodule ℂ (Fin n → ℂ) :=
  _root_.HiaiPetz.matrixSupportSubspace C

@[simp] theorem matrixSupportSubspace_zero {n : ℕ} :
    matrixSupportSubspace (0 : Mₙ n) = ⊥ := by
  ext x
  simp [matrixSupportSubspace]

/-- A positive-definite matrix has full matrix-support subspace. -/
theorem matrixSupportSubspace_eq_top_of_posDef {n : ℕ} {C : Mₙ n}
    (hC : MatrixPosDef C) :
    matrixSupportSubspace C = ⊤ := by
  apply LinearMap.range_eq_top.2
  have hUnit : IsUnit C := matrixPosDef_isUnit hC
  exact LinearMap.injective_iff_surjective.mp <| by
    intro u v huv
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hUnit) (by
      simpa [Matrix.mulVecLin_apply] using huv)

/-- A matrix projection for the general-output support-corner layer. -/
abbrev IsMatrixProj {m : ℕ} (P : Mₙ m) : Prop :=
  _root_.HiaiPetz.IsMatrixProj P

/-- Compatibility characterization of `IsMatrixProj` by the conjunction used
by the original Loewner surface. -/
theorem isMatrixProj_iff_mul_self_and_isSelfAdjoint {m : ℕ} {P : Mₙ m} :
    IsMatrixProj P ↔ P * P = P ∧ IsSelfAdjoint P := by
  exact isStarProjection_iff P

/-- The ambient linear map whose matrix is `matrixSupportProj`. -/
private noncomputable def matrixSupportProjLin {n : ℕ} (C : Mₙ n) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  e.toLinearMap.comp (p.toLinearMap.comp e.symm.toLinearMap)

/-- The matrix of the orthogonal projection onto the support subspace of `C`. -/
noncomputable abbrev matrixSupportProj {n : ℕ} (C : Mₙ n) : Mₙ n :=
  _root_.HiaiPetz.matrixSupportProj C

private theorem matrixSupportProjLin_idempotent {n : ℕ} (C : Mₙ n) :
    matrixSupportProjLin C * matrixSupportProjLin C = matrixSupportProjLin C := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := (matrixSupportSubspace C).map e.symm.toLinearMap
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

@[simp] theorem matrixSupportProj_toEuclideanLin {n : ℕ} (C : Mₙ n) :
    Matrix.toEuclideanLin (matrixSupportProj C) =
      let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
      let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
        (matrixSupportSubspace C).map e.symm.toLinearMap
      let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
        Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
      p.toLinearMap := by
  exact _root_.HiaiPetz.matrixSupportProj_toEuclideanLin C

private theorem matrixSupportProj_isSelfAdjoint_aux {n : ℕ} (C : Mₙ n) :
    IsSelfAdjoint (matrixSupportProj C) := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := (matrixSupportSubspace C).map e.symm.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    Submodule.starProjection (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) U
  rw [← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_iff_isSymmetric]
  simpa [e, U, p] using (Submodule.starProjection_isSymmetric U)

/-- `matrixSupportProj` is an idempotent self-adjoint matrix projection. -/
theorem matrixSupportProj_isProj {n : ℕ} (C : Mₙ n) :
    IsMatrixProj (matrixSupportProj C) := by
  exact _root_.HiaiPetz.matrixSupportProj_isProj C

@[simp] theorem matrixSupportProj_mulVec_eq_self_iff {n : ℕ} (C : Mₙ n)
    (x : Fin n → ℂ) :
    (matrixSupportProj C).mulVec x = x ↔ x ∈ matrixSupportSubspace C := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := (matrixSupportSubspace C).map e.symm.toLinearMap
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
  _root_.HiaiPetz.outputSupportSubspace Φ

/-- The named output-support projection associated with `Φ(I)`. -/
noncomputable abbrev outputSupportProj {n m : ℕ} (Φ : HSMap n m) : Mₙ m :=
  _root_.HiaiPetz.outputSupportProj Φ

/-- The matrix-support projection of a positive-definite matrix is the identity. -/
theorem matrixSupportProj_eq_one_of_posDef {n : ℕ} {C : Mₙ n}
    (hC : MatrixPosDef C) :
    matrixSupportProj C = 1 := by
  apply Matrix.toEuclideanLin.injective
  simpa [matrixSupportProj_toEuclideanLin, matrixSupportSubspace_eq_top_of_posDef hC]
    using (Submodule.starProjection_top (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)))

theorem outputSupportSubspace_eq_top_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    outputSupportSubspace Φ = ⊤ :=
  matrixSupportSubspace_eq_top_of_posDef hΦ1

theorem outputSupportProj_eq_one_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    outputSupportProj Φ = 1 :=
  matrixSupportProj_eq_one_of_posDef hΦ1

/-- The corner submodule cut out by a matrix `P`, consisting of matrices satisfying `PXP = X`. -/
abbrev matrixCornerSubmodule {m : ℕ} (P : Mₙ m) : Submodule ℂ (Mₙ m) :=
  _root_.HiaiPetz.matrixCornerSubmodule P

@[simp] theorem mem_matrixCornerSubmodule_iff {m : ℕ} {P X : Mₙ m} :
    X ∈ matrixCornerSubmodule P ↔ P * X * P = X := Iff.rfl

/-- The raw cornering map `X ↦ PXP` on matrices. -/
noncomputable abbrev matrixCornerProj {m : ℕ} (P : Mₙ m) : HSOp m :=
  _root_.HiaiPetz.matrixCornerProj P

@[simp] theorem matrixCornerProj_apply {m : ℕ} (P X : Mₙ m) :
    matrixCornerProj P X = P * X * P := by
  simp [matrixCornerProj, Matrix.mul_assoc]

/-- Elements of a projection corner are fixed by left multiplication by the projection. -/
theorem matrixCornerSubmodule.left_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    P * X = X := by
  rcases hP with ⟨hPidem, _⟩
  rw [mem_matrixCornerSubmodule_iff] at hX
  calc
    P * X = P * (P * X * P) := by rw [hX]
    _ = (P * P) * X * P := by simp [Matrix.mul_assoc]
    _ = P * X * P := by rw [hPidem]
    _ = X := hX

/-- Elements of a projection corner are fixed by right multiplication by the projection. -/
theorem matrixCornerSubmodule.right_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    X * P = X := by
  rcases hP with ⟨hPidem, _⟩
  rw [mem_matrixCornerSubmodule_iff] at hX
  calc
    X * P = (P * X * P) * P := by rw [hX]
    _ = P * X * (P * P) := by simp [Matrix.mul_assoc]
    _ = P * X * P := by rw [hPidem]
    _ = X := hX

/-- Wrapper form of left fixation for elements of a matrix projection corner. -/
theorem matrixCornerSubmodule_left_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    P * X = X :=
  matrixCornerSubmodule.left_fix hP hX

/-- Wrapper form of right fixation for elements of a matrix projection corner. -/
theorem matrixCornerSubmodule_right_fix {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    X * P = X :=
  matrixCornerSubmodule.right_fix hP hX

/- Namespaced API for the matrix corner cut out by an idempotent self-adjoint projection. -/
namespace MatrixCornerSubmodule

/-- Membership in a matrix corner is the equation `P * X * P = X`. -/
theorem mem_iff {m : ℕ} {P X : Mₙ m} :
    X ∈ matrixCornerSubmodule P ↔ P * X * P = X :=
  mem_matrixCornerSubmodule_iff

/-- Elements of an idempotent self-adjoint matrix corner are left-fixed by `P`. -/
theorem left_fix_of_isProj {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    P * X = X :=
  matrixCornerSubmodule_left_fix hP hX

/-- Elements of an idempotent self-adjoint matrix corner are right-fixed by `P`. -/
theorem right_fix_of_isProj {m : ℕ} {P X : Mₙ m}
    (hP : IsMatrixProj P) (hX : X ∈ matrixCornerSubmodule P) :
    X * P = X :=
  matrixCornerSubmodule_right_fix hP hX

end MatrixCornerSubmodule

/- Namespaced API for the projection onto the matrix support subspace. -/
namespace MatrixSupportProj

theorem isProj {n : ℕ} (C : Mₙ n) :
    IsMatrixProj (matrixSupportProj C) :=
  matrixSupportProj_isProj C

/-- The support projection of a matrix is idempotent. -/
theorem idempotent {n : ℕ} (C : Mₙ n) :
    matrixSupportProj C * matrixSupportProj C = matrixSupportProj C :=
  (isProj C).1

/-- The support projection of a matrix is self-adjoint. -/
theorem isSelfAdjoint {n : ℕ} (C : Mₙ n) :
    IsSelfAdjoint (matrixSupportProj C) :=
  (isProj C).2

/-- A positive-definite matrix has identity support projection. -/
theorem eq_one_of_posDef {n : ℕ} {C : Mₙ n} (hC : MatrixPosDef C) :
    matrixSupportProj C = 1 :=
  matrixSupportProj_eq_one_of_posDef hC

/-- The support projection fixes exactly the vectors in the matrix support. -/
theorem mulVec_eq_self_iff {n : ℕ} (C : Mₙ n) (x : Fin n → ℂ) :
    (matrixSupportProj C).mulVec x = x ↔ x ∈ matrixSupportSubspace C :=
  matrixSupportProj_mulVec_eq_self_iff C x

/-- Matrix-support corner elements are left-fixed by the support projection. -/
theorem left_mul_eq_self_of_mem {n : ℕ} {C X : Mₙ n}
    (hX : X ∈ matrixCornerSubmodule (matrixSupportProj C)) :
    matrixSupportProj C * X = X :=
  MatrixCornerSubmodule.left_fix_of_isProj (isProj C) hX

/-- Matrix-support corner elements are right-fixed by the support projection. -/
theorem right_mul_eq_self_of_mem {n : ℕ} {C X : Mₙ n}
    (hX : X ∈ matrixCornerSubmodule (matrixSupportProj C)) :
    X * matrixSupportProj C = X :=
  MatrixCornerSubmodule.right_fix_of_isProj (isProj C) hX

/-- Matrix-support corner membership expands to `P * X * P = X`. -/
theorem mem_corner_iff {n : ℕ} {C X : Mₙ n} :
    X ∈ matrixCornerSubmodule (matrixSupportProj C) ↔
      matrixSupportProj C * X * matrixSupportProj C = X :=
  MatrixCornerSubmodule.mem_iff

end MatrixSupportProj

/- Namespaced API for the projection onto the output support of `Φ(1)`. -/
namespace OutputSupportProj

theorem isProj {n m : ℕ} (Φ : HSMap n m) :
    IsMatrixProj (outputSupportProj Φ) :=
  MatrixSupportProj.isProj (Φ (1 : Mₙ n))

/-- The output-support projection is idempotent. -/
theorem idempotent {n m : ℕ} (Φ : HSMap n m) :
    outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
  (isProj Φ).1

/-- The output-support projection is self-adjoint. -/
theorem isSelfAdjoint {n m : ℕ} (Φ : HSMap n m) :
    IsSelfAdjoint (outputSupportProj Φ) :=
  (isProj Φ).2

/-- If `Φ(1)` is positive definite, the output-support projection is identity. -/
theorem eq_one_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    outputSupportProj Φ = 1 :=
  outputSupportProj_eq_one_of_posDef Φ hΦ1

/-- The output-support projection fixes exactly the output-support vectors. -/
theorem mulVec_eq_self_iff {n m : ℕ} (Φ : HSMap n m) (x : Fin m → ℂ) :
    (outputSupportProj Φ).mulVec x = x ↔ x ∈ outputSupportSubspace Φ :=
  MatrixSupportProj.mulVec_eq_self_iff (Φ (1 : Mₙ n)) x

/-- Output-corner elements are left-fixed by the output-support projection. -/
theorem left_mul_eq_self_of_mem {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m}
    (hX : X ∈ matrixCornerSubmodule (outputSupportProj Φ)) :
    outputSupportProj Φ * X = X :=
  MatrixSupportProj.left_mul_eq_self_of_mem (C := Φ (1 : Mₙ n)) hX

/-- Output-corner elements are right-fixed by the output-support projection. -/
theorem right_mul_eq_self_of_mem {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m}
    (hX : X ∈ matrixCornerSubmodule (outputSupportProj Φ)) :
    X * outputSupportProj Φ = X :=
  MatrixSupportProj.right_mul_eq_self_of_mem (C := Φ (1 : Mₙ n)) hX

/-- Output-corner membership expands to `P * X * P = X`. -/
theorem mem_corner_iff {n m : ℕ} {Φ : HSMap n m} {X : Mₙ m} :
    X ∈ matrixCornerSubmodule (outputSupportProj Φ) ↔
      outputSupportProj Φ * X * outputSupportProj Φ = X :=
  MatrixSupportProj.mem_corner_iff (C := Φ (1 : Mₙ n))

end OutputSupportProj

/-! ### Corner Endomorphism Model -/

/-- Project an ambient output vector onto the output-support subspace. -/
noncomputable abbrev outputSupportProjToSubspace {n m : ℕ} (Φ : HSMap n m) :
    (Fin m → ℂ) →ₗ[ℂ] outputSupportSubspace Φ :=
  _root_.HiaiPetz.outputSupportProjToSubspace Φ

@[simp] theorem outputSupportProjToSubspace_apply_coe {n m : ℕ} (Φ : HSMap n m)
    (x : outputSupportSubspace Φ) :
    outputSupportProjToSubspace Φ x = x := by
  exact _root_.HiaiPetz.outputSupportProjToSubspace_apply_coe Φ x

@[simp] theorem outputSupportProjToSubspace_apply_proj {n m : ℕ} (Φ : HSMap n m)
    (x : Fin m → ℂ) :
    outputSupportProjToSubspace Φ ((outputSupportProj Φ).mulVec x) =
      outputSupportProjToSubspace Φ x := by
  exact _root_.HiaiPetz.outputSupportProjToSubspace_apply_proj Φ x

/-- The action of a corner matrix on the output-support subspace. -/
noncomputable abbrev outputCornerToSubspaceMap {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) →ₗ[ℂ]
      (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) :=
  _root_.HiaiPetz.outputCornerToSubspaceMap Φ

/-- Extend an endomorphism of the support subspace to the ambient corner by `P T P`. -/
noncomputable abbrev subspaceMapToOutputCorner {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) →ₗ[ℂ]
      matrixCornerSubmodule (outputSupportProj Φ) :=
  _root_.HiaiPetz.subspaceMapToOutputCorner Φ

/-- The corner algebra is linearly equivalent to endomorphisms of the output support. -/
noncomputable abbrev outputCornerSubspaceLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) :=
  _root_.HiaiPetz.outputCornerSubspaceLinearEquiv Φ

/-! ### Finite Matrix Coordinates for the Output Corner -/

/-- A finite basis of the output-support subspace. -/
noncomputable def outputSupportBasis {n m : ℕ} (Φ : HSMap n m) :
    Module.Basis (Fin (Module.finrank ℂ (outputSupportSubspace Φ))) ℂ
      (outputSupportSubspace Φ) :=
  let b := Module.Basis.ofVectorSpace ℂ (outputSupportSubspace Φ)
  b.reindex (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm)

/-- Matrix coordinates for endomorphisms of the output-support subspace. -/
noncomputable def outputSupportSubspaceToMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportSubspace Φ →ₗ[ℂ] outputSupportSubspace Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportSubspace Φ)) :=
  LinearMap.toMatrix (outputSupportBasis Φ) (outputSupportBasis Φ)

/-- Matrix coordinates for the output-support corner. -/
noncomputable def outputCornerToMatrixLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      Mₙ (Module.finrank ℂ (outputSupportSubspace Φ)) :=
  (outputCornerSubspaceLinearEquiv Φ).trans (outputSupportSubspaceToMatrixLinearEquiv Φ)

theorem outputSupportProj_mem_outputCorner {n m : ℕ} (Φ : HSMap n m) :
    outputSupportProj Φ ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [OutputSupportProj.mem_corner_iff]
  have hPidem : outputSupportProj Φ * outputSupportProj Φ = outputSupportProj Φ :=
    OutputSupportProj.idempotent Φ
  calc
    outputSupportProj Φ * outputSupportProj Φ * outputSupportProj Φ =
        outputSupportProj Φ * outputSupportProj Φ := by
      simpa [Matrix.mul_assoc] using congrArg (fun M : Mₙ m => outputSupportProj Φ * M) hPidem
    _ = outputSupportProj Φ := hPidem

/-- The output-corner subspace coordinate map sends the support projection to identity. -/
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

theorem outputCorner_mul_mem {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    X.1 * Y.1 ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  have hPX : outputSupportProj Φ * X.1 = X.1 :=
    OutputSupportProj.left_mul_eq_self_of_mem (Φ := Φ) X.2
  have hYP : Y.1 * outputSupportProj Φ = Y.1 :=
    OutputSupportProj.right_mul_eq_self_of_mem (Φ := Φ) Y.2
  calc
    outputSupportProj Φ * (X.1 * Y.1) * outputSupportProj Φ =
        (outputSupportProj Φ * X.1) * (Y.1 * outputSupportProj Φ) := by
      simp [Matrix.mul_assoc]
    _ = X.1 * Y.1 := by rw [hPX, hYP]

theorem outputCorner_star_mem {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) :
    star X.1 ∈ matrixCornerSubmodule (outputSupportProj Φ) := by
  rw [mem_matrixCornerSubmodule_iff]
  have hPsa : Matrix.conjTranspose (outputSupportProj Φ) = outputSupportProj Φ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (OutputSupportProj.isSelfAdjoint Φ).star_eq
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc, hPsa] using
    congrArg star X.property

/-- The output-corner subspace coordinate map preserves multiplication. -/
theorem outputCornerSubspaceLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerSubspaceLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      (outputCornerSubspaceLinearEquiv Φ X) * (outputCornerSubspaceLinearEquiv Φ Y) := by
  exact _root_.HiaiPetz.outputCornerSubspaceLinearEquiv_mul Φ X Y

theorem outputCornerToMatrixLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToMatrixLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToMatrixLinearEquiv Φ X * outputCornerToMatrixLinearEquiv Φ Y := by
  simp [outputCornerToMatrixLinearEquiv, outputCornerSubspaceLinearEquiv_mul,
    outputSupportSubspaceToMatrixLinearEquiv, LinearMap.toMatrix_mul]

theorem outputCornerToMatrixLinearEquiv_proj {n m : ℕ} (Φ : HSMap n m) :
    outputCornerToMatrixLinearEquiv Φ
      ⟨outputSupportProj Φ, outputSupportProj_mem_outputCorner Φ⟩ = 1 := by
  simp [outputCornerToMatrixLinearEquiv, outputSupportSubspaceToMatrixLinearEquiv,
    outputCornerSubspaceLinearEquiv_proj]


end

end Quantum.TraceInequality.Loewner.HiaiPetz
