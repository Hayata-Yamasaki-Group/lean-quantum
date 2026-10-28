/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Support.OutputSupport
import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Subspace
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.Basic

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

/-- The Euclidean support subspace equals the range of the Euclidean linear map of `Φ(1)`;
that is, it is the image (support) of the output `Φ(1)`. -/
theorem outputSupportEuclideanSubspace_eq_range_toEuclideanLin {n m : ℕ} (Φ : HSMap n m) :
    outputSupportEuclideanSubspace Φ = LinearMap.range (Matrix.toEuclideanLin (Φ (1 : Mₙ
      n))) := by
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

/-- If `Φ(1)` is positive definite then its output support is the whole space, so the
Euclidean support subspace is `⊤`. -/
theorem outputSupportEuclideanSubspace_eq_top_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    outputSupportEuclideanSubspace Φ = ⊤ := by
  rw [outputSupportEuclideanSubspace_eq_range_toEuclideanLin]
  apply LinearMap.range_eq_top.2
  have hUnit : IsUnit (Φ (1 : Mₙ n)) := Matrix.PosDef.isUnit hΦ1
  exact LinearMap.injective_iff_surjective.mp <| by
    intro u v huv
    have huv' :
        (Φ (1 : Mₙ n)).mulVec (WithLp.ofLp u) = (Φ (1 : Mₙ n)).mulVec (WithLp.ofLp v) := by
      simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp huv
    have huv0 : WithLp.ofLp u = WithLp.ofLp v :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hUnit) huv'
    exact (WithLp.ofLp_injective (p := 2)) huv0

/-- If `Φ(1)` is positive definite then the output-support projection is the identity
matrix `1`. -/
theorem outputSupportProj_eq_one_of_posDef {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    outputSupportProj Φ = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [outputSupportProj_toEuclideanLin]
  rw [outputSupportEuclideanSubspace_eq_top_of_posDef Φ hΦ1]
  rw [Submodule.starProjection_top']
  ext x
  simp

/-- Evaluation formula for `outputCornerToEuclideanEndLinearEquiv Φ X` in terms of the
underlying subspace endomorphism and the Euclidean/bare-subspace identification. -/
theorem outputCornerToEuclideanEndLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (X : matrixCornerSubmodule (outputSupportProj Φ)) (u : outputSupportEuclideanSubspace Φ) :
    outputCornerToEuclideanEndLinearEquiv Φ X u =
      (outputSupportEuclideanSubspaceLinearEquiv Φ).symm
        ((outputCornerSubspaceLinearEquiv Φ X)
          ((outputSupportEuclideanSubspaceLinearEquiv Φ) u)) := by
  rfl

end HiaiPetz
