/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LiebAndo.JensenOperatorInequalityIImpIV
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.Calculus.ClosedPositiveOperatorConvexity

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 transport

Carlen 2022 Theorem 1.45 (AH1): star-equivalence transport, Euclidean
compression, endpoint perturbation continuity, and scalar restriction.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

-- Keep the complex-to-real algebra local to the real-spectrum transport proofs.
attribute [local instance] instAH1TransportCStarMatrixRealAlgebra

/--
The concrete star-algebra equivalence from operators on the two-fold Hilbert
sum of a finite Euclidean space to a finite `CStarMatrix` algebra.
-/
private noncomputable def positiveRayHSumOperatorCStarMatrixEquiv (n : ℕ) :
    (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n)) →L[ℂ]
        JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n))) ≃⋆ₐ[ℂ]
      CStarMatrix
        (Fin (Module.finrank ℂ
          (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n)))))
        (Fin (Module.finrank ℂ
          (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n))))) ℂ :=
  ((LinearMap.toMatrixOrthonormal
        (stdOrthonormalBasis ℂ
          (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n))))).symm.trans
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }).symm.trans
    (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ)
      (n := Fin (Module.finrank ℂ
        (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n))))))

/--
Closed positive-ray matrix CFC convexity gives operator convexity on the two-fold
Hilbert sum of a finite Euclidean space.

Star-algebra equivalence transport creates a dense finite-dimensional instance search.
-/
theorem positiveRayHSumOperatorConvexOn_of_closedMatrixCfcConvex
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hcontIci : ContinuousOn h (Set.Ici (0 : ℝ))) (n : ℕ)
    [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n)) →L[ℂ]
        JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n)))
      (Set.Ici (0 : ℝ)) h := by
  letI : Nontrivial (JensenOperatorInequality.HSum (EuclideanSpace ℂ (Fin n))) :=
    inferInstance
  exact operatorConvexOnClosedPositive_starAlgEquiv_of_closedMatrixCfcConvex_on_Ici
    (positiveRayHSumOperatorCStarMatrixEquiv n) hcontIci hclosed

/--
Closed positive-ray matrix CFC convexity yields the shifted Bendat--Sherman
compression inequality on a finite Euclidean space.

Compression through the HSum equivalence uses the same heavy CFC instance chain.
-/
theorem positiveRayEuclidean_compression_sub_value_zero_of_closedMatrixCfcConvex
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hcontIci : ContinuousOn h (Set.Ici (0 : ℝ)))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A X : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hA : IsSelfAdjoint A)
    (hAs : spectrum ℝ A ⊆ Set.Ici (0 : ℝ)) (hX : ‖X‖ ≤ 1) :
    LownerHeinzTheorem.cfcR
        (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0)
        (star X * A * X) ≤
      star X *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) A *
        X := by
  let H := EuclideanSpace ℂ (Fin n)
  have hconv_h :
      LownerHeinzCore.OperatorConvexOn
        (𝓐 := JensenOperatorInequality.HSum H →L[ℂ] JensenOperatorInequality.HSum H)
        (Set.Ici (0 : ℝ)) h := by
    simpa [H] using
      positiveRayHSumOperatorConvexOn_of_closedMatrixCfcConvex
        (h := h) hclosed hcontIci n
  have hconv_shift :
      LownerHeinzTheorem.OperatorConvexOn
        (ℋ := JensenOperatorInequality.HSum H) (Set.Ici (0 : ℝ))
        (fun x : ℝ => h x - h 0) := by
    simpa [LownerHeinzTheorem.OperatorConvexOn] using
      operatorConvexOn_Ici_sub_value_zero
        (𝓐 := JensenOperatorInequality.HSum H →L[ℂ] JensenOperatorInequality.HSum H)
        hconv_h hcontIci
  have hcont_shift : ContinuousOn (fun x : ℝ => h x - h 0) (Set.Ici (0 : ℝ)) :=
    hcontIci.sub continuousOn_const
  have hf0 : (fun x : ℝ => h x - h 0) 0 ≤ 0 := by
    simp
  refine JensenOperatorInequality.cfcR_compression_le_of_midpoint
    (ℋ := H) (f := fun x : ℝ => h x - h 0)
    hcont_shift hf0 ?_ hA hAs hX
  intro B₁ B₂ hB₁ hB₂ hs₁ hs₂
  have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
  simpa [H, hhalf] using
    (hconv_shift (A := B₁) (B := B₂) (t := (1 / 2 : ℝ)) hB₁ hB₂
      (by positivity) (by norm_num) hs₁ hs₂)

/--
A matrix bridge from all finite positive-ray matrix algebras converts closed matrix
CFC convexity into closed positive-ray operator convexity.
-/
theorem operatorConvexOnClosedPositive_of_closedMatrixCfcConvex_matrixBridge
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hbridge :
      (∀ n : ℕ,
        LownerHeinzCore.OperatorConvexOn
          (𝓐 := HansenPedersen.Mₙ n) (Set.Ici (0 : ℝ)) h) →
        OperatorConvexOnClosedPositive h) :
    OperatorConvexOnClosedPositive h := by
  intro 𝓑 _ _ _ _ A B t hA hB ht0 ht1 hAs hBs
  exact (hbridge fun n =>
    operatorConvexOnClosedPositive_matrix_of_closedMatrixCfcConvex hclosed n)
      hA hB ht0 ht1 hAs hBs

end Quantum.TraceInequality.Loewner
