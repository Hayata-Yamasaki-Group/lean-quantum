import Quantum.Analysis.Calculus.ClosedPositiveOperatorConvexity
import Quantum.Analysis.Matrix.UnitIntervalOrder
import Quantum.Analysis.Real.PositiveCayley
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
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 primitives

Carlen 2022 Theorem 1.45 (AH1): positive-ray matrix primitives, abstract
convexity/twist bridges, and the closed-positive CFC realization bridge.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

/--
The theorem-facing bridge from finite-dimensional closed-positive matrix CFC
convexity to the uniform C*-algebra closed-positive operator convexity
predicate, with the actual finite-dimensional-to-C*-algebra bridge supplied
explicitly.
-/
theorem operatorConvexOnClosedPositive_of_closedMatrixCfcConvex_bridge
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hbridge :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h) →
        OperatorConvexOnClosedPositive h) :
    OperatorConvexOnClosedPositive h := by
  intro 𝓑 _ _ _ _ A B t hA hB ht0 ht1 hAs hBs
  exact (hbridge hclosed) hA hB ht0 ht1 hAs hBs

end Quantum.TraceInequality.Loewner
