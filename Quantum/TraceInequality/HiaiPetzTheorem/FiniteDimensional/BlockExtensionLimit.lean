/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionOrder
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionSpectrum

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
Finite-dimensional block-extension limiting argument for Proposition 5.1.5.

This module carries the heavy finite-span CFC limiting payload used by the
finite-dimensional monotonicity and convexity bridge surfaces.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology MatrixOrder CStarAlgebra
open Filter
open HansenPedersen.Internal

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

/-- Thin wrapper around complex normal CFC for continuous linear maps.  It is
used to keep later finite-span limiting statements phrased uniformly. -/
noncomputable def complexCfcCLM
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedRing (K →L[ℂ] K)] [NormedAlgebra ℂ (K →L[ℂ] K)]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    (g : ℂ → ℂ) (T : K →L[ℂ] K) : K →L[ℂ] K :=
  cfc (R := ℂ) g T

/-- **Proposition 5.1.5 (1)**: matrix monotonicity implies operator monotonicity.
Source: Hiai--Yanagi, Proposition 5.1.5(1). -/
def MatrixMonotoneImpliesOperatorMonotone : Prop :=
  ∀ {J : Set ℝ} {f : ℝ → ℝ},
    Convex ℝ J →
    ContinuousOn f J →
    _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval J f →
    OperatorMonotoneOnInterval (ℋ := ℋ) J f

/--
**Proposition 5.1.5 (2)**: matrix midpoint convexity implies operator convexity
in the midpoint sense of Definition 5.1.3(2).
Source: Hiai--Yanagi, Proposition 5.1.5(2).
-/
def MatrixConvexImpliesOperatorMidpointConvex : Prop :=
  ∀ {J : Set ℝ} {f : ℝ → ℝ},
    Convex ℝ J →
    ContinuousOn f J →
    MatrixOperatorMidpointConvexOnInterval J f →
    OperatorMidpointConvexOnInterval (ℋ := ℋ) J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Reformulation of Proposition 5.1.5(2): matrix midpoint convexity implies
`H`-midpoint operator convexity for every complex Hilbert space.
Source: Hiai--Yanagi, Proposition 5.1.5(2). -/
def MatrixConvexImpliesAllHOperatorMidpointConvex : Prop :=
  ∀ {J : Set ℝ} {f : ℝ → ℝ},
    Convex ℝ J →
    ContinuousOn f J →
    MatrixOperatorMidpointConvexOnInterval J f →
    AllHOperatorMidpointConvexOnInterval.{u} J f

namespace BlockExtensionInternal

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Nonnegative-spectrum class for endomorphisms of a complete submodule
(subtype spelling), extracted from the finite-span compression proof of
Proposition 5.1.5 (1) so that the associated scalar-action instance searches
elaborate once. -/
theorem nonnegSpectrumClass_submoduleEndSubtype
    (U : Submodule ℂ ℋ) (hUSubComplete : CompleteSpace ↥U) :
    NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U) := by
  exact @ContinuousLinearMap.instNonnegSpectrumClassRealId ℂ ↥U _ _ _ hUSubComplete _
    (instIsScalarTowerRealComplexSubtypeSubmoduleEnd (U := U))

end BlockExtensionInternal

end NormalCFC514

end HansenPedersen
