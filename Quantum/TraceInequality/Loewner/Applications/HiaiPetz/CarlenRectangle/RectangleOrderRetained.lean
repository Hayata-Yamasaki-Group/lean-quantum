/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.ConditionIToLoewner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.PositiveInverse
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.Infrastructure
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.RectangleOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.ConditionsRetained

-- positive-part decomposition for positive maps

/-!
# Carlen rectangle order conversion

This module contains the rectangle-order conversion stage of the Carlen 2022
Theorem 1.46 argument: inverse/direct rectangle order equivalence and the
Carlen condition (2)/(3) equivalence for the G-operator.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instCarlenRectangleHSOpCStarAlgebra
  instCarlenRectangleHSOpPartialOrder
  instCarlenRectangleHSOpStarRing
  instCarlenRectangleHSOpStarOrderedRing
  instCarlenRectangleComplexCFC
  instCarlenRectangleRealCFC
  instCarlenRectangleHSOpNonnegSpectrumClass
  instCarlenRectangleHSOpSMulZeroClass
  instCarlenRectangleHSOpIsBoundedSMul
  instCarlenRectangleHSOpContinuousSMul
  instCarlenRectangleHSOpRealAlgebra
  instCarlenRectangleHSOpRealRealTower

noncomputable section

/-- Carlen's inverse-form and direct-form `opmontI` conditions are equivalent. -/
theorem carlenOpMontICondition2_iff_condition3_of_functionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontICondition2 f ↔ CarlenOpMontICondition3 f := by
  constructor
  · intro h2 n m Φ X Y hΦ hX hY hΦX hΦY
    exact
      (gOperator_inverse_dpi_iff_direct_dpi_of_carlenFunctionHypothesis
        Φ hf hX hY hΦX hΦY).mp (h2 Φ hΦ hX hY hΦX hΦY)
  · intro h3 n m Φ X Y hΦ hX hY hΦX hΦY
    exact
      (gOperator_inverse_dpi_iff_direct_dpi_of_carlenFunctionHypothesis
        Φ hf hX hY hΦX hΦY).mpr (h3 Φ hΦ hX hY hΦX hΦY)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
