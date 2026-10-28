/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.ReducedMap
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.ReducedMapRetained

/-!
# Hiai--Petz 6.2 output-support strict-output lift

This module contains the general and book-facing output-support conditions,
their strict-output lift through the canonical reduced map, and the final
Hiai--Petz 6.2 output-support wrappers.
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

theorem canonicalReduction_reducedMap_ready {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hTrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) :
    let reduction := outputSupportReductionData Φ hPos
    IsPositiveMap reduction.reducedMap ∧
      _root_.HiaiPetz.TracePreserving reduction.reducedMap ∧
      HSAdjointSchwarz reduction.reducedMap ∧
      MatrixPosDef (reduction.reducedMap (1 : Mₙ n)) := by
  simpa [outputSupportReductionData, outputSupportReductionDataOfModel] using
    outputSupportReducedMap_strictOutputReady Φ hPos hTrace hSch

end

end Quantum.TraceInequality.Loewner.HiaiPetz
