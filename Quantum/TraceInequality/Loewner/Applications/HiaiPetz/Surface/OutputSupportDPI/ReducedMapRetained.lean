/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.CornerModels
import Quantum.TraceInequality.HansenPedersen.Reduction.ReducedMap

/-!
# Hiai--Petz 6.2 output-support reduced map

This module contains the canonical reduced-map construction and strict-output
readiness API for the output-support stage of Hiai--Petz 6.2.
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

/-! ### Canonical Reduced Map API and Ready Package -/

/-- The output-support reduction before transport to a concrete matrix model: `Φ` with codomain
restricted to the output corner cut out by `outputSupportProj Φ`. -/
noncomputable abbrev outputSupportReducedMapToCorner {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    Mₙ n →L[ℂ] matrixCornerSubmodule (outputSupportProj Φ) :=
  _root_.HiaiPetz.outputSupportReducedMapToCorner Φ hPos

@[simp] theorem outputSupportReducedMapToCorner_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    ((outputSupportReducedMapToCorner Φ hPos) X : Mₙ m) = Φ X := by
  rfl

/-- Loewner-surface compatibility name for the canonical output-support reduction data.
The two former structures had field-for-field identical bodies after the shared
matrix and projection vocabulary is unfolded.
Source: the Hiai--Petz output-support setup, `HiaiPetz.OutputSupportReductionData`. -/
abbrev OutputSupportReductionData {n m : ℕ} (Φ : HSMap n m) :=
  _root_.HiaiPetz.OutputSupportReductionData Φ

/-- Package the already-proved output-support projection facts once a corner model and a reduced
map have been chosen. -/
noncomputable abbrev outputSupportReductionDataOfModel {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (model : MatrixCornerModel (outputSupportProj Φ))
    (reducedMap : HSMap n model.dim) : OutputSupportReductionData Φ :=
  _root_.HiaiPetz.outputSupportReductionDataOfModel Φ hPos model reducedMap

noncomputable abbrev outputSupportReductionData {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) : OutputSupportReductionData Φ :=
  _root_.HiaiPetz.outputSupportReductionData Φ hPos

end

end Quantum.TraceInequality.Loewner.HiaiPetz
