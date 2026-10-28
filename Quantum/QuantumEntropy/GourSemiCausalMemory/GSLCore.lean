/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourBipartiteChoiDictionary.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Isometries as channels

`gourMemory_isometry_channel`: conjugation by a linear isometry is a CPTP channel (used for
one-way memory channels, Gour, *Resources of the Quantum World*).  This module keeps the
declarations of the original module that the public development uses.
-/

open QuantumState QuantumChannel GourChoi CategoryTheory
open scoped TensorProduct BigOperators ComplexOrder MonoidalCategory

universe u

set_option autoImplicit false

namespace GourSemiCausal

theorem gourMemory_isometry_channel :
    ∀ {H K : Type u} [Qudit H] [Qudit K] (V : H →ₗᵢ[ℂ] K),
      ∃ Φ : CPTP H K, Φ.toLinearMap = krausTerm V.toLinearMap := by
  intro H K _ _ V
  have hV : (LinearMap.adjoint V.toLinearMap).comp V.toLinearMap =
      LinearMap.id := by
    ext x
    apply ext_inner_right ℂ
    intro y
    change inner ℂ (LinearMap.adjoint V.toLinearMap (V x)) y = inner ℂ x y
    rw [LinearMap.adjoint_inner_left]
    exact V.inner_map_map x y
  obtain ⟨D, hD⟩ := krausTerm_isCompletelyPositive V.toLinearMap
  refine ⟨{ toCompletelyPositiveMap := D, trace_map := ?_ }, hD⟩
  intro X
  change Tr X = Tr (D.toLinearMap X)
  rw [hD]
  change Tr X = Tr (V.toLinearMap.comp (X.comp (LinearMap.adjoint V.toLinearMap)))
  rw [← LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV, LinearMap.comp_id]

end GourSemiCausal

open Lean

-- The concrete and abstract definitions share this node.
