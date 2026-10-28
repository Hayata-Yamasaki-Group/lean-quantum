/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Observation tests from effect families

`EffectFamilyObservationTestTheory` records that a finite family of effects summing to the
deterministic effect forms an observation test (`observationTest_of_effects_sum_detEffect`); the
instance is obtained from finite deterministic-family completion.
-/

namespace OPT

universe u v w

namespace DistinguishableStates

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys]
  [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- CDP Corollary 4 / effect-valued-measure normalization bridge:
a finite family of effects whose sum is the deterministic effect forms an
observation test. -/
class EffectFamilyObservationTestTheory (Sys : Type u) [Category.{v} Sys]
    [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    [CausalOperationalProbabilisticTheory Sys] : Prop where
  observationTest_of_effects_sum_detEffect :
    ∀ {A : Sys} {ι : Type} [Fintype ι] (c : ι → Effect A),
      (∀ i, IsEffect (Sys := Sys) (c i)) →
        Finset.univ.sum c = detEffect (Sys := Sys) A →
          ∃ M : ObservationTest (Sys := Sys) A ι,
            ∀ i, M.outcome i = c i

/-- Projection for the effect-family observation-test bridge. -/
theorem observationTest_of_effects_sum_detEffect
    [EffectFamilyObservationTestTheory Sys]
    {A : Sys} {ι : Type} [Fintype ι] (c : ι → Effect A)
    (hc : ∀ i, IsEffect (Sys := Sys) (c i))
    (hsum : Finset.univ.sum c = detEffect (Sys := Sys) A) :
    ∃ M : ObservationTest (Sys := Sys) A ι,
      ∀ i, M.outcome i = c i :=
  EffectFamilyObservationTestTheory.observationTest_of_effects_sum_detEffect
    c hc hsum

/-- Finite deterministic-family completion supplies the effect-family
observation-test bridge by specializing the output system to the tensor
unit. -/
@[implicit_reducible]
noncomputable def
effectFamilyObservationTestTheory_of_finiteDeterministicFamilyCompletion
    [FiniteDeterministicFamilyCompletionTheory Sys] :
    EffectFamilyObservationTestTheory Sys where
  observationTest_of_effects_sum_detEffect := by
    intro A ι _ c hc hsum
    have htest : IsTest (Sys := Sys) c := by
      apply finiteDeterministicFamilyCompletesToTest (Sys := Sys) c
      · exact hc
      · simpa [detEffect_unit] using hsum
    exact ⟨{ outcome := c, isTest := htest }, fun _ => rfl⟩

end DistinguishableStates
end OPT
