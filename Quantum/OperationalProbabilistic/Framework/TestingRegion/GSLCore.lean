/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TestingRegionDefinitions.GSLCore

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Testing regions for binary observations

The testing region of two normalized states records the two acceptance
probabilities attainable by allowed binary observation tests.  Its equivalent
physical-effect presentation and unit-square bound are proved here.
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- The allowed-binary-test region equals the range over all physical effects. -/
theorem testingRegion_eq_effectRange {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    testingRegion (Sys := Sys) rho sigma =
      Set.range
        (fun a : {a : Effect (Sys := Sys) A // IsEffect (Sys := Sys) a} =>
          (prob (Sys := Sys) a.1 rho.1,
            prob (Sys := Sys) a.1 sigma.1)) := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨⟨M.outcome BinaryObservationIndex.one,
      binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.one⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    rcases binaryObservationTest_of_effect_as_one (Sys := Sys) a.1 a.2 with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    simp [testingPoint, hM]

/-- Every attainable acceptance-probability pair lies in the unit square. -/
theorem testingRegion_subset_unitSquare {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    testingRegion (Sys := Sys) rho sigma ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  rw [testingRegion_eq_effectRange (Sys := Sys)]
  rintro _ ⟨a, rfl⟩
  exact
    ⟨⟨prob_nonneg_of_isState_isEffect (Sys := Sys) rho.2.1 a.2,
        prob_le_one_of_isNormalizedState_isEffect (Sys := Sys) rho.2 a.2⟩,
      ⟨prob_nonneg_of_isState_isEffect (Sys := Sys) sigma.2.1 a.2,
        prob_le_one_of_isNormalizedState_isEffect (Sys := Sys) sigma.2 a.2⟩⟩

end

end OPT
