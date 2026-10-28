/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Lightweight testing-region definitions
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- The pair of `one`-outcome acceptance probabilities for two normalized states. -/
noncomputable def testingPoint {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A)
    (M : BinaryObservationTest (Sys := Sys) A) : ℝ × ℝ :=
  (prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1,
    prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1)

/-- The feasible acceptance-probability region of allowed binary observation tests. -/
noncomputable def testingRegion {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) : Set (ℝ × ℝ) :=
  Set.range (testingPoint (Sys := Sys) rho sigma)

end

end OPT
