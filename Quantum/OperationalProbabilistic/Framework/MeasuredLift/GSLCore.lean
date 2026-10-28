/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Generic measured lifts

This file lifts an arbitrary classical score on pairs of finite probability
mass functions to normalized states in an operational probabilistic theory.
-/

namespace OPT

noncomputable section

universe u v w

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- A classical score on a pair of probability mass functions with the same
finite outcome type. -/
abbrev ClassicalPMFScore (V : Type w) :=
  ∀ {iota : Type}, [Fintype iota] → PMF iota → PMF iota → V

/-- The supremum of a classical PMF score over all allowed finite observation
tests on two normalized OPT states. -/
noncomputable def measuredSup {V : Type w} [CompleteLattice V]
    (score : ClassicalPMFScore V) {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) : V :=
  ⨆ M : Test (Sys := Sys) A (𝟙_ Sys),
    score (observationPMF M rho) (observationPMF M sigma)

end

end OPT
