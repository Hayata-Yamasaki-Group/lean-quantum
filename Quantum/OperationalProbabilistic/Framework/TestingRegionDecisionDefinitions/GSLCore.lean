/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Lightweight testing-region decision definitions
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- A public probability parameter, carrying the bounds `0 ≤ p ≤ 1`. -/
abbrev ProbabilityLevel := Set.Icc (0 : ℝ) 1

/-- Supremum of an `ENNReal`-valued function over a region. -/
noncomputable def regionSupENNReal {α : Type*}
    (f : α → ℝ≥0∞) (R : Set α) : ℝ≥0∞ :=
  ⨆ z : R, f z.1

end

end OPT
