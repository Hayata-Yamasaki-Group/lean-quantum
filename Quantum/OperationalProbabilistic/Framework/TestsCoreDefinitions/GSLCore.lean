/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.Core.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: lightweight state, effect, and probability definitions
-/

namespace OPT

universe u v

section OperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
variable [Preadditive Sys]
variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
variable [OperationalProbabilisticTheory Sys]

/-- Ambient type of states of a system. -/
abbrev State (A : Sys) : Type v :=
  𝟙_ Sys ⟶ A

/-- Ambient type of effects of a system. -/
abbrev Effect (A : Sys) : Type v :=
  A ⟶ 𝟙_ Sys

/-- Top-level wrapper for physical transformations. -/
def IsTransformation {A B : Sys} (f : A ⟶ B) : Prop :=
  OperationalProbabilisticTheory.IsTransformation f

/-- Top-level wrapper for scalar evaluation. -/
noncomputable def scalarEval : (𝟙_ Sys ⟶ 𝟙_ Sys) →ₗ[ℝ] ℝ :=
  OperationalProbabilisticTheory.scalarEval

/-- Physical states are transformations from the monoidal unit. -/
def IsState {A : Sys} (ρ : State A) : Prop :=
  IsTransformation ρ

/-- Physical effects are transformations to the monoidal unit. -/
def IsEffect {A : Sys} (a : Effect A) : Prop :=
  IsTransformation a

/-- Probability pairing between an effect and a state. -/
noncomputable def prob {A : Sys} (a : Effect A) (ρ : State A) : ℝ :=
  scalarEval (ρ ≫ a)

end OperationalProbabilisticTheory

end OPT
