/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: the normed operational state space

The operational real state space carries the normed additive-group structure
`instNormedAddCommGroupOperationalStateSpaceReal` given by the operational state norm.
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The Mathlib normed additive group structure on the operational real state
space generated from the operational norm core. -/
noncomputable instance instNormedAddCommGroupOperationalStateSpaceReal {A : Sys} :
    NormedAddCommGroup (OperationalStateSpaceReal (Sys := Sys) A) :=
  NormedAddCommGroup.ofCore (operationalStateNormedSpaceCore (Sys := Sys) (A := A))

end CausalOperationalProbabilisticTheory
end OPT
