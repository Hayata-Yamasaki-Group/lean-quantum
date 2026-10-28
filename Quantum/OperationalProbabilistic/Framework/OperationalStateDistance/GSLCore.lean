/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TransformationNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: state distance

The operational state distance is half the operational norm of the difference
of two operational real states.
-/

namespace OPT

universe u v

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The operational distance between two operational real states is half the
operational norm of their difference. -/
noncomputable def operationalStateDistance {A : Sys}
    (rho sigma : OperationalStateSpaceReal (Sys := Sys) A) : ℝ :=
  (2 : ℝ)⁻¹ * operationalStateNorm (Sys := Sys) (rho - sigma)

end CausalOperationalProbabilisticTheory

end OPT
