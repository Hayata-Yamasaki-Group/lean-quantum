/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TransformationQuotients.GSLCore
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: representatives of physical state classes

`physicalStateClassRepresentative_class_eq`: the chosen representative of a physical state
class lies in that class.
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The chosen representative represents the given physical state class. -/
theorem physicalStateClassRepresentative_class_eq {A : Sys}
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    stateOperationalClass (Sys := Sys) A
        (physicalStateClassRepresentative (Sys := Sys) x) = x :=
  (Classical.choose_spec x.2).2

end CausalOperationalProbabilisticTheory
end OPT
