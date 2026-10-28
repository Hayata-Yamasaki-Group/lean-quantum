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
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore

open CategoryTheory
open Set
open scoped MonoidalCategory BigOperators

/-!
# Decomposition: the operational effect class

`operationalEffectClass` sends a physical effect to its class in the real operational effect
space.
Related source: CDP (arXiv:1011.6451).
-/

namespace OPT

universe u v

namespace Decomposition

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys]
  [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- Operational real effect class represented by a physical effect. -/
noncomputable def operationalEffectClass {A : Sys} (a : Effect A) (ha : IsEffect a) :
    OperationalEffectSpaceReal (Sys := Sys) A :=
  ⟨effectOperationalClass (Sys := Sys) A a,
    effectClass_mem_OperationalEffectSpaceRealSubmodule (Sys := Sys) ha⟩

end Decomposition
end OPT
