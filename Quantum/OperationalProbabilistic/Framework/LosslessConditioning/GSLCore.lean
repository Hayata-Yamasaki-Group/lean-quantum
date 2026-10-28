/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: marginals and conditioning

`marginalLeft` discards the right wing of a bipartite state, `applyEffectRight` applies an
effect on the right wing, and `conditionRight` is the resulting conditional state; it is a state
(`conditionRight_isState`) with the corresponding effect evaluations.
Related source: CDP (arXiv:1011.6451).
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- Left marginal of a bipartite state, discarding the right system. -/
noncomputable def marginalLeft {A B : Sys} (ω : State (A ⊗ B)) : State A :=
  ω ≫ (𝟙 A ⊗ₘ detEffect B) ≫ (ρ_ A).hom

/-- Apply an effect on the right system of a bipartite state. -/
noncomputable def applyEffectRight {A B : Sys}
    (b : Effect B) (ω : State (A ⊗ B)) : State A :=
  ω ≫ (𝟙 A ⊗ₘ b) ≫ (ρ_ A).hom

/-- Conditional state obtained by applying an effect on the right system. -/
noncomputable abbrev conditionRight {A B : Sys}
    (b : Effect B) (ω : State (A ⊗ B)) : State A :=
  applyEffectRight b ω

/-- Applying a physical effect on the right component of a physical bipartite
state gives a physical state on the left component. -/
theorem conditionRight_isState {A B : Sys} {b : Effect B} {ω : State (A ⊗ B)}
    (hb : IsEffect b) (hω : IsState ω) :
    IsState (conditionRight (Sys := Sys) b ω) := by
  have htensor : IsTransformation ((𝟙 A) ⊗ₘ b) :=
    CausalOperationalProbabilisticTheory.transformation_tensor (Sys := Sys)
      (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
        (CausalOperationalProbabilisticTheory.channel_id (Sys := Sys) A)) hb
  have hright : IsTransformation ((ρ_ A).hom) :=
    CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
      (CausalOperationalProbabilisticTheory.rightUnitor_hom_channel (Sys := Sys) A)
  have hcomp1 : IsTransformation (ω ≫ (𝟙 A ⊗ₘ b)) :=
    CausalOperationalProbabilisticTheory.transformation_comp (Sys := Sys) hω htensor
  have hcomp2 : IsTransformation ((ω ≫ (𝟙 A ⊗ₘ b)) ≫ (ρ_ A).hom) :=
    CausalOperationalProbabilisticTheory.transformation_comp (Sys := Sys) hcomp1 hright
  simpa [conditionRight, applyEffectRight, Category.assoc] using hcomp2

/-- Evaluating an effect after conditioning on the right component is the same
as evaluating the tensor product effect on the original bipartite state. -/
theorem conditionRight_effect_eval {A B : Sys}
    (a : Effect A) (b : Effect B) (ω : State (A ⊗ B)) :
    prob (Sys := Sys) a (conditionRight (Sys := Sys) b ω) =
      prob (Sys := Sys) (tensorEffect (Sys := Sys) a b) ω := by
  have hmorph :
      (𝟙 A ⊗ₘ b) ≫ (ρ_ A).hom ≫ a =
        (a ⊗ₘ b) ≫ (λ_ (𝟙_ Sys)).hom := by
    rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    congr 1
    rw [← MonoidalCategory.rightUnitor_naturality]
    simp [MonoidalCategory.unitors_equal]
  unfold prob conditionRight applyEffectRight tensorEffect
  rw [Category.assoc, Category.assoc, hmorph]

end CausalOperationalProbabilisticTheory
end OPT
