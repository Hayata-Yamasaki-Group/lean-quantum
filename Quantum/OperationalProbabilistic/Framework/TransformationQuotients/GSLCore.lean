/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Quantum.OperationalProbabilistic.Framework.TransformationApplication.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: unit ancillas and physical state classes

States with a unit ancilla (`stateWithUnitAncilla`) and the right-unitor bridge for applying
transformations to them; the action of transformations on state classes
(`operationalTransformationApplyToStateClass`); and the presentation of the real operational
state space by combinations of physical state classes, with chosen representatives
(`physicalStateClassRepresentative`).
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- A normalized state on `A`, regarded as a normalized state on `A ⊗ I`. -/
noncomputable def stateWithUnitAncilla {A : Sys} (ρ : State A) :
    State (A ⊗ 𝟙_ Sys) :=
  ρ ≫ (ρ_ A).inv

/-- Adding the monoidal unit as a right ancilla preserves physicality. -/
private theorem stateWithUnitAncilla_isState {A : Sys} {ρ : State A} (hρ : IsState ρ) :
    IsState (stateWithUnitAncilla (Sys := Sys) ρ) :=
  CausalOperationalProbabilisticTheory.transformation_comp (Sys := Sys) hρ
    (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
      (CausalOperationalProbabilisticTheory.rightUnitor_inv_channel (Sys := Sys) A))

omit [Preadditive Sys] [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys]
  [MonoidalLinear ℝ Sys] [CausalOperationalProbabilisticTheory Sys] in
/-- Applying a raw transformation with the monoidal unit as right ancilla and
then removing that unit ancilla is the same as applying the transformation
directly. -/
theorem applyTransformationWithUnitAncilla_rightUnitor {A B : Sys}
    (f : A ⟶ B) (ρ : State A) :
    applyTransformationWithAncilla (Sys := Sys) f
        (stateWithUnitAncilla (Sys := Sys) ρ) ≫ (ρ_ B).hom =
      ρ ≫ f := by
  unfold applyTransformationWithAncilla stateWithUnitAncilla
  simp only [Category.assoc]
  rw [MonoidalCategory.tensorHom_id]
  rw [MonoidalCategory.rightUnitor_naturality]
  simp

/-- An operational transformation class acts on a physical state class by
using the monoidal unit as ancillary system and then removing it. -/
noncomputable def operationalTransformationApplyToStateClass {A B : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    (ρ : State A) (hρ : IsState ρ) :
    OperationalStateSpaceReal (Sys := Sys) B :=
  transformationStateMap (Sys := Sys) (ρ_ B).hom
      (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
        (CausalOperationalProbabilisticTheory.rightUnitor_hom_channel (Sys := Sys) B))
    (operationalTransformationApplyWithAncilla (Sys := Sys) Δ
      (stateWithUnitAncilla (Sys := Sys) ρ)
      (stateWithUnitAncilla_isState (Sys := Sys) hρ))

/-- On physical transformation representatives, the state-class action agrees
with the ordinary postcomposition action. -/
theorem operationalTransformationApplyToStateClass_mk {A B : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    {ρ : State A} (hρ : IsState ρ) :
    operationalTransformationApplyToStateClass (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf) ρ hρ =
      transformationStateMap (Sys := Sys) f hf
        (operationalStateClass (Sys := Sys) ρ hρ) := by
  unfold operationalTransformationApplyToStateClass operationalTransformationClass
  rw [operationalTransformationApplyWithAncilla_mk (Sys := Sys) hf
    (stateWithUnitAncilla_isState (Sys := Sys) hρ)]
  rw [transformationStateMap_mk (Sys := Sys)
    (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
      (CausalOperationalProbabilisticTheory.rightUnitor_hom_channel (Sys := Sys) B))
    (applyTransformationWithAncilla_isState (Sys := Sys) hf
      (stateWithUnitAncilla_isState (Sys := Sys) hρ))]
  rw [transformationStateMap_mk (Sys := Sys) hf hρ]
  apply Subtype.ext
  change stateOperationalClass (Sys := Sys) B
      (applyTransformationWithAncilla (Sys := Sys) f
        (stateWithUnitAncilla (Sys := Sys) ρ) ≫ (ρ_ B).hom) =
    stateOperationalClass (Sys := Sys) B
      (transformationStateMapRaw (Sys := Sys) f ρ)
  congr 1
  exact applyTransformationWithUnitAncilla_rightUnitor (Sys := Sys) f ρ

/-- The state-class action is additive in the operational transformation. -/
theorem operationalTransformationApplyToStateClass_add {A B : Sys}
    (Δ Γ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    {ρ : State A} (hρ : IsState ρ) :
    operationalTransformationApplyToStateClass (Sys := Sys) (Δ + Γ) ρ hρ =
      operationalTransformationApplyToStateClass (Sys := Sys) Δ ρ hρ +
        operationalTransformationApplyToStateClass (Sys := Sys) Γ ρ hρ := by
  unfold operationalTransformationApplyToStateClass
  rw [operationalTransformationApplyWithAncilla_add]
  exact map_add (transformationStateMap (Sys := Sys) (ρ_ B).hom
    (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
      (CausalOperationalProbabilisticTheory.rightUnitor_hom_channel (Sys := Sys) B)))
    (operationalTransformationApplyWithAncilla (Sys := Sys) Δ
      (stateWithUnitAncilla (Sys := Sys) ρ)
      (stateWithUnitAncilla_isState (Sys := Sys) hρ))
    (operationalTransformationApplyWithAncilla (Sys := Sys) Γ
      (stateWithUnitAncilla (Sys := Sys) ρ)
      (stateWithUnitAncilla_isState (Sys := Sys) hρ))

/-- The state-class action is homogeneous in the operational transformation. -/
theorem operationalTransformationApplyToStateClass_smul {A B : Sys}
    (r : ℝ) (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    {ρ : State A} (hρ : IsState ρ) :
    operationalTransformationApplyToStateClass (Sys := Sys) (r • Δ) ρ hρ =
      r • operationalTransformationApplyToStateClass (Sys := Sys) Δ ρ hρ := by
  unfold operationalTransformationApplyToStateClass
  rw [operationalTransformationApplyWithAncilla_smul]
  exact map_smul (transformationStateMap (Sys := Sys) (ρ_ B).hom
    (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
      (CausalOperationalProbabilisticTheory.rightUnitor_hom_channel (Sys := Sys) B)))
    r
    (operationalTransformationApplyWithAncilla (Sys := Sys) Δ
      (stateWithUnitAncilla (Sys := Sys) ρ)
      (stateWithUnitAncilla_isState (Sys := Sys) hρ))

/-- The free linear-combination map from physical state classes onto the
operational real state space. -/
noncomputable def operationalStatePhysicalClassCombination (A : Sys) :
    (PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) →ₗ[ℝ]
      OperationalStateSpaceReal (Sys := Sys) A :=
  LinearMap.codRestrict
    (OperationalStateSpaceRealSubmodule (Sys := Sys) A)
    (Finsupp.linearCombination ℝ
      (fun x : PhysicalStateClassSet (Sys := Sys) A =>
        (x : StateOperationalQuotient (Sys := Sys) A)))
    (by
      intro l
      rw [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem _ (fun x _ =>
        Submodule.smul_mem _ (l x) (Submodule.subset_span x.2)))

/-- The physical-state-class linear-combination map is onto the operational
real state space. -/
theorem operationalStatePhysicalClassCombination_surjective (A : Sys) :
    Function.Surjective
      (operationalStatePhysicalClassCombination (Sys := Sys) A) := by
  intro x
  rcases (Finsupp.mem_span_iff_linearCombination
      (R := ℝ) (s := PhysicalStateClassSet (Sys := Sys) A)
      (x := (x : StateOperationalQuotient (Sys := Sys) A))).mp x.2 with
    ⟨l, hl⟩
  refine ⟨l, ?_⟩
  apply Subtype.ext
  exact hl

/-- A chosen raw physical state representative for a physical state class. -/
noncomputable def physicalStateClassRepresentative {A : Sys}
    (x : PhysicalStateClassSet (Sys := Sys) A) : State A :=
  Classical.choose x.2

/-- The chosen representative is physical. -/
theorem physicalStateClassRepresentative_isState {A : Sys}
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    IsState (physicalStateClassRepresentative (Sys := Sys) x) :=
  (Classical.choose_spec x.2).1

end CausalOperationalProbabilisticTheory
end OPT
