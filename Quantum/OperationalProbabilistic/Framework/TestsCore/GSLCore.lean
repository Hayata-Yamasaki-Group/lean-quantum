/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: operational quotients of states and effects

Operational equivalence of states and of effects is quotiented into `StateOperationalQuotient`
and `EffectOperationalQuotient`, with their evaluation pairings and the real operational state
space `OperationalStateSpaceReal`.  The action of a transformation on state classes is
`transformationStateMap`.

Related source: CDP (arXiv:1011.6451).
-/

namespace OPT

universe u v w


section OperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
variable [Preadditive Sys]
variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
variable [OperationalProbabilisticTheory Sys]

/-- Top-level wrapper for the ambient event cone. -/
def EventCone (A B : Sys) : Set (A ⟶ B) :=
  OperationalProbabilisticTheory.EventCone A B

/-- Top-level wrapper for channels in an operational probabilistic theory. -/
def IsChannel {A B : Sys} (f : A ⟶ B) : Prop :=
  OperationalProbabilisticTheory.IsChannel f

/-- Top-level wrapper for finite tests. -/
def IsTest {A B : Sys} {ι : Type} [Fintype ι] (T : ι → (A ⟶ B)) : Prop :=
  OperationalProbabilisticTheory.IsTest T

/-- Evaluation of a state candidate by a fixed effect is real-linear. -/
noncomputable def stateEvalLinearMap {A : Sys} (a : Effect A) : State A →ₗ[ℝ] ℝ where
  toFun := fun ρ => prob a ρ
  map_add' := by
    intro ρ σ
    unfold prob
    rw [OperationalProbabilisticTheory.add_comp]
    exact map_add (scalarEval (Sys := Sys)) (ρ ≫ a) (σ ≫ a)
  map_smul' := by
    intro r ρ
    unfold prob
    rw [OperationalProbabilisticTheory.smul_comp]
    exact map_smul (scalarEval (Sys := Sys)) r (ρ ≫ a)

/-- Null subspace of state candidates that all physical effects evaluate as zero. -/
noncomputable def StateOperationalNullSubmodule (A : Sys) : Submodule ℝ (State A) where
  carrier := {δ | ∀ a : Effect A, IsEffect a → prob a δ = 0}
  zero_mem' := by
    intro a _ha
    exact map_zero (stateEvalLinearMap (Sys := Sys) (A := A) a)
  add_mem' := by
    intro δ ε hδ hε a ha
    calc
      prob a (δ + ε) =
          prob a δ + prob a ε := by
            exact map_add (stateEvalLinearMap (Sys := Sys) (A := A) a) δ ε
      _ = 0 := by simp [hδ a ha, hε a ha]
  smul_mem' := by
    intro r δ hδ a ha
    calc
      prob a (r • δ) =
          r • prob a δ := by
            exact map_smul (stateEvalLinearMap (Sys := Sys) (A := A) a) r δ
      _ = 0 := by simp [hδ a ha]

/-- Quotient of state candidates by operational equivalence. -/
abbrev StateOperationalQuotient (A : Sys) : Type v :=
  State A ⧸ StateOperationalNullSubmodule (Sys := Sys) A

/-- Canonical map from state candidates to operational equivalence classes. -/
noncomputable def stateOperationalClass (A : Sys) :
    State A →ₗ[ℝ] StateOperationalQuotient (Sys := Sys) A :=
  (StateOperationalNullSubmodule (Sys := Sys) A).mkQ

/-- Evaluation of an operational state class by a physical effect. -/
noncomputable def stateOperationalQuotientEval {A : Sys} (a : Effect A) (ha : IsEffect a) :
    StateOperationalQuotient (Sys := Sys) A →ₗ[ℝ] ℝ :=
  (StateOperationalNullSubmodule (Sys := Sys) A).liftQ
    (stateEvalLinearMap (Sys := Sys) (A := A) a) (by
      intro δ hδ
      exact hδ a ha)

/-- Quotient evaluation agrees with the raw probability pairing on representatives. -/
@[simp]
theorem stateOperationalQuotientEval_mk {A : Sys} (a : Effect A) (ha : IsEffect a)
    (ρ : State A) :
    stateOperationalQuotientEval (Sys := Sys) a ha (stateOperationalClass (Sys := Sys) A ρ) =
      prob a ρ := by
  rfl

/-- Quotient state evaluation sends zero to zero. -/
@[simp]
theorem stateOperationalQuotientEval_zero {A : Sys} (a : Effect A) (ha : IsEffect a) :
    stateOperationalQuotientEval (Sys := Sys) a ha
      (0 : StateOperationalQuotient (Sys := Sys) A) = 0 :=
  map_zero (stateOperationalQuotientEval (Sys := Sys) a ha)

/-- Quotient state evaluation preserves addition. -/
theorem stateOperationalQuotientEval_add {A : Sys} (a : Effect A) (ha : IsEffect a)
    (δ ε : StateOperationalQuotient (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) a ha (δ + ε) =
      stateOperationalQuotientEval (Sys := Sys) a ha δ +
        stateOperationalQuotientEval (Sys := Sys) a ha ε :=
  map_add (stateOperationalQuotientEval (Sys := Sys) a ha) δ ε

/-- Quotient state evaluation preserves real scalar multiplication. -/
theorem stateOperationalQuotientEval_smul {A : Sys} (a : Effect A) (ha : IsEffect a)
    (r : ℝ) (δ : StateOperationalQuotient (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) a ha (r • δ) =
      r • stateOperationalQuotientEval (Sys := Sys) a ha δ :=
  map_smul (stateOperationalQuotientEval (Sys := Sys) a ha) r δ

/-- Quotient state evaluation is insensitive to the particular proof that an
effect is physical. -/
theorem stateOperationalQuotientEval_congr_effect {A : Sys} {a b : Effect A}
    (h : a = b) (ha : IsEffect a) (hb : IsEffect b)
    (δ : StateOperationalQuotient (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) a ha δ =
      stateOperationalQuotientEval (Sys := Sys) b hb δ := by
  subst h
  rfl

/-- Quotient state evaluation is additive in the effect argument. -/
theorem stateOperationalQuotientEval_add_effect {A : Sys}
    (a b : Effect A) (ha : IsEffect a) (hb : IsEffect b)
    (hab : IsEffect (a + b)) (δ : StateOperationalQuotient (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) (a + b) hab δ =
      stateOperationalQuotientEval (Sys := Sys) a ha δ +
        stateOperationalQuotientEval (Sys := Sys) b hb δ := by
  refine Submodule.Quotient.induction_on
    (StateOperationalNullSubmodule (Sys := Sys) A) δ ?_
  intro ρ
  change prob (a + b) ρ = prob a ρ + prob b ρ
  unfold prob
  rw [OperationalProbabilisticTheory.comp_add]
  exact map_add (scalarEval (Sys := Sys)) (ρ ≫ a) (ρ ≫ b)

/-- Evaluation by the zero effect is the zero functional on state operational classes. -/
theorem stateOperationalQuotientEval_zero_effect {A : Sys}
    (h0 : IsEffect (0 : Effect A)) (δ : StateOperationalQuotient (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) (0 : Effect A) h0 δ = 0 := by
  refine Submodule.Quotient.induction_on
    (StateOperationalNullSubmodule (Sys := Sys) A) δ ?_
  intro ρ
  change prob (0 : Effect A) ρ = 0
  unfold prob
  have hcomp : ρ ≫ (0 : A ⟶ 𝟙_ Sys) = 0 := by simp
  rw [hcomp]
  exact map_zero (scalarEval (Sys := Sys))

/-- If all physical effects evaluate an operational state class as zero, the class is zero. -/
theorem stateOperationalQuotient_eq_zero_of_forall_eval_zero {A : Sys}
    {δ : StateOperationalQuotient (Sys := Sys) A}
    (hδ : ∀ a : Effect A, (ha : IsEffect a) →
      stateOperationalQuotientEval (Sys := Sys) a ha δ = 0) :
    δ = 0 := by
  revert hδ
  refine Submodule.Quotient.induction_on
    (StateOperationalNullSubmodule (Sys := Sys) A) δ ?_
  intro ρ hδ
  rw [Submodule.Quotient.mk_eq_zero]
  intro a ha
  exact hδ a ha

/-- Equivalence classes represented by physical states. -/
noncomputable def PhysicalStateClassSet (A : Sys) :
    Set (StateOperationalQuotient (Sys := Sys) A) :=
  {x | ∃ ρ : State A, IsState ρ ∧ stateOperationalClass (Sys := Sys) A ρ = x}

/-- The real vector space generated by physical states after operational quotienting. -/
noncomputable def OperationalStateSpaceRealSubmodule (A : Sys) :
    Submodule ℝ (StateOperationalQuotient (Sys := Sys) A) :=
  Submodule.span ℝ (PhysicalStateClassSet (Sys := Sys) A)

/-- Operational real state space: the span of physical state classes in the quotient. -/
abbrev OperationalStateSpaceReal (A : Sys) : Type v :=
  OperationalStateSpaceRealSubmodule (Sys := Sys) A

/-- A physical state class belongs to the operational real state space. -/
theorem stateClass_mem_OperationalStateSpaceRealSubmodule {A : Sys} {ρ : State A}
    (hρ : IsState ρ) :
    stateOperationalClass (Sys := Sys) A ρ ∈
      OperationalStateSpaceRealSubmodule (Sys := Sys) A :=
  Submodule.subset_span ⟨ρ, hρ, rfl⟩

/-- Operational real state class represented by a physical state. -/
noncomputable def operationalStateClass {A : Sys} (ρ : State A) (hρ : IsState ρ) :
    OperationalStateSpaceReal (Sys := Sys) A :=
  ⟨stateOperationalClass (Sys := Sys) A ρ,
    stateClass_mem_OperationalStateSpaceRealSubmodule (Sys := Sys) hρ⟩

/-- Raw action of a transformation on state candidates, as a real-linear map. -/
noncomputable def transformationStateMapRaw {A B : Sys} (f : A ⟶ B) :
    State (Sys := Sys) A →ₗ[ℝ] State (Sys := Sys) B where
  toFun := fun ρ => ρ ≫ f
  map_add' := by
    intro ρ σ
    exact OperationalProbabilisticTheory.add_comp (Sys := Sys) ρ σ f
  map_smul' := by
    intro r ρ
    exact OperationalProbabilisticTheory.smul_comp (Sys := Sys) r ρ f

/-- A physical transformation sends physical states to physical states. -/
theorem transformationStateMapRaw_isState {A B : Sys} {f : A ⟶ B}
    (hf : IsTransformation f) {ρ : State A} (hρ : IsState ρ) :
    IsState (transformationStateMapRaw (Sys := Sys) f ρ) :=
  OperationalProbabilisticTheory.transformation_comp (Sys := Sys) hρ hf

/-- A physical transformation induces a linear map on state operational quotients. -/
noncomputable def transformationStateMapQuotient {A B : Sys}
    (f : A ⟶ B) (hf : IsTransformation f) :
    StateOperationalQuotient (Sys := Sys) A →ₗ[ℝ]
      StateOperationalQuotient (Sys := Sys) B :=
  (StateOperationalNullSubmodule (Sys := Sys) A).liftQ
    ((stateOperationalClass (Sys := Sys) B).comp
      (transformationStateMapRaw (Sys := Sys) f))
    (by
      intro δ hδ
      apply stateOperationalQuotient_eq_zero_of_forall_eval_zero (Sys := Sys)
      intro b hb
      change stateOperationalQuotientEval (Sys := Sys) b hb
        (stateOperationalClass (Sys := Sys) B
          (transformationStateMapRaw (Sys := Sys) f δ)) = 0
      rw [stateOperationalQuotientEval_mk]
      simpa [prob, transformationStateMapRaw, Category.assoc] using
        hδ (f ≫ b)
          (OperationalProbabilisticTheory.transformation_comp (Sys := Sys) hf hb))

/-- On representatives, the induced quotient map is postcomposition by the transformation. -/
@[simp]
theorem transformationStateMapQuotient_mk {A B : Sys}
    (f : A ⟶ B) (hf : IsTransformation f) (ρ : State A) :
    transformationStateMapQuotient (Sys := Sys) f hf
        (stateOperationalClass (Sys := Sys) A ρ) =
      stateOperationalClass (Sys := Sys) B
        (transformationStateMapRaw (Sys := Sys) f ρ) := by
  rfl

/-- A physical transformation induces a linear map between the operational real state spaces. -/
noncomputable def transformationStateMap {A B : Sys}
    (f : A ⟶ B) (hf : IsTransformation f) :
    OperationalStateSpaceReal (Sys := Sys) A →ₗ[ℝ]
      OperationalStateSpaceReal (Sys := Sys) B where
  toFun := fun δ =>
    ⟨transformationStateMapQuotient (Sys := Sys) f hf
        (δ : StateOperationalQuotient (Sys := Sys) A),
      by
        exact Submodule.span_induction
          (p := fun x _ =>
            transformationStateMapQuotient (Sys := Sys) f hf x ∈
              OperationalStateSpaceRealSubmodule (Sys := Sys) B)
          (fun x hx => by
            rcases hx with ⟨ρ, hρ, rfl⟩
            rw [transformationStateMapQuotient_mk]
            exact stateClass_mem_OperationalStateSpaceRealSubmodule (Sys := Sys)
              (transformationStateMapRaw_isState (Sys := Sys) hf hρ))
          (by
            change transformationStateMapQuotient (Sys := Sys) f hf 0 ∈
              OperationalStateSpaceRealSubmodule (Sys := Sys) B
            rw [map_zero]
            exact Submodule.zero_mem _)
          (fun x y _hx _hy hx_mem hy_mem => by
            change transformationStateMapQuotient (Sys := Sys) f hf (x + y) ∈
              OperationalStateSpaceRealSubmodule (Sys := Sys) B
            rw [map_add]
            exact Submodule.add_mem _ hx_mem hy_mem)
          (fun r x _hx hx_mem => by
            change transformationStateMapQuotient (Sys := Sys) f hf (r • x) ∈
              OperationalStateSpaceRealSubmodule (Sys := Sys) B
            rw [map_smul]
            exact Submodule.smul_mem _ r hx_mem)
          δ.2⟩
  map_add' := by
    intro δ ε
    ext
    exact map_add (transformationStateMapQuotient (Sys := Sys) f hf)
      (δ : StateOperationalQuotient (Sys := Sys) A)
      (ε : StateOperationalQuotient (Sys := Sys) A)
  map_smul' := by
    intro r δ
    ext
    exact map_smul (transformationStateMapQuotient (Sys := Sys) f hf) r
      (δ : StateOperationalQuotient (Sys := Sys) A)

/-- On physical state classes, the induced real-state-space map is postcomposition. -/
theorem transformationStateMap_mk {A B : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    {ρ : State A} (hρ : IsState ρ) :
    transformationStateMap (Sys := Sys) f hf
        (operationalStateClass (Sys := Sys) ρ hρ) =
      operationalStateClass (Sys := Sys)
        (transformationStateMapRaw (Sys := Sys) f ρ)
        (transformationStateMapRaw_isState (Sys := Sys) hf hρ) := by
  ext
  exact transformationStateMapQuotient_mk (Sys := Sys) f hf ρ

/-- Operational equivalence of effects: all physical states give the same probabilities. -/
def EffectOperationalEquiv {A : Sys} (a b : Effect A) : Prop :=
  ∀ ρ : State A, IsState ρ → prob a ρ = prob b ρ

/-- Evaluation of an effect candidate by a fixed state is real-linear. -/
noncomputable def effectEvalLinearMap {A : Sys} (ρ : State A) : Effect A →ₗ[ℝ] ℝ where
  toFun := fun a => prob a ρ
  map_add' := by
    intro a b
    unfold prob
    rw [OperationalProbabilisticTheory.comp_add]
    exact map_add (scalarEval (Sys := Sys)) (ρ ≫ a) (ρ ≫ b)
  map_smul' := by
    intro r a
    unfold prob
    rw [OperationalProbabilisticTheory.comp_smul]
    exact map_smul (scalarEval (Sys := Sys)) r (ρ ≫ a)

/-- Null subspace of effect candidates that all physical states evaluate as zero. -/
noncomputable def EffectOperationalNullSubmodule (A : Sys) : Submodule ℝ (Effect A) where
  carrier := {ξ | ∀ ρ : State A, IsState ρ → prob ξ ρ = 0}
  zero_mem' := by
    intro ρ _hρ
    exact map_zero (effectEvalLinearMap (Sys := Sys) (A := A) ρ)
  add_mem' := by
    intro ξ η hξ hη ρ hρ
    calc
      prob (ξ + η) ρ =
          prob ξ ρ + prob η ρ := by
            exact map_add (effectEvalLinearMap (Sys := Sys) (A := A) ρ) ξ η
      _ = 0 := by simp [hξ ρ hρ, hη ρ hρ]
  smul_mem' := by
    intro r ξ hξ ρ hρ
    calc
      prob (r • ξ) ρ =
          r • prob ξ ρ := by
            exact map_smul (effectEvalLinearMap (Sys := Sys) (A := A) ρ) r ξ
      _ = 0 := by simp [hξ ρ hρ]

/-- Quotient of effect candidates by operational equivalence. -/
abbrev EffectOperationalQuotient (A : Sys) : Type v :=
  Effect A ⧸ EffectOperationalNullSubmodule (Sys := Sys) A

/-- Canonical map from effect candidates to operational equivalence classes. -/
noncomputable def effectOperationalClass (A : Sys) :
    Effect A →ₗ[ℝ] EffectOperationalQuotient (Sys := Sys) A :=
  (EffectOperationalNullSubmodule (Sys := Sys) A).mkQ

/-- Evaluation of an operational effect class by a physical state. -/
noncomputable def effectOperationalQuotientEval {A : Sys} (ρ : State A) (hρ : IsState ρ) :
    EffectOperationalQuotient (Sys := Sys) A →ₗ[ℝ] ℝ :=
  (EffectOperationalNullSubmodule (Sys := Sys) A).liftQ
    (effectEvalLinearMap (Sys := Sys) (A := A) ρ) (by
      intro ξ hξ
      exact hξ ρ hρ)

/-- Quotient evaluation agrees with the raw probability pairing on representatives. -/
@[simp]
theorem effectOperationalQuotientEval_mk {A : Sys} (ρ : State A) (hρ : IsState ρ)
    (a : Effect A) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
        (effectOperationalClass (Sys := Sys) A a) =
      prob a ρ := by
  rfl

/-- Quotient effect evaluation sends zero to zero. -/
@[simp]
theorem effectOperationalQuotientEval_zero {A : Sys} (ρ : State A) (hρ : IsState ρ) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
      (0 : EffectOperationalQuotient (Sys := Sys) A) = 0 :=
  map_zero (effectOperationalQuotientEval (Sys := Sys) ρ hρ)

/-- Quotient effect evaluation preserves addition. -/
theorem effectOperationalQuotientEval_add {A : Sys} (ρ : State A) (hρ : IsState ρ)
    (ξ η : EffectOperationalQuotient (Sys := Sys) A) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ (ξ + η) =
      effectOperationalQuotientEval (Sys := Sys) ρ hρ ξ +
        effectOperationalQuotientEval (Sys := Sys) ρ hρ η :=
  map_add (effectOperationalQuotientEval (Sys := Sys) ρ hρ) ξ η

/-- Quotient effect evaluation preserves real scalar multiplication. -/
theorem effectOperationalQuotientEval_smul {A : Sys} (ρ : State A) (hρ : IsState ρ)
    (r : ℝ) (ξ : EffectOperationalQuotient (Sys := Sys) A) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ (r • ξ) =
      r • effectOperationalQuotientEval (Sys := Sys) ρ hρ ξ :=
  map_smul (effectOperationalQuotientEval (Sys := Sys) ρ hρ) r ξ

end OperationalProbabilisticTheory
end OPT
