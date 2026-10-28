/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: probability bounds and the state-norm evaluation range

Probability bounds for states and effects (`prob_nonneg_of_isState_isEffect`,
`prob_le_detEffect_of_isState_isEffect`, `prob_le_one_of_isNormalizedState_isEffect`), bounded
effects (`boundedEffect_of_isEffect`), separation of operational effects by normalized states,
and the evaluation range `operationalStateNormEvalRange`, which is nonempty and bounded above
and below for states.
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The deterministic effect is a physical effect. -/
theorem detEffect_isEffect (A : Sys) : IsEffect (detEffect A) :=
  CausalOperationalProbabilisticTheory.channel_transformation
    (CausalOperationalProbabilisticTheory.detEffect_channel (Sys := Sys) A)

/-- The two outcomes of a binary observation test sum to the deterministic effect. -/
theorem binaryObservation_total_eq_detEffect {A : Sys}
    (M : BinaryObservationTest (Sys := Sys) A) :
    M.outcome BinaryObservationIndex.zero + M.outcome BinaryObservationIndex.one =
      detEffect A := by
  have htotal : Finset.univ.sum M.outcome = detEffect A := by
    simpa [detEffect] using
      CausalOperationalProbabilisticTheory.detEffect_unique (Sys := Sys)
        (CausalOperationalProbabilisticTheory.test_total_channel M.outcome M.isTest)
  rw [sum_binaryObservationIndex] at htotal
  exact htotal

/-- The zero effect is a physical effect. -/
theorem zero_isEffect (A : Sys) : IsEffect (0 : Effect A) :=
  CausalOperationalProbabilisticTheory.transformation_zero (Sys := Sys) A (𝟙_ Sys)

/-- Probabilities of physical states against physical effects are nonnegative. -/
theorem prob_nonneg_of_isState_isEffect {A : Sys} {ρ : State A} {a : Effect A}
    (hρ : IsState ρ) (ha : IsEffect a) : 0 ≤ prob a ρ := by
  have hclosed : ρ ≫ a ∈ EventCone (𝟙_ Sys) (𝟙_ Sys) := by
    exact CausalOperationalProbabilisticTheory.event_comp
      (CausalOperationalProbabilisticTheory.transformation_event hρ)
      (CausalOperationalProbabilisticTheory.transformation_event ha)
  exact CausalOperationalProbabilisticTheory.scalarEval_nonneg hclosed

/-- Physical states have deterministic-effect probability at most one. -/
theorem prob_detEffect_le_one_of_isState {A : Sys} {ρ : State A}
    (hρ : IsState ρ) : prob (detEffect A) ρ ≤ 1 := by
  have hI_state : IsState (𝟙 (𝟙_ Sys)) := by
    exact CausalOperationalProbabilisticTheory.channel_transformation
      (CausalOperationalProbabilisticTheory.channel_id (Sys := Sys) (𝟙_ Sys))
  have hle : LeEffect (ρ ≫ detEffect A) (detEffect (𝟙_ Sys)) := by
    exact transformation_effect_bound (Sys := Sys) hρ
  have hraw := hle (𝟙 (𝟙_ Sys)) hI_state
  have hleft : prob (ρ ≫ detEffect A) (𝟙 (𝟙_ Sys)) = prob (detEffect A) ρ := by
    simp [prob]
  have hright : prob (detEffect (𝟙_ Sys)) (𝟙 (𝟙_ Sys)) = 1 := by
    rw [prob, detEffect_unit (Sys := Sys)]
    simpa using CausalOperationalProbabilisticTheory.scalarEval_id (Sys := Sys)
  simpa [hleft, hright] using hraw

/-- A physical effect is bounded above by the deterministic effect on every physical state. -/
theorem prob_le_detEffect_of_isState_isEffect {A : Sys} {ρ : State A} {a : Effect A}
    (hρ : IsState ρ) (ha : IsEffect a) : prob a ρ ≤ prob (detEffect A) ρ := by
  have hle : LeEffect (a ≫ detEffect (Sys := Sys) (𝟙_ Sys)) (detEffect (Sys := Sys) A) := by
    exact transformation_effect_bound (Sys := Sys) ha
  have hle' : LeEffect a (detEffect (Sys := Sys) A) := by
    simpa [detEffect_unit (Sys := Sys)] using hle
  exact hle' ρ hρ

/-- Physical effects have probability at most one on physical states. -/
theorem prob_le_one_of_isState_isEffect {A : Sys} {ρ : State A} {a : Effect A}
    (hρ : IsState ρ) (ha : IsEffect a) : prob a ρ ≤ 1 :=
  le_trans (prob_le_detEffect_of_isState_isEffect (Sys := Sys) hρ ha)
    (prob_detEffect_le_one_of_isState (Sys := Sys) hρ)

/-- Physical effects evaluate to zero on zero-weight physical states. -/
theorem prob_eq_zero_of_prob_detEffect_eq_zero
    {A : Sys} {ρ : State A} {a : Effect A} (hρ : IsState ρ)
    (hprob : prob (detEffect A) ρ = 0) (ha : IsEffect a) :
    prob a ρ = 0 := by
  have hnonneg : 0 ≤ prob a ρ :=
    prob_nonneg_of_isState_isEffect (Sys := Sys) hρ ha
  have hle_det : prob a ρ ≤ prob (detEffect A) ρ :=
    prob_le_detEffect_of_isState_isEffect (Sys := Sys) hρ ha
  exact le_antisymm (by simpa [hprob] using hle_det) hnonneg

/-- Physical effect classes evaluate to zero on zero-weight physical states. -/
theorem effectOperationalQuotientEval_effectClass_eq_zero_of_prob_detEffect_eq_zero
    {A : Sys} {ρ : State A} {a : Effect A} (hρ : IsState ρ)
    (hprob : prob (detEffect A) ρ = 0) (ha : IsEffect a) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
      (effectOperationalClass (Sys := Sys) A a) = 0 := by
  rw [effectOperationalQuotientEval_mk]
  exact prob_eq_zero_of_prob_detEffect_eq_zero (Sys := Sys) hρ hprob ha

/-- Operational real effect classes evaluate to zero on zero-weight physical states. -/
theorem effectOperationalQuotientEval_eq_zero_of_prob_detEffect_eq_zero
    {A : Sys} {ρ : State A} (hρ : IsState ρ)
    (hprob : prob (detEffect A) ρ = 0)
    (ξ : OperationalEffectSpaceReal (Sys := Sys) A) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
      (ξ : EffectOperationalQuotient (Sys := Sys) A) = 0 := by
  exact Submodule.span_induction
    (p := fun x _ => effectOperationalQuotientEval (Sys := Sys) ρ hρ x = 0)
    (fun x hx => by
      rcases hx with ⟨a, ha, rfl⟩
      exact effectOperationalQuotientEval_effectClass_eq_zero_of_prob_detEffect_eq_zero
        (Sys := Sys) hρ hprob ha)
    (effectOperationalQuotientEval_zero (Sys := Sys) ρ hρ)
    (fun x y _hx _hy hx_zero hy_zero => by
      change effectOperationalQuotientEval (Sys := Sys) ρ hρ (x + y) = 0
      rw [effectOperationalQuotientEval_add, hx_zero, hy_zero, add_zero])
    (fun r x _hx hx_zero => by
      change effectOperationalQuotientEval (Sys := Sys) ρ hρ (r • x) = 0
      rw [effectOperationalQuotientEval_smul, hx_zero, smul_zero])
    ξ.2

/-- Operational effect evaluation is linear in a rescaled physical state. -/
theorem effectOperationalQuotientEval_eq_smul_of_state_eq_smul
    {A : Sys} {ρ ρbar : State A} {p : ℝ}
    (hρ : IsState ρ) (hρbar : IsState ρbar)
    (hscale : ρ = p • ρbar)
    (ξ : OperationalEffectSpaceReal (Sys := Sys) A) :
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
      (ξ : EffectOperationalQuotient (Sys := Sys) A) =
      p • effectOperationalQuotientEval (Sys := Sys) ρbar hρbar
        (ξ : EffectOperationalQuotient (Sys := Sys) A) := by
  refine Submodule.Quotient.induction_on
    (EffectOperationalNullSubmodule (Sys := Sys) A)
    (ξ : EffectOperationalQuotient (Sys := Sys) A) ?_
  intro a
  change
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
      (effectOperationalClass (Sys := Sys) A a) =
      p • effectOperationalQuotientEval (Sys := Sys) ρbar hρbar
        (effectOperationalClass (Sys := Sys) A a)
  calc
    effectOperationalQuotientEval (Sys := Sys) ρ hρ
        (effectOperationalClass (Sys := Sys) A a) =
        prob a ρ := by
      rw [effectOperationalQuotientEval_mk]
    _ = prob a (p • ρbar) := by
      rw [hscale]
    _ = p • prob a ρbar := by
      exact map_smul (stateEvalLinearMap (Sys := Sys) (A := A) a) p ρbar
    _ = p • effectOperationalQuotientEval (Sys := Sys) ρbar hρbar
        (effectOperationalClass (Sys := Sys) A a) := by
      rw [effectOperationalQuotientEval_mk]

/-- Rescaled preparations transport effect evaluation to a normalized state. -/
theorem effectOperationalQuotientEval_rescaled_preparation
    [RescaledPreparationTheory Sys]
    {A : Sys} {ρ : State A} (hρ : IsState ρ)
    (hprob : 0 < prob (detEffect A) ρ)
    (ξ : OperationalEffectSpaceReal (Sys := Sys) A) :
    ∃ ρbar : State A, ∃ hρbar : IsNormalizedState ρbar,
      effectOperationalQuotientEval (Sys := Sys) ρ hρ
        (ξ : EffectOperationalQuotient (Sys := Sys) A) =
        prob (detEffect A) ρ •
          effectOperationalQuotientEval (Sys := Sys) ρbar hρbar.1
            (ξ : EffectOperationalQuotient (Sys := Sys) A) := by
  rcases rescaled_preparation (Sys := Sys) ρ hρ hprob with
    ⟨ρbar, hρbar, hscale⟩
  exact ⟨ρbar, hρbar,
    effectOperationalQuotientEval_eq_smul_of_state_eq_smul
      (Sys := Sys) hρ hρbar.1 hscale ξ⟩

/-- If every physical state evaluates an operational effect class as zero, the class is zero. -/
theorem effectOperationalQuotient_eq_zero_of_forall_state_eval_eq_zero {A : Sys}
    {ξ : EffectOperationalQuotient (Sys := Sys) A}
    (hξ : ∀ ρ : State A, (hρ : IsState ρ) →
      effectOperationalQuotientEval (Sys := Sys) ρ hρ ξ = 0) :
    ξ = 0 := by
  revert hξ
  refine Submodule.Quotient.induction_on
    (EffectOperationalNullSubmodule (Sys := Sys) A) ξ ?_
  intro a hξ
  rw [Submodule.Quotient.mk_eq_zero]
  intro ρ hρ
  simpa [effectOperationalQuotientEval_mk] using hξ ρ hρ

/-- Normalized states separate operational real effects. -/
theorem normalizedStates_separate_operationalEffects
    [RescaledPreparationTheory Sys]
    {A : Sys} (ξ : OperationalEffectSpaceReal (Sys := Sys) A)
    (hξ : ∀ ρ : State A, (hρ : IsNormalizedState ρ) →
      effectOperationalQuotientEval (Sys := Sys) ρ hρ.1
        (ξ : EffectOperationalQuotient (Sys := Sys) A) = 0) :
    ξ = 0 := by
  apply Subtype.ext
  apply effectOperationalQuotient_eq_zero_of_forall_state_eval_eq_zero (Sys := Sys)
  intro ρ hρ
  by_cases hprob_zero : prob (detEffect A) ρ = 0
  · exact effectOperationalQuotientEval_eq_zero_of_prob_detEffect_eq_zero
      (Sys := Sys) hρ hprob_zero ξ
  · have hprob_nonneg : 0 ≤ prob (detEffect A) ρ :=
      prob_nonneg_of_isState_isEffect (Sys := Sys) hρ (detEffect_isEffect (Sys := Sys) A)
    have hprob_pos : 0 < prob (detEffect A) ρ :=
      lt_of_le_of_ne hprob_nonneg (Ne.symm hprob_zero)
    rcases effectOperationalQuotientEval_rescaled_preparation
        (Sys := Sys) hρ hprob_pos ξ with
      ⟨ρbar, hρbar, heval⟩
    rw [heval, hξ ρbar hρbar, smul_zero]

/-- Two operational real effects are equal if normalized states give the same evaluations. -/
theorem normalizedStates_ext_operationalEffects
    [RescaledPreparationTheory Sys]
    {A : Sys} (ξ η : OperationalEffectSpaceReal (Sys := Sys) A)
    (hξη : ∀ ρ : State A, (hρ : IsNormalizedState ρ) →
      effectOperationalQuotientEval (Sys := Sys) ρ hρ.1
        (ξ : EffectOperationalQuotient (Sys := Sys) A) =
      effectOperationalQuotientEval (Sys := Sys) ρ hρ.1
        (η : EffectOperationalQuotient (Sys := Sys) A)) :
    ξ = η := by
  have hdiff : ξ - η = 0 := by
    apply normalizedStates_separate_operationalEffects (Sys := Sys)
    intro ρ hρ
    change
      effectOperationalQuotientEval (Sys := Sys) ρ hρ.1
        ((ξ : EffectOperationalQuotient (Sys := Sys) A) -
          (η : EffectOperationalQuotient (Sys := Sys) A)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hξη ρ hρ)
  exact sub_eq_zero.mp hdiff

/-- Physical effects have probability at most one on normalized states. -/
theorem prob_le_one_of_isNormalizedState_isEffect {A : Sys} {ρ : State A} {a : Effect A}
    (hρ : IsNormalizedState ρ) (ha : IsEffect a) : prob a ρ ≤ 1 := by
  have hle : LeEffect (a ≫ detEffect (Sys := Sys) (𝟙_ Sys)) (detEffect (Sys := Sys) A) := by
    exact transformation_effect_bound (Sys := Sys) ha
  have hle' : LeEffect a (detEffect (Sys := Sys) A) := by
    simpa [detEffect_unit (Sys := Sys)] using hle
  have hprob_le : prob a ρ ≤ prob (detEffect (Sys := Sys) A) ρ :=
    hle' ρ hρ.1
  simpa [hρ.2] using hprob_le

/-- Every physical effect is bounded on normalized states. -/
theorem boundedEffect_of_isEffect {A : Sys} {a : Effect A}
    (ha : IsEffect a) : IsBoundedEffect a := by
  constructor
  · exact ha
  · intro ρ hρ
    exact ⟨prob_nonneg_of_isState_isEffect (Sys := Sys) hρ.1 ha,
      prob_le_one_of_isNormalizedState_isEffect (Sys := Sys) hρ ha⟩

/-- The zero effect is bounded. -/
theorem zero_boundedEffect (A : Sys) : IsBoundedEffect (0 : Effect A) :=
  boundedEffect_of_isEffect (Sys := Sys) (zero_isEffect (Sys := Sys) A)

/-- The deterministic effect is bounded on normalized states. -/
theorem detEffect_bounded (A : Sys) : IsBoundedEffect (detEffect A) := by
  exact boundedEffect_of_isEffect (Sys := Sys) (detEffect_isEffect (Sys := Sys) A)

/-- Bounded physical effects are nonempty: the deterministic effect is one. -/
theorem boundedEffectSubtype_nonempty (A : Sys) :
    Nonempty {a : Effect A // IsBoundedEffect a} :=
  ⟨⟨detEffect A, detEffect_bounded (Sys := Sys) A⟩⟩

/-- The state-side evaluation range used by the operational norm formula. -/
noncomputable def operationalStateNormEvalRange {A : Sys}
    (δ : StateOperationalQuotient (Sys := Sys) A) : Set ℝ :=
  (fun a : {a : Effect A // IsBoundedEffect a} =>
    stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1 δ) '' Set.univ

/-- The state-side operational-norm evaluation range is nonempty. -/
theorem operationalStateNorm_evalRange_nonempty {A : Sys}
    (δ : OperationalStateSpaceReal A) :
    (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)).Nonempty := by
  rcases boundedEffectSubtype_nonempty (Sys := Sys) A with ⟨a⟩
  exact ⟨stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1 δ, ⟨a, trivial, rfl⟩⟩

/-- On a physical state class, bounded effects give a state-side evaluation range
bounded above by one. -/
theorem operationalStateNorm_evalRange_bddAbove_of_isState
    {A : Sys} {ρ : State A} (hρ : IsState ρ) :
    BddAbove ((fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        ((⟨stateOperationalClass (Sys := Sys) A ρ,
          stateClass_mem_OperationalStateSpaceRealSubmodule (Sys := Sys) hρ⟩ :
          OperationalStateSpaceReal (Sys := Sys) A))) '' Set.univ) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨a, _ha_univ, rfl⟩
  simpa [stateOperationalQuotientEval_mk] using
    prob_le_one_of_isState_isEffect (Sys := Sys) hρ a.2.1

/-- On a physical state class, bounded effects give a state-side evaluation range
bounded below by zero. -/
theorem operationalStateNorm_evalRange_bddBelow_of_isState
    {A : Sys} {ρ : State A} (hρ : IsState ρ) :
    BddBelow ((fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        ((⟨stateOperationalClass (Sys := Sys) A ρ,
          stateClass_mem_OperationalStateSpaceRealSubmodule (Sys := Sys) hρ⟩ :
          OperationalStateSpaceReal (Sys := Sys) A))) '' Set.univ) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨a, _ha_univ, rfl⟩
  simpa [stateOperationalQuotientEval_mk] using
    prob_nonneg_of_isState_isEffect (Sys := Sys) hρ a.2.1

end CausalOperationalProbabilisticTheory
end OPT
