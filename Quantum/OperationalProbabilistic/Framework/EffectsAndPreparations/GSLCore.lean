/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: Effects and preparations

The deterministic effect `detEffect` of a causal OPT, its preservation by channels and its
tensor law; completion of finite deterministic families to tests
(`FiniteDeterministicFamilyCompletionTheory`); the state predicates `IsDeterministicState` and
`IsNormalizedState`; rescaled preparations (`RescaledPreparationTheory`); and bounded effects
(`IsBoundedEffect`).
-/

namespace OPT

universe u v w


section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
variable [Preadditive Sys]
variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
variable [CausalOperationalProbabilisticTheory Sys]

/-- Top-level wrapper for the deterministic effect of a causal OPT. -/
def detEffect (A : Sys) : Effect A :=
  CausalOperationalProbabilisticTheory.detEffect A

/-- Channels preserve deterministic effects. -/
theorem channel_preserves_detEffect {A B : Sys} {f : A ⟶ B}
    (hf : IsChannel f) :
    f ≫ detEffect B = detEffect A :=
  CausalOperationalProbabilisticTheory.channel_preserves_detEffect (Sys := Sys) hf

/-- The deterministic effect of a composite system factors as a tensor product.

Not a `@[simp]` lemma: existing proofs use this equality in both directions
(collapsing and expanding), so neither orientation is a safe global normal form. -/
theorem detEffect_tensor (A B : Sys) :
    detEffect (A ⊗ B) = tensorEffect (detEffect A) (detEffect B) := by
  symm
  unfold tensorEffect
  exact CausalOperationalProbabilisticTheory.detEffect_unique (Sys := Sys)
    (CausalOperationalProbabilisticTheory.channel_comp (Sys := Sys)
      (CausalOperationalProbabilisticTheory.channel_tensor (Sys := Sys)
        (CausalOperationalProbabilisticTheory.detEffect_channel (Sys := Sys) A)
        (CausalOperationalProbabilisticTheory.detEffect_channel (Sys := Sys) B))
      (CausalOperationalProbabilisticTheory.leftUnitor_hom_channel (Sys := Sys) (𝟙_ Sys)))

/-- Completion principle needed for the converse direction of CDP Corollary 4.

It states that a finite physical family whose coarse-grained discard is
deterministic is itself a finite test.  This is kept as a `Prop` wrapper rather
than inserted into the primitive `TestStructure`: Corollary 4 consumes it, and
the existence of such a test is an explicit hypothesis. -/
def FiniteDeterministicFamilyCompletesToTest : Prop :=
  ∀ {A B : Sys} {ι : Type} [Fintype ι] (T : ι → (A ⟶ B)),
    (∀ i : ι, IsTransformation (Sys := Sys) (T i)) →
      (Finset.univ.sum T) ≫ detEffect (Sys := Sys) B = detEffect (Sys := Sys) A →
        IsTest (Sys := Sys) (A := A) (B := B) (ι := ι) T

/-- Assumption that finite deterministic families complete to tests, packaged as a class.

It is kept separate from `CausalOperationalProbabilisticTheory`.  Corollary 4 uses it as a
hypothesis; it is not proved here, and an instance has to be supplied by a proof or by a
concrete theory. -/
class FiniteDeterministicFamilyCompletionTheory (Sys : Type u) [Category.{v} Sys]
    [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    [CausalOperationalProbabilisticTheory Sys] : Prop where
  completes_to_test :
    FiniteDeterministicFamilyCompletesToTest (Sys := Sys)

/-- Projection from the finite deterministic-family completion producer
interface. -/
theorem finiteDeterministicFamilyCompletesToTest
    [FiniteDeterministicFamilyCompletionTheory Sys] :
    FiniteDeterministicFamilyCompletesToTest (Sys := Sys) :=
  FiniteDeterministicFamilyCompletionTheory.completes_to_test (Sys := Sys)

/-- Physical transformations cannot increase the deterministic effect. -/
theorem transformation_effect_bound {A B : Sys} {f : A ⟶ B}
    (hf : IsTransformation f) :
    LeEffect (f ≫ detEffect B) (detEffect A) := by
  intro ρ hρ
  have hcone : detEffect A - (f ≫ detEffect B) ∈ EventCone A (𝟙_ Sys) :=
    CausalOperationalProbabilisticTheory.transformation_effect_bound hf
  have hclosed : ρ ≫ (detEffect A - (f ≫ detEffect B)) ∈
      EventCone (𝟙_ Sys) (𝟙_ Sys) := by
    exact CausalOperationalProbabilisticTheory.event_comp
      (CausalOperationalProbabilisticTheory.transformation_event hρ) hcone
  have hnonneg :
      0 ≤ scalarEval (Sys := Sys) (ρ ≫ (detEffect A - (f ≫ detEffect B))) :=
    CausalOperationalProbabilisticTheory.scalarEval_nonneg hclosed
  have hcomp_neg :
      ρ ≫ (-(f ≫ detEffect B)) = -(ρ ≫ (f ≫ detEffect B)) := by simp
  have hcomp_sub :
      ρ ≫ (detEffect A - (f ≫ detEffect B)) =
        ρ ≫ detEffect A - ρ ≫ (f ≫ detEffect B) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, CausalOperationalProbabilisticTheory.comp_add, hcomp_neg]
  have hprob :
      scalarEval (Sys := Sys) (ρ ≫ (detEffect A - (f ≫ detEffect B))) =
        prob (detEffect A) ρ - prob (f ≫ detEffect B) ρ := by
    rw [hcomp_sub]
    simp [prob]
  rw [hprob] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Deterministic states are channels with trivial input. -/
def IsDeterministicState {A : Sys} (ρ : State A) : Prop :=
  IsChannel ρ

/-- Deterministic states are physical states. -/
theorem isDeterministicState_isState {A : Sys} {ρ : State A}
    (hρ : IsDeterministicState ρ) : IsState ρ :=
  CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys) hρ

/-- Normalized states return probability one against the deterministic effect. -/
def IsNormalizedState {A : Sys} (ρ : State A) : Prop :=
  IsState ρ ∧ prob (detEffect A) ρ = 1

/-- Source-backed rescaling principle for preparation events.

This is Ref.21, lines 1179--1189, where the authors state “we will always
assume this fact.”  Thus  is the original standing assumption itself, now
disclosed as a primitive foundation assumption rather than a result to be
derived.  Causality alone gives `0 ≤ (e_A|ρ) ≤ 1`, but not closure under the
inverse scalar needed to rescale a nonzero preparation event into a
deterministic state.  The field records the resulting equality in the current
raw Lean presentation; reflecting operational equality back to such raw
equality is the separate role of `StateRawExtensionalityTheory`. -/
class RescaledPreparationTheory (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    [CausalOperationalProbabilisticTheory Sys] : Prop where
  rescaled_deterministic_preparation :
    ∀ {A : Sys} (ρ : State A),
      IsState ρ →
      0 < prob (detEffect A) ρ →
      ∃ σ : State A,
        IsDeterministicState σ ∧ ρ = prob (detEffect A) ρ • σ

/-- Wrapper for the source-backed deterministic rescaling principle. -/
theorem rescaled_deterministic_preparation [RescaledPreparationTheory Sys]
    {A : Sys} (ρ : State A) (hρ : IsState ρ)
    (hprob : 0 < prob (detEffect A) ρ) :
    ∃ σ : State A,
      IsDeterministicState σ ∧ ρ = prob (detEffect A) ρ • σ :=
  RescaledPreparationTheory.rescaled_deterministic_preparation ρ hρ hprob

/-- Bounded physical effects have probabilities in `[0,1]` on normalized states. -/
def IsBoundedEffect {A : Sys} (a : Effect A) : Prop :=
  IsEffect a ∧ ∀ ρ : State A, IsNormalizedState ρ → 0 ≤ prob a ρ ∧ prob a ρ ≤ 1

/-- The deterministic effect on the monoidal unit is the identity scalar. -/
theorem detEffect_unit : detEffect (Sys := Sys) (𝟙_ Sys) = 𝟙 (𝟙_ Sys) := by
  symm
  exact CausalOperationalProbabilisticTheory.detEffect_unique (Sys := Sys)
    (CausalOperationalProbabilisticTheory.channel_id (Sys := Sys) (𝟙_ Sys))

/-- Deterministic states are normalized states. -/
theorem isDeterministicState_isNormalizedState {A : Sys} {ρ : State A}
    (hρ : IsDeterministicState ρ) : IsNormalizedState ρ := by
  constructor
  · exact isDeterministicState_isState (Sys := Sys) hρ
  · have hpres : ρ ≫ detEffect A = detEffect (𝟙_ Sys) :=
      channel_preserves_detEffect (Sys := Sys) hρ
    rw [prob, hpres, detEffect_unit (Sys := Sys)]
    simpa using CausalOperationalProbabilisticTheory.scalarEval_id (Sys := Sys)

/-- Channels send normalized states to normalized states. -/
theorem normalizedState_comp_channel {A B : Sys} {ρ : State A}
    (hρ : IsNormalizedState (Sys := Sys) ρ) {f : A ⟶ B}
    (hf : IsChannel (Sys := Sys) f) :
    IsNormalizedState (Sys := Sys) (ρ ≫ f) := by
  constructor
  · exact CausalOperationalProbabilisticTheory.transformation_comp
      (Sys := Sys) hρ.1
      (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys) hf)
  · have hpres : f ≫ detEffect (Sys := Sys) B = detEffect (Sys := Sys) A :=
      channel_preserves_detEffect (Sys := Sys) hf
    unfold prob
    rw [Category.assoc, hpres]
    exact hρ.2

/-- The normalized-state form of the deterministic rescaling principle. -/
theorem rescaled_preparation [RescaledPreparationTheory Sys]
    {A : Sys} (ρ : State A) (hρ : IsState ρ)
    (hprob : 0 < prob (detEffect A) ρ) :
    ∃ ρbar : State A,
      IsNormalizedState ρbar ∧ ρ = prob (detEffect A) ρ • ρbar := by
  rcases rescaled_deterministic_preparation (Sys := Sys) ρ hρ hprob with
    ⟨σ, hσ, hscale⟩
  exact ⟨σ, isDeterministicState_isNormalizedState (Sys := Sys) hσ, hscale⟩

end CausalOperationalProbabilisticTheory
end OPT
