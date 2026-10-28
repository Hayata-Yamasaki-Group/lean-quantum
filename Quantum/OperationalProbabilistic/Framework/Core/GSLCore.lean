/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Geometry.Convex.Cone.Pointed

open CategoryTheory
open scoped MonoidalCategory

/-!
# Abstract operational probabilistic theories

This file contains the abstract core of operational probabilistic theories
(after CDP, arXiv:1011.6451).  The category-theoretic syntax is kept separate from normalization
predicates: `EventCone` is an ambient positive cone for coarse-graining, while
`IsTransformation` and `IsChannel` carry the physical normalization
requirements.
Data-carrying `...Theory` classes in this module intentionally remain `Type` classes.
-/

namespace OPT

universe u v w

/-- Tensor product of scalar events, transported back to the monoidal unit by the left unitor. -/
noncomputable def tensorScalar {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
    (s t : 𝟙_ Sys ⟶ 𝟙_ Sys) : 𝟙_ Sys ⟶ 𝟙_ Sys :=
  (λ_ (𝟙_ Sys)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ Sys)).hom

/- Hom-space linearity (additive/ℝ-linear composition and tensoring) is supplied by
Mathlib's `Preadditive`, `CategoryTheory.Linear ℝ`, `MonoidalPreadditive`, and
`MonoidalLinear ℝ` type classes. -/

/-- Primitive finite tests, before interpreting outcomes as physical transformations. -/
structure RawTestStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] where
  IsTest : ∀ {A B : Sys} {ι : Type} [Fintype ι], (ι → (A ⟶ B)) → Prop
  identity_test :
    ∀ A : Sys, IsTest (A := A) (B := A) (ι := PUnit) (fun _ => 𝟙 A)
  sequential_test :
    ∀ {A B C : Sys} {ι κ : Type} [Fintype ι] [Fintype κ]
      {T : ι → (A ⟶ B)} {U : κ → (B ⟶ C)},
        IsTest T → IsTest U → IsTest (fun x : ι × κ => T x.1 ≫ U x.2)
  parallel_test :
    ∀ {A B C D : Sys} {ι κ : Type} [Fintype ι] [Fintype κ]
      {T : ι → (A ⟶ B)} {U : κ → (C ⟶ D)},
        IsTest T → IsTest U → IsTest (fun x : ι × κ => T x.1 ⊗ₘ U x.2)
  coarse_grain_test :
    ∀ {A B : Sys} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
      {T : ι → (A ⟶ B)} (_hT : IsTest T) (p : ι → κ),
        IsTest (fun k : κ => (Finset.univ.filter (fun i : ι => p i = k)).sum T)

/-- Ambient positive cones used for coarse-graining and refinement.

Each Hom space carries a pointed convex cone (`PointedCone ℝ`, i.e. a submodule
over the nonnegative reals), so closure under zero, addition, and nonnegative
scalar multiplication comes from Mathlib; the fields below only add the
compatibility of the cones with identities, composition, and tensoring. -/
structure EventConeStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] where
  EventCone : ∀ A B : Sys, PointedCone ℝ (A ⟶ B)
  event_id : ∀ A : Sys, (𝟙 A) ∈ EventCone A A
  event_comp :
    ∀ {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C},
      f ∈ EventCone A B → g ∈ EventCone B C → f ≫ g ∈ EventCone A C
  event_tensor :
    ∀ {A B C D : Sys} {f : A ⟶ B} {g : C ⟶ D},
      f ∈ EventCone A B → g ∈ EventCone C D →
        f ⊗ₘ g ∈ EventCone (A ⊗ C) (B ⊗ D)

namespace EventConeStructure

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys]
  [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

end EventConeStructure

/-- Physically allowed, generally subnormalized, transformations. -/
structure TransformationStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys) where
  IsTransformation : ∀ {A B : Sys}, (A ⟶ B) → Prop
  transformation_event :
    ∀ {A B : Sys} {f : A ⟶ B}, IsTransformation f → f ∈ E.EventCone A B
  transformation_zero : ∀ A B : Sys, IsTransformation (0 : A ⟶ B)
  transformation_comp :
    ∀ {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C},
      IsTransformation f → IsTransformation g → IsTransformation (f ≫ g)
  transformation_tensor :
    ∀ {A B C D : Sys} {f : A ⟶ B} {g : C ⟶ D},
      IsTransformation f → IsTransformation g → IsTransformation (f ⊗ₘ g)
  transformation_convex :
    ∀ {A B : Sys} {f g : A ⟶ B} {p q : ℝ},
      0 ≤ p → 0 ≤ q → p + q = 1 →
        IsTransformation f → IsTransformation g →
          IsTransformation (p • f + q • g)

/-- Deterministic transformations, also called channels. -/
structure ChannelStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys)
    (Tr : TransformationStructure Sys E) where
  IsChannel : ∀ {A B : Sys}, (A ⟶ B) → Prop
  channel_transformation :
    ∀ {A B : Sys} {f : A ⟶ B}, IsChannel f → Tr.IsTransformation f
  channel_id : ∀ A : Sys, IsChannel (𝟙 A)
  channel_comp :
    ∀ {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C},
      IsChannel f → IsChannel g → IsChannel (f ≫ g)
  channel_tensor :
    ∀ {A B C D : Sys} {f : A ⟶ B} {g : C ⟶ D},
      IsChannel f → IsChannel g → IsChannel (f ⊗ₘ g)

/-- Monoidal structural isomorphisms are deterministic transformations. -/
structure StructuralChannelStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys)
    (Tr : TransformationStructure Sys E)
    (Ch : ChannelStructure Sys E Tr) where
  leftUnitor_hom_channel : ∀ A : Sys, Ch.IsChannel (λ_ A).hom
  leftUnitor_inv_channel : ∀ A : Sys, Ch.IsChannel (λ_ A).inv
  rightUnitor_hom_channel : ∀ A : Sys, Ch.IsChannel (ρ_ A).hom
  rightUnitor_inv_channel : ∀ A : Sys, Ch.IsChannel (ρ_ A).inv
  associator_hom_channel : ∀ A B C : Sys, Ch.IsChannel (α_ A B C).hom
  associator_inv_channel : ∀ A B C : Sys, Ch.IsChannel (α_ A B C).inv

/-- Causal deterministic effects and their interaction with channels. -/
structure CausalStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys)
    (Tr : TransformationStructure Sys E)
    (Ch : ChannelStructure Sys E Tr) where
  detEffect : ∀ A : Sys, A ⟶ 𝟙_ Sys
  detEffect_channel : ∀ A : Sys, Ch.IsChannel (detEffect A)
  detEffect_unique :
    ∀ {A : Sys} {e : A ⟶ 𝟙_ Sys}, Ch.IsChannel e → e = detEffect A
  transformation_effect_bound :
    ∀ {A B : Sys} {f : A ⟶ B},
      Tr.IsTransformation f → detEffect A - (f ≫ detEffect B) ∈ E.EventCone A (𝟙_ Sys)
  channel_of_transformation_preserves_detEffect :
    ∀ {A B : Sys} {f : A ⟶ B},
      Tr.IsTransformation f → f ≫ detEffect B = detEffect A → Ch.IsChannel f

/-- Finite outcome tests and their coarse-grainings. -/
structure TestStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys)
    (Tr : TransformationStructure Sys E)
    (Ch : ChannelStructure Sys E Tr) where
  IsTest : ∀ {A B : Sys} {ι : Type} [Fintype ι], (ι → (A ⟶ B)) → Prop
  test_event :
    ∀ {A B : Sys} {ι : Type} [Fintype ι] {T : ι → (A ⟶ B)},
      IsTest (A := A) (B := B) (ι := ι) T → ∀ i, T i ∈ E.EventCone A B
  test_transformation :
    ∀ {A B : Sys} {ι : Type} [Fintype ι] {T : ι → (A ⟶ B)},
      IsTest (A := A) (B := B) (ι := ι) T → ∀ i, Tr.IsTransformation (T i)
  transformation_test_outcome :
    ∀ {A B : Sys} {f : A ⟶ B},
      Tr.IsTransformation f →
        ∃ (ι : Type) (_ : Fintype ι) (T : ι → (A ⟶ B)),
          IsTest (A := A) (B := B) (ι := ι) T ∧ ∃ i0 : ι, T i0 = f
  test_coarse_grain :
    ∀ {A B : Sys} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
      {T : ι → (A ⟶ B)} (_hT : IsTest (A := A) (B := B) (ι := ι) T) (p : ι → κ),
        IsTest (fun k : κ => (Finset.univ.filter (fun i : ι => p i = k)).sum T)
  test_partial_sum_transformation :
    ∀ {A B : Sys} {ι : Type} [Fintype ι] {T : ι → (A ⟶ B)}
      (_hT : IsTest (A := A) (B := B) (ι := ι) T) (s : Finset ι),
        Tr.IsTransformation (s.sum T)
  test_total_channel :
    ∀ {A B : Sys} {ι : Type} [Fintype ι] (T : ι → (A ⟶ B)),
      IsTest (A := A) (B := B) (ι := ι) T → Ch.IsChannel (Finset.univ.sum T)
  channel_singleton_test :
    ∀ {A B : Sys} {f : A ⟶ B},
      Ch.IsChannel f → IsTest (A := A) (B := B) (ι := PUnit) (fun _ => f)

/-- Evaluation of closed scalar events as real probabilities. -/
structure ScalarEvaluationStructure (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    (E : EventConeStructure Sys) where
  scalarEval : (𝟙_ Sys ⟶ 𝟙_ Sys) →ₗ[ℝ] ℝ
  scalarEval_id : scalarEval (𝟙 (𝟙_ Sys)) = 1
  scalarEval_nonneg :
    ∀ {s : 𝟙_ Sys ⟶ 𝟙_ Sys}, s ∈ E.EventCone (𝟙_ Sys) (𝟙_ Sys) →
      0 ≤ scalarEval s
  scalarEval_tensor :
    ∀ {s t : 𝟙_ Sys ⟶ 𝟙_ Sys},
      s ∈ E.EventCone (𝟙_ Sys) (𝟙_ Sys) →
      t ∈ E.EventCone (𝟙_ Sys) (𝟙_ Sys) →
      scalarEval (tensorScalar s t) = scalarEval s * scalarEval t

/-- Operational probabilistic theory data on a monoidal category, before causality axioms. -/
class OperationalProbabilisticTheory (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] where
  /-- Primitive finite tests before extracting physical transformation predicates. -/
  rawTest : RawTestStructure Sys
  /-- Ambient event cones. -/
  event : EventConeStructure Sys
  /-- Physical transformations. -/
  transformation : TransformationStructure Sys event
  /-- Deterministic transformations/channels. -/
  channel : ChannelStructure Sys event transformation
  /-- Monoidal structural isomorphisms as channels. -/
  structural : StructuralChannelStructure Sys event transformation channel
  /-- Finite tests. -/
  test : TestStructure Sys event transformation channel
  /-- Scalar evaluation as real probabilities. -/
  scalar : ScalarEvaluationStructure Sys event

/-- Causal operational probabilistic theory data on a monoidal category. -/
class CausalOperationalProbabilisticTheory (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] where
  /-- Operational probabilistic theory data before adding causality. -/
  base : OperationalProbabilisticTheory Sys
  /-- Causal deterministic effects. -/
  causal : CausalStructure Sys base.event base.transformation base.channel

instance instOperationalProbabilisticTheoryOfCausalOperationalProbabilisticTheory
    (Sys : Type u) [Category.{v} Sys] [MonoidalCategory Sys]
    [Preadditive Sys]
    [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
    [HT : CausalOperationalProbabilisticTheory Sys] : OperationalProbabilisticTheory Sys :=
  HT.base

namespace OperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
variable [Preadditive Sys]
variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
variable [HT : OperationalProbabilisticTheory Sys]

/-- Projection for the ambient event cone, as a set of morphisms. -/
def EventCone (A B : Sys) : Set (A ⟶ B) :=
  (HT.event.EventCone A B : Set (A ⟶ B))

/-- Projection for physical transformations. -/
def IsTransformation {A B : Sys} (f : A ⟶ B) : Prop :=
  HT.transformation.IsTransformation f

/-- Physical transformations are closed under sequential composition. -/
theorem transformation_comp {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (f ≫ g) :=
  HT.transformation.transformation_comp hf hg

/-- Projection for deterministic transformations/channels. -/
def IsChannel {A B : Sys} (f : A ⟶ B) : Prop :=
  HT.channel.IsChannel f

/-- Every channel is a physical transformation. -/
theorem channel_transformation {A B : Sys} {f : A ⟶ B}
    (hf : IsChannel f) :
    IsTransformation f :=
  HT.channel.channel_transformation hf

/-- Projection for finite tests. -/
def IsTest {A B : Sys} {ι : Type} [Fintype ι]
    (T : ι → (A ⟶ B)) : Prop :=
  HT.test.IsTest T

/-- Every outcome of a test is a physical transformation. -/
theorem test_transformation {A B : Sys} {ι : Type} [Fintype ι]
    {T : ι → (A ⟶ B)} (hT : IsTest T) :
    ∀ i, IsTransformation (T i) :=
  HT.test.test_transformation hT

/-- Every physical transformation occurs as an outcome of some test. -/
theorem transformation_test_outcome {A B : Sys} {f : A ⟶ B}
    (hf : IsTransformation f) :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → (A ⟶ B)),
      IsTest T ∧ ∃ i0 : ι, T i0 = f :=
  HT.test.transformation_test_outcome hf

/-- Coarse-graining a test along an outcome map yields a test. -/
theorem test_coarse_grain {A B : Sys} {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {T : ι → (A ⟶ B)} (hT : IsTest T) (p : ι → κ) :
    IsTest (fun k : κ => (Finset.univ.filter (fun i : ι => p i = k)).sum T) :=
  HT.test.test_coarse_grain hT p

/-- A channel constitutes a singleton test. -/
theorem channel_singleton_test {A B : Sys} {f : A ⟶ B}
    (hf : IsChannel f) :
    IsTest (A := A) (B := B) (ι := PUnit) (fun _ => f) :=
  HT.test.channel_singleton_test hf

/-- Projection for scalar evaluation. -/
noncomputable def scalarEval : (𝟙_ Sys ⟶ 𝟙_ Sys) →ₗ[ℝ] ℝ :=
  HT.scalar.scalarEval

omit [MonoidalCategory Sys] [Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] HT in
/-- Composition is additive in its left argument. -/
theorem add_comp {A B C : Sys} (f g : A ⟶ B) (h : B ⟶ C) :
    (f + g) ≫ h = f ≫ h + g ≫ h :=
  Preadditive.add_comp _ _ _ f g h

omit [MonoidalCategory Sys] [Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] HT in
/-- Composition is additive in its right argument. -/
theorem comp_add {A B C : Sys} (f : A ⟶ B) (g h : B ⟶ C) :
    f ≫ (g + h) = f ≫ g + f ≫ h :=
  Preadditive.comp_add _ _ _ f g h

omit [MonoidalCategory Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] HT in
/-- Scaling the left factor of a composite scales the composite. -/
theorem smul_comp {A B C : Sys} (r : ℝ) (f : A ⟶ B) (g : B ⟶ C) :
    (r • f) ≫ g = r • (f ≫ g) :=
  CategoryTheory.Linear.smul_comp _ _ _ r f g

omit [MonoidalCategory Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] HT in
/-- Scaling the right factor of a composite scales the composite. -/
theorem comp_smul {A B C : Sys} (r : ℝ) (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ (r • g) = r • (f ≫ g) :=
  CategoryTheory.Linear.comp_smul _ _ _ f r g

omit [Linear ℝ Sys] [MonoidalLinear ℝ Sys] HT in
/-- The tensor product is additive in its left argument. -/
theorem tensor_add_left {A B C D : Sys} (f g : A ⟶ B) (h : C ⟶ D) :
    (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h :=
  MonoidalPreadditive.add_tensor f g h

omit HT in
/-- Scaling the left factor of a tensor product scales the product. -/
theorem tensor_smul_left {A B C D : Sys} (r : ℝ) (f : A ⟶ B) (g : C ⟶ D) :
    (r • f) ⊗ₘ g = r • (f ⊗ₘ g) :=
  by simp [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight]

end OperationalProbabilisticTheory

namespace CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
variable [Preadditive Sys]
variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
variable [HT : CausalOperationalProbabilisticTheory Sys]

/-- Compatibility projection for the ambient event cone, as a set of morphisms. -/
def EventCone (A B : Sys) : Set (A ⟶ B) :=
  (HT.base.event.EventCone A B : Set (A ⟶ B))

/-- Events are closed under sequential composition. -/
theorem event_comp {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C}
    (hf : f ∈ EventCone A B) (hg : g ∈ EventCone B C) :
    f ≫ g ∈ EventCone A C :=
  HT.base.event.event_comp hf hg

/-- Compatibility projection for physical transformations. -/
def IsTransformation {A B : Sys} (f : A ⟶ B) : Prop :=
  HT.base.transformation.IsTransformation f

/-- Every physical transformation is an event. -/
theorem transformation_event {A B : Sys} {f : A ⟶ B}
    (hf : IsTransformation f) :
    f ∈ EventCone A B :=
  HT.base.transformation.transformation_event hf

/-- The zero morphism is a physical transformation. -/
theorem transformation_zero (A B : Sys) :
    IsTransformation (0 : A ⟶ B) :=
  HT.base.transformation.transformation_zero A B

/-- Physical transformations are closed under sequential composition. -/
theorem transformation_comp {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (f ≫ g) :=
  HT.base.transformation.transformation_comp hf hg

/-- Physical transformations are closed under the tensor product. -/
theorem transformation_tensor {A B C D : Sys} {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (f ⊗ₘ g) :=
  HT.base.transformation.transformation_tensor hf hg

/-- Compatibility projection for deterministic transformations/channels. -/
def IsChannel {A B : Sys} (f : A ⟶ B) : Prop :=
  HT.base.channel.IsChannel f

/-- Every channel is a physical transformation. -/
theorem channel_transformation {A B : Sys} {f : A ⟶ B}
    (hf : IsChannel f) :
    IsTransformation f :=
  HT.base.channel.channel_transformation hf

/-- The identity morphism is a channel. -/
theorem channel_id (A : Sys) :
    IsChannel (𝟙 A) :=
  HT.base.channel.channel_id A

/-- Channels are closed under sequential composition. -/
theorem channel_comp {A B C : Sys} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsChannel f) (hg : IsChannel g) :
    IsChannel (f ≫ g) :=
  HT.base.channel.channel_comp hf hg

/-- Channels are closed under the tensor product. -/
theorem channel_tensor {A B C D : Sys} {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsChannel f) (hg : IsChannel g) :
    IsChannel (f ⊗ₘ g) :=
  HT.base.channel.channel_tensor hf hg

/-- The left unitor is a channel. -/
theorem leftUnitor_hom_channel (A : Sys) :
    IsChannel (λ_ A).hom :=
  HT.base.structural.leftUnitor_hom_channel A

/-- The right unitor is a channel. -/
theorem rightUnitor_hom_channel (A : Sys) :
    IsChannel (ρ_ A).hom :=
  HT.base.structural.rightUnitor_hom_channel A

/-- The inverse of the right unitor is a channel. -/
theorem rightUnitor_inv_channel (A : Sys) :
    IsChannel (ρ_ A).inv :=
  HT.base.structural.rightUnitor_inv_channel A

/-- Compatibility projection for the deterministic effect. -/
def detEffect (A : Sys) : A ⟶ 𝟙_ Sys :=
  HT.causal.detEffect A

/-- The deterministic effect is a channel. -/
theorem detEffect_channel (A : Sys) :
    IsChannel (detEffect A) :=
  HT.causal.detEffect_channel A

/-- The deterministic effect is the unique channel from a system to the unit object. -/
theorem detEffect_unique {A : Sys} {e : A ⟶ 𝟙_ Sys}
    (he : IsChannel e) :
    e = detEffect A :=
  HT.causal.detEffect_unique he

/-- Composing a channel with the deterministic effect on its output recovers the deterministic
effect on its input; channels preserve normalization.
-/
theorem channel_preserves_detEffect {A B : Sys} {f : A ⟶ B}
    (hf : IsChannel f) :
    f ≫ detEffect B = detEffect A :=
  detEffect_unique (channel_comp hf (detEffect_channel B))

/-- For a physical transformation, the input deterministic effect minus its pullback along the
transformation is an event.
-/
theorem transformation_effect_bound {A B : Sys} {f : A ⟶ B}
    (hf : IsTransformation f) :
    detEffect A - (f ≫ detEffect B) ∈ EventCone A (𝟙_ Sys) := by
  simpa [detEffect, EventCone] using HT.causal.transformation_effect_bound hf

/-- Compatibility projection for finite tests. -/
def IsTest {A B : Sys} {ι : Type} [Fintype ι]
    (T : ι → (A ⟶ B)) : Prop :=
  HT.base.test.IsTest T

/-- The sum of all outcomes of a test is a channel. -/
theorem test_total_channel {A B : Sys} {ι : Type} [Fintype ι]
    (T : ι → (A ⟶ B)) (hT : IsTest T) :
    IsChannel (Finset.univ.sum T) :=
  HT.base.test.test_total_channel T hT

/-- Compatibility projection for scalar evaluation. -/
noncomputable def scalarEval : (𝟙_ Sys ⟶ 𝟙_ Sys) →ₗ[ℝ] ℝ :=
  HT.base.scalar.scalarEval

/-- Scalar evaluation sends the identity on the unit object to `1`. -/
theorem scalarEval_id :
    scalarEval (Sys := Sys) (𝟙 (𝟙_ Sys)) = 1 :=
  HT.base.scalar.scalarEval_id

/-- Scalar evaluation is nonnegative on events. -/
theorem scalarEval_nonneg {s : 𝟙_ Sys ⟶ 𝟙_ Sys}
    (hs : s ∈ EventCone (𝟙_ Sys) (𝟙_ Sys)) :
    0 ≤ scalarEval (Sys := Sys) s :=
  HT.base.scalar.scalarEval_nonneg hs

omit [MonoidalCategory Sys] [Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys] HT in
/-- Composition is additive in its right argument. -/
theorem comp_add {A B C : Sys} (f : A ⟶ B) (g h : B ⟶ C) :
    f ≫ (g + h) = f ≫ g + f ≫ h :=
  Preadditive.comp_add _ _ _ f g h

end CausalOperationalProbabilisticTheory

end OPT
