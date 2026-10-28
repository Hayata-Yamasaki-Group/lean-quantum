/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.UnitTrace.GSLCore

/-!
# Operational probabilistic theory instances for finite-dimensional quantum systems

The event cone consists of completely positive maps.  A finite test is a
family of completely positive maps whose total is a channel.  The remaining
structures package the closure and trace-effect results proved in the
preceding calculus files.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory

variable {A B C D : Sys}

/-- A quantum test is a finite CP family whose total map is trace preserving. -/
def IsQuantumTest {A B : Sys} {ι : Type} [Fintype ι]
    (T : ι → (A ⟶ B)) : Prop :=
  (∀ i, IsEvent (T i)) ∧ IsChannel (Finset.univ.sum T)

private theorem quantumTest_identity (A : Sys) :
    IsQuantumTest (A := A) (B := A) (fun _ : PUnit => 𝟙 A) := by
  constructor
  · intro i
    exact isEvent_id
  · simpa using (isChannel_id (A := A))

private theorem quantumTest_sequential
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {T : ι → (A ⟶ B)} {U : κ → (B ⟶ C)}
    (hT : IsQuantumTest T) (hU : IsQuantumTest U) :
    IsQuantumTest (fun x : ι × κ => T x.1 ≫ U x.2) := by
  constructor
  · intro x
    exact QuantumChannel.comp_isCompletelyPositive
      (HPHom.toRawSuperoperator (T x.1))
      (HPHom.toRawSuperoperator (U x.2))
      (hT.1 x.1) (hU.1 x.2)
  · have hsum :
        (∑ x : ι × κ, T x.1 ≫ U x.2) =
          (∑ i, T i) ≫ ∑ j, U j := by
      rw [Preadditive.sum_comp]
      simp_rw [Preadditive.comp_sum]
      exact Fintype.sum_prod_type _
    exact hsum.symm ▸ isChannel_comp hT.2 hU.2

private theorem quantumTest_parallel
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {T : ι → (A ⟶ B)} {U : κ → (C ⟶ D)}
    (hT : IsQuantumTest T) (hU : IsQuantumTest U) :
    IsQuantumTest (fun x : ι × κ => T x.1 ⊗ₘ U x.2) := by
  constructor
  · intro x
    exact tensorHom_isEvent (hT.1 x.1) (hU.1 x.2)
  · have hsum :
        (∑ x : ι × κ, T x.1 ⊗ₘ U x.2) =
          (∑ i, T i) ⊗ₘ ∑ j, U j := by
      calc
        (∑ x : ι × κ, T x.1 ⊗ₘ U x.2) =
            ∑ i, ∑ j, T i ⊗ₘ U j := Fintype.sum_prod_type _
        _ = ∑ i, T i ⊗ₘ ∑ j, U j := by
          apply Finset.sum_congr rfl
          intro i _
          exact (CategoryTheory.tensor_sum Finset.univ (T i) U).symm
        _ = (∑ i, T i) ⊗ₘ ∑ j, U j := by
          exact (CategoryTheory.sum_tensor Finset.univ (∑ j, U j) T).symm
    exact hsum.symm ▸ isChannel_tensor hT.2 hU.2

private theorem quantumTest_coarseGrain
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {T : ι → (A ⟶ B)} (hT : IsQuantumTest T) (p : ι → κ) :
    IsQuantumTest
      (fun k : κ => (Finset.univ.filter (fun i : ι => p i = k)).sum T) := by
  constructor
  · intro k
    exact (partialSum_isTransformation hT.1 hT.2
      (Finset.univ.filter (fun i : ι => p i = k))).1
  · have hsum :
        (∑ k : κ, (Finset.univ.filter (fun i : ι => p i = k)).sum T) =
          Finset.univ.sum T := by
      simpa using Finset.sum_fiberwise (Finset.univ : Finset ι) p T
    exact hsum.symm ▸ hT.2

/-- The completely positive cone on a quantum Hom space. -/
def quantumEventCone (A B : Sys) : PointedCone ℝ (A ⟶ B) where
  carrier := {f | IsEvent f}
  zero_mem' := isEvent_zero
  add_mem' hf hg := isEvent_add hf hg
  smul_mem' r f hf := by
    exact isEvent_nonneg_smul r.property hf

/-- Primitive quantum tests. -/
def quantumRawTestStructure : OPT.RawTestStructure Sys where
  IsTest := @IsQuantumTest
  identity_test := quantumTest_identity
  sequential_test hT hU := quantumTest_sequential hT hU
  parallel_test hT hU := quantumTest_parallel hT hU
  coarse_grain_test hT p := quantumTest_coarseGrain hT p

/-- Completely positive maps as the ambient event cones. -/
def quantumEventConeStructure : OPT.EventConeStructure Sys where
  EventCone := quantumEventCone
  event_id A := isEvent_id (A := A)
  event_comp hf hg := by
    exact QuantumChannel.comp_isCompletelyPositive
      (HPHom.toRawSuperoperator _)
      (HPHom.toRawSuperoperator _) hf hg
  event_tensor hf hg := tensorHom_isEvent hf hg

/-- CP trace-nonincreasing maps as physical transformations. -/
def quantumTransformationStructure :
    OPT.TransformationStructure Sys quantumEventConeStructure where
  IsTransformation := @IsTransformation
  transformation_event hf := hf.1
  transformation_zero A B := isTransformation_zero (A := A) (B := B)
  transformation_comp hf hg := isTransformation_comp hf hg
  transformation_tensor hf hg := isTransformation_tensor hf hg
  transformation_convex hp hq hpq hf hg :=
    isTransformation_convex hp hq hpq hf hg

/-- Completely positive trace-preserving maps as channels. -/
def quantumChannelStructure :
    OPT.ChannelStructure Sys quantumEventConeStructure
      quantumTransformationStructure where
  IsChannel := @IsChannel
  channel_transformation hf := isChannel_isTransformation hf
  channel_id A := isChannel_id (A := A)
  channel_comp hf hg := isChannel_comp hf hg
  channel_tensor hf hg := isChannel_tensor hf hg

/-- The canonical unitors and associator are quantum channels. -/
def quantumStructuralChannelStructure :
    OPT.StructuralChannelStructure Sys quantumEventConeStructure
      quantumTransformationStructure quantumChannelStructure where
  leftUnitor_hom_channel := leftUnitor_hom_isChannel
  leftUnitor_inv_channel := leftUnitor_inv_isChannel
  rightUnitor_hom_channel := rightUnitor_hom_isChannel
  rightUnitor_inv_channel := rightUnitor_inv_isChannel
  associator_hom_channel := associator_hom_isChannel
  associator_inv_channel := associator_inv_isChannel

/-- Finite quantum instruments as tests. -/
def quantumTestStructure :
    OPT.TestStructure Sys quantumEventConeStructure
      quantumTransformationStructure quantumChannelStructure where
  IsTest := @IsQuantumTest
  test_event hT := hT.1
  test_transformation hT i := by
    classical
    simpa using partialSum_isTransformation hT.1 hT.2 ({i} : Finset _)
  transformation_test_outcome := by
    intro A B f hf
    obtain ⟨g, hg, hfg⟩ := exists_cp_complement_of_isTransformation f hf
    let T : Bool → (A ⟶ B) := fun b => if b then g else f
    refine ⟨Bool, inferInstance, T, ?_, false, ?_⟩
    · constructor
      · intro b
        cases b <;> simp [T, hf.1, hg]
      · have hsum : Finset.univ.sum T = f + g := by
          rw [Fintype.sum_bool]
          simp [add_comm]
        exact hsum.symm ▸ hfg
    · simp [T]
  test_coarse_grain hT p := quantumTest_coarseGrain hT p
  test_partial_sum_transformation hT s :=
    partialSum_isTransformation hT.1 hT.2 s
  test_total_channel T hT := hT.2
  channel_singleton_test hf := by
    constructor
    · intro i
      exact hf.1
    · simpa using hf

/-- Evaluation of closed quantum circuits by their real scalar coordinate. -/
def quantumScalarEvaluationStructure :
    OPT.ScalarEvaluationStructure Sys quantumEventConeStructure where
  scalarEval := quantumScalarEval
  scalarEval_id := quantumScalarEval_id
  scalarEval_nonneg hs := quantumScalarEval_nonneg hs
  scalarEval_tensor hs ht := quantumScalarEval_tensor hs ht

/-- The complete pre-causal operational probabilistic theory structure. -/
@[reducible]
def quantumOperationalProbabilisticTheory :
    OPT.OperationalProbabilisticTheory Sys where
  rawTest := quantumRawTestStructure
  event := quantumEventConeStructure
  transformation := quantumTransformationStructure
  channel := quantumChannelStructure
  structural := quantumStructuralChannelStructure
  test := quantumTestStructure
  scalar := quantumScalarEvaluationStructure

/-- Causality is witnessed by the trace effect. -/
def quantumCausalStructure :
    OPT.CausalStructure Sys quantumEventConeStructure
      quantumTransformationStructure quantumChannelStructure where
  detEffect := traceEffect
  detEffect_channel := traceEffect_isChannel
  detEffect_unique he := traceEffect_unique he
  transformation_effect_bound hf := traceEffect_sub_comp_isEvent hf
  channel_of_transformation_preserves_detEffect hf hpres :=
    isChannel_of_isTransformation_comp_traceEffect hf hpres

/-- Finite-dimensional quantum theory is an operational probabilistic theory. -/
instance instOperationalProbabilisticTheory :
    OPT.OperationalProbabilisticTheory Sys :=
  quantumOperationalProbabilisticTheory

/-- Finite-dimensional quantum theory is causal, with trace as discard. -/
instance instCausalOperationalProbabilisticTheory :
    OPT.CausalOperationalProbabilisticTheory Sys where
  base := quantumOperationalProbabilisticTheory
  causal := quantumCausalStructure

end QuantumModel
