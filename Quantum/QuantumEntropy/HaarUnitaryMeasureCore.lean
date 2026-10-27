/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Algebra.Central.Basic
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

import Quantum.QuantumEntropy.TensorCFCCore
import Quantum.TraceInequality.GeneralizedPerspectiveFunction.IntegralJensen
import Quantum.TraceInequality.LiebAndo.PositiveDefiniteGeometry

/-!
# Haar measure and integrals on the unitary group

Canonical topology, normalized Haar measure, tensor conjugation and integrability.
-/

open QuantumState QuantumChannel TensorCFC
open MeasureTheory MeasureTheory.Measure
open GeneralizedPerspectiveFunction
open scoped ComplexOrder TensorProduct

namespace HaarUnitaryCLM

universe u

/-! ## Compact unitary group and normalized Haar measure -/

section CompactHaar

variable {ℋ : Type u} [Qudit ℋ]

/-- Every unitary continuous endomorphism has operator norm at most one. -/
lemma norm_coe_unitary_le_one [Nontrivial ℋ] (U : unitary (B ℋ)) :
    ‖(U : B ℋ)‖ ≤ 1 := by
  rw [CStarRing.norm_coe_unitary]

/-- The unitary group of a finite-dimensional Hilbert space is bounded. -/
lemma isBounded_unitary [Nontrivial ℋ] :
    Bornology.IsBounded (unitary (B ℋ) : Set (B ℋ)) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  exact ⟨2, fun x hx => by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_coe_unitary_le_one ⟨x, hx⟩) one_lt_two⟩

/-- Compactness of the CLM-native unitary group. -/
instance compactSpace_unitary [Nontrivial ℋ] : CompactSpace (unitary (B ℋ)) := by
  have : ProperSpace (B ℋ) := FiniteDimensional.proper ℂ (B ℋ)
  exact isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_unitary isBounded_unitary)

/-- Local compactness of the CLM-native unitary group. -/
instance locallyCompactSpace_unitary [Nontrivial ℋ] :
    LocallyCompactSpace (unitary (B ℋ)) := by
  haveI : ProperSpace (unitary (B ℋ)) := proper_of_compact
  exact locallyCompact_of_proper

/-- The positive compact normalizer used to construct normalized Haar measure. -/
noncomputable def unitaryPC (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    TopologicalSpace.PositiveCompacts (unitary (B ℋ)) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

/-- The normalized Haar measure on `unitary (ℋ →L[ℂ] ℋ)`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def haarUnitary (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    Measure (unitary (B ℋ)) :=
  haarMeasure (unitaryPC ℋ)

instance isHaarMeasure_haarUnitary [Nontrivial ℋ] :
    IsHaarMeasure (haarUnitary ℋ) := by
  unfold haarUnitary
  infer_instance

/-- The normalized Haar measure has total mass one. -/
instance isProbabilityMeasure_haarUnitary [Nontrivial ℋ] :
    IsProbabilityMeasure (haarUnitary ℋ) :=
  ⟨by
    change haarMeasure (unitaryPC ℋ) Set.univ = 1
    have hself : haarMeasure (unitaryPC ℋ) (unitaryPC ℋ : Set _) = 1 := haarMeasure_self
    simpa [unitaryPC] using hself⟩

end CompactHaar

/-! ## Continuity and integrability of conjugation -/

section Measurability

variable {ℋ : Type u} [Qudit ℋ]

/-- Unitary conjugation on continuous endomorphisms is continuous. -/
lemma continuous_unitaryConj (X : B ℋ) :
    Continuous (fun u : unitary (B ℋ) =>
      (u : B ℋ) * X * star (u : B ℋ)) := by
  exact ((continuous_subtype_val.mul continuous_const).mul
    (continuous_star.comp continuous_subtype_val))

/-- Unitary conjugation is Bochner-integrable for normalized Haar measure. -/
lemma integrable_unitaryConj [Nontrivial ℋ] (X : B ℋ) :
    Integrable (fun u : unitary (B ℋ) =>
      (u : B ℋ) * X * star (u : B ℋ))
      (haarUnitary ℋ) :=
  (continuous_unitaryConj X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

end Measurability

/-! ## Tensor-factor twirling -/

section TensorTwirl

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-- The canonical CLM tensor product of two continuous endomorphisms. -/
noncomputable def tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap

/-- The first-factor partial trace, with CLM input and output. -/
noncomputable def traceOutLeft (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    B ℋ₂ :=
  (QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma traceOutLeft_toLinearMap
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ((traceOutLeft X : B ℋ₂) : L ℋ₂) =
      QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) := rfl

/-- The second-factor partial trace, with CLM input and output. -/
noncomputable def traceOutRight (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    B ℋ₁ :=
  (QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma traceOutRight_toLinearMap
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ((traceOutRight X : B ℋ₁) : L ℋ₁) =
      QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma tensorMap_product (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A B =
      rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A *
        lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁) *
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_rTensor_mul_lTensor (A : L ℋ₁) (B : L ℋ₂))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_tensorMap_right (A : ℋ₁ →L[ℂ] ℋ₁) :
    Continuous (fun B : ℋ₂ →L[ℂ] ℋ₂ => tensorMap A B) := by
  simp_rw [tensorMap_product]
  exact continuous_const.mul
    (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
      (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Second-factor tensor conjugation is continuous. -/
lemma continuous_unitaryConj_tensor_right
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂) * X *
        tensorMap (1 : B ℋ₁) (star (u : B ℋ₂))) := by
  have hleft : Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂)) :=
    (continuous_tensorMap_right (1 : B ℋ₁)).comp continuous_subtype_val
  have hright : Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (star (u : B ℋ₂))) :=
    (continuous_tensorMap_right (1 : B ℋ₁)).comp
      (continuous_star.comp continuous_subtype_val)
  exact (hleft.mul continuous_const).mul hright

omit [Nontrivial ℋ₁] in
/-- Second-factor tensor conjugation is Haar-integrable. -/
lemma integrable_unitaryConj_tensor_right
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂) * X *
        tensorMap (1 : B ℋ₁) (star (u : B ℋ₂)))
      (haarUnitary ℋ₂) :=
  (continuous_unitaryConj_tensor_right X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

end TensorTwirl

end HaarUnitaryCLM
