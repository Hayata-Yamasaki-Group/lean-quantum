/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.CategoryInstances.GSLCore

/-!
# CP, CP-TNI, and CPTP predicates

The ambient hom is the real vector space of Hermiticity-preserving maps.  Kraus maps
are constructed first as raw complex-linear superoperators and then bundled through
their star-preservation equation.  Complete positivity and trace normalization remain
predicates on the resulting categorical morphisms.
-/

namespace QuantumModel

open CategoryTheory
open QuantumState

/-- A finite Kraus family from `A` to `B`. -/
structure KrausFamily (A B : Sys) where
  index : Type
  fintypeIndex : Fintype index
  decidableEqIndex : DecidableEq index
  operator : index → (Space A →ₗ[ℂ] Space B)

namespace KrausFamily

variable {A B C : Sys}

/-- The raw complex-linear superoperator represented by a finite Kraus family. -/
noncomputable def rawMap (K : KrausFamily A B) : RawSuperoperator A B := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  exact ∑ i, QuantumChannel.krausTerm (K.operator i)

theorem krausTerm_map_star (V : Space A →ₗ[ℂ] Space B) (X : Operator A) :
    QuantumChannel.krausTerm V (star X) =
      star (QuantumChannel.krausTerm V X) := by
  simp [QuantumChannel.krausTerm, LinearMap.star_eq_adjoint,
    LinearMap.adjoint_comp, LinearMap.comp_assoc]

/-- A finite Kraus sum preserves Hermiticity. -/
theorem rawMap_map_star (K : KrausFamily A B) (X : Operator A) :
    K.rawMap (star X) = star (K.rawMap X) := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  simp only [rawMap, LinearMap.sum_apply]
  rw [star_sum]
  exact Finset.sum_congr rfl fun i _ ↦ krausTerm_map_star (K.operator i) X

/-- The HP categorical morphism represented by a finite Kraus family. -/
noncomputable def map (K : KrausFamily A B) : A ⟶ B :=
  ⟨WithConv.toConv K.rawMap,
    LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr K.rawMap_map_star⟩

@[simp]
theorem map_toRawSuperoperator (K : KrausFamily A B) :
    HPHom.toRawSuperoperator K.map = K.rawMap :=
  rfl

/-- The input-side Kraus normalization operator `∑ᵢ Kᵢ† Kᵢ`. -/
noncomputable def normalization (K : KrausFamily A B) : Operator A := by
  letI : QuantumState.Qudit (Space A) := spaceQudit A
  letI : QuantumState.Qudit (Space B) := spaceQudit B
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  exact ∑ i, (LinearMap.adjoint (K.operator i)).comp (K.operator i)

theorem rawMap_isCompletelyPositive (K : KrausFamily A B) :
    QuantumChannel.IsCompletelyPositive K.rawMap := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  simpa [rawMap] using QuantumChannel.sum_krausTerm_isCompletelyPositive K.operator

theorem map_isCompletelyPositive (K : KrausFamily A B) :
    QuantumChannel.IsCompletelyPositive (HPHom.toRawSuperoperator K.map) := by
  rw [map_toRawSuperoperator]
  exact K.rawMap_isCompletelyPositive

end KrausFamily

/-- The event cone: completely positive HP morphisms. -/
def IsEvent {A B : Sys} (Φ : A ⟶ B) : Prop :=
  QuantumChannel.IsCompletelyPositive (HPHom.toRawSuperoperator Φ)

/-- Trace nonincrease, in its finite-dimensional Kraus contraction characterization. -/
def IsTraceNonincreasing {A B : Sys} (Φ : A ⟶ B) : Prop :=
  ∃ K : KrausFamily A B, K.map = Φ ∧ K.normalization ≤ LinearMap.id

/-- Trace preservation, in its finite-dimensional Kraus normalization characterization. -/
def IsTracePreserving {A B : Sys} (Φ : A ⟶ B) : Prop :=
  ∃ K : KrausFamily A B, K.map = Φ ∧ K.normalization = LinearMap.id

/-- Physical transformations are CP-TNI superoperators. -/
def IsTransformation {A B : Sys} (Φ : A ⟶ B) : Prop :=
  IsEvent Φ ∧ IsTraceNonincreasing Φ

/-- Channels are CPTP superoperators. -/
def IsChannel {A B : Sys} (Φ : A ⟶ B) : Prop :=
  IsEvent Φ ∧ IsTracePreserving Φ

end QuantumModel
