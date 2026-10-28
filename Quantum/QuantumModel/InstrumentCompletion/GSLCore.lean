/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.Predicates.GSLCore

/-!
# CP-TNI instrument completion

This file completes a CP-TNI map to a two-outcome instrument
(`exists_cp_complement_of_isTransformation`).  The complementary map is a measure-and-prepare map
obtained from the spectral decomposition of the input-side Kraus deficit.
-/

namespace QuantumModel

open CategoryTheory
open QuantumState

variable {A B : Sys}

/-- A fixed unit vector in every (nonzero) output system. -/
noncomputable def outputUnit (B : Sys) : Space B :=
  EuclideanSpace.basisFun (Fin B.dim) ℂ ⟨0, B.dim_pos⟩

@[simp]
theorem norm_outputUnit (B : Sys) : ‖outputUnit B‖ = 1 := by
  simp [outputUnit]

/-- A rank-one Kraus operator into the fixed output ray recovers its input effect. -/
theorem rankOneKraus_normalization (u : Space A) :
    (LinearMap.adjoint (QuantumChannel.outer_product u (outputUnit B))).comp
        (QuantumChannel.outer_product u (outputUnit B)) =
      QuantumChannel.outer_product u u := by
  let W := QuantumChannel.outer_product u (outputUnit B)
  have hadj : LinearMap.adjoint W (outputUnit B) = u := by
    apply ext_inner_right ℂ
    intro x
    rw [LinearMap.adjoint_inner_left]
    rw [show W x = inner ℂ u x • outputUnit B by
      simp [W, QuantumChannel.outer_product_eq_rankOne]]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [norm_outputUnit]
  change (LinearMap.adjoint W).comp W = QuantumChannel.outer_product u u
  ext x
  rw [LinearMap.comp_apply]
  rw [show W x = inner ℂ u x • outputUnit B by
    simp [W, QuantumChannel.outer_product_eq_rankOne]]
  rw [map_smul, hadj]
  simp [QuantumChannel.outer_product_eq_rankOne]

/-- Every CP-TNI superoperator is one outcome of a two-outcome CPTP instrument. -/
theorem exists_cp_complement_of_isTransformation
    (T : A ⟶ B) (hT : IsTransformation T) :
    ∃ T' : A ⟶ B, IsEvent T' ∧ IsChannel (T + T') := by
  rcases hT.2 with ⟨K, hKT, hKle⟩
  let D : Operator A := LinearMap.id - K.normalization
  have hD : 0 ≤ D := sub_nonneg.mpr hKle
  obtain ⟨u, hu, _⟩ :=
    QuantumChannel.positive_full_spectral_outer_product D hD
  let K' : KrausFamily A B :=
    { index := Fin (Module.finrank ℂ (Space A))
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := fun i => QuantumChannel.outer_product (u i) (outputUnit B) }
  have hK'norm : K'.normalization = D := by
    change
      (∑ i : Fin (Module.finrank ℂ (Space A)),
        (LinearMap.adjoint
          (QuantumChannel.outer_product (u i) (outputUnit B))).comp
            (QuantumChannel.outer_product (u i) (outputUnit B))) = D
    simp_rw [rankOneKraus_normalization]
    exact hu.symm
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  let Ksum : KrausFamily A B :=
    { index := Sum K.index (Fin (Module.finrank ℂ (Space A)))
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Sum.elim K.operator K'.operator }
  have hKsumMap : Ksum.map = T + K'.map := by
    calc
      Ksum.map = K.map + K'.map := by
        apply HPHom.ext
        intro X
        change Ksum.rawMap X = K.rawMap X + K'.rawMap X
        simp [KrausFamily.rawMap, Ksum, K', Fintype.sum_sum_type]
      _ = T + K'.map := by rw [hKT]
  have hKsumNorm : Ksum.normalization = LinearMap.id := by
    calc
      Ksum.normalization = K.normalization + K'.normalization := by
        simp [KrausFamily.normalization, Ksum, K', Fintype.sum_sum_type]
      _ = K.normalization + D := by rw [hK'norm]
      _ = LinearMap.id := by simp [D]
  refine ⟨K'.map, K'.map_isCompletelyPositive, ?_⟩
  constructor
  · rw [← hKsumMap]
    exact Ksum.map_isCompletelyPositive
  · exact ⟨Ksum, hKsumMap, hKsumNorm⟩

end QuantumModel
