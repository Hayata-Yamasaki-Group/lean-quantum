import Quantum.QuantumMechanics.QuantumChannelKWCompat.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore
import Quantum.QuantumModel.CategoryInstances.GSLCore
import Quantum.QuantumMechanics.Channel.BasicGeneralizedStein
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

/-!
# Finite-dimensional quantum purification

This file uses Mathlib's Hilbert-space tensor product, `QuantumChannel.TrRight`, rank-one
outer products, and vectorization.  Every density matrix has a spectral purification
(`spectralPurification_purifies`).
-/

namespace QuantumModel

open QuantumState
open TensorProduct

/-- The Hilbert-space carrier of the composite of `A` and `R`. -/
abbrev JointSpace (A R : Sys) := Space A ⊗[ℂ] Space R

/-- A pure bipartite state, represented by a unit vector. -/
structure PureState (A R : Sys) where
  vector : JointSpace A R
  norm_one : ‖vector‖ = 1

/-- Partial trace over the right-hand (purifying) system. -/
noncomputable def partialTrace {A R : Sys} :
    L (JointSpace A R) →ₗ[ℂ] Operator A :=
  QuantumChannel.TrRight

/-- `psi` is a purification of `rho` when its right partial trace is `rho`. -/
def Purifies {A R : Sys} (rho : DensityMatrix A) (psi : PureState A R) : Prop :=
  partialTrace (QuantumChannel.outer_product psi.vector psi.vector) = rho.operator

/-! ## Vectorization and partial trace -/

private lemma tensorRightSlice_vec
    {E F : Type*} [QuantumState.Qudit E] [QuantumState.Qudit F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ F) (K : F →ₗ[ℂ] E) (i : ι) :
    QuantumChannel.tensorRightSlice b i (QuantumChannel.vec b.toBasis K) = K (b i) := by
  rw [QuantumChannel.vec_apply]
  simp [QuantumChannel.tensorRightSlice_tmul]

private lemma comp_adjoint_eq_sum_outer_product
    {E F : Type*} [QuantumState.Qudit E] [QuantumState.Qudit F]
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ F) (K : F →ₗ[ℂ] E) :
    K.comp (LinearMap.adjoint K) =
      ∑ i : ι, QuantumChannel.outer_product (K (b i)) (K (b i)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  conv_lhs =>
    rw [← b.sum_repr ((LinearMap.adjoint K) x)]
  simp [QuantumChannel.outer_product_eq_rankOne,
    OrthonormalBasis.repr_apply_apply, LinearMap.adjoint_inner_right]

/-- The right partial trace of a vectorized operator is its Gram operator. -/
lemma partialTrace_outer_product_vec
    {E F : Type*} [QuantumState.Qudit E] [QuantumState.Qudit F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ F) (K : F →ₗ[ℂ] E) :
    QuantumChannel.TrRight
        (QuantumChannel.outer_product
          (QuantumChannel.vec b.toBasis K)
          (QuantumChannel.vec b.toBasis K)) =
      K.comp (LinearMap.adjoint K) := by
  rw [QuantumChannel.TrRight_outer_product_compat b]
  simp_rw [tensorRightSlice_vec]
  exact (comp_adjoint_eq_sum_outer_product b K).symm

/-! ## Spectral purification: existence -/

/-- A full-size canonical purifier.  Its dimension equals the input Hilbert-space dimension. -/
noncomputable def canonicalPurifier (A : Sys) : Sys where
  dim := Module.finrank ℂ (Space A)
  dim_pos := by simpa using A.dim_pos

noncomputable def canonicalPurifierBasis (A : Sys) :
    OrthonormalBasis (Fin (Module.finrank ℂ (Space A))) ℂ
      (Space (canonicalPurifier A)) :=
  EuclideanSpace.basisFun (Fin (Module.finrank ℂ (Space A))) ℂ

/-- The coefficient operator whose columns are `sqrt(p_i) • e_i` from the spectral
decomposition of `rho`. -/
noncomputable def spectralPurificationOperator {A : Sys} (rho : DensityMatrix A) :
    Space (canonicalPurifier A) →ₗ[ℂ] Space A :=
  let u := Classical.choose
    (QuantumChannel.positive_full_spectral_outer_product rho.operator rho.nonneg)
  (canonicalPurifierBasis A).toBasis.constr ℂ u

private lemma spectralPurificationOperator_apply {A : Sys}
    (rho : DensityMatrix A) (i : Fin (Module.finrank ℂ (Space A))) :
    spectralPurificationOperator rho (canonicalPurifierBasis A i) =
      Classical.choose
        (QuantumChannel.positive_full_spectral_outer_product
          rho.operator rho.nonneg) i := by
  simp [spectralPurificationOperator]

theorem spectralPurificationOperator_comp_adjoint {A : Sys}
    (rho : DensityMatrix A) :
    (spectralPurificationOperator rho).comp
        (LinearMap.adjoint (spectralPurificationOperator rho)) = rho.operator := by
  have hu := Classical.choose_spec
    (QuantumChannel.positive_full_spectral_outer_product rho.operator rho.nonneg)
  rw [comp_adjoint_eq_sum_outer_product (canonicalPurifierBasis A)]
  simp_rw [spectralPurificationOperator_apply]
  exact hu.1.symm

/-- The standard vector `sum_i sqrt(p_i) e_i tensor f_i`, expressed as `vec(K)`. -/
noncomputable def spectralPurificationVector {A : Sys} (rho : DensityMatrix A) :
    JointSpace A (canonicalPurifier A) :=
  QuantumChannel.vec (canonicalPurifierBasis A).toBasis
    (spectralPurificationOperator rho)

theorem norm_spectralPurificationVector {A : Sys} (rho : DensityMatrix A) :
    ‖spectralPurificationVector rho‖ = 1 := by
  have hinner : inner ℂ (spectralPurificationVector rho)
      (spectralPurificationVector rho) = 1 := by
    rw [spectralPurificationVector, QuantumChannel.inner_vec_eq_trace]
    rw [LinearMap.trace_comp_comm']
    rw [spectralPurificationOperator_comp_adjoint]
    exact rho.trace_one
  have hsqC : ((‖spectralPurificationVector rho‖ : ℂ) ^ 2) = 1 := by
    calc
      ((‖spectralPurificationVector rho‖ : ℂ) ^ 2) =
          inner ℂ (spectralPurificationVector rho)
            (spectralPurificationVector rho) :=
        (inner_self_eq_norm_sq_to_K (spectralPurificationVector rho)).symm
      _ = 1 := hinner
  have hsqR : ‖spectralPurificationVector rho‖ ^ 2 = 1 := by
    exact_mod_cast hsqC
  nlinarith [norm_nonneg (spectralPurificationVector rho)]

noncomputable def spectralPurification {A : Sys} (rho : DensityMatrix A) :
    PureState A (canonicalPurifier A) where
  vector := spectralPurificationVector rho
  norm_one := norm_spectralPurificationVector rho

theorem spectralPurification_purifies {A : Sys} (rho : DensityMatrix A) :
    Purifies rho (spectralPurification rho) := by
  rw [Purifies]
  change QuantumChannel.TrRight
      (QuantumChannel.outer_product
        (spectralPurificationVector rho) (spectralPurificationVector rho)) = rho.operator
  rw [spectralPurificationVector, partialTrace_outer_product_vec]
  exact spectralPurificationOperator_comp_adjoint rho

end QuantumModel
