/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeFidelity.GSLCore
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore

/-!
# Native fidelity against a pure target

This file supplies the two rank-one operator identities needed to reduce the
operator root fidelity against a pure target to its Born overlap.
-/

noncomputable section

namespace QuantumModel

open QuantumState

namespace NativeTraceDistance

/-- The trace norm of a rank-one operator is the product of the two vector
norms. -/
theorem traceNorm_outer_product_eq {A : Sys} (u v : Space A) :
    traceNorm (QuantumChannel.outer_product u v) = ‖u‖ * ‖v‖ := by
  apply le_antisymm
  · exact traceNorm_outer_product_le u v
  · by_cases hu : u = 0
    · subst u
      simpa using traceNorm_nonneg
        (QuantumChannel.outer_product (0 : Space A) v)
    by_cases hv : v = 0
    · subst v
      simpa using traceNorm_nonneg
        (QuantumChannel.outer_product u (0 : Space A))
    let K : Operator A :=
      (((‖u‖ * ‖v‖ : ℝ)⁻¹ : ℝ) : ℂ) •
        QuantumChannel.outer_product v u
    have huNorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hvNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have huvNorm : ‖u‖ * ‖v‖ ≠ 0 := mul_ne_zero huNorm hvNorm
    have huvPos : 0 < ‖u‖ * ‖v‖ :=
      mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
    have hopNorm :
        ‖(QuantumChannel.outer_product v u).toContinuousLinearMap‖ =
          ‖v‖ * ‖u‖ := by
      have h := congrArg LinearMap.toContinuousLinearMap
        (QuantumChannel.outer_product_eq_rankOne v u)
      change (QuantumChannel.outer_product v u).toContinuousLinearMap =
        InnerProductSpace.rankOne ℂ u v at h
      rw [h, InnerProductSpace.norm_rankOne, mul_comm]
    have hKnorm : ‖K.toContinuousLinearMap‖ ≤ 1 := by
      rw [show K.toContinuousLinearMap =
          (((‖u‖ * ‖v‖ : ℝ)⁻¹ : ℝ) : ℂ) •
            (QuantumChannel.outer_product v u).toContinuousLinearMap by
        rfl]
      rw [norm_smul, hopNorm]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr huvPos)]
      rw [mul_comm ‖v‖ ‖u‖]
      exact (inv_mul_cancel₀ huvNorm).le
    have hdual :=
      (traceNorm_unitary_duality
        (QuantumChannel.outer_product u v)).2 K hKnorm
    have htrace :
        (Tr (K.comp (QuantumChannel.outer_product u v))).re =
          ‖u‖ * ‖v‖ := by
      have hcomp :
          (QuantumChannel.outer_product v u).comp
              (QuantumChannel.outer_product u v) =
            (((‖v‖ ^ 2 : ℝ) : ℂ) •
              QuantumChannel.outer_product u u) := by
        apply LinearMap.ext
        intro x
        simp [QuantumChannel.outer_product_eq_rankOne,
          inner_self_eq_norm_sq_to_K, smul_smul, mul_comm]
      rw [show K.comp (QuantumChannel.outer_product u v) =
          (((‖u‖ * ‖v‖ : ℝ)⁻¹ : ℝ) : ℂ) •
            ((‖v‖ ^ 2 : ℝ) : ℂ) •
              QuantumChannel.outer_product u u by
        change ((((‖u‖ * ‖v‖ : ℝ)⁻¹ : ℝ) : ℂ) •
            QuantumChannel.outer_product v u).comp
              (QuantumChannel.outer_product u v) = _
        rw [LinearMap.smul_comp, hcomp, smul_smul]]
      rw [map_smul, map_smul, QuantumChannel.trace_outer_product,
        inner_self_eq_norm_sq_to_K]
      simp only [smul_eq_mul, pow_two, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      field_simp
      norm_num
    rw [← htrace]
    exact hdual

end NativeTraceDistance

namespace NativeFidelity

/-- Squared operator root fidelity against a pure unit-vector state equals
the corresponding density-operator overlap. -/
theorem operatorRootFidelity_sq_pureOfUnitVector {A : Sys}
    (rho : DensityMatrix A) (v : Space A) (hv : ‖v‖ = 1) :
    operatorRootFidelity rho (DensityMatrix.pureOfUnitVector v hv) ^ 2 =
      (Tr ((DensityMatrix.pureOfUnitVector v hv).operator.comp
        rho.operator)).re := by
  let P : Operator A :=
    (DensityMatrix.pureOfUnitVector v hv).operator
  let S : Operator A := CFC.sqrt rho.operator
  have hPnonneg : 0 ≤ P :=
    (DensityMatrix.pureOfUnitVector v hv).nonneg
  have hPsquare : P * P = P := by
    apply LinearMap.ext
    intro x
    simp [P, DensityMatrix.pureOfUnitVector,
      QuantumChannel.outer_product_eq_rankOne,
      inner_self_eq_norm_sq_to_K, hv]
  have hsqrtP : CFC.sqrt P = P := CFC.sqrt_unique hPsquare hPnonneg
  have hfactor :
      S.comp P = QuantumChannel.outer_product v (S v) := by
    apply LinearMap.ext
    intro x
    simp [S, P, DensityMatrix.pureOfUnitVector,
      QuantumChannel.outer_product_eq_rankOne]
  have hSadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (densitySqrt_nonneg rho).isSelfAdjoint
  have hinner :
      inner ℂ (S v) (S v) = inner ℂ v (rho.operator v) := by
    calc
      inner ℂ (S v) (S v) =
          inner ℂ v ((LinearMap.adjoint S) (S v)) :=
        (LinearMap.adjoint_inner_right S v (S v)).symm
      _ = inner ℂ v ((S.comp S) v) := by rw [hSadj]; rfl
      _ = inner ℂ v (rho.operator v) := by
        rw [show S.comp S = rho.operator by
          exact densitySqrt_comp_self rho]
  have htrace :
      Tr ((DensityMatrix.pureOfUnitVector v hv).operator.comp rho.operator) =
        inner ℂ v (rho.operator v) := by
    rw [LinearMap.trace_comp_comm']
    rw [show rho.operator.comp
        (DensityMatrix.pureOfUnitVector v hv).operator =
          QuantumChannel.outer_product v (rho.operator v) by
      apply LinearMap.ext
      intro x
      simp [DensityMatrix.pureOfUnitVector,
        QuantumChannel.outer_product_eq_rankOne]]
    exact QuantumChannel.trace_outer_product v (rho.operator v)
  rw [operatorRootFidelity]
  change NativeTraceDistance.traceNorm
      (S.comp (CFC.sqrt P)) ^ 2 = _
  rw [hsqrtP, hfactor,
    NativeTraceDistance.traceNorm_outer_product_eq, hv, one_mul, htrace]
  calc
    ‖S v‖ ^ 2 = (inner ℂ (S v) (S v)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [Complex.mul_re, pow_two]
    _ = (inner ℂ v (rho.operator v)).re := congrArg Complex.re hinner

end NativeFidelity
end QuantumModel
