/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.PetzRenyiRelativeEntropyLaws.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki

/-! # Order-one Petz laws

Data processing, tensor additivity and binary normalization for Umegaki relative entropy.
-/

namespace OPT

universe u v

/-- Data processing, tensor additivity and binary normalization for order-one Petz divergence. -/
theorem petzOrderOneLaws_from_umegakiDPI :
    PetzMatrixRelativeEntropyLaws.{u, v} petzRenyiOrderOne := by
  refine
    { dataProcessing := ?_
      tensorAdditivity := ?_
      binaryNormalization := ?_ }
  · intro H K _ _ _ _ E rho sigma hrho hsigma
    rw [petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
      petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN]
    exact mul_le_mul_of_nonneg_left
      (UmegakiDPI.monotoneOnNonNeg E
        ((LinearMap.nonneg_iff_isPositive rho).mpr hrho.1)
        ((LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1))
      (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Real.log_pos (by norm_num)).le))
  · intro H K _ _ _ _ _ rho₁ sigma₁ rho₂ sigma₂
      hrho₁ hsigma₁ hrho₂ hsigma₂
    let beta : PetzRenyiFiniteOrder := ⟨(petzRenyiOrderOne : ℝ), petzRenyiOrderOne.property.1⟩
    have hclosed :
        PetzRenyiFiniteOrder.toClosed beta petzRenyiOrderOne.property.2 =
          petzRenyiOrderOne := by
      apply Subtype.ext
      rfl
    have hadd := petzQuantumRenyiDivergenceFinite_tensorProduct beta
      rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂
    rw [petzQuantumRenyiDivergenceFinite_compatibility beta petzRenyiOrderOne.property.2,
      petzQuantumRenyiDivergenceFinite_compatibility beta petzRenyiOrderOne.property.2,
      petzQuantumRenyiDivergenceFinite_compatibility beta petzRenyiOrderOne.property.2,
      hclosed] at hadd
    exact hadd
  · intro H _ _ pair
    let beta : PetzRenyiFiniteOrder := ⟨(petzRenyiOrderOne : ℝ), petzRenyiOrderOne.property.1⟩
    have hclosed :
        PetzRenyiFiniteOrder.toClosed beta petzRenyiOrderOne.property.2 =
          petzRenyiOrderOne := by
      apply Subtype.ext
      rfl
    have hnorm := petzQuantumRenyiDivergenceFinite_binary_normalization beta pair
    rw [petzQuantumRenyiDivergenceFinite_compatibility beta petzRenyiOrderOne.property.2,
      hclosed] at hnorm
    exact hnorm

end OPT
