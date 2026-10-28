/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumModel.KW.Distances.HypothesisTestingBounds.PetzLowerBound.GSLCore
import Quantum.QuantumModel.RegularizationUmegaki.GSLCore
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.Tensor.GSLCore

/-!
# Rényi analysis for native quantum-model carriers

This module supplies the support-sensitive binary tensor laws and the two
one-sided order-one limits used by the Stein prerequisites.
-/

noncomputable section

open QuantumState QuantumChannel TensorProduct Filter Set
open scoped ComplexOrder MatrixOrder Topology TensorProduct ENNReal NNReal

namespace QuantumModel.NativeHypothesisTesting

open SandwichedRenyiRelativeEntropy

attribute [local instance] operatorSelfAdjointUnitalCFCRenyiAnalysis

attribute [local instance] operatorNonnegSpectrumRenyiAnalysis

private noncomputable def conjugateEndStarAlgEquivRenyi
    {E F : Type*} [Qudit E] [Qudit F] (U : E ≃ₗᵢ[ℂ] F) :
    L E ≃⋆ₐ[ℂ] L F :=
  (QuantumChannel.linearToContinuousEndStarAlgEquiv E).trans
    (U.conjStarAlgEquiv.trans
      (QuantumChannel.linearToContinuousEndStarAlgEquiv F).symm)

private theorem conjugateEnd_map_rpow
    {E F : Type*} [Qudit E] [Qudit F]
    (U : E ≃ₗᵢ[ℂ] F) (X : L E) (p : ℝ) :
    conjugateEndStarAlgEquivRenyi U (CFC.rpow X p) =
      CFC.rpow (conjugateEndStarAlgEquivRenyi U X) p := by
  letI : IsScalarTower ℝ≥0 ℂ (L E) := RestrictScalars.isScalarTower ℝ≥0 ℂ (L E)
  letI : IsScalarTower ℝ≥0 ℂ (L F) := RestrictScalars.isScalarTower ℝ≥0 ℂ (L F)
  let phi := conjugateEndStarAlgEquivRenyi U
  let f : ℝ≥0 → ℝ≥0 := fun x => x ^ p
  change phi (cfc f X) = cfc f (phi X)
  have hnn : (0 : L F) ≤ phi X ↔ (0 : L E) ≤ X := by
    conv_lhs => rw [show (0 : L F) = phi 0 from (map_zero phi).symm]
    exact OrderIsoClass.map_le_map_iff phi
  have hspec : spectrum ℝ≥0 (phi X) = spectrum ℝ≥0 X :=
    AlgEquiv.spectrum_eq (phi.restrictScalars ℝ≥0).toAlgEquiv X
  by_cases h : (0 ≤ X) ∧ ContinuousOn f (spectrum ℝ≥0 X)
  · exact StarAlgHomClass.map_cfc (S := ℂ) phi f X h.2
      (map_continuous phi) h.1 (hnn.mpr h.1)
  · rw [cfc_apply_of_not_and X h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

private theorem trace_mul_im_eq_zero_of_selfAdjoint
    {E : Type*} [Qudit E] (X Y : L E)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    (Tr (X * Y)).im = 0 := by
  let hXsym : X.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint X).mpr hX
  let hYsym : Y.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint Y).mpr hY
  let ob := hXsym.eigenvectorBasis
    (rfl : Module.finrank ℂ E = Module.finrank ℂ E)
  let b := ob.toBasis
  rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := b)]
  let MX := LinearMap.toMatrix b b X
  let MY := LinearMap.toMatrix b b Y
  have hMX : Matrix.conjTranspose MX = MX := by
    change Matrix.conjTranspose
      (LinearMap.toMatrix ob.toBasis ob.toBasis X) =
        LinearMap.toMatrix ob.toBasis ob.toBasis X
    rw [← LinearMap.toMatrix_adjoint ob ob]
    exact congrArg (LinearMap.toMatrix ob.toBasis ob.toBasis) hXsym.adjoint_eq
  have hMY : Matrix.conjTranspose MY = MY := by
    change Matrix.conjTranspose
      (LinearMap.toMatrix ob.toBasis ob.toBasis Y) =
        LinearMap.toMatrix ob.toBasis ob.toBasis Y
    rw [← LinearMap.toMatrix_adjoint ob ob]
    exact congrArg (LinearMap.toMatrix ob.toBasis ob.toBasis) hYsym.adjoint_eq
  rw [LinearMap.toMatrix_mul]
  apply Complex.conj_eq_iff_im.mp
  calc
    (starRingEnd ℂ) (Matrix.trace (MX * MY)) =
        Matrix.trace (Matrix.conjTranspose (MX * MY)) :=
      (Matrix.trace_conjTranspose (MX * MY)).symm
    _ = Matrix.trace (MY * MX) := by
      rw [Matrix.conjTranspose_mul, hMY, hMX]
    _ = Matrix.trace (MX * MY) := Matrix.trace_mul_comm MY MX

private theorem petzQuasi_unitaryConjugateEnd
    {E F : Type*} [Qudit E] [Qudit F]
    (U : E ≃ₗᵢ[ℂ] F) (alpha : ℝ) (rho sigma : L E) :
    (Tr (CFC.rpow (QuantumChannel.conjugateEnd U.toLinearEquiv rho) alpha *
      CFC.rpow (QuantumChannel.conjugateEnd U.toLinearEquiv sigma) (1 - alpha))).re =
    (Tr (CFC.rpow rho alpha * CFC.rpow sigma (1 - alpha))).re := by
  let phi := conjugateEndStarAlgEquivRenyi U
  change (Tr (CFC.rpow (phi rho) alpha * CFC.rpow (phi sigma) (1 - alpha))).re = _
  rw [← conjugateEnd_map_rpow U rho alpha,
    ← conjugateEnd_map_rpow U sigma (1 - alpha), ← map_mul]
  change (Tr (QuantumChannel.conjugateEnd U.toLinearEquiv
    (CFC.rpow rho alpha * CFC.rpow sigma (1 - alpha)))).re = _
  rw [QuantumChannel.trace_conjugateEnd]

private theorem sandwichedQuasi_unitaryConjugateEnd
    {E F : Type*} [Qudit E] [Qudit F]
    (U : E ≃ₗᵢ[ℂ] F) (alpha : ℝ) (rho sigma : L E) :
    SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha
        (QuantumChannel.conjugateEnd U.toLinearEquiv rho)
        (QuantumChannel.conjugateEnd U.toLinearEquiv sigma) =
      SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha rho sigma := by
  let phi := conjugateEndStarAlgEquivRenyi U
  change SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha (phi rho) (phi sigma) = _
  unfold SandwichedRenyiRelativeEntropy.sandwichedQuasi
  let p := (1 - alpha) / (2 * alpha)
  rw [← conjugateEnd_map_rpow U sigma p]
  have hinner : phi (CFC.rpow sigma p) * phi rho * phi (CFC.rpow sigma p) =
      phi (CFC.rpow sigma p * rho * CFC.rpow sigma p) := by simp
  rw [hinner, ← conjugateEnd_map_rpow U]
  change Tr (QuantumChannel.conjugateEnd U.toLinearEquiv
      (CFC.rpow (CFC.rpow sigma p * rho * CFC.rpow sigma p) alpha)) = _
  rw [QuantumChannel.trace_conjugateEnd]

private theorem sandwichedRenyiDiv_unitaryConjugateEnd
    {E F : Type*} [Qudit E] [Qudit F]
    (U : E ≃ₗᵢ[ℂ] F) (alpha : ℝ) (rho sigma : L E) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha
        (QuantumChannel.conjugateEnd U.toLinearEquiv rho)
        (QuantumChannel.conjugateEnd U.toLinearEquiv sigma) =
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha rho sigma := by
  unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
  rw [sandwichedQuasi_unitaryConjugateEnd,
    QuantumChannel.trace_conjugateEnd]

private theorem petzQuasi_tensorMap
    {E F : Type*} [Qudit E] [Qudit F]
    (alpha : ℝ) (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : 0 ≤ rho₁) (hsigma₁ : 0 ≤ sigma₁)
    (hrho₂ : 0 ≤ rho₂) (hsigma₂ : 0 ≤ sigma₂) :
    (Tr (CFC.rpow (TensorProduct.map rho₁ rho₂) alpha *
      CFC.rpow (TensorProduct.map sigma₁ sigma₂) (1 - alpha))).re =
    (Tr (CFC.rpow rho₁ alpha * CFC.rpow sigma₁ (1 - alpha))).re *
      (Tr (CFC.rpow rho₂ alpha * CFC.rpow sigma₂ (1 - alpha))).re := by
  change (Tr (CFC.rpow
      (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F)) alpha *
      CFC.rpow (TensorProduct.map sigma₁ sigma₂ : L (E ⊗[ℂ] F))
        (1 - alpha))).re = _
  rw [TensorCFC.rpow_tensorProduct_lm rho₁ rho₂ alpha hrho₁ hrho₂,
    TensorCFC.rpow_tensorProduct_lm sigma₁ sigma₂ (1 - alpha) hsigma₁ hsigma₂,
    ← TensorProduct.map_mul, LinearMap.trace_tensorProduct']
  have h₁ := trace_mul_im_eq_zero_of_selfAdjoint
    (CFC.rpow rho₁ alpha) (CFC.rpow sigma₁ (1 - alpha))
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)
  have h₂ := trace_mul_im_eq_zero_of_selfAdjoint
    (CFC.rpow rho₂ alpha) (CFC.rpow sigma₂ (1 - alpha))
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg)
  rw [Complex.mul_re, h₁, h₂]
  ring

/-- Petz quasi-entropy is multiplicative under the native density tensor.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1653--1754` (`prop-Petz_rel_ent`), specifically the
multiplicative quasi-entropy calculation underlying tensor additivity. -/
theorem petzQuasi_densityTensor
    {A B : Sys} (alpha : ℝ)
    (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1)
    (rho₁ sigma₁ : DensityMatrix A) (rho₂ sigma₂ : DensityMatrix B) :
    petzQuasi alpha (densityTensor rho₁ rho₂)
        (densityTensor sigma₁ sigma₂).operator =
        petzQuasi alpha rho₁ sigma₁.operator *
        petzQuasi alpha rho₂ sigma₂.operator := by
  letI : Nontrivial (Space A ⊗[ℂ] Space B) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  unfold petzQuasi
  let U := nativeTensorEquiv A B
  have htransport := petzQuasi_unitaryConjugateEnd U alpha
    (densityTensor rho₁ rho₂).operator (densityTensor sigma₁ sigma₂).operator
  have hmaprho : QuantumChannel.conjugateEnd U.toLinearEquiv
      (densityTensor rho₁ rho₂).operator =
      nativeTensorOperatorTransport A B (densityTensor rho₁ rho₂).operator := rfl
  have hmapsigma : QuantumChannel.conjugateEnd U.toLinearEquiv
      (densityTensor sigma₁ sigma₂).operator =
      nativeTensorOperatorTransport A B (densityTensor sigma₁ sigma₂).operator := rfl
  rw [hmaprho, hmapsigma,
    nativeTensorOperatorTransport_densityTensor_operator,
    nativeTensorOperatorTransport_densityTensor_operator] at htransport
  exact htransport.symm.trans
    (petzQuasi_tensorMap alpha rho₁.operator sigma₁.operator
      rho₂.operator sigma₂.operator rho₁.nonneg sigma₁.nonneg
      rho₂.nonneg sigma₂.nonneg)

/-- Petz Rényi divergence is additive under the native density tensor,
including the orthogonal (`top`) branch.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1653--1754` (`prop-Petz_rel_ent`), with the source's tensor
additivity extended explicitly to the orthogonal-support branch. -/
theorem petzRenyiDivBits_densityTensor
    {A B : Sys} (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (rho₁ sigma₁ : DensityMatrix A) (rho₂ sigma₂ : DensityMatrix B) :
    petzRenyiDivBits alpha (densityTensor rho₁ rho₂)
        (densityTensor sigma₁ sigma₂).operator =
      petzRenyiDivBits alpha rho₁ sigma₁.operator +
        petzRenyiDivBits alpha rho₂ sigma₂.operator := by
  have hmul := petzQuasi_densityTensor alpha halpha0 halpha1
    rho₁ sigma₁ rho₂ sigma₂
  have hq₁ : 0 ≤ petzQuasi alpha rho₁ sigma₁.operator :=
    petzQuasi_nonneg alpha halpha0 halpha1 rho₁ sigma₁.operator sigma₁.nonneg
  have hq₂ : 0 ≤ petzQuasi alpha rho₂ sigma₂.operator :=
    petzQuasi_nonneg alpha halpha0 halpha1 rho₂ sigma₂.operator sigma₂.nonneg
  unfold petzRenyiDivBits
  rw [hmul]
  by_cases hz₁ : petzQuasi alpha rho₁ sigma₁.operator = 0
  · rw [hz₁, zero_mul, if_pos rfl]
    by_cases hz₂ : petzQuasi alpha rho₂ sigma₂.operator = 0
    · rw [if_pos hz₂, EReal.top_add_top]
    · rw [if_neg hz₂, EReal.top_add_coe]
  by_cases hz₂ : petzQuasi alpha rho₂ sigma₂.operator = 0
  · rw [hz₂, mul_zero, if_pos rfl, if_neg hz₁,
      EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  have hp₁ : 0 < petzQuasi alpha rho₁ sigma₁.operator := lt_of_le_of_ne hq₁ (Ne.symm hz₁)
  have hp₂ : 0 < petzQuasi alpha rho₂ sigma₂.operator := lt_of_le_of_ne hq₂ (Ne.symm hz₂)
  rw [if_neg (mul_ne_zero hz₁ hz₂), if_neg hz₁, if_neg hz₂,
    Real.logb_mul (ne_of_gt hp₁) (ne_of_gt hp₂)]
  norm_cast
  ring

private theorem suppLE_densityTensor_operator_iff
    {A B : Sys} (rho₁ sigma₁ : DensityMatrix A)
    (rho₂ sigma₂ : DensityMatrix B) :
    SandwichedRenyiRelativeEntropy.suppLE
        (densityTensor rho₁ rho₂).operator
        (densityTensor sigma₁ sigma₂).operator ↔
      SandwichedRenyiRelativeEntropy.suppLE rho₁.operator sigma₁.operator ∧
        SandwichedRenyiRelativeEntropy.suppLE rho₂.operator sigma₂.operator := by
  rw [← DensityMatrix.supportLE_iff_suppLE,
    DensityMatrix.supportLE_densityTensor_iff,
    DensityMatrix.supportLE_iff_suppLE,
    DensityMatrix.supportLE_iff_suppLE]

private theorem sandwichedRenyiDiv_densityTensor
    {A B : Sys} (alpha : ℝ) (halpha : 1 < alpha)
    (rho₁ sigma₁ : DensityMatrix A) (rho₂ sigma₂ : DensityMatrix B)
    (hsupp₁ : SandwichedRenyiRelativeEntropy.suppLE rho₁.operator sigma₁.operator)
    (hsupp₂ : SandwichedRenyiRelativeEntropy.suppLE rho₂.operator sigma₂.operator) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha
        (densityTensor rho₁ rho₂).operator
        (densityTensor sigma₁ sigma₂).operator =
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha
          rho₁.operator sigma₁.operator +
        SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha
          rho₂.operator sigma₂.operator := by
  letI : Nontrivial (Space A ⊗[ℂ] Space B) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  let U := nativeTensorEquiv A B
  have htransport := sandwichedRenyiDiv_unitaryConjugateEnd U alpha
    (densityTensor rho₁ rho₂).operator (densityTensor sigma₁ sigma₂).operator
  have hmaprho : QuantumChannel.conjugateEnd U.toLinearEquiv
      (densityTensor rho₁ rho₂).operator =
      nativeTensorOperatorTransport A B (densityTensor rho₁ rho₂).operator := rfl
  have hmapsigma : QuantumChannel.conjugateEnd U.toLinearEquiv
      (densityTensor sigma₁ sigma₂).operator =
      nativeTensorOperatorTransport A B (densityTensor sigma₁ sigma₂).operator := rfl
  rw [hmaprho, hmapsigma,
    nativeTensorOperatorTransport_densityTensor_operator,
    nativeTensorOperatorTransport_densityTensor_operator] at htransport
  have hq₁ := SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_pos_of_suppLE
    halpha rho₁.nonneg sigma₁.nonneg hsupp₁ rho₁.operator_ne_zero
  have hq₂ := SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_pos_of_suppLE
    halpha rho₂.nonneg sigma₂.nonneg hsupp₂ rho₂.operator_ne_zero
  have hTensor := SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tensor alpha
    rho₁.operator sigma₁.operator rho₂.operator sigma₂.operator
    rho₁.nonneg sigma₁.nonneg rho₂.nonneg sigma₂.nonneg
    (ne_of_gt hq₁) (ne_of_gt hq₂)
    (by rw [rho₁.trace_one]; norm_num) (by rw [rho₂.trace_one]; norm_num)
  exact htransport.symm.trans hTensor

/-- Sandwiched Rényi divergence is additive under the native density tensor,
with support mismatch retained as `top`.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:2261--2272,2419--2437`
(`prop-sand_rel_ent_properties`, `eq-sand_ren_rel_ent_additive`), with support
mismatch retained in the extended-value carrier. -/
theorem sandwichedRenyiDivBits_densityTensor
    {A B : Sys} (alpha : ℝ) (halpha : 1 < alpha)
    (rho₁ sigma₁ : DensityMatrix A) (rho₂ sigma₂ : DensityMatrix B) :
    sandwichedRenyiDivBits alpha (densityTensor rho₁ rho₂)
        (densityTensor sigma₁ sigma₂).operator =
      sandwichedRenyiDivBits alpha rho₁ sigma₁.operator +
        sandwichedRenyiDivBits alpha rho₂ sigma₂.operator := by
  let h₁ := SandwichedRenyiRelativeEntropy.suppLE rho₁.operator sigma₁.operator
  let h₂ := SandwichedRenyiRelativeEntropy.suppLE rho₂.operator sigma₂.operator
  have htensor : SandwichedRenyiRelativeEntropy.suppLE
      (densityTensor rho₁ rho₂).operator
      (densityTensor sigma₁ sigma₂).operator ↔ h₁ ∧ h₂ :=
    suppLE_densityTensor_operator_iff rho₁ sigma₁ rho₂ sigma₂
  have hfinite {E : Type} [Qudit E] [Nontrivial E]
      (rho sigma : L E) (hs : SandwichedRenyiRelativeEntropy.suppLE rho sigma) :
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN alpha rho sigma =
        ((SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv alpha rho sigma : ℝ) : EReal) := by
    unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
    rw [if_neg]
    rintro (⟨_, hn⟩ | ⟨hlt, _⟩)
    · exact hn hs
    · exact (not_lt_of_ge halpha.le) hlt
  have htop {E : Type} [Qudit E] [Nontrivial E]
      (rho sigma : L E) (hs : ¬ SandwichedRenyiRelativeEntropy.suppLE rho sigma) :
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN alpha rho sigma =
        (⊤ : EReal) := by
    unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
    rw [if_pos (Or.inl ⟨halpha, hs⟩)]
  have hlogpos : (0 : EReal) < ((Real.log 2 : ℝ) : EReal) := by
    exact EReal.coe_pos.mpr (Real.log_pos one_lt_two)
  have htopdiv : (⊤ : EReal) / ((Real.log 2 : ℝ) : EReal) = ⊤ :=
    EReal.top_div_of_pos_ne_top hlogpos (EReal.coe_ne_top _)
  unfold sandwichedRenyiDivBits
  by_cases hs₁ : h₁
  · by_cases hs₂ : h₂
    · have hsT : SandwichedRenyiRelativeEntropy.suppLE
          (densityTensor rho₁ rho₂).operator
          (densityTensor sigma₁ sigma₂).operator := htensor.mpr ⟨hs₁, hs₂⟩
      rw [hfinite _ _ hsT, hfinite _ _ hs₁, hfinite _ _ hs₂]
      rw [sandwichedRenyiDiv_densityTensor alpha halpha rho₁ sigma₁ rho₂ sigma₂ hs₁ hs₂]
      rw [← EReal.coe_div, ← EReal.coe_div, ← EReal.coe_div]
      norm_cast
      ring
    · have hsT : ¬ SandwichedRenyiRelativeEntropy.suppLE
          (densityTensor rho₁ rho₂).operator
          (densityTensor sigma₁ sigma₂).operator := fun h => hs₂ (htensor.mp h).2
      rw [htop _ _ hsT, hfinite _ _ hs₁, htop _ _ hs₂, htopdiv,
        EReal.add_top_of_ne_bot]
      exact EReal.coe_ne_bot _
  · have hsT : ¬ SandwichedRenyiRelativeEntropy.suppLE
        (densityTensor rho₁ rho₂).operator
        (densityTensor sigma₁ sigma₂).operator := fun h => hs₁ (htensor.mp h).1
    rw [htop _ _ hsT, htop _ _ hs₁, htopdiv]
    by_cases hs₂ : h₂
    · rw [hfinite _ _ hs₂, ← EReal.coe_div, EReal.top_add_coe]
    · rw [htop _ _ hs₂, htopdiv, EReal.top_add_top]

private theorem spectrum_real_finite_petz
    {E : Type*} [Qudit E] (X : L E) : (spectrum ℝ X).Finite := by
  letI : IsScalarTower ℝ ℂ (L E) :=
    RestrictScalars.isScalarTower ℝ ℂ (L E)
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum X).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem rpow_eq_cfc_singular {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) (p : ℝ) :
    CFC.rpow sigma p = cfc (fun x : ℝ => x ^ p) sigma := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hsigma

private theorem rpow_mul_rpow_singular {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) (p q : ℝ) :
    CFC.rpow sigma p * CFC.rpow sigma q =
      cfc (fun x : ℝ => x ^ p * x ^ q) sigma := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ sigma) :=
    fun f => (spectrum_real_finite_petz sigma).continuousOn f
  rw [rpow_eq_cfc_singular hsigma p, rpow_eq_cfc_singular hsigma q]
  exact (cfc_mul _ _ sigma (hcont _) (hcont _)).symm

private theorem self_mul_rpow_support {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) :
    sigma * (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))) = sigma := by
  rw [← mul_assoc]
  nth_rewrite 1 [show sigma = CFC.rpow sigma (1 : ℝ) from
    (CFC.rpow_one sigma hsigma).symm]
  rw [rpow_mul_rpow_singular hsigma]
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ sigma) :=
    fun f => (spectrum_real_finite_petz sigma).continuousOn f
  rw [rpow_eq_cfc_singular hsigma]
  rw [← cfc_mul _ _ sigma (hcont _) (hcont _)]
  trans cfc (fun x : ℝ => x) sigma
  · apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hsigma hx
    change x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) = x
    rcases eq_or_lt_of_le hx0 with rfl | hxpos
    · norm_num [Real.zero_rpow]
    · rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      norm_num
  · exact cfc_id' ℝ sigma

private theorem mul_rpow_support_eq {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {X sigma : L ℋ} (hsigma : 0 ≤ sigma) (hsupp : suppLE X sigma) :
    X * (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))) = X := by
  let P := CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  have hsigmaP : sigma * P = sigma := self_mul_rpow_support hsigma
  refine LinearMap.ext fun v => ?_
  have hker : v - P v ∈ LinearMap.ker sigma := by
    rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hsigmaP, sub_self]
  have hz := LinearMap.mem_ker.mp (hsupp hker)
  rw [map_sub] at hz
  change (X * P) v = X v
  rw [Module.End.mul_apply]
  exact (sub_eq_zero.mp hz).symm

private theorem rpow_apply_eigenvector_singular
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ] {sigma : L ℋ} (hsigma : 0 ≤ sigma)
    (p mu : ℝ) {v : ℋ} (hev : sigma v = (mu : ℂ) • v)
    (hmu : mu ∈ spectrum ℝ sigma) :
    CFC.rpow sigma p v = ((mu ^ p : ℝ) : ℂ) • v := by
  rw [rpow_eq_cfc_singular hsigma]
  exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hsigma)
    (fun x : ℝ => x ^ p) hev hmu

private theorem outer_product_apply_test {ℋ₁ ℋ₂ : Type*} [Qudit ℋ₁] [Qudit ℋ₂]
    (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outer_product u v x = (inner ℂ u x : ℂ) • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

private noncomputable def outerLTest {ℋ : Type*} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] L ℋ where
  toFun v := outer_product u v
  map_add' v w := by ext x; simp [outer_product_apply_test, smul_add]
  map_smul' c v := by
    ext x
    simp only [outer_product_apply_test, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem continuous_outerL_test {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => outer_product u v) :=
  (outerLTest u).continuous_of_finiteDimensional

private theorem tendsto_rpow_exponent_to_support
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {ι : Type*} {l : Filter ι} {e : ι → ℝ} {sigma : L ℋ}
    (hsigma : 0 ≤ sigma) (he : Tendsto e l (𝓝 (0 : ℝ)))
    (hene : ∀ᶠ i in l, e i ≠ 0) :
    Tendsto (fun i => CFC.rpow sigma (e i)) l
      (𝓝 (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)))) := by
  classical
  set n := Module.finrank ℂ ℋ
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hsigmaPos : sigma.IsPositive := (LinearMap.nonneg_iff_isPositive sigma).mp hsigma
  have hsigmaSym := hsigmaPos.isSymmetric
  let b := hsigmaSym.eigenvectorBasis hn
  let eig := hsigmaSym.eigenvalues hn
  have heig0 : ∀ j, 0 ≤ eig j := hsigmaPos.nonneg_eigenvalues hn
  have heigApply : ∀ j, sigma (b j) = ((eig j : ℝ) : ℂ) • b j :=
    hsigmaSym.apply_eigenvectorBasis hn
  have hbne : ∀ j, b j ≠ 0 := fun j => b.orthonormal.ne_zero j
  have heigSpec : ∀ j, eig j ∈ spectrum ℝ sigma := fun j =>
    mem_spectrum_real_of_eigenvector_lm (hbne j) (heigApply j)
  let P := CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  have hpoint : ∀ j, Tendsto (fun i => CFC.rpow sigma (e i) (b j)) l (𝓝 (P (b j))) := by
    intro j
    have hrpow : ∀ p : ℝ,
        CFC.rpow sigma p (b j) = (((eig j) ^ p : ℝ) : ℂ) • b j := fun p =>
      rpow_apply_eigenvector_singular hsigma p (eig j) (heigApply j) (heigSpec j)
    have hPapply : P (b j) =
        (((eig j) ^ (-(1 / 2 : ℝ)) * (eig j) ^ (1 / 2 : ℝ) : ℝ) : ℂ) • b j := by
      simp only [P, Module.End.mul_apply, hrpow, map_smul, smul_smul]
      norm_cast
    rw [hPapply]
    simp only [hrpow]
    apply Filter.Tendsto.smul_const
    apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    rcases eq_or_lt_of_le (heig0 j) with hzero | hpos
    · rw [← hzero]
      simp only [Real.zero_rpow (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num), zero_mul]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hene] with i hi
      rw [Real.zero_rpow hi]
    · have htarget : eig j ^ (-(1 / 2 : ℝ)) * eig j ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hpos]
        norm_num
      rw [htarget]
      simpa [Function.comp_def, Real.rpow_zero] using
        ((Real.continuous_const_rpow (ne_of_gt hpos)).tendsto (0 : ℝ)).comp he
  have hrecon : P = ∑ j, outer_product (b j) (P (b j)) :=
    linearMap_eq_sum_outer_product b P
  have hfun : (fun i => CFC.rpow sigma (e i)) =
      fun i => ∑ j, outer_product (b j) (CFC.rpow sigma (e i) (b j)) :=
    funext fun i => linearMap_eq_sum_outer_product b _
  change Tendsto (fun i => CFC.rpow sigma (e i)) l (𝓝 P)
  rw [hrecon, hfun]
  apply tendsto_finset_sum
  intro j _
  exact ((continuous_outerL_test (b j)).tendsto _).comp (hpoint j)

private theorem hasDerivAt_trace_mul_rpow_singular
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hsigma : 0 ≤ sigma) (hsupp : suppLE rho sigma)
    {f : ℝ → ℝ} {a f' : ℝ} (hf : HasDerivAt f f' a) (hfa : f a = 0) :
    HasDerivAt (fun t => (Tr (rho * CFC.rpow sigma (f t))).re)
      (f' * (Tr (rho * CFC.log sigma)).re) a := by
  classical
  set n := Module.finrank ℂ ℋ
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hsigmaPos : sigma.IsPositive := (LinearMap.nonneg_iff_isPositive sigma).mp hsigma
  have hsigmaSym := hsigmaPos.isSymmetric
  let b := hsigmaSym.eigenvectorBasis hn
  let eig := hsigmaSym.eigenvalues hn
  let c : Fin n → ℝ := fun j => (inner ℂ (b j) (rho (b j))).re
  have heig0 : ∀ j, 0 ≤ eig j := hsigmaPos.nonneg_eigenvalues hn
  have heigApply : ∀ j, sigma (b j) = ((eig j : ℝ) : ℂ) • b j :=
    hsigmaSym.apply_eigenvectorBasis hn
  have hbne : ∀ j, b j ≠ 0 := fun j => b.orthonormal.ne_zero j
  have heigSpec : ∀ j, eig j ∈ spectrum ℝ sigma := fun j =>
    mem_spectrum_real_of_eigenvector_lm (hbne j) (heigApply j)
  have hc0 : ∀ j, eig j = 0 → c j = 0 := by
    intro j hj
    have hbker : b j ∈ LinearMap.ker sigma := by
      rw [LinearMap.mem_ker, heigApply j, hj]
      simp
    have hrhob : rho (b j) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp [c, hrhob]
  have hrpowApply : ∀ (p : ℝ) j,
      CFC.rpow sigma p (b j) = (((eig j) ^ p : ℝ) : ℂ) • b j := fun p j =>
    rpow_apply_eigenvector_singular hsigma p (eig j) (heigApply j) (heigSpec j)
  have hlogApply : ∀ j,
      CFC.log sigma (b j) = ((Real.log (eig j) : ℝ) : ℂ) • b j := fun j =>
    cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hsigma) Real.log
      (heigApply j) (heigSpec j)
  have hexpand : ∀ t,
      (Tr (rho * CFC.rpow sigma (f t))).re = ∑ j, eig j ^ (f t) * c j := by
    intro t
    rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.rpow sigma (f t)) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.End.mul_apply, hrpowApply, map_smul, inner_smul_right,
      Complex.re_ofReal_mul]
  have hlogExpand :
      (Tr (rho * CFC.log sigma)).re = ∑ j, Real.log (eig j) * c j := by
    rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.log sigma) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.End.mul_apply, hlogApply, map_smul, inner_smul_right,
      Complex.re_ofReal_mul]
  rw [show (fun t => (Tr (rho * CFC.rpow sigma (f t))).re) =
      (fun t => ∑ j, eig j ^ (f t) * c j) from funext hexpand,
    hlogExpand, Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro j _
  rcases eq_or_lt_of_le (heig0 j) with hzero | hpos
  · have hc : c j = 0 := hc0 j hzero.symm
    simp only [hc, mul_zero]
    exact hasDerivAt_const (x := a) (c := 0)
  · have hd := hf.const_rpow hpos |>.mul_const (c j)
    rw [hfa, Real.rpow_zero] at hd
    convert hd using 1
    all_goals ring

private theorem tendsto_rpow_slope_one
    {E : Type*} [Qudit E] [Nontrivial E] {rho : L E} (hrho : 0 ≤ rho) :
    Tendsto (fun alpha : ℝ =>
      ((alpha - 1)⁻¹ : ℝ) • (CFC.rpow rho alpha - rho))
      (𝓝[<] (1 : ℝ)) (𝓝 (rho * CFC.log rho)) := by
  classical
  set n := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  have hrhoPos : rho.IsPositive := (LinearMap.nonneg_iff_isPositive rho).mp hrho
  have hrhoSym := hrhoPos.isSymmetric
  let b := hrhoSym.eigenvectorBasis hn
  let eig := hrhoSym.eigenvalues hn
  have heig0 : ∀ i, 0 ≤ eig i := hrhoPos.nonneg_eigenvalues hn
  have heigApply : ∀ i, rho (b i) = ((eig i : ℝ) : ℂ) • b i :=
    hrhoSym.apply_eigenvectorBasis hn
  have hbne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have heigSpec : ∀ i, eig i ∈ spectrum ℝ rho := fun i =>
    mem_spectrum_real_of_eigenvector_lm (hbne i) (heigApply i)
  have hrpowApply : ∀ (p : ℝ) i,
      CFC.rpow rho p (b i) = (((eig i) ^ p : ℝ) : ℂ) • b i := fun p i =>
    rpow_apply_eigenvector_singular hrho p (eig i) (heigApply i) (heigSpec i)
  have hlogApply : ∀ i,
      CFC.log rho (b i) = ((Real.log (eig i) : ℝ) : ℂ) • b i := fun i =>
    cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hrho) Real.log
      (heigApply i) (heigSpec i)
  let S : ℝ → L E := fun alpha =>
    ((alpha - 1)⁻¹ : ℝ) • (CFC.rpow rho alpha - rho)
  let T : L E := rho * CFC.log rho
  have hSapply : ∀ alpha i, S alpha (b i) =
      ((((alpha - 1)⁻¹ * (eig i ^ alpha - eig i) : ℝ) : ℂ) • b i) := by
    intro alpha i
    change (((alpha - 1)⁻¹ : ℝ) : ℂ) •
        ((CFC.rpow rho alpha) (b i) - rho (b i)) = _
    rw [hrpowApply, heigApply, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hTapply : ∀ i, T (b i) =
      (((eig i * Real.log (eig i) : ℝ) : ℂ) • b i) := by
    intro i
    simp only [T, Module.End.mul_apply, hlogApply, map_smul, heigApply,
      smul_smul]
    congr 1
    push_cast
    ring
  have hpoint : ∀ i, Tendsto (fun alpha => S alpha (b i))
      (𝓝[<] (1 : ℝ)) (𝓝 (T (b i))) := by
    intro i
    rw [show (fun alpha => S alpha (b i)) = fun alpha =>
        ((((alpha - 1)⁻¹ * (eig i ^ alpha - eig i) : ℝ) : ℂ) • b i) from
      funext fun alpha => hSapply alpha i,
      hTapply]
    apply Filter.Tendsto.smul_const
    apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    rcases eq_or_lt_of_le (heig0 i) with hzero | hpos
    · rw [← hzero]
      simp only [Real.log_zero]
      refine tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < alpha :=
        Filter.Eventually.filter_mono inf_le_left
          (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
      filter_upwards [hev] with alpha halpha
      have ha0 : alpha ≠ 0 := ne_of_gt (lt_trans (by norm_num) halpha)
      rw [Real.zero_rpow ha0]
      simp
    · have hd := (hasDerivAt_id (1 : ℝ)).const_rpow hpos
      have hd' : HasDerivAt (fun x : ℝ => eig i ^ x)
          (eig i * Real.log (eig i)) 1 := by
        simpa only [id_eq, Real.rpow_one, mul_one, one_mul, mul_comm] using hd
      rw [hasDerivAt_iff_tendsto_slope] at hd'
      have hsl := hd'.mono_left (nhdsWithin_mono _ fun _ h => ne_of_lt h)
      have heq : (fun x : ℝ => (x - 1)⁻¹ * (eig i ^ x - eig i)) =
          slope (fun x : ℝ => eig i ^ x) 1 := by
        funext x
        rw [slope_def_field, Real.rpow_one, div_eq_mul_inv, mul_comm]
      rw [heq]
      exact hsl
  have hreconT : T = ∑ i, outer_product (b i) (T (b i)) :=
    linearMap_eq_sum_outer_product b T
  have hreconS : S = fun alpha => ∑ i, outer_product (b i) (S alpha (b i)) := by
    funext alpha
    exact linearMap_eq_sum_outer_product b _
  change Tendsto S (𝓝[<] (1 : ℝ)) (𝓝 T)
  rw [hreconT, hreconS]
  apply tendsto_finset_sum
  intro i _
  exact ((continuous_outerL_test (b i)).tendsto _).comp (hpoint i)

private theorem tendsto_rpow_one_left
    {E : Type*} [Qudit E] [Nontrivial E] {rho : L E} (hrho : 0 ≤ rho) :
    Tendsto (fun alpha : ℝ => CFC.rpow rho alpha)
      (𝓝[<] (1 : ℝ)) (𝓝 rho) := by
  let S : ℝ → L E := fun alpha =>
    ((alpha - 1)⁻¹ : ℝ) • (CFC.rpow rho alpha - rho)
  have hS : Tendsto S (𝓝[<] (1 : ℝ)) (𝓝 (rho * CFC.log rho)) :=
    tendsto_rpow_slope_one hrho
  have hz : Tendsto (fun alpha : ℝ => alpha - 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert ((continuous_id.sub continuous_const).tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds using 1
    all_goals norm_num
  have hscaled : Tendsto (fun alpha => (alpha - 1) • S alpha)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : L E)) := by
    simpa using hz.smul hS
  have hadd : Tendsto (fun alpha : ℝ => rho + (alpha - 1) • S alpha)
      (𝓝[<] (1 : ℝ)) (𝓝 rho) :=
    by simpa only [add_zero] using (tendsto_const_nhds (x := rho)).add hscaled
  refine hadd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  have hne : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt halpha)
  change rho +
    (alpha - 1) • (((alpha - 1)⁻¹ : ℝ) • (CFC.rpow rho alpha - rho))
      = CFC.rpow rho alpha
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul, add_sub_cancel]

private theorem tendsto_rpow_one_sub_to_support_left
    {E : Type*} [Qudit E] [Nontrivial E] {sigma : L E} (hsigma : 0 ≤ sigma) :
    Tendsto (fun alpha : ℝ => CFC.rpow sigma (1 - alpha))
      (𝓝[<] (1 : ℝ))
      (𝓝 (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)))) := by
  have he : Tendsto (fun alpha : ℝ => 1 - alpha)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert ((continuous_const.sub continuous_id).tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds using 1
    all_goals norm_num
  have hene : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), 1 - alpha ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with alpha halpha
    exact sub_ne_zero.mpr (ne_of_gt halpha)
  exact tendsto_rpow_exponent_to_support hsigma he hene

private theorem tendsto_petzQuasi_slope_of_suppLE
    {A : Sys} (rho : DensityMatrix A) {sigma : Operator A}
    (hsigma : 0 ≤ sigma) (hsupp : suppLE rho.operator sigma) :
    Tendsto (fun alpha : ℝ =>
      (petzQuasi alpha rho sigma - 1) / (alpha - 1))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((Tr (rho.operator *
        (CFC.log rho.operator - CFC.log sigma))).re)) := by
  let P := CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  let S : ℝ → Operator A := fun alpha =>
    ((alpha - 1)⁻¹ : ℝ) • (CFC.rpow rho.operator alpha - rho.operator)
  let B : ℝ → Operator A := fun alpha => CFC.rpow sigma (1 - alpha)
  have hS : Tendsto S (𝓝[<] (1 : ℝ))
      (𝓝 (rho.operator * CFC.log rho.operator)) :=
    tendsto_rpow_slope_one rho.nonneg
  have hB : Tendsto B (𝓝[<] (1 : ℝ)) (𝓝 P) :=
    tendsto_rpow_one_sub_to_support_left hsigma
  have hcomm : rho.operator * CFC.log rho.operator =
      CFC.log rho.operator * rho.operator := by
    exact ((IsSelfAdjoint.of_nonneg rho.nonneg).commute_cfc
      (Commute.refl rho.operator) Real.log).eq.symm
  have hsuppLog : suppLE (rho.operator * CFC.log rho.operator) sigma := by
    intro v hv
    have hzero := LinearMap.mem_ker.mp (hsupp hv)
    rw [LinearMap.mem_ker, hcomm, Module.End.mul_apply, hzero, map_zero]
  have hfirst : Tendsto (fun alpha => (Tr (S alpha * B alpha)).re)
      (𝓝[<] (1 : ℝ)) (𝓝 ((Tr (rho.operator * CFC.log rho.operator)).re)) := by
    have h := (QuantumState.continuous_re_trace_lm.tendsto _).comp (hS.mul hB)
    have hfix : (rho.operator * CFC.log rho.operator) * P =
        rho.operator * CFC.log rho.operator := by
      exact mul_rpow_support_eq hsigma hsuppLog
    rw [hfix] at h
    simpa only [Function.comp_apply] using h
  let f : ℝ → ℝ := fun alpha => 1 - alpha
  have hf : HasDerivAt f (-1) 1 := by
    simpa [f] using (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).sub
      (hasDerivAt_id (1 : ℝ))
  have hderiv := hasDerivAt_trace_mul_rpow_singular hsigma hsupp hf (by norm_num [f])
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  have hsecond : Tendsto (fun alpha =>
      ((Tr (rho.operator * B alpha)).re - 1) / (alpha - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (-(Tr (rho.operator * CFC.log sigma)).re)) := by
    have h := hderiv.mono_left (nhdsWithin_mono _ fun _ h => ne_of_lt h)
    have hrpow0 : CFC.rpow sigma (0 : ℝ) = 1 := CFC.rpow_zero sigma hsigma
    have hbase : (Tr (rho.operator * CFC.rpow sigma (f 1))).re = 1 := by
      rw [show f 1 = 0 by norm_num [f], hrpow0, mul_one, rho.trace_one]
      norm_num
    have hbase' : (Tr (rho.operator * CFC.rpow sigma (1 - (1 : ℝ)))).re = 1 := by
      simpa only [f] using hbase
    convert h using 1
    · funext alpha
      rw [slope_def_field]
      simp only [f, B]
      congr 2
      exact hbase'.symm
    · ring
  have hsum := hfirst.add hsecond
  have hsum' := hsum.congr' (by
    filter_upwards [self_mem_nhdsWithin] with alpha halpha
    have hne : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt halpha)
    change (Tr (S alpha * B alpha)).re +
        ((Tr (rho.operator * B alpha)).re - 1) / (alpha - 1) =
      ((Tr (CFC.rpow rho.operator alpha * CFC.rpow sigma (1 - alpha))).re - 1) /
        (alpha - 1)
    unfold S B
    change (Tr (((((alpha - 1)⁻¹ : ℝ) : ℂ) •
        (CFC.rpow rho.operator alpha - rho.operator)) *
          CFC.rpow sigma (1 - alpha))).re +
        ((Tr (rho.operator * CFC.rpow sigma (1 - alpha))).re - 1) /
          (alpha - 1) = _
    rw [smul_mul_assoc, map_smul, sub_mul, map_sub]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
    field_simp
    ring)
  convert hsum' using 1
  rw [mul_sub, map_sub, Complex.sub_re]
  ring

private theorem petzRenyiDivBits_tendsto_umegaki_of_suppLE
    {A : Sys} (rho : DensityMatrix A) {sigma : Operator A}
    (hsigma : 0 ≤ sigma) (hsupp : suppLE rho.operator sigma) :
    Tendsto (fun alpha : ℝ => petzRenyiDivBits alpha rho sigma)
      (𝓝[<] (1 : ℝ)) (𝓝 (umegakiRelEntropyBits rho sigma)) := by
  let q : ℝ → ℝ := fun alpha => petzQuasi alpha rho sigma
  let d : ℝ := (Tr (rho.operator *
    (CFC.log rho.operator - CFC.log sigma))).re
  have hrpowRhoOne : CFC.rpow rho.operator (1 : ℝ) = rho.operator :=
    CFC.rpow_one rho.operator rho.nonneg
  have hrpowSigmaZero : CFC.rpow sigma (0 : ℝ) = 1 :=
    CFC.rpow_zero sigma hsigma
  have hq1 : q 1 = 1 := by
    unfold q petzQuasi
    rw [hrpowRhoOne, show 1 - (1 : ℝ) = 0 by norm_num,
      hrpowSigmaZero, mul_one, rho.trace_one]
    norm_num
  have hslope : Tendsto (slope q 1) (𝓝[<] (1 : ℝ)) (𝓝 d) := by
    have h := tendsto_petzQuasi_slope_of_suppLE rho hsigma hsupp
    convert h using 1
    funext alpha
    rw [slope_def_field, hq1]
  have hqderiv : HasDerivWithinAt q d (Set.Iio 1) 1 :=
    (hasDerivWithinAt_iff_tendsto_slope'
      (s := Set.Iio (1 : ℝ)) (by simp)).mpr hslope
  have hlogderiv := hqderiv.log (by rw [hq1]; norm_num)
  have hlogslope :=
    (hasDerivWithinAt_iff_tendsto_slope'
      (s := Set.Iio (1 : ℝ)) (by simp)).mp hlogderiv
  have hlogtwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hreal : Tendsto (fun alpha : ℝ =>
      Real.logb 2 (q alpha) / (alpha - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (d / Real.log 2)) := by
    have h := hlogslope.div_const (Real.log 2)
    convert h using 1
    · funext alpha
      rw [slope_def_field, hq1, Real.log_one]
      unfold Real.logb
      ring
    · rw [hq1]
      ring
  have hcoe : Tendsto (fun alpha : ℝ =>
      ((Real.logb 2 (q alpha) / (alpha - 1) : ℝ) : EReal))
      (𝓝[<] (1 : ℝ)) (𝓝 (((d / Real.log 2 : ℝ) : EReal))) :=
    EReal.tendsto_coe.mpr hreal
  have hqcont : Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    by
      have h := hqderiv.continuousWithinAt
      change Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 (q 1)) at h
      rw [hq1] at h
      exact h
  have hqpos : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), 0 < q alpha :=
    hqcont.eventually (Ioi_mem_nhds zero_lt_one)
  have htarget : umegakiRelEntropyBits rho sigma =
      ((d / Real.log 2 : ℝ) : EReal) := by
    unfold umegakiRelEntropyBits
    rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_pos hsupp]
    unfold SandwichedRenyiRelativeEntropy.umegakiNorm d
    rw [rho.trace_one]
    norm_num
    rw [← EReal.coe_div]
  rw [htarget]
  refine hcoe.congr' ?_
  filter_upwards [hqpos] with alpha halpha
  unfold petzRenyiDivBits
  rw [if_neg (ne_of_gt halpha)]

private theorem operator_rpow_eq_cfc_singular {A : Sys}
    {sigma : Operator A} (hsigma : 0 ≤ sigma) (p : ℝ) :
    CFC.rpow sigma p = cfc (fun x : ℝ => x ^ p) sigma := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hsigma

private theorem operator_rpow_mul_rpow_singular {A : Sys}
    {sigma : Operator A} (hsigma : 0 ≤ sigma) (p q : ℝ) :
    CFC.rpow sigma p * CFC.rpow sigma q =
      cfc (fun x : ℝ => x ^ p * x ^ q) sigma := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ sigma) :=
    fun f => (spectrum_real_finite_petz sigma).continuousOn f
  rw [operator_rpow_eq_cfc_singular hsigma p,
    operator_rpow_eq_cfc_singular hsigma q]
  exact (cfc_mul _ _ sigma (hcont _) (hcont _)).symm

private theorem operator_rpow_half_sq {A : Sys} {X : Operator A}
    (hX : 0 ≤ X) : CFC.rpow X (1 / 2) * CFC.rpow X (1 / 2) = X := by
  rw [operator_rpow_mul_rpow_singular hX]
  trans cfc (fun x : ℝ => x) X
  · apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hX hx
    rcases eq_or_lt_of_le hx0 with rfl | hxpos
    · change (0 : ℝ) ^ (1 / 2 : ℝ) * 0 ^ (1 / 2 : ℝ) = 0
      rw [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num), zero_mul]
    · change x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x
      rw [← Real.rpow_add hxpos]
      norm_num
  · exact cfc_id' ℝ X

private theorem rpow_support_nonneg {A : Sys} {sigma : Operator A}
    (hsigma : 0 ≤ sigma) :
    0 ≤ CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)) := by
  rw [operator_rpow_mul_rpow_singular hsigma]
  apply cfc_nonneg
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hsigma hx
  exact mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hx0 _)

private theorem rpow_support_le_one {A : Sys} {sigma : Operator A}
    (hsigma : 0 ≤ sigma) :
    CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)) ≤ 1 := by
  rw [operator_rpow_mul_rpow_singular hsigma]
  apply cfc_le_one
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hsigma hx
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · rw [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num), zero_mul]
    norm_num
  · rw [← Real.rpow_add hxpos]
    norm_num

private theorem nonneg_apply_eq_zero_of_inner_self_eq_zero_petz
    {A : Sys} {R : Operator A} (hR : 0 ≤ R) {x : Space A}
    (hinner : (inner ℂ (R x) x).re = 0) : R x = 0 := by
  let s : Operator A := CFC.rpow R (1 / 2)
  have hs_sq : s * s = R := operator_rpow_half_sq hR
  have hs_symm : s.IsSymmetric :=
    (LinearMap.nonneg_iff_isPositive s).mp CFC.rpow_nonneg |>.isSymmetric
  have hs_apply : s (s x) = R x := by
    have h := congrArg (fun T : Operator A => T x) hs_sq
    simpa using h
  have hnorm : ‖s x‖ ^ 2 = (inner ℂ (R x) x).re := by
    have hpair : inner ℂ (s x) (s x) = inner ℂ (R x) x := by
      calc
        inner ℂ (s x) (s x) = inner ℂ (s (s x)) x :=
          (hs_symm (s x) x).symm
        _ = inner ℂ (R x) x := by rw [hs_apply]
    calc
      ‖s x‖ ^ 2 = (inner ℂ (s x) (s x)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) (E := Space A) (s x)
      _ = (inner ℂ (R x) x).re := congrArg Complex.re hpair
  rw [hinner] at hnorm
  have hsx : s x = 0 := by
    apply norm_eq_zero.mp
    exact pow_eq_zero_iff two_ne_zero |>.mp hnorm
  rw [← hs_apply, hsx, map_zero]

private theorem nonneg_operator_eq_zero_of_trace_re_eq_zero_petz
    {A : Sys} {R : Operator A} (hR : 0 ≤ R)
    (htrace : (Tr R).re = 0) : R = 0 := by
  let MR : Matrix (Fin A.dim) (Fin A.dim) ℂ :=
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin A.dim)
      (n := Fin A.dim)).symm R
  have hMR : Matrix.toEuclideanLin MR = R :=
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin A.dim)
      (n := Fin A.dim)).apply_symm_apply R
  have hMpos : MR.PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff]
    simpa [hMR] using (LinearMap.nonneg_iff_isPositive R).mp hR
  have htrace_toEuclideanLin :
      Tr (Matrix.toEuclideanLin MR) = Matrix.trace MR := by
    change LinearMap.trace ℂ _ (Matrix.toEuclideanLin MR) = Matrix.trace MR
    rw [LinearMap.trace_eq_matrix_trace
      (R := ℂ)
      (b := (EuclideanSpace.basisFun (Fin A.dim) ℂ).toBasis)
      (f := Matrix.toEuclideanLin MR)]
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hMtrace_re : (Matrix.trace MR).re = 0 := by
    rw [← htrace_toEuclideanLin, hMR]
    exact htrace
  have hMtrace_im : (Matrix.trace MR).im = 0 :=
    (Complex.nonneg_iff.mp hMpos.trace_nonneg).2.symm
  have hMtrace : Matrix.trace MR = 0 := by
    apply Complex.ext
    · simpa using hMtrace_re
    · simpa using hMtrace_im
  have hMzero : MR = 0 := hMpos.trace_eq_zero_iff.mp hMtrace
  rw [← hMR, hMzero]
  exact map_zero (Matrix.toEuclideanLin
    (𝕜 := ℂ) (m := Fin A.dim) (n := Fin A.dim))

private theorem mul_eq_zero_of_nonneg_of_trace_re_eq_zero_petz
    {A : Sys} {X Y : Operator A} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (htrace : (Tr (X * Y)).re = 0) : X * Y = 0 := by
  let s : Operator A := CFC.rpow Y (1 / 2)
  have hs_nonneg : 0 ≤ s := CFC.rpow_nonneg
  have hs_symm : s.IsSymmetric :=
    (LinearMap.nonneg_iff_isPositive s).mp hs_nonneg |>.isSymmetric
  have hs_sq : s * s = Y := operator_rpow_half_sq hY
  let T : Operator A := s * (X * s)
  have hTpos : T.IsPositive := by
    have hXpos : X.IsPositive := (LinearMap.nonneg_iff_isPositive X).mp hX
    simpa [T, hs_symm.adjoint_eq, mul_assoc] using hXpos.adjoint_conj s
  have hTtrace : (Tr T).re = 0 := by
    have hcycle : Tr T = Tr (X * Y) := by
      calc
        Tr T = Tr ((X * s) * s) := by
          unfold T
          rw [LinearMap.trace_mul_comm]
        _ = Tr (X * (s * s)) := by rw [mul_assoc]
        _ = Tr (X * Y) := by rw [hs_sq]
    rw [hcycle]
    exact htrace
  have hTzero : T = 0 :=
    nonneg_operator_eq_zero_of_trace_re_eq_zero_petz
      ((LinearMap.nonneg_iff_isPositive T).mpr hTpos) hTtrace
  have hXs : X * s = 0 := by
    apply LinearMap.ext
    intro x
    apply nonneg_apply_eq_zero_of_inner_self_eq_zero_petz hX
    have hquad : inner ℂ (T x) x = inner ℂ (X (s x)) (s x) := by
      change inner ℂ (s (X (s x))) x = inner ℂ (X (s x)) (s x)
      exact hs_symm (X (s x)) x
    rw [show T x = 0 by rw [hTzero]; rfl, inner_zero_left] at hquad
    simpa using congrArg Complex.re hquad.symm
  rw [← hs_sq, ← mul_assoc, hXs, zero_mul]

private theorem petzQuasi_tendsto_support_left
    {A : Sys} (rho : DensityMatrix A) {sigma : Operator A}
    (hsigma : 0 ≤ sigma) :
    Tendsto (fun alpha : ℝ => petzQuasi alpha rho sigma)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((Tr (rho.operator *
        (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))))).re)) := by
  have hR := tendsto_rpow_one_left rho.nonneg
  have hS := tendsto_rpow_one_sub_to_support_left hsigma
  have hmul := hR.mul hS
  have htrace := (QuantumState.continuous_re_trace_lm.tendsto _).comp hmul
  simpa only [petzQuasi, Function.comp_apply] using htrace

private theorem trace_rpow_support_lt_one_of_not_suppLE
    {A : Sys} (rho : DensityMatrix A) {sigma : Operator A}
    (hsigma : 0 ≤ sigma) (hnsupp : ¬ suppLE rho.operator sigma) :
    (Tr (rho.operator *
      (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))))).re < 1 := by
  let P : Operator A :=
    CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  let D : Operator A := 1 - P
  let c : ℝ := (Tr (rho.operator * P)).re
  have hP0 : 0 ≤ P := rpow_support_nonneg hsigma
  have hP1 : P ≤ 1 := rpow_support_le_one hsigma
  have hD0 : 0 ≤ D := sub_nonneg.mpr hP1
  have htraceD := NativeMeasuredRelativeEntropy.trace_comp_nonneg
    D rho.operator hD0 rho.nonneg
  have htraceD' : 0 ≤ (Tr (D * rho.operator)).re := by
    simpa only [Module.End.mul_eq_comp] using (Complex.nonneg_iff.mp htraceD).1
  have htraceEq : (Tr (D * rho.operator)).re = 1 - c := by
    unfold D c
    rw [sub_mul, one_mul, map_sub, Complex.sub_re, rho.trace_one,
      LinearMap.trace_mul_comm]
    norm_num
  have hc1 : c ≤ 1 := by linarith
  have hPcomm :
      CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)) =
        CFC.rpow sigma (-(1 / 2)) * CFC.rpow sigma (1 / 2) := by
    rw [operator_rpow_mul_rpow_singular hsigma,
      operator_rpow_mul_rpow_singular hsigma]
    exact cfc_congr fun _ _ => mul_comm _ _
  have hPsa : IsSelfAdjoint P := by
    have hneg : IsSelfAdjoint (CFC.rpow sigma (-(1 / 2))) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hpos : IsSelfAdjoint (CFC.rpow sigma (1 / 2)) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    simp only [IsSelfAdjoint, P]
    rw [star_mul, hneg.star_eq, hpos.star_eq, ← hPcomm]
  have hDsa : IsSelfAdjoint D := by
    exact (IsSelfAdjoint.one (R := Operator A)).sub hPsa
  have hrhosa : IsSelfAdjoint rho.operator := IsSelfAdjoint.of_nonneg rho.nonneg
  have hcne : c ≠ 1 := by
    intro hc
    have htraceZero : (Tr (D * rho.operator)).re = 0 := by
      rw [htraceEq, hc, sub_self]
    have hDrho : D * rho.operator = 0 :=
      mul_eq_zero_of_nonneg_of_trace_re_eq_zero_petz hD0 rho.nonneg htraceZero
    have hrhoD : rho.operator * D = 0 := by
      have h := congrArg star hDrho
      rwa [star_mul, hDsa.star_eq, hrhosa.star_eq, star_zero] at h
    apply hnsupp
    intro v hv
    rw [LinearMap.mem_ker]
    by_cases hv0 : v = 0
    · simp [hv0]
    have hev : sigma v = ((0 : ℝ) : ℂ) • v := by
      rw [LinearMap.mem_ker] at hv
      simpa using hv
    have hspec : (0 : ℝ) ∈ spectrum ℝ sigma :=
      mem_spectrum_real_of_eigenvector_lm hv0 hev
    have hneg : CFC.rpow sigma (-(1 / 2)) v =
        ((((0 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • v) := by
      rw [operator_rpow_eq_cfc_singular hsigma]
      exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hsigma)
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) hev hspec
    have hneg0 : CFC.rpow sigma (-(1 / 2)) v = 0 := by
      rw [hneg, Real.zero_rpow (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num)]
      simp
    have hPv : P v = 0 := by
      simp only [P, Module.End.mul_apply]
      rw [hneg0, map_zero]
    have hDv : D v = v := by
      simp only [D, LinearMap.sub_apply, hPv, sub_zero]
      rfl
    have h := LinearMap.congr_fun hrhoD v
    rw [Module.End.mul_apply, hDv] at h
    exact h
  exact lt_of_le_of_ne hc1 hcne

private theorem petzRenyiDivBits_tendsto_top_of_not_suppLE
    {A : Sys} (rho : DensityMatrix A) {sigma : Operator A}
    (hsigma : 0 ≤ sigma) (hnsupp : ¬ suppLE rho.operator sigma) :
    Tendsto (fun alpha : ℝ => petzRenyiDivBits alpha rho sigma)
      (𝓝[<] (1 : ℝ)) (𝓝 (⊤ : EReal)) := by
  let P : Operator A :=
    CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  let c : ℝ := (Tr (rho.operator * P)).re
  let d : ℝ := (c + 1) / 2
  let k : ℝ := -Real.logb 2 d
  have hP0 : 0 ≤ P := rpow_support_nonneg hsigma
  have htraceP := NativeMeasuredRelativeEntropy.trace_comp_nonneg
    P rho.operator hP0 rho.nonneg
  have hc0 : 0 ≤ c := by
    have h := (Complex.nonneg_iff.mp htraceP).1
    unfold c
    rw [← LinearMap.trace_mul_comm]
    simpa only [Module.End.mul_eq_comp] using h
  have hc1 : c < 1 := trace_rpow_support_lt_one_of_not_suppLE rho hsigma hnsupp
  have hcd : c < d := by unfold d; linarith
  have hd0 : 0 < d := by unfold d; linarith
  have hd1 : d < 1 := by unfold d; linarith
  have hk : 0 < k := by
    unfold k
    exact neg_pos.mpr (Real.logb_neg one_lt_two hd0 hd1)
  have hq : Tendsto (fun alpha : ℝ => petzQuasi alpha rho sigma)
      (𝓝[<] (1 : ℝ)) (𝓝 c) := petzQuasi_tendsto_support_left rho hsigma
  have hq_lt : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), petzQuasi alpha rho sigma < d :=
    hq.eventually (Iio_mem_nhds hcd)
  have hhalf : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < alpha :=
    Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have htozero : Tendsto (fun alpha : ℝ => 1 - alpha)
      (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [show 𝓝[>] (0 : ℝ) = 𝓝 (0 : ℝ) ⊓ 𝓟 (Set.Ioi 0) from rfl,
      tendsto_inf]
    constructor
    · convert ((continuous_const.sub continuous_id).tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds using 1
      all_goals norm_num
    · rw [tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with alpha halpha
      exact sub_pos.mpr (show alpha < 1 from halpha)
  have hinv : Tendsto (fun alpha : ℝ => (1 - alpha)⁻¹)
      (𝓝[<] (1 : ℝ)) atTop := tendsto_inv_nhdsGT_zero.comp htozero
  have hg : Tendsto (fun alpha : ℝ => k * (1 - alpha)⁻¹)
      (𝓝[<] (1 : ℝ)) atTop := hinv.const_mul_atTop hk
  rw [EReal.tendsto_nhds_top_iff_real]
  intro x
  have hgx : ∀ᶠ alpha in 𝓝[<] (1 : ℝ), x < k * (1 - alpha)⁻¹ :=
    hg.eventually_gt_atTop x
  filter_upwards [hq_lt, hhalf, self_mem_nhdsWithin, hgx] with
      alpha hqd halpha0 halpha1 hgrowth
  have ha0 : 0 < alpha := lt_trans (by norm_num) halpha0
  have hq0 : 0 ≤ petzQuasi alpha rho sigma :=
    petzQuasi_nonneg alpha ha0 halpha1 rho sigma hsigma
  by_cases hz : petzQuasi alpha rho sigma = 0
  · unfold petzRenyiDivBits
    rw [if_pos hz]
    exact EReal.coe_lt_top x
  · have hqpos : 0 < petzQuasi alpha rho sigma :=
      lt_of_le_of_ne hq0 (Ne.symm hz)
    have hlog : Real.logb 2 (petzQuasi alpha rho sigma) < Real.logb 2 d :=
      Real.logb_lt_logb one_lt_two hqpos hqd
    have hden : alpha - 1 < 0 := sub_neg.mpr halpha1
    have hdiv : Real.logb 2 d / (alpha - 1) <
        Real.logb 2 (petzQuasi alpha rho sigma) / (alpha - 1) :=
      div_lt_div_of_neg_of_lt hden hlog
    have hkg : k * (1 - alpha)⁻¹ = Real.logb 2 d / (alpha - 1) := by
      unfold k
      rw [show 1 - alpha = -(alpha - 1) by ring, inv_neg]
      simp only [neg_mul, div_eq_mul_inv]
      ring
    unfold petzRenyiDivBits
    rw [if_neg hz, EReal.coe_lt_coe_iff]
    rw [hkg] at hgrowth
    exact hgrowth.trans hdiv

/-- The support-sensitive Petz Rényi divergence in bits converges from below
to native Umegaki relative entropy for every positive second argument.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1566--1651` (`prop-petz_rel_ent_lim_1`). -/
theorem petzRenyiDivBits_tendsto_umegaki_of_nonneg
    {A : Sys} (rho : DensityMatrix A) (sigma : Operator A)
    (hsigma : 0 ≤ sigma) :
    Tendsto (fun alpha : ℝ => petzRenyiDivBits alpha rho sigma)
      (𝓝[<] (1 : ℝ)) (𝓝 (umegakiRelEntropyBits rho sigma)) := by
  by_cases hsupp : suppLE rho.operator sigma
  · exact petzRenyiDivBits_tendsto_umegaki_of_suppLE rho hsigma hsupp
  · have htarget : umegakiRelEntropyBits rho sigma = (⊤ : EReal) := by
      unfold umegakiRelEntropyBits
      rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_neg hsupp]
      exact EReal.top_div_of_pos_ne_top
        (EReal.coe_pos.mpr (Real.log_pos one_lt_two)) (EReal.coe_ne_top _)
    rw [htarget]
    exact petzRenyiDivBits_tendsto_top_of_not_suppLE rho hsigma hsupp

end QuantumModel.NativeHypothesisTesting
