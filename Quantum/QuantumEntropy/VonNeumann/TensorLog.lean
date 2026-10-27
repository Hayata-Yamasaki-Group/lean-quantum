/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.TensorCFCCore
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift

/-!
# Logarithm of a tensor product

`log (A ⊗ B) = log A ⊗ 1 + 1 ⊗ log B` for positive-definite `A`, `B`,
via the continuous functional calculus.

The proof mirrors `TensorCFC.rpow_tensorProduct`: both sides are computed on
the tensor-product eigenvector basis of `A` and `B`; on an eigenvector with
eigenvalue `λᵢ · μⱼ` the left side acts by `Real.log (λᵢ * μⱼ)` and the right
side by `Real.log λᵢ + Real.log μⱼ`, which agree because positive-definiteness
puts both eigenvalues in `(0, ∞)`.
-/

namespace TensorCFC

open QuantumState QuantumChannel TensorProduct
open GeneralizedPerspectiveFunction SandwichedRenyiRelativeEntropy

universe u v

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- **Logarithm of a tensor product**: for positive-definite `A`, `B`,
`log (A ⊗ B) = log A ⊗ 1 + 1 ⊗ log B`. -/
theorem log_tensorProduct [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂)
    (hA : A ∈ pdSet) (hB : B ∈ pdSet) :
    CFC.log
        (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
          L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap =
      (TensorProduct.map ((CFC.log A : ℋ₁ →L[ℂ] ℋ₁) : L ℋ₁) (1 : L ℋ₂) :
          L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap +
        (TensorProduct.map (1 : L ℋ₁) ((CFC.log B : ℋ₂ →L[ℂ] ℋ₂) : L ℋ₂) :
          L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap := by
  classical
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨hB_sa, hB_spec⟩ := hB
  haveI : Nontrivial (ℋ₁ ⊗[ℂ] ℋ₂) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  have hA_sym : (A : L ℋ₁).IsSymmetric := hA_sa.isSymmetric
  have hB_sym : (B : L ℋ₂).IsSymmetric := hB_sa.isSymmetric
  set n₁ := Module.finrank ℂ ℋ₁
  set n₂ := Module.finrank ℂ ℋ₂
  set eA := hA_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eB := hB_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₂ = n₂)
  set eigA := hA_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eigB := hB_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₂ = n₂)
  -- Self-adjointness of the tensor-product operator, via symmetry on tensors
  have hAB_sym : (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).IsSymmetric := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul c d =>
            rw [map_tmul, map_tmul, TensorProduct.inner_tmul, TensorProduct.inner_tmul,
              hA_sym a c, hB_sym b d]
        | add y₁ y₂ h₁ h₂ => rw [map_add, inner_add_right, inner_add_right, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => rw [map_add, inner_add_left, inner_add_left, h₁, h₂]
  have hAB_sa :
      IsSelfAdjoint (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by
      simpa using hAB_sym)
  -- Compute both sides on the tensor-product eigenvector basis
  apply ContinuousLinearMap.coe_injective
  apply (eA.toBasis.tensorProduct eB.toBasis).ext
  intro ⟨i, j⟩
  have hA_eig : A (eA i) = ((eigA i : ℝ) : ℂ) • eA i :=
    hA_sym.apply_eigenvectorBasis _ i
  have hB_eig : B (eB j) = ((eigB j : ℝ) : ℂ) • eB j :=
    hB_sym.apply_eigenvectorBasis _ j
  have heigA_spec : eigA i ∈ spectrum ℝ A := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage,
      ContinuousLinearMap.spectrum_eq]
    exact (hA_sym.hasEigenvalue_eigenvalues _ i).mem_spectrum
  have heigB_spec : eigB j ∈ spectrum ℝ B := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage,
      ContinuousLinearMap.spectrum_eq]
    exact (hB_sym.hasEigenvalue_eigenvalues _ j).mem_spectrum
  have heigA_pos : (0 : ℝ) < eigA i := hA_spec heigA_spec
  have heigB_pos : (0 : ℝ) < eigB j := hB_spec heigB_spec
  have htb : (eA.toBasis.tensorProduct eB.toBasis) (i, j) = eA i ⊗ₜ eB j := by
    rw [eA.toBasis.tensorProduct_apply]; simp [OrthonormalBasis.coe_toBasis]
  rw [htb]
  change CFC.log
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap (eA i ⊗ₜ eB j) =
    ((TensorProduct.map ((CFC.log A : ℋ₁ →L[ℂ] ℋ₁) : L ℋ₁) (1 : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)) +
      (TensorProduct.map (1 : L ℋ₁) ((CFC.log B : ℋ₂ →L[ℂ] ℋ₂) : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂))) (eA i ⊗ₜ eB j)
  -- Eigenvector equation for the tensor-product operator
  have hAB_eig :
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap (eA i ⊗ₜ eB j) =
      ((eigA i * eigB j : ℝ) : ℂ) • (eA i ⊗ₜ eB j) := by
    change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
      L (ℋ₁ ⊗[ℂ] ℋ₂)) (eA i ⊗ₜ eB j) = _
    rw [map_tmul]
    change (A (eA i)) ⊗ₜ[ℂ] (B (eB j)) = _
    rw [hA_eig, hB_eig, TensorProduct.smul_tmul_smul, ← Complex.ofReal_mul]
  have hAB_spec : (eigA i * eigB j : ℝ) ∈ spectrum ℝ
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap := by
    have hv0 : eA i ⊗ₜ[ℂ] eB j ≠ 0 := by
      intro hzero
      exact (eA.toBasis.tensorProduct eB.toBasis).ne_zero (i, j) (htb.trans hzero)
    exact TensorCFC.mem_spectrum_real_of_eigenvector hv0 hAB_eig
  -- Left side: `log` acts by `Real.log (λᵢ * μⱼ)` on the eigenvector
  have hLHS : CFC.log
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap (eA i ⊗ₜ eB j) =
      ((Real.log (eigA i * eigB j) : ℝ) : ℂ) • (eA i ⊗ₜ eB j) := by
    unfold CFC.log
    exact TensorCFC.cfc_real_apply_eigenvector hAB_sa Real.log hAB_eig hAB_spec
  -- Right side: the two summands act by `Real.log λᵢ` and `Real.log μⱼ`
  have hlogA : (CFC.log A) (eA i) = ((Real.log (eigA i) : ℝ) : ℂ) • eA i := by
    unfold CFC.log
    exact TensorCFC.cfc_real_apply_eigenvector hA_sa Real.log hA_eig heigA_spec
  have hlogB : (CFC.log B) (eB j) = ((Real.log (eigB j) : ℝ) : ℂ) • eB j := by
    unfold CFC.log
    exact TensorCFC.cfc_real_apply_eigenvector hB_sa Real.log hB_eig heigB_spec
  rw [hLHS, LinearMap.add_apply, map_tmul, map_tmul]
  change _ = ((CFC.log A) (eA i)) ⊗ₜ[ℂ] ((1 : L ℋ₂) (eB j)) +
    ((1 : L ℋ₁) (eA i)) ⊗ₜ[ℂ] ((CFC.log B) (eB j))
  rw [hlogA, hlogB]
  change ((Real.log (eigA i * eigB j) : ℝ) : ℂ) • (eA i ⊗ₜ[ℂ] eB j) =
    (((Real.log (eigA i) : ℝ) : ℂ) • eA i) ⊗ₜ[ℂ] eB j +
      eA i ⊗ₜ[ℂ] (((Real.log (eigB j) : ℝ) : ℂ) • eB j)
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    Real.log_mul heigA_pos.ne' heigB_pos.ne', Complex.ofReal_add, add_smul]

end TensorCFC
