/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumMechanics.Channel.Basic

/-!
# Sandwiched Rényi relative entropy: tensor laws

Tensor multiplicativity of the sandwiched quasi-entropy and tensor additivity of the
sandwiched Rényi divergence, together with the CLM/LM real-power transport helpers
(`TensorInternal`) that `SandwichedRenyi.JointConvexity` also uses.
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

namespace TensorInternal

open LiebAndoTrace GeneralizedPerspectiveFunction
open scoped MatrixOrder

universe u₃

variable {ℋ : Type u₃} [Qudit ℋ]

lemma toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

lemma rpow_toContinuousLinearMap (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  letI : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower ℝ≥0 ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eNN : L ℋ ≃ₐ[ℝ≥0] B ℋ := e.toAlgEquiv.restrictScalars ℝ≥0
  change e (cfc (fun x : ℝ≥0 => x ^ p) A) = cfc (fun x : ℝ≥0 => x ^ p) (e A)
  by_cases hA : 0 ≤ A
  · have heA : (0 : B ℋ) ≤ e A := by
      exact (ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mp hA
    by_cases hf : ContinuousOn (fun x : ℝ≥0 => x ^ p) (spectrum ℝ≥0 A)
    · exact StarAlgHomClass.map_cfc (R := ℝ≥0) (S := ℂ) e _ A hf
        (StarAlgEquiv.isometry e).continuous hA heA
    · have hf' : ¬ ContinuousOn (fun x : ℝ≥0 => x ^ p)
          (spectrum ℝ≥0 (e A)) := by
        rw [show e A = eNN A from rfl, AlgEquiv.spectrum_eq eNN A]
        exact hf
      rw [cfc_apply_of_not_continuousOn A hf,
        cfc_apply_of_not_continuousOn (e A) hf', map_zero]
  · have heA : ¬ (0 : B ℋ) ≤ e A := by
      intro heA
      exact hA ((ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mpr heA)
    rw [cfc_apply_of_not_predicate A hA,
      cfc_apply_of_not_predicate (e A) heA, map_zero]

lemma rpow_toLinearMap (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := TensorInternal.rpow_toContinuousLinearMap A.toLinearMap p
  rw [TensorInternal.toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

end TensorInternal

section TensorMultiplicativity

open QuantumChannel TensorProduct

universe u₁ u₂

variable {ℋ₁ : Type u₁} {ℋ₂ : Type u₂} [Qudit ℋ₁] [Qudit ℋ₂]

private lemma rpow_tensorProduct_direct (A : L ℋ₁) (B : L ℋ₂) (p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) := by
  have hAc : (0 : ℋ₁ →L[ℂ] ℋ₁) ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff
      (0 : ℋ₁ →L[ℂ] ℋ₁) A.toContinuousLinearMap).mp hA
  have hBc : (0 : ℋ₂ →L[ℂ] ℋ₂) ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff
      (0 : ℋ₂ →L[ℂ] ℋ₂) B.toContinuousLinearMap).mp hB
  have h := TensorCFC.rpow_tensorProduct
    A.toContinuousLinearMap B.toContinuousLinearMap p hAc hBc
  have h' := congrArg ContinuousLinearMap.toLinearMap h
  simpa only [TensorInternal.rpow_toLinearMap] using h'

/-- Tensor multiplicativity of sandwichedQuasi:
    Q_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q_α(ρ₁ ‖ σ₁) · Q_α(ρ₂ ‖ σ₂).

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedQuasi_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    sandwichedQuasi α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂ := by
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct,
    sandwichedQuasi_eq_direct]
  set β := (1 - α) / (2 * α)
  set P₁ := CFC.rpow σ₁ β
  set P₂ := CFC.rpow σ₂ β
  rw [rpow_tensorProduct_direct σ₁ σ₂ β hσ₁ hσ₂,
    show TensorProduct.map P₁ P₂ * TensorProduct.map ρ₁ ρ₂ * TensorProduct.map P₁ P₂ =
      TensorProduct.map (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) from by
        rw [← TensorProduct.map_mul, ← TensorProduct.map_mul],
    rpow_tensorProduct_direct (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) α
      (conjugate_nonneg_of_nonneg hρ₁ CFC.rpow_nonneg)
      (conjugate_nonneg_of_nonneg hρ₂ CFC.rpow_nonneg)]
  exact LinearMap.trace_tensorProduct'
    (CFC.rpow (P₁ * ρ₁ * P₁) α) (CFC.rpow (P₂ * ρ₂ * P₂) α)

/-- Tensor additivity of sandwichedRenyiDiv:
    D_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D_α(ρ₁ ‖ σ₁) + D_α(ρ₂ ‖ σ₂).

The real-valued version is defined for all PSD inputs, but for `α > 1` it agrees with the standard
finite-valued divergence only when `supp ρ ⊆ supp σ`.
For example, for `α = 2`, `ρ = I₂/2`, `σ = diag(1,0)` one has `Q = 1/4` and `D = log(1/4)`, but
since the support inclusion fails, the NN version `sandwichedRenyiDivNN` is `⊤`.

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem sandwichedRenyiDiv_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂)
    (hQ₁ : (sandwichedQuasi α ρ₁ σ₁).re ≠ 0)
    (hQ₂ : (sandwichedQuasi α ρ₂ σ₂).re ≠ 0)
    (hT₁ : (Tr ρ₁).re ≠ 0) (hT₂ : (Tr ρ₂).re ≠ 0) :
    sandwichedRenyiDiv α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedRenyiDiv α ρ₁ σ₁ + sandwichedRenyiDiv α ρ₂ σ₂ := by
  have hQ₁im : (sandwichedQuasi α ρ₁ σ₁).im = 0 :=
    (Complex.nonneg_iff.mp
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).trace_nonneg).2.symm
  have hQ₂im : (sandwichedQuasi α ρ₂ σ₂).im = 0 :=
    (Complex.nonneg_iff.mp
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).trace_nonneg).2.symm
  have hT₁im : (Tr ρ₁).im = 0 :=
    (Complex.nonneg_iff.mp ((LinearMap.nonneg_iff_isPositive ρ₁).mp hρ₁).trace_nonneg).2.symm
  have hT₂im : (Tr ρ₂).im = 0 :=
    (Complex.nonneg_iff.mp ((LinearMap.nonneg_iff_isPositive ρ₂).mp hρ₂).trace_nonneg).2.symm
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_tensor α ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂,
    LinearMap.trace_tensorProduct' ρ₁ ρ₂]
  have hre_mul_Q : (sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂).re =
      (sandwichedQuasi α ρ₁ σ₁).re * (sandwichedQuasi α ρ₂ σ₂).re := by
    simp [Complex.mul_re, hQ₁im, hQ₂im]
  have hre_mul_T : ((Tr ρ₁) * (Tr ρ₂)).re = (Tr ρ₁).re * (Tr ρ₂).re := by
    simp [Complex.mul_re, hT₁im, hT₂im]
  rw [hre_mul_Q, hre_mul_T, mul_div_mul_comm, Real.log_mul
    (div_ne_zero hQ₁ hT₁) (div_ne_zero hQ₂ hT₂), mul_add]

end TensorMultiplicativity

end SandwichedRenyiRelativeEntropy
