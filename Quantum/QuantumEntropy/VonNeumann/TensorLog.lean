/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.Common.OperatorScalarTower

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

/-- An operator whose eigenbasis is known has its logarithm determined on that basis. -/
private lemma log_eq_of_eigenbasis {E : Type*} [Qudit E] {ι : Type*}
    (T S : E →L[ℂ] E) (hT : IsSelfAdjoint T) (b : Module.Basis ι ℂ E) (μ : ι → ℝ)
    (hTb : ∀ i, T (b i) = (μ i : ℂ) • b i)
    (hSb : ∀ i, S (b i) = ((Real.log (μ i) : ℝ) : ℂ) • b i) :
    CFC.log T = S := by
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun i => ?_
  haveI : Nontrivial E := ⟨⟨b i, 0, b.ne_zero i⟩⟩
  exact (cfc_real_apply_eigenvector hT Real.log (hTb i)
    (mem_spectrum_real_of_eigenvector (b.ne_zero i) (hTb i))).trans (hSb i).symm

/-- Eigenbasis data of a self-adjoint operator: eigenvalue equations, spectrum membership, and
the action of its logarithm on the eigenbasis. -/
private lemma log_eigenbasis_data {E : Type*} [Qudit E] [Nontrivial E] (T : E →L[ℂ] E)
    (hT : IsSelfAdjoint T) (hT_sym : (T : L E).IsSymmetric) (i : Fin (Module.finrank ℂ E)) :
    T ((hT_sym.eigenvectorBasis rfl).toBasis i) =
        ((hT_sym.eigenvalues rfl i : ℝ) : ℂ) • (hT_sym.eigenvectorBasis rfl).toBasis i ∧
      hT_sym.eigenvalues rfl i ∈ spectrum ℝ T ∧
      ((CFC.log T : E →L[ℂ] E) : L E) ((hT_sym.eigenvectorBasis rfl).toBasis i) =
        ((Real.log (hT_sym.eigenvalues rfl i) : ℝ) : ℂ) •
          (hT_sym.eigenvectorBasis rfl).toBasis i := by
  have heig : T ((hT_sym.eigenvectorBasis rfl).toBasis i) =
      ((hT_sym.eigenvalues rfl i : ℝ) : ℂ) • (hT_sym.eigenvectorBasis rfl).toBasis i := by
    rw [OrthonormalBasis.coe_toBasis]
    exact hT_sym.apply_eigenvectorBasis _ i
  have hspec := mem_spectrum_real_of_eigenvector
    ((hT_sym.eigenvectorBasis rfl).toBasis.ne_zero i) heig
  exact ⟨heig, hspec, cfc_real_apply_eigenvector hT Real.log heig hspec⟩

/-- A tensor product of operators acts diagonally on a tensor product of eigenbases. -/
private lemma log_map_toCLM_tensorBasis {ι κ : Type*} (A : L ℋ₁) (B : L ℋ₂)
    (b₁ : Module.Basis ι ℂ ℋ₁) (b₂ : Module.Basis κ ℂ ℋ₂) (a : ι → ℝ) (c : κ → ℝ)
    (μ : ι × κ → ℝ) (ha : ∀ i, A (b₁ i) = (a i : ℂ) • b₁ i)
    (hc : ∀ j, B (b₂ j) = (c j : ℂ) • b₂ j) (hμ : ∀ i j, a i * c j = μ (i, j))
    (ij : ι × κ) :
    (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
        ((b₁.tensorProduct b₂) ij) =
      (μ ij : ℂ) • (b₁.tensorProduct b₂) ij := by
  obtain ⟨i, j⟩ := ij
  change TensorProduct.map A B ((b₁.tensorProduct b₂) (i, j)) = _
  rw [Module.Basis.tensorProduct_apply, map_tmul, ha, hc, TensorProduct.smul_tmul_smul,
    ← Complex.ofReal_mul, hμ]

/-- `log A ⊗ 1 + 1 ⊗ log B` acts diagonally on a tensor product of eigenbases. -/
private lemma log_sum_toCLM_tensorBasis {ι κ : Type*} (A : L ℋ₁) (B : L ℋ₂)
    (b₁ : Module.Basis ι ℂ ℋ₁) (b₂ : Module.Basis κ ℂ ℋ₂) (a : ι → ℝ) (c : κ → ℝ)
    (μ : ι × κ → ℝ) (ha : ∀ i, A (b₁ i) = ((Real.log (a i) : ℝ) : ℂ) • b₁ i)
    (hc : ∀ j, B (b₂ j) = ((Real.log (c j) : ℝ) : ℂ) • b₂ j)
    (hμ : ∀ i j, Real.log (a i) + Real.log (c j) = Real.log (μ (i, j))) (ij : ι × κ) :
    ((TensorProduct.map A (1 : L ℋ₂) : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap +
        (TensorProduct.map (1 : L ℋ₁) B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap)
        ((b₁.tensorProduct b₂) ij) =
      ((Real.log (μ ij) : ℝ) : ℂ) • (b₁.tensorProduct b₂) ij := by
  obtain ⟨i, j⟩ := ij
  change TensorProduct.map A (1 : L ℋ₂) ((b₁.tensorProduct b₂) (i, j)) +
      TensorProduct.map (1 : L ℋ₁) B ((b₁.tensorProduct b₂) (i, j)) = _
  rw [Module.Basis.tensorProduct_apply, map_tmul, map_tmul, ha, hc, Module.End.one_apply,
    Module.End.one_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul,
    ← Complex.ofReal_add, hμ]

/-- The tensor product of self-adjoint operators is self-adjoint. -/
private lemma isSelfAdjoint_map_toCLM (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
      L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap := by
  have hA_sym : (A : L ℋ₁).IsSymmetric := hA.isSymmetric
  have hB_sym : (B : L ℋ₂).IsSymmetric := hB.isSymmetric
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
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by simpa using hAB_sym)

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
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨hB_sa, hB_spec⟩ := hB
  have hA_sym : (A : L ℋ₁).IsSymmetric := hA_sa.isSymmetric
  have hB_sym : (B : L ℋ₂).IsSymmetric := hB_sa.isSymmetric
  have hA_d := log_eigenbasis_data A hA_sa hA_sym
  have hB_d := log_eigenbasis_data B hB_sa hB_sym
  exact log_eq_of_eigenbasis _ _ (isSelfAdjoint_map_toCLM A B hA_sa hB_sa)
    ((hA_sym.eigenvectorBasis rfl).toBasis.tensorProduct (hB_sym.eigenvectorBasis rfl).toBasis)
    (fun ij => hA_sym.eigenvalues rfl ij.1 * hB_sym.eigenvalues rfl ij.2)
    (log_map_toCLM_tensorBasis _ _ _ _ _ _ _ (fun i => (hA_d i).1) (fun j => (hB_d j).1)
      fun _ _ => rfl)
    (log_sum_toCLM_tensorBasis _ _ _ _ _ _ _ (fun i => (hA_d i).2.2) (fun j => (hB_d j).2.2)
      fun i j => (Real.log_mul (hA_spec (hA_d i).2.1).ne' (hB_spec (hB_d j).2.1).ne').symm)

end TensorCFC
