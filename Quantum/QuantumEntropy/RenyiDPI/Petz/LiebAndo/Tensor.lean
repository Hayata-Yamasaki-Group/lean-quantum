/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Petz.Tensor

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem petzTracePower_tensor_maxmixed :
∀ {H K : Type u} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
  {α : ℝ} {ρ σ : L H}, α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ ρ → 0 ≤ σ →
  petzTracePower α
    (TensorProduct.map ρ ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K)))
    (TensorProduct.map σ ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K))) =
      petzTracePower α ρ σ := by
  intro H K _ _ _ _ α ρ σ hα hρ hσ
  let τ : L K := (Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K)
  have hd : (Module.finrank ℂ K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := K)).ne'
  have hτ : 0 ≤ τ := by
    exact (LinearMap.nonneg_iff_isPositive _).mpr
      (LinearMap.isPositive_one.smul_of_nonneg (by positivity))
  have hτUnit : IsUnit τ := by
    refine ⟨⟨τ, (Module.finrank ℂ K : ℂ) • (1 : L K), ?_, ?_⟩, rfl⟩
    · dsimp [τ]
      rw [smul_mul_smul_comm, inv_mul_cancel₀ hd, mul_one, one_smul]
    · dsimp [τ]
      rw [smul_mul_smul_comm, mul_inv_cancel₀ hd, mul_one, one_smul]
  have hτTrace : Tr τ = 1 := by
    dsimp [τ]
    rw [map_smul, smul_eq_mul, LinearMap.trace_one, inv_mul_cancel₀ hd]
  have hτPow : CFC.rpow τ α * CFC.rpow τ (1 - α) = τ := by
    calc
      _ = CFC.rpow τ (α + (1 - α)) := (CFC.rpow_add hτUnit).symm
      _ = τ := by
        rw [show α + (1 - α) = 1 by ring]
        exact CFC.rpow_one τ hτ
  have hτQ : petzTracePower α τ τ = 1 := by
    rw [petzTracePower_eq_trace_rpow_mul hα hτ hτ, hτPow, hτTrace,
      Complex.one_re]
  have hHK : Nontrivial (H ⊗[ℂ] K) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  change petzTracePower α (TensorProduct.map ρ τ) (TensorProduct.map σ τ) = _
  rw [@petzTracePower_tensorMap H K _ _ _ _ hHK α ρ σ τ τ hα hρ hσ hτ hτ,
    hτQ, mul_one]

end RenyiDPI
