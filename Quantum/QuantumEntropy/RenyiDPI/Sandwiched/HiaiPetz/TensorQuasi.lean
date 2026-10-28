/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Tensor

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem c09_quasi_self_of_nonneg_isUnit
    {K : Type u} [Qudit K] {α : ℝ} (hα : α ≠ 0)
    {τ : L K} (hτ : 0 ≤ τ) (hτunit : IsUnit τ) :
    sandwichedQuasi α τ τ = Tr τ := by
  have hexp : (1 - α) / (2 * α) + 1 + (1 - α) / (2 * α) = 1 / α := by
    field_simp
    ring
  have hpow_one : CFC.rpow τ 1 = τ := CFC.rpow_one τ hτ
  have hpow_add (x y : ℝ) :
      CFC.rpow τ (x + y) = CFC.rpow τ x * CFC.rpow τ y :=
    CFC.rpow_add hτunit
  have hmiddle :
      CFC.rpow τ ((1 - α) / (2 * α)) * τ * CFC.rpow τ ((1 - α) / (2 * α)) =
        CFC.rpow τ (1 / α) := by
    calc
      _ = CFC.rpow τ ((1 - α) / (2 * α)) * CFC.rpow τ 1 *
          CFC.rpow τ ((1 - α) / (2 * α)) := by rw [hpow_one]
      _ = CFC.rpow τ ((1 - α) / (2 * α) + 1 + (1 - α) / (2 * α)) := by
          rw [hpow_add, hpow_add]
      _ = CFC.rpow τ (1 / α) := by rw [hexp]
  have houter : CFC.rpow (CFC.rpow τ (1 / α)) α = τ := by
    calc
      _ = CFC.rpow τ ((1 / α) * α) :=
        CFC.rpow_rpow τ (1 / α) α hτunit (one_div_ne_zero hα) hτ
      _ = CFC.rpow τ 1 := by rw [one_div_mul_cancel hα]
      _ = τ := hpow_one
  exact (sandwichedQuasi_eq_direct α τ τ).trans
    (congrArg Tr ((congrArg (fun X : L K => CFC.rpow X α) hmiddle).trans houter))

theorem sandwichedQuasi_tensor_maxmixed_gt :
∀ {H K : Type u} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
  {α : ℝ} {ρ σ : L H}, 1 < α → 0 ≤ ρ → 0 ≤ σ →
  sandwichedQuasi α
    (TensorProduct.map ρ ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K)))
    (TensorProduct.map σ ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K))) =
      sandwichedQuasi α ρ σ := by
  intro H K _ _ _ _ α ρ σ hα hρ hσ
  have hd : (Module.finrank ℂ K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := K)).ne'
  have hτ : (0 : L K) ≤ (Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K) :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (LinearMap.isPositive_one.smul_of_nonneg (by positivity))
  have hτunit : IsUnit ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K)) := by
    refine ⟨⟨(Module.finrank ℂ K : ℂ)⁻¹ • 1,
      (Module.finrank ℂ K : ℂ) • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hd, mul_one, one_smul]
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hd, mul_one, one_smul]
  have htrace : Tr ((Module.finrank ℂ K : ℂ)⁻¹ • (1 : L K)) = 1 := by
    rw [map_smul, smul_eq_mul, LinearMap.trace_one, inv_mul_cancel₀ hd]
  have hHK : Nontrivial (H ⊗[ℂ] K) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  rw [@sandwichedQuasi_tensorMap H K _ _ _ _ hHK α ρ σ _ _ hρ hσ hτ hτ,
    c09_quasi_self_of_nonneg_isUnit (ne_of_gt (lt_trans zero_lt_one hα)) hτ hτunit,
    htrace, mul_one]

end RenyiDPI
