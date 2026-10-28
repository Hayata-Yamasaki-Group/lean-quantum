/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorBridge

/-! Real trace bounds for finite-dimensional positive operators. -/

namespace QuantumEntropy

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- Real trace of a continuous operator, transported through the linear model. -/
noncomputable def realTrace (a : B ℋ) : ℝ :=
  (Tr (a : L ℋ)).re

/-- The real trace agrees with the trace in the linear-operator model. -/
theorem realTrace_toCLM (X : L ℋ) :
    realTrace (X.toContinuousLinearMap) = (Tr X).re := by
  rfl

/-- For a non-zero non-negative operator, the real part of the trace is strictly positive. -/
lemma trace_re_pos_of_ne_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ : L ℋ} (hρ : 0 ≤ ρ) (hne : ρ ≠ 0) :
    0 < (Tr ρ).re := by
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hρ
  have hρ_sym := hρ_pos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  rw [show (Tr ρ).re = ∑ i, hρ_sym.eigenvalues hn i from
        hρ_sym.re_trace_eq_sum_eigenvalues hn]
  have h_eig_nn : ∀ i, 0 ≤ hρ_sym.eigenvalues hn i := fun i => hρ_pos.nonneg_eigenvalues hn i
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i _ => h_eig_nn i)) with hsum | hsum
  · exfalso
    apply hne
    have h_all : ∀ i, hρ_sym.eigenvalues hn i = 0 := by
      intro i
      have hle : hρ_sym.eigenvalues hn i ≤ ∑ j, hρ_sym.eigenvalues hn j :=
        Finset.single_le_sum (f := fun j => hρ_sym.eigenvalues hn j)
          (fun j _ => h_eig_nn j) (Finset.mem_univ i)
      linarith [h_eig_nn i, hsum, hle]
    have h_apply : ∀ i, ρ (hρ_sym.eigenvectorBasis hn i) = 0 := by
      intro i
      rw [hρ_sym.apply_eigenvectorBasis hn i, h_all i]; simp
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    conv_lhs => rw [← (hρ_sym.eigenvectorBasis hn).sum_repr x]
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => by rw [LinearMap.map_smul, h_apply i, smul_zero])
  · exact hsum

end

end QuantumEntropy
