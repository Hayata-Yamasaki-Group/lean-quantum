/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.Common.OperatorScalarTower

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section TraceConjPowConcavity
open LiebAndoTrace GeneralizedPerspectiveFunction
universe u''
variable {ℋ : Type u''} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
lemma nonneg_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : (0 : L ℋ) ≤ A := by
  exact ((pdSetLM_strictPositivity_certificate A).1 hA).nonneg

omit [Nontrivial ℋ] in
lemma isUnit_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : IsUnit A := by
  exact ((pdSetLM_strictPositivity_certificate A).1 hA).isUnit

end TraceConjPowConcavity

section Monotonicity
open MeasureTheory QuantumChannel TensorProduct GeneralizedPerspectiveFunction
universe u₅
variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

/-- For any positive-definite operator in `pdSetLM`, the trace is a real positive number.
    Proof: trace = sum of eigenvalues; each eigenvalue is ≥ 0 (from positivity) and ≠ 0
    (from invertibility), hence > 0. The sum over a nonempty index set of positives is positive. -/
lemma trace_re_pos_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    0 < (Tr A).re := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hA_nn
  have hA_sym := hA_pos.isSymmetric
  have hA_unit := isUnit_of_pdSetLM hA
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hn_pos : 0 < n := Module.finrank_pos
  -- Re (Tr A) = ∑ eigenvalues.
  rw [show (Tr A).re = ∑ i, hA_sym.eigenvalues hn i from
        hA_sym.re_trace_eq_sum_eigenvalues hn]
  -- Each eigenvalue is positive; the sum over a nonempty index set is positive.
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  apply Finset.sum_pos _ h_nonempty
  intro i _
  -- eigenvalues are ≥ 0 from `IsPositive.nonneg_eigenvalues`.
  have hlam_nn : 0 ≤ hA_sym.eigenvalues hn i := hA_pos.nonneg_eigenvalues hn i
  -- eigenvalues are ≠ 0 because `A` is a unit (so `0 ∉ spectrum`).
  rcases lt_or_eq_of_le hlam_nn with hpos | hzero
  · exact hpos
  · exfalso
    have h_eig : Module.End.HasEigenvalue A ((hA_sym.eigenvalues hn i : ℂ)) :=
      hA_sym.hasEigenvalue_eigenvalues hn i
    rw [← hzero] at h_eig
    push_cast at h_eig
    obtain ⟨v, hv_mem, hv_ne⟩ := h_eig.exists_hasEigenvector
    have hAv : A v = 0 := by
      rw [Module.End.mem_eigenspace_iff] at hv_mem
      simpa using hv_mem
    obtain ⟨uA, huA⟩ := hA_unit
    have h_inv_mul : (↑uA⁻¹ : L ℋ) * A = 1 := by rw [← huA, Units.inv_mul]
    have hv_eq : v = ((↑uA⁻¹ : L ℋ) * A) v := by rw [h_inv_mul]; rfl
    rw [show ((↑uA⁻¹ : L ℋ) * A) v = (↑uA⁻¹ : L ℋ) (A v) from rfl, hAv, map_zero]
      at hv_eq
    exact hv_ne hv_eq

end Monotonicity

end SandwichedRenyiRelativeEntropy
