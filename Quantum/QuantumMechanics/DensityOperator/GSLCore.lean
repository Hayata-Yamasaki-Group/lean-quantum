/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.OuterProduct.GSLCore
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.Channel.ChoiKraus
import Quantum.QuantumMechanics.Channel.Representations
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

/-!
# Density-operator identities

General properties of finite-dimensional density operators.
-/

open scoped ComplexOrder
open QuantumState QuantumChannel

namespace OPT

universe u

/-- Density matrices as a subtype of the finite-dimensional operator space. -/
abbrev QuantumDensityMatrix (H : Type u) [Qudit H] :=
  {rho : QuantumState.L H // QuantumState.IsDensity rho}

end OPT

namespace QuantumState.IsDensity

open QuantumChannel

universe u

/-- A density operator is nonzero. -/
theorem ne_zero
    {H : Type u} [Qudit H] {rho : L H} (hrho : IsDensity rho) :
    rho ≠ 0 := by
  intro hrhoZero
  have htraceZero : Tr rho = 0 := by
    rw [hrhoZero]
    exact map_zero Tr
  rw [hrho.2] at htraceZero
  exact one_ne_zero htraceZero

/-- Comparable density operators are equal. -/
theorem eq_of_le
    {H : Type u} [Qudit H] [Nontrivial H]
    {rho sigma : L H} (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (h : rho ≤ sigma) : rho = sigma := by
  have hdiff : 0 ≤ sigma - rho := sub_nonneg.mpr h
  obtain ⟨x, hx, _⟩ := positive_full_spectral_outer_product
    (sigma - rho) hdiff
  have htrace : Tr (sigma - rho) = 0 := by
    rw [map_sub, hsigma.2, hrho.2, sub_self]
  have hsum : ∑ i, inner ℂ (x i) (x i) = 0 := by
    rw [hx, map_sum] at htrace
    simpa only [trace_outer_product] using htrace
  have hnormSum : ∑ i, ‖x i‖ ^ 2 = 0 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [inner_self_eq_norm_sq_to_K] using hsum
  have hxzero : ∀ i, x i = 0 := by
    intro i
    have hi : ‖x i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖x j‖)).mp
        hnormSum i (Finset.mem_univ i)
    exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hi)
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  rw [hxzero i]
  ext z
  simp [QuantumChannel.outer_product_apply]

end QuantumState.IsDensity

namespace QuantumChannel.CPTP

universe u v

end QuantumChannel.CPTP
