/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

section MaximallyMixedPositiveDefinite

open MeasureTheory QuantumChannel TensorProduct GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u₅

/-- The maximally mixed state on a finite-dimensional Hilbert space is positive definite. -/
lemma maxmixed_pdSetLM (ℋ_env : Type u₅) [Qudit ℋ_env] [Nontrivial ℋ_env] :
    ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM (ℋ := ℋ_env) := by
  set d : ℕ := Module.finrank ℂ ℋ_env
  have hd_pos : 0 < d := Module.finrank_pos
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  set c : ℂ := (d : ℂ)⁻¹
  have hc_ne : c ≠ 0 := inv_ne_zero hd_ne
  -- `0 ≤ c` in `ℂ` (using `ComplexOrder`): `c.re ≥ 0` and `c.im = 0`.
  have hc_nn : (0 : ℂ) ≤ c := by
    refine ⟨?_, ?_⟩
    · change 0 ≤ ((d : ℂ)⁻¹).re
      rw [Complex.inv_re]
      have hd_re : ((d : ℂ)).re = (d : ℝ) := Complex.natCast_re d
      have hd_im : ((d : ℂ)).im = 0 := Complex.natCast_im d
      rw [hd_re,
          show Complex.normSq (d : ℂ) = (d : ℝ)^2 from by
            rw [Complex.normSq_apply, hd_re, hd_im]; ring]
      positivity
    · symm
      change ((d : ℂ)⁻¹).im = 0
      rw [Complex.inv_im]
      simp [Complex.natCast_im]
  -- `(c • 1).IsPositive` via `LinearMap.isPositive_one.smul_of_nonneg`.
  have h_isPos : ((c • (1 : L ℋ_env)) : L ℋ_env).IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hc_nn
  have h_nn : (0 : L ℋ_env) ≤ c • (1 : L ℋ_env) :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  -- `c • 1` is a unit (inverse is `c⁻¹ • 1`).
  have h_unit : IsUnit (c • (1 : L ℋ_env)) := by
    refine ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc_ne, mul_one, one_smul]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc_ne, mul_one, one_smul]
  apply (pdSetLM_strictPositivity_certificate _).2
  exact h_unit.isStrictlyPositive h_nn

end MaximallyMixedPositiveDefinite

end SandwichedRenyiRelativeEntropy
