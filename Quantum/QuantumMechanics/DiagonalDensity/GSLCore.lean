/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.OuterProduct.GSLCore
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.Channel.ChoiKraus
import Quantum.QuantumMechanics.QuantumState

/-!
# Finite PMFs as diagonal density operators

The diagonal embedding of probability vectors as density operators.
-/

open scoped ComplexOrder ENNReal

namespace PMF

open QuantumState QuantumChannel

universe u

/-- The density operator whose diagonal in `b` is the finite PMF `p`. -/
noncomputable def diagonalDensity
    {H : Type u} [Qudit H] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (p : PMF ι) : L H :=
  ∑ i, (((p i).toReal : ℝ) : ℂ) • outer_product (b i) (b i)

/-- The diagonal embedding has the prescribed eigenvalue on every basis
vector. -/
@[simp]
theorem diagonalDensity_apply
    {H : Type u} [Qudit H] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (p : PMF ι) (i : ι) :
    diagonalDensity b p (b i) =
      (((p i).toReal : ℝ) : ℂ) • b i := by
  classical
  unfold diagonalDensity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    outer_product_eq_rankOne]
  rw [Finset.sum_eq_single i]
  · simp [InnerProductSpace.rankOne_apply, b.norm_eq_one]
  · intro j _ hji
    simp [InnerProductSpace.rankOne_apply, b.orthonormal.2 hji]
  · simp

/-- Every finite PMF embeds as a density operator. -/
theorem diagonalDensity_isDensity
    {H : Type u} [Qudit H] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (p : PMF ι) :
    IsDensity (diagonalDensity b p) := by
  classical
  constructor
  · unfold diagonalDensity
    apply LinearMap.isPositive_sum
    intro i _
    have houter : (outer_product (b i) (b i)).IsPositive :=
      (LinearMap.nonneg_iff_isPositive _).mp (outer_product_self_nonneg (b i))
    exact houter.smul_of_nonneg
      (Complex.zero_le_real.mpr ENNReal.toReal_nonneg)
  · unfold diagonalDensity
    simp only [map_sum, map_smul, trace_outer_product,
      inner_self_eq_one_of_norm_eq_one (b.norm_eq_one _), smul_eq_mul, mul_one]
    have hsum : ∑ i, p i = 1 := by
      simpa only [tsum_fintype] using p.tsum_coe
    have hsumReal : ∑ i, (p i).toReal = 1 := by
      rw [← ENNReal.toReal_sum]
      · rw [hsum]
        norm_num
      · intro i _
        exact p.apply_ne_top i
    exact_mod_cast hsumReal

end PMF
