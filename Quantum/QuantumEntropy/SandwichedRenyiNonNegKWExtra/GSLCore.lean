import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity

namespace SandwichedRenyiRelativeEntropy
open QuantumState QuantumChannel
open scoped ComplexOrder Topology

universe u

private lemma sandwichedQuasi_re_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (α : ℝ) (ρ σ : L ℋ) :
    0 ≤ (sandwichedQuasi α ρ σ).re := by
  have hpos : (0 : L ℋ) ≤ CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α := CFC.rpow_nonneg
  have h := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  rw [Complex.le_def] at h
  rw [sandwichedQuasi_eq_direct]
  exact h.1

/-! ### Sign and support facts for the sandwiched quasi-entropy

Nonnegativity and reality of the sandwiched quasi-entropy, and its positivity under support
inclusion. -/

/-- The sandwiched quasi-entropy is real on positive operators. -/
theorem sandwichedQuasi_im_eq_zero_of_nonneg
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (_hrho : 0 ≤ rho) (_hsigma : 0 ≤ sigma) :
    (sandwichedQuasi alpha rho sigma).im = 0 := by
  have hpos : (0 : L ℋ) ≤ CFC.rpow
      (CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
        CFC.rpow sigma ((1 - alpha) / (2 * alpha))) alpha :=
    CFC.rpow_nonneg
  have htrace := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  rw [sandwichedQuasi_eq_direct]
  exact (Complex.nonneg_iff.mp htrace).2.symm

/-- On the finite support branch and for `alpha > 1`, a nonzero positive first
argument has strictly positive sandwiched quasi-entropy. -/
theorem sandwichedQuasi_re_pos_of_suppLE
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {alpha : ℝ} (halpha : 1 < alpha) {rho sigma : L ℋ}
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) (hrho0 : rho ≠ 0) :
    0 < (sandwichedQuasi alpha rho sigma).re :=
  lt_of_le_of_ne (sandwichedQuasi_re_nonneg alpha rho sigma)
    (Ne.symm (sandwichedQuasi_re_ne_zero_of_suppLE
      halpha hrho hsigma hsupp hrho0))

end SandwichedRenyiRelativeEntropy
