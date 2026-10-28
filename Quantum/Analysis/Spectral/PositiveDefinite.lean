import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive-definite functions on the real line

This file introduces the function-valued notion of positive definiteness used in the
finite-dimensional side of Bochner's theorem.  The convention is chosen to agree with
`Matrix.PosSemidef`: for sample points `x`, the `(i,j)` entry is `C (x j - x i)`, so the
quadratic form is `\sum i, j, conj (c i) * C (x j - x i) * c j`.

Only the elementary, measure-free part of Bochner's theorem belongs here.
-/

namespace Quantum
namespace Analysis
namespace Spectral

open Filter Matrix
open scoped ComplexConjugate ComplexOrder Topology

/-- A complex-valued function on `ℝ` is positive definite when all of its
translation-invariant finite kernel matrices are positive semidefinite.

The subtraction order is `x j - x i`.  Thus `Matrix.PosSemidef` tests the quadratic form
`\sum i, j, conj (c i) * C (x j - x i) * c j`, matching Mathlib's conjugate-linear-first
inner-product convention. -/
def IsPositiveDefinite (C : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ),
    (Matrix.of fun i j => C (x j - x i)).PosSemidef

namespace IsPositiveDefinite

variable {C D : ℝ → ℂ}

/-- The value at zero of a positive-definite function is nonnegative in the complex order. -/
theorem zero_nonneg (hC : IsPositiveDefinite C) : 0 ≤ C 0 := by
  let x : Fin 1 → ℝ := fun _ => 0
  simpa [x] using (hC 1 x).diag_nonneg (i := (0 : Fin 1))

/-- The real part of the value at zero is nonnegative. -/
theorem zero_re_nonneg (hC : IsPositiveDefinite C) : 0 ≤ (C 0).re :=
  (Complex.nonneg_iff.mp hC.zero_nonneg).1

/-- The imaginary part of the value at zero vanishes. -/
theorem zero_im_eq_zero (hC : IsPositiveDefinite C) : (C 0).im = 0 :=
  (Complex.nonneg_iff.mp hC.zero_nonneg).2.symm

/-- Positive-definite functions have Hermitian symmetry. -/
theorem neg_eq_conj (hC : IsPositiveDefinite C) (t : ℝ) :
    C (-t) = conj (C t) := by
  let x : Fin 2 → ℝ := ![0, t]
  have hherm := (hC 2 x).isHermitian.apply (1 : Fin 2) (0 : Fin 2)
  simpa [x] using hherm.symm

/-- The standard two-by-two minor estimate for a positive-definite function. -/
theorem norm_le_norm_zero (hC : IsPositiveDefinite C) (t : ℝ) :
    ‖C t‖ ≤ ‖C 0‖ := by
  let x : Fin 2 → ℝ := ![0, t]
  have hdet : 0 ≤ (Matrix.of fun i j => C (x j - x i)).det :=
    (hC 2 x).det_nonneg
  have hre := (Complex.nonneg_iff.mp hdet).1
  have hzeroRe : (C 0).re = ‖C 0‖ :=
    Complex.re_eq_norm.mpr hC.zero_nonneg
  have hzeroIm : (C 0).im = 0 := hC.zero_im_eq_zero
  have hneg : C (-t) = conj (C t) := hC.neg_eq_conj t
  have hsq : ‖C t‖ ^ 2 ≤ ‖C 0‖ ^ 2 := by
    rw [Matrix.det_fin_two] at hre
    simp only [Matrix.of_apply] at hre
    simp only [Fin.isValue, cons_val_zero, sub_self, cons_val_one, cons_val_fin_one,
      sub_zero, zero_sub, hneg, Complex.sub_re, Complex.mul_re, hzeroRe, hzeroIm,
      mul_zero, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add,
      sub_nonneg, x] at hre
    have hnormSq : Complex.normSq (C t) ≤ ‖C 0‖ * ‖C 0‖ := by
      simpa [Complex.normSq_apply] using hre
    simpa [Complex.normSq_eq_norm_sq, pow_two] using hnormSq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The zero function is positive definite. -/
protected theorem zero : IsPositiveDefinite (0 : ℝ → ℂ) := by
  intro n x
  simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)

/-- Pointwise sums preserve positive definiteness. -/
protected theorem add (hC : IsPositiveDefinite C) (hD : IsPositiveDefinite D) :
    IsPositiveDefinite (C + D) := by
  intro n x
  simpa [Pi.add_apply] using (hC n x).add (hD n x)

/-- Multiplication by a nonnegative real scalar preserves positive definiteness. -/
protected theorem smul (hC : IsPositiveDefinite C) {a : ℝ} (ha : 0 ≤ a) :
    IsPositiveDefinite (a • C) := by
  intro n x
  have ha' : 0 ≤ (a : ℂ) := Complex.zero_le_real.mpr ha
  simpa [Pi.smul_apply, Complex.real_smul] using (hC n x).smul ha'

/-- Pointwise complex conjugation preserves positive definiteness. -/
protected theorem pointwise_conj (hC : IsPositiveDefinite C) :
    IsPositiveDefinite (fun t => conj (C t)) := by
  intro n x
  let y : Fin n → ℝ := fun i => -x i
  convert hC n y using 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← hC.neg_eq_conj]
  congr 1
  dsimp [y]
  ring

private theorem isClosed_nonnegative_complex :
    IsClosed {z : ℂ | 0 ≤ z} := by
  have hset : {z : ℂ | 0 ≤ z} =
      Complex.re ⁻¹' Set.Ici 0 ∩ Complex.im ⁻¹' {0} := by
    ext z
    simp [Complex.nonneg_iff, eq_comm]
  rw [hset]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

/-- Pointwise limits along a nontrivial filter preserve positive definiteness. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ k, IsPositiveDefinite (F k))
    (hlim : ∀ t, Tendsto (fun k => F k t) l (𝓝 (f t))) :
    IsPositiveDefinite f := by
  intro n x
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · apply Matrix.IsHermitian.ext
    intro i j
    have hstar : Tendsto (fun k => star (F k (x i - x j))) l
        (𝓝 (star (f (x i - x j)))) :=
      (continuous_star.tendsto _).comp (hlim (x i - x j))
    have hright : Tendsto (fun k => F k (x j - x i)) l
        (𝓝 (f (x j - x i))) := hlim (x j - x i)
    have heq : (fun k => star (F k (x i - x j))) =
        fun k => F k (x j - x i) := by
      funext k
      exact (hF k n x).isHermitian.apply i j
    exact tendsto_nhds_unique hstar (heq ▸ hright)
  · intro c
    let q : ι → ℂ := fun k =>
      star c ⬝ᵥ ((Matrix.of fun i j => F k (x j - x i)) *ᵥ c)
    let qlim : ℂ :=
      star c ⬝ᵥ ((Matrix.of fun i j => f (x j - x i)) *ᵥ c)
    have hq : Tendsto q l (𝓝 qlim) := by
      dsimp [q, qlim]
      simp only [dotProduct, mulVec, Matrix.of_apply]
      refine tendsto_finset_sum Finset.univ fun i _ => ?_
      refine (tendsto_const_nhds.mul ?_)
      refine tendsto_finset_sum Finset.univ fun j _ => ?_
      exact (hlim (x j - x i)).mul tendsto_const_nhds
    apply isClosed_nonnegative_complex.mem_of_tendsto hq
    exact Filter.Eventually.of_forall fun k =>
      (hF k n x).dotProduct_mulVec_nonneg c

end IsPositiveDefinite

end Spectral
end Analysis
end Quantum
