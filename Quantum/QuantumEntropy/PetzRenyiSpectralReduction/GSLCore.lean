/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiInterior.GSLCore
import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore

/-!
# Spectral reduction for the Petz quantum Rényi divergence

This file constructs the two finite probability distributions used internally
to reduce the punctured Petz quantum Rényi divergence to its classical
counterpart.  Only the endpoint bridge is developed here; the full statement
of Gour's Exercise 6.27 remains outside this file.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open scoped BigOperators ENNReal

universe u

private noncomputable def densityEigenbasis
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (hA : IsDensity A) :
    OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ :=
  hA.1.isSymmetric.eigenvectorBasis rfl

private noncomputable def densityEigenvalue
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (hA : IsDensity A) :
    Fin (Module.finrank ℂ ℋ) → ℝ :=
  hA.1.isSymmetric.eigenvalues rfl

private noncomputable def petzSpectralOverlap
    {ℋ : Type u} [Qudit ℋ] (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i j : Fin (Module.finrank ℂ ℋ)) : ℝ :=
  ‖inner ℂ (densityEigenbasis rho hrho i)
    (densityEigenbasis sigma hsigma j)‖ ^ 2

private theorem densityEigenvalue_nonneg
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ ℋ)) :
    0 ≤ densityEigenvalue A hA i :=
  hA.1.nonneg_eigenvalues rfl i

private theorem densityEigenvalue_sum
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (hA : IsDensity A) :
    ∑ i, densityEigenvalue A hA i = 1 := by
  have hsym := hA.1.isSymmetric
  rw [show (∑ i, densityEigenvalue A hA i) = (Tr A).re by
    simpa only [densityEigenvalue] using
      (hsym.re_trace_eq_sum_eigenvalues rfl).symm]
  rw [hA.2]
  norm_num

private theorem petzSpectralOverlap_sum_right
    {ℋ : Type u} [Qudit ℋ] (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i : Fin (Module.finrank ℂ ℋ)) :
    ∑ j, petzSpectralOverlap rho sigma hrho hsigma i j = 1 := by
  change (∑ j, ‖inner ℂ (densityEigenbasis rho hrho i)
    (densityEigenbasis sigma hsigma j)‖ ^ 2) = 1
  rw [(densityEigenbasis sigma hsigma).sum_sq_norm_inner_left]
  rw [(densityEigenbasis rho hrho).norm_eq_one]
  norm_num

private theorem petzSpectralOverlap_sum_left
    {ℋ : Type u} [Qudit ℋ] (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (j : Fin (Module.finrank ℂ ℋ)) :
    ∑ i, petzSpectralOverlap rho sigma hrho hsigma i j = 1 := by
  change (∑ i, ‖inner ℂ (densityEigenbasis rho hrho i)
    (densityEigenbasis sigma hsigma j)‖ ^ 2) = 1
  rw [(densityEigenbasis rho hrho).sum_sq_norm_inner_right]
  rw [(densityEigenbasis sigma hsigma).norm_eq_one]
  norm_num

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27:
internal construction of the finite distribution \(p^{XY}\) appearing in Eq. (6.103).

With eigenvalues \(r_i\) of \(\rho\), a corresponding eigenbasis \(a_i\), and an eigenbasis
\(b_j\) of \(\sigma\), define \(p^{XY}_{ij}=r_i|\langle a_i,b_j\rangle|^2\).

**Difference from the source.** The full divergence identity of Exercise 6.27 is not asserted;
only the construction of the finite probability distribution used for the endpoint limit is
extracted as an internal bridge.

**Finite-dimensional dependence.** The eigenbasis is indexed by `Fin (finrank ℂ ℋ)`, and the
normalization follows from the finite Parseval sum and trace 1.
-/
noncomputable def petzSpectralP
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    PMF (Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) := by
  let p : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → ℝ :=
    fun ij => densityEigenvalue rho hrho ij.1 *
      petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2
  refine PMF.ofFintype (fun ij => ENNReal.ofReal (p ij)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [show (∑ ij, p ij) = ∑ i, densityEigenvalue rho hrho i *
        ∑ j, petzSpectralOverlap rho sigma hrho hsigma i j by
      simp only [p, Fintype.sum_prod_type, Finset.mul_sum]]
    simp_rw [petzSpectralOverlap_sum_right rho sigma hrho hsigma]
    simpa using congrArg ENNReal.ofReal (densityEigenvalue_sum rho hrho)
  · intro ij _
    exact mul_nonneg (densityEigenvalue_nonneg rho hrho ij.1) (sq_nonneg _)

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27:
internal construction of the finite distribution \(q^{XY}\) appearing in Eq. (6.103).

With eigenvalues \(s_j\) of \(\sigma\), define
\(q^{XY}_{ij}=s_j|\langle a_i,b_j\rangle|^2\).

**Difference from the source.** Exercise 6.27 itself is not covered; only the finite probability
distribution referred to by the subsequent endpoint limit is defined.

**Finite-dimensional dependence.** The normalization uses the Parseval identity for the overlaps
between the two finite eigenbases and \(\operatorname{Tr}\sigma=1\).
-/
noncomputable def petzSpectralQ
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    PMF (Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) := by
  let q : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → ℝ :=
    fun ij => densityEigenvalue sigma hsigma ij.2 *
      petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2
  refine PMF.ofFintype (fun ij => ENNReal.ofReal (q ij)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [show (∑ ij, q ij) = ∑ j, densityEigenvalue sigma hsigma j *
        ∑ i, petzSpectralOverlap rho sigma hrho hsigma i j by
      simp only [q, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]]
    simp_rw [petzSpectralOverlap_sum_left rho sigma hrho hsigma]
    simpa using congrArg ENNReal.ofReal (densityEigenvalue_sum sigma hsigma)
  · intro ij _
    exact mul_nonneg (densityEigenvalue_nonneg sigma hsigma ij.2) (sq_nonneg _)

private theorem petzSpectralP_apply
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    petzSpectralP rho sigma hrho hsigma ij = ENNReal.ofReal
      (densityEigenvalue rho hrho ij.1 *
        petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) := by
  rw [petzSpectralP]
  rfl

private theorem petzSpectralQ_apply
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    petzSpectralQ rho sigma hrho hsigma ij = ENNReal.ofReal
      (densityEigenvalue sigma hsigma ij.2 *
        petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) := by
  rw [petzSpectralQ]
  rfl

private theorem petzSpectralP_ne_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    petzSpectralP rho sigma hrho hsigma ij ≠ 0 ↔
      densityEigenvalue rho hrho ij.1 ≠ 0 ∧
        inner ℂ (densityEigenbasis rho hrho ij.1)
          (densityEigenbasis sigma hsigma ij.2) ≠ 0 := by
  rw [petzSpectralP_apply, ne_eq, ENNReal.ofReal_eq_zero]
  have heig : 0 ≤ densityEigenvalue rho hrho ij.1 :=
    densityEigenvalue_nonneg rho hrho ij.1
  have hoverlap : 0 ≤ petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 :=
    sq_nonneg _
  rw [not_le, mul_pos_iff]
  simp only [not_lt_of_ge heig, not_lt_of_ge hoverlap, and_false,
    or_false]
  have heig_pos : 0 < densityEigenvalue rho hrho ij.1 ↔
      densityEigenvalue rho hrho ij.1 ≠ 0 :=
    ⟨ne_of_gt, fun h => lt_of_le_of_ne heig h.symm⟩
  rw [heig_pos]
  unfold petzSpectralOverlap
  rw [sq_pos_iff]
  constructor
  · rintro ⟨heig_ne, hnorm_ne⟩
    exact ⟨heig_ne, fun hinner => hnorm_ne (norm_eq_zero.mpr hinner)⟩
  · rintro ⟨heig_ne, hinner_ne⟩
    exact ⟨heig_ne, fun hnorm => hinner_ne (norm_eq_zero.mp hnorm)⟩

private theorem petzSpectralQ_ne_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    petzSpectralQ rho sigma hrho hsigma ij ≠ 0 ↔
      densityEigenvalue sigma hsigma ij.2 ≠ 0 ∧
        inner ℂ (densityEigenbasis rho hrho ij.1)
          (densityEigenbasis sigma hsigma ij.2) ≠ 0 := by
  rw [petzSpectralQ_apply, ne_eq, ENNReal.ofReal_eq_zero]
  have heig : 0 ≤ densityEigenvalue sigma hsigma ij.2 :=
    densityEigenvalue_nonneg sigma hsigma ij.2
  have hoverlap : 0 ≤ petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 :=
    sq_nonneg _
  rw [not_le, mul_pos_iff]
  simp only [not_lt_of_ge heig, not_lt_of_ge hoverlap, and_false,
    or_false]
  have heig_pos : 0 < densityEigenvalue sigma hsigma ij.2 ↔
      densityEigenvalue sigma hsigma ij.2 ≠ 0 :=
    ⟨ne_of_gt, fun h => lt_of_le_of_ne heig h.symm⟩
  rw [heig_pos]
  unfold petzSpectralOverlap
  rw [sq_pos_iff]
  constructor
  · rintro ⟨heig_ne, hnorm_ne⟩
    exact ⟨heig_ne, fun hinner => hnorm_ne (norm_eq_zero.mpr hinner)⟩
  · rintro ⟨heig_ne, hinner_ne⟩
    exact ⟨heig_ne, fun hnorm => hinner_ne (norm_eq_zero.mp hnorm)⟩

private theorem density_apply_eigenbasis
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ ℋ)) :
    A (densityEigenbasis A hA i) =
      ((densityEigenvalue A hA i : ℝ) : ℂ) • densityEigenbasis A hA i := by
  simpa only [densityEigenbasis, densityEigenvalue] using
    hA.1.isSymmetric.apply_eigenvectorBasis rfl i

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27:
in the classicalization used in Eq. (6.103), the quantum support condition
\(\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma\) is equivalent to the support of
\(p^{XY}\) being contained in the support of \(q^{XY}\).

**Difference from the source.** The full divergence identity of Exercise 6.27 is not asserted;
only the internal equivalence transferring the \(\alpha>1\) branch of Definition 6.6 to finite
classical distributions is stated.

**Finite-dimensional dependence.** In both directions vectors are expanded in finite eigenbases.
In one direction \(\ker\sigma\subseteq\ker\rho\) is applied to eigenvectors; in the other, each
vector of \(\ker\sigma\) is expanded as a finite sum in the eigenbasis of \(\sigma\).

The proof first assumes the support inclusion. If \(p^{XY}_{ij}>0\), then \(r_i>0\) and
\(\langle a_i,b_j\rangle\ne0\). If \(s_j=0\), then
\(b_j\in\ker\sigma\subseteq\ker\rho\), but the self-adjointness of \(\rho\) and
\(\rho a_i=r_i a_i\) give
\(r_i\langle a_i,b_j\rangle=0\), a contradiction. Hence
\(q^{XY}_{ij}>0\).

Conversely, assume the classical support inclusion and expand \(x\in\ker\sigma\) in the \(b_j\).
For the components with \(s_j\ne0\), the coefficients vanish because \(\sigma x=0\).
For the components with \(s_j=0\), for each \(a_i\) one uses the eigenvalue equation if
\(r_i=0\), and the classical support inclusion if \(r_i\ne0\), to obtain
\(\langle a_i,\rho b_j\rangle=0\). By completeness of the eigenbasis,
\(\rho b_j=0\), and therefore \(\rho x=0\) for the whole finite sum.
-/
theorem petzSpectral_support_subset_iff_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (petzSpectralP rho sigma hrho hsigma).support ⊆
        (petzSpectralQ rho sigma hrho hsigma).support ↔
      suppLE rho sigma := by
  classical
  let brho := densityEigenbasis rho hrho
  let bsigma := densityEigenbasis sigma hsigma
  constructor
  · intro hsupport x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show x = ∑ j, inner ℂ (bsigma j) x • bsigma j from
      (bsigma.sum_repr' x).symm, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [LinearMap.map_smul]
    by_cases hesigma : densityEigenvalue sigma hsigma j = 0
    · have hrho_bsigma : rho (bsigma j) = 0 := by
        rw [show rho (bsigma j) = ∑ i, inner ℂ (brho i) (rho (bsigma j)) • brho i
          from (brho.sum_repr' (rho (bsigma j))).symm]
        apply Finset.sum_eq_zero
        intro i _
        have hcoeff : inner ℂ (brho i) (rho (bsigma j)) = 0 := by
          by_cases herho : densityEigenvalue rho hrho i = 0
          · calc
              inner ℂ (brho i) (rho (bsigma j)) =
                  inner ℂ (rho (brho i)) (bsigma j) :=
                hrho.1.isSymmetric (brho i) (bsigma j) |>.symm
              _ = 0 := by rw [density_apply_eigenbasis, herho]; simp
          · have hoverlap : inner ℂ (brho i) (bsigma j) = 0 := by
              by_contra hoverlap_ne
              have hp : (i, j) ∈
                  (petzSpectralP rho sigma hrho hsigma).support :=
                (PMF.mem_support_iff _ _).2
                  ((petzSpectralP_ne_zero_iff rho sigma hrho hsigma (i, j)).2
                    ⟨herho, hoverlap_ne⟩)
              have hq := (PMF.mem_support_iff _ _).1 (hsupport hp)
              exact
                ((petzSpectralQ_ne_zero_iff rho sigma hrho hsigma (i, j)).1 hq).1
                  hesigma
            calc
              inner ℂ (brho i) (rho (bsigma j)) =
                  inner ℂ (rho (brho i)) (bsigma j) :=
                hrho.1.isSymmetric (brho i) (bsigma j) |>.symm
              _ = 0 := by
                rw [density_apply_eigenbasis, inner_smul_left,
                  Complex.conj_ofReal, hoverlap, mul_zero]
        rw [hcoeff, zero_smul]
      rw [hrho_bsigma, smul_zero]
    · have hcoeff : inner ℂ (bsigma j) x = 0 := by
        have hinner : inner ℂ (sigma (bsigma j)) x = 0 := by
          rw [hsigma.1.isSymmetric (bsigma j) x, hx, inner_zero_right]
        rw [density_apply_eigenbasis, inner_smul_left, Complex.conj_ofReal] at hinner
        exact (mul_eq_zero.mp hinner).resolve_left
          (Complex.ofReal_ne_zero.mpr hesigma)
      rw [hcoeff, zero_smul]
  · intro hsupp ij hp
    rw [PMF.mem_support_iff] at hp ⊢
    have hpdata :=
      (petzSpectralP_ne_zero_iff rho sigma hrho hsigma ij).1 hp
    apply (petzSpectralQ_ne_zero_iff rho sigma hrho hsigma ij).2
    refine ⟨?_, hpdata.2⟩
    intro hesigma
    have hker : densityEigenbasis sigma hsigma ij.2 ∈ LinearMap.ker sigma := by
      rw [LinearMap.mem_ker, density_apply_eigenbasis, hesigma]
      simp
    have hrho_zero := hsupp hker
    rw [LinearMap.mem_ker] at hrho_zero
    have hinner : ((densityEigenvalue rho hrho ij.1 : ℝ) : ℂ) *
        inner ℂ (densityEigenbasis rho hrho ij.1)
          (densityEigenbasis sigma hsigma ij.2) = 0 := by
      calc
        ((densityEigenvalue rho hrho ij.1 : ℝ) : ℂ) *
            inner ℂ (densityEigenbasis rho hrho ij.1)
              (densityEigenbasis sigma hsigma ij.2) =
            inner ℂ (rho (densityEigenbasis rho hrho ij.1))
              (densityEigenbasis sigma hsigma ij.2) := by
          rw [density_apply_eigenbasis, inner_smul_left, Complex.conj_ofReal]
        _ = inner ℂ (densityEigenbasis rho hrho ij.1)
              (rho (densityEigenbasis sigma hsigma ij.2)) :=
          hrho.1.isSymmetric _ _
        _ = 0 := by rw [hrho_zero, inner_zero_right]
    exact hpdata.2 ((mul_eq_zero.mp hinner).resolve_left
      (Complex.ofReal_ne_zero.mpr hpdata.1))

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27:
in the finite classicalization of Eq. (6.103), \(\rho\sigma=0\) is equivalent to the supports of
\(p^{XY},q^{XY}\) being disjoint.

**Difference from the source.** The non-orthogonality condition \(\rho\sigma\ne0\) of the source
is not replaced by \(Q_\alpha\ne0\); it is transferred exactly to the existence of a common support
point of the classical distributions. The divergence identity of Eq. (6.103) is not part of the
statement of this lemma.

**Finite-dimensional dependence.** The vanishing of \(\rho\sigma\) is tested on all components with
respect to the two finite eigenbases, and the operator is reconstructed as a finite sum over an
eigenbasis.

First assume that the classical supports are disjoint. For each eigenvector \(b_j\) of \(\sigma\),
if \(s_j=0\) then immediately \(\rho\sigma b_j=0\).
If \(s_j\ne0\), expand \(\rho b_j\) in the \(a_i\). The components with \(r_i=0\)
vanish by the eigenvalue equation, and for the components with \(r_i\ne0\) the disjointness of the
supports gives \(\langle a_i,b_j\rangle=0\), so the coefficients vanish as well. Hence
\(\rho\sigma\) is 0 on each \(b_j\), and by completeness of the basis the whole operator is
0.

Conversely, let \(\rho\sigma=0\) and suppose that some \((i,j)\) lies in both supports.
Then \(r_i,s_j,\langle a_i,b_j\rangle\) are all nonzero. On the other hand, taking the
\(a_i\) component of \(\rho\sigma b_j=0\) and using the two eigenvalue equations and the
self-adjointness of \(\rho\), one obtains
\[
  s_j r_i\langle a_i,b_j\rangle=0 .
\]
This contradicts the nonvanishing of the three factors, so the two supports are disjoint.
-/
theorem petzSpectral_disjoint_iff_mul_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    Disjoint (petzSpectralP rho sigma hrho hsigma).support
        (petzSpectralQ rho sigma hrho hsigma).support ↔
      rho * sigma = 0 := by
  classical
  let brho := densityEigenbasis rho hrho
  let bsigma := densityEigenbasis sigma hsigma
  constructor
  · intro hdisjoint
    apply LinearMap.ext
    intro x
    rw [LinearMap.zero_apply]
    rw [show x = ∑ j, inner ℂ (bsigma j) x • bsigma j from
      (bsigma.sum_repr' x).symm, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [LinearMap.map_smul]
    have hmul_basis : (rho * sigma) (bsigma j) = 0 := by
      rw [Module.End.mul_apply, density_apply_eigenbasis, map_smul]
      by_cases hesigma : densityEigenvalue sigma hsigma j = 0
      · rw [hesigma]
        simp
      · have hrho_bsigma : rho (bsigma j) = 0 := by
          rw [show rho (bsigma j) =
            ∑ i, inner ℂ (brho i) (rho (bsigma j)) • brho i from
              (brho.sum_repr' (rho (bsigma j))).symm]
          apply Finset.sum_eq_zero
          intro i _
          have hcoeff : inner ℂ (brho i) (rho (bsigma j)) = 0 := by
            by_cases herho : densityEigenvalue rho hrho i = 0
            · calc
                inner ℂ (brho i) (rho (bsigma j)) =
                    inner ℂ (rho (brho i)) (bsigma j) :=
                  hrho.1.isSymmetric (brho i) (bsigma j) |>.symm
                _ = 0 := by rw [density_apply_eigenbasis, herho]; simp
            · have hoverlap : inner ℂ (brho i) (bsigma j) = 0 := by
                by_contra hoverlap_ne
                have hp : (i, j) ∈
                    (petzSpectralP rho sigma hrho hsigma).support :=
                  (PMF.mem_support_iff _ _).2
                    ((petzSpectralP_ne_zero_iff rho sigma hrho hsigma (i, j)).2
                      ⟨herho, hoverlap_ne⟩)
                have hq : (i, j) ∈
                    (petzSpectralQ rho sigma hrho hsigma).support :=
                  (PMF.mem_support_iff _ _).2
                    ((petzSpectralQ_ne_zero_iff rho sigma hrho hsigma (i, j)).2
                      ⟨hesigma, hoverlap_ne⟩)
                exact (Set.disjoint_left.1 hdisjoint hp) hq
              calc
                inner ℂ (brho i) (rho (bsigma j)) =
                    inner ℂ (rho (brho i)) (bsigma j) :=
                  hrho.1.isSymmetric (brho i) (bsigma j) |>.symm
                _ = 0 := by
                  rw [density_apply_eigenbasis, inner_smul_left,
                    Complex.conj_ofReal, hoverlap, mul_zero]
          rw [hcoeff, zero_smul]
        rw [hrho_bsigma, smul_zero]
    rw [hmul_basis, smul_zero]
  · intro hmul
    apply Set.disjoint_left.2
    intro ij hp hq
    have hpdata :=
      (petzSpectralP_ne_zero_iff rho sigma hrho hsigma ij).1
        ((PMF.mem_support_iff _ _).1 hp)
    have hqdata :=
      (petzSpectralQ_ne_zero_iff rho sigma hrho hsigma ij).1
        ((PMF.mem_support_iff _ _).1 hq)
    have happ := LinearMap.congr_fun hmul (densityEigenbasis sigma hsigma ij.2)
    have hinner := congrArg
      (fun v => inner ℂ (densityEigenbasis rho hrho ij.1) v) happ
    change inner ℂ (densityEigenbasis rho hrho ij.1)
        ((rho * sigma) (densityEigenbasis sigma hsigma ij.2)) =
      inner ℂ (densityEigenbasis rho hrho ij.1)
        ((0 : L ℋ) (densityEigenbasis sigma hsigma ij.2)) at hinner
    rw [Module.End.mul_apply, density_apply_eigenbasis, map_smul,
      inner_smul_right] at hinner
    rw [show inner ℂ (densityEigenbasis rho hrho ij.1)
          (rho (densityEigenbasis sigma hsigma ij.2)) =
        inner ℂ (rho (densityEigenbasis rho hrho ij.1))
          (densityEigenbasis sigma hsigma ij.2) from
      (hrho.1.isSymmetric _ _).symm,
      density_apply_eigenbasis, inner_smul_left, Complex.conj_ofReal] at hinner
    simp only [LinearMap.zero_apply, inner_zero_right] at hinner
    have hleft : ((densityEigenvalue sigma hsigma ij.2 : ℝ) : ℂ) *
        ((densityEigenvalue rho hrho ij.1 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hqdata.1)
        (Complex.ofReal_ne_zero.mpr hpdata.1)
    rw [← mul_assoc] at hinner
    exact hpdata.2 ((mul_eq_zero.mp hinner).resolve_left hleft)

private theorem petzSupportTracePower_zero_eq_spectral_support_sum
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzSupportTracePower 0 rho sigma =
      ∑ ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        if densityEigenvalue rho hrho ij.1 = 0 then 0 else
          densityEigenvalue sigma hsigma ij.2 *
            petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
  classical
  let brho := densityEigenbasis rho hrho
  let bsigma := densityEigenbasis sigma hsigma
  let P : L ℋ := (LinearMap.range rho).starProjection.toLinearMap
  have hrho_symm : rho.IsSymmetric := hrho.1.isSymmetric
  have hP_apply (i : Fin (Module.finrank ℂ ℋ)) :
      P (brho i) = if densityEigenvalue rho hrho i = 0 then 0 else brho i := by
    by_cases hi : densityEigenvalue rho hrho i = 0
    · rw [if_pos hi]
      dsimp only [P]
      change (LinearMap.range rho).starProjection (brho i) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff,
        LinearMap.orthogonal_range, hrho_symm.adjoint_eq]
      rw [LinearMap.mem_ker, density_apply_eigenbasis, hi]
      simp
    · rw [if_neg hi]
      apply Submodule.starProjection_eq_self_iff.mpr
      refine ⟨(((densityEigenvalue rho hrho i : ℝ) : ℂ)⁻¹ • brho i), ?_⟩
      rw [map_smul, density_apply_eigenbasis, smul_smul]
      simp [hi, brho]
  have hsigma_rpow_one : CFC.rpow sigma 1 = sigma :=
    CFC.rpow_one sigma ((LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1)
  have hsigma_inner (i : Fin (Module.finrank ℂ ℋ)) :
      inner ℂ (brho i) (sigma (brho i)) =
        ∑ j, (((densityEigenvalue sigma hsigma j *
          petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ)) := by
    calc
      inner ℂ (brho i) (sigma (brho i)) =
          inner ℂ (brho i)
            (sigma (∑ j, inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [bsigma.sum_repr']
      _ = ∑ j, inner ℂ (brho i)
          (sigma (inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [map_sum, inner_sum]
      _ = ∑ j, (((densityEigenvalue sigma hsigma j *
          petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, density_apply_eigenbasis, smul_smul, inner_smul_right]
        rw [show inner ℂ (bsigma j) (brho i) =
            starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) from
          (inner_conj_symm (bsigma j) (brho i)).symm]
        change starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) *
            ((densityEigenvalue sigma hsigma j : ℝ) : ℂ) *
              inner ℂ (brho i) (bsigma j) =
          ((densityEigenvalue sigma hsigma j *
            ‖inner ℂ (brho i) (bsigma j)‖ ^ 2 : ℝ) : ℂ)
        rw [← Complex.normSq_eq_norm_sq, Complex.ofReal_mul,
          Complex.normSq_eq_conj_mul_self]
        ring
  unfold petzSupportTracePower
  rw [petzSupportRpow_zero, show 1 - (0 : ℝ) = 1 by norm_num,
    petzSupportRpow_of_ne_zero sigma one_ne_zero, hsigma_rpow_one]
  rw [show Tr (P * sigma) =
      ∑ i, inner ℂ (brho i) ((P * sigma) (brho i)) by
    simpa only [P] using
      LinearMap.trace_eq_sum_inner (T := P * sigma) brho]
  rw [Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply]
  rw [show inner ℂ (brho i) (P (sigma (brho i))) =
      inner ℂ (P (brho i)) (sigma (brho i)) from
    (Submodule.isSymmetricProjection_starProjection
      (LinearMap.range rho)).isSymmetric (brho i) (sigma (brho i)) |>.symm]
  rw [hP_apply]
  by_cases hi : densityEigenvalue rho hrho i = 0
  · simp [hi]
  · rw [if_neg hi, hsigma_inner, Complex.re_sum]
    simp only [Complex.ofReal_re, hi, if_false]

/-- The order-zero spectral support overlap is the trace of the support
projection of the first density against the second density. -/
theorem classicalSupportOverlapPMF_petzSpectral_toReal_eq
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (classicalSupportOverlapPMF
      (petzSpectralP rho sigma hrho hsigma)
      (petzSpectralQ rho sigma hrho hsigma)).toReal =
        petzSupportTracePower 0 rho sigma := by
  classical
  rw [petzSupportTracePower_zero_eq_spectral_support_sum
    rho sigma hrho hsigma]
  unfold classicalSupportOverlapPMF
  rw [ENNReal.toReal_sum (fun a _ => by
    split_ifs
    · exact (petzSpectralQ rho sigma hrho hsigma).apply_ne_top a
    · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro ij _
  rw [PMF.mem_support_iff]
  by_cases hp : petzSpectralP rho sigma hrho hsigma ij = 0
  · rw [if_neg (not_not.mpr hp)]
    simp
    by_cases heig : densityEigenvalue rho hrho ij.1 = 0
    · simp [heig]
    · have hoverlap : inner ℂ (densityEigenbasis rho hrho ij.1)
          (densityEigenbasis sigma hsigma ij.2) = 0 := by
        by_contra hinner
        exact ((petzSpectralP_ne_zero_iff rho sigma hrho hsigma ij).2
          ⟨heig, hinner⟩) hp
      simp [heig, petzSpectralOverlap, hoverlap]
  · rw [if_pos hp]
    rw [petzSpectralQ_apply]
    rw [ENNReal.toReal_ofReal]
    · have hpdata :=
        (petzSpectralP_ne_zero_iff rho sigma hrho hsigma ij).1 hp
      simp [hpdata.1]
    · exact mul_nonneg (densityEigenvalue_nonneg sigma hsigma ij.2)
        (sq_nonneg _)

private theorem rpow_eq_cfc_density
    {ℋ : Type u} [Qudit ℋ] {A : L ℋ} (hA : IsDensity A) (p : ℝ) :
    CFC.rpow A p = cfc (fun x : ℝ => x ^ p) A := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real
    ((LinearMap.nonneg_iff_isPositive A).mpr hA.1)

private theorem rpow_apply_density_eigenbasis
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (A : L ℋ) (hA : IsDensity A) (p : ℝ)
    (i : Fin (Module.finrank ℂ ℋ)) :
    CFC.rpow A p (densityEigenbasis A hA i) =
      (((densityEigenvalue A hA i) ^ p : ℝ) : ℂ) •
        densityEigenbasis A hA i := by
  rw [rpow_eq_cfc_density hA p]
  exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg
      ((LinearMap.nonneg_iff_isPositive A).mpr hA.1))
    (fun x : ℝ => x ^ p) (density_apply_eigenbasis A hA i)
    (mem_spectrum_real_of_eigenvector_lm
      ((densityEigenbasis A hA).orthonormal.ne_zero i)
      (density_apply_eigenbasis A hA i))

private theorem petzTracePower_eq_spectral_sum
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzTracePower alpha rho sigma hrho hsigma =
      ∑ ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (densityEigenvalue rho hrho ij.1) ^ (alpha : ℝ) *
          (densityEigenvalue sigma hsigma ij.2) ^ (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
  classical
  let brho := densityEigenbasis rho hrho
  let bsigma := densityEigenbasis sigma hsigma
  let X : L ℋ := CFC.rpow rho (alpha : ℝ)
  let Y : L ℋ := CFC.rpow sigma (1 - (alpha : ℝ))
  have hXsym : X.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive X).mp CFC.rpow_nonneg).isSymmetric
  have hYinner (i : Fin (Module.finrank ℂ ℋ)) :
      inner ℂ (brho i) (Y (brho i)) =
        ∑ j, (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ) := by
    calc
      inner ℂ (brho i) (Y (brho i)) =
          inner ℂ (brho i)
            (Y (∑ j, inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [bsigma.sum_repr']
      _ = ∑ j, inner ℂ (brho i)
          (Y (inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [map_sum, inner_sum]
      _ = ∑ j, (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, show Y (bsigma j) =
            (((densityEigenvalue sigma hsigma j) ^ (1 - (alpha : ℝ)) : ℝ) : ℂ) •
              bsigma j by
          exact rpow_apply_density_eigenbasis sigma hsigma _ j,
          smul_smul, inner_smul_right]
        rw [show inner ℂ (bsigma j) (brho i) =
            starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) from
          (inner_conj_symm (bsigma j) (brho i)).symm]
        change starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) *
            (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) : ℝ) : ℂ) *
              inner ℂ (brho i) (bsigma j) =
          (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            ‖inner ℂ (brho i) (bsigma j)‖ ^ 2 : ℝ) : ℂ)
        rw [← Complex.normSq_eq_norm_sq,
          Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        ring
  unfold petzTracePower
  rw [show Tr (CFC.rpow rho (alpha : ℝ) *
        CFC.rpow sigma (1 - (alpha : ℝ))) =
      ∑ i, inner ℂ (brho i) ((X * Y) (brho i)) by
    simpa only [X, Y] using
      LinearMap.trace_eq_sum_inner
        (T := CFC.rpow rho (alpha : ℝ) *
          CFC.rpow sigma (1 - (alpha : ℝ))) brho]
  rw [Complex.re_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply]
  rw [show inner ℂ (brho i) (X (Y (brho i))) =
      inner ℂ (X (brho i)) (Y (brho i)) from
    (hXsym (brho i) (Y (brho i))).symm]
  rw [show X (brho i) =
      (((densityEigenvalue rho hrho i) ^ (alpha : ℝ) : ℝ) : ℂ) • brho i by
    exact rpow_apply_density_eigenbasis rho hrho _ i,
    inner_smul_left, Complex.conj_ofReal, hYinner]
  rw [Finset.mul_sum, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27 and
Eq. (6.103): the power-sum computation is used internally for the endpoint limit of
Definition 6.6.

On the admissible branch \(0<\alpha\le2\), \(\alpha\ne1\), the real value of the Rényi power sum
of the finite distributions \(p^{XY},q^{XY}\) equals the Petz trace power:
\[
 \left(\sum_{i,j}(p^{XY}_{ij})^\alpha
   (q^{XY}_{ij})^{1-\alpha}\right)_{\mathbb R}
 =\operatorname{Re}\operatorname{Tr}
   [\rho^\alpha\sigma^{1-\alpha}].
\]

**Difference from the source.** The full divergence identity of Eq. (6.103) is not asserted;
only the identification of the power sums on the admissible branch without the endpoints is used
as a bridge. For \(\alpha>1\), the classical support inclusion, equivalent to the quantum support
inclusion, is used first to check that the components with negative powers are not \(+\infty\).

**Finite-dimensional dependence.** The trace is expanded in the finite eigenbasis of \(\rho\), and
each diagonal entry is further expanded in the finite eigenbasis of \(\sigma\). Finiteness of the
sum is also used when the extended nonnegative real power sum is transferred to the reals.

The proof applies the eigenvector formula for CFC real powers to the two eigenbases.
Writing the trace as a diagonal sum over the \(a_i\) and substituting the Parseval expansion in the
\(b_j\) gives
\[
 \operatorname{Re}\operatorname{Tr}[\rho^\alpha\sigma^{1-\alpha}]
 =\sum_{i,j}r_i^\alpha s_j^{1-\alpha}
   |\langle a_i,b_j\rangle|^2 .
\]
On the other hand, using \(p^{XY}_{ij}=r_iw_{ij}\),
\(q^{XY}_{ij}=s_jw_{ij}\) with \(w_{ij}=|\langle a_i,b_j\rangle|^2\), and applying the product
formula for real powers and
\(w_{ij}^\alpha w_{ij}^{1-\alpha}=w_{ij}\) to each component,
each term of the classical power sum agrees with the corresponding term of the double sum above.

For \(\alpha<1\) both exponents are nonnegative, so all components are finite.
For \(\alpha>1\) the admissibility condition gives the quantum support inclusion, hence the
classical support inclusion. Therefore \(p^{XY}_{ij}>0\) implies \(q^{XY}_{ij}>0\), and the powers
of \(q\) with negative exponent are also finite. Hence the finite sum of extended nonnegative reals
can be transferred to the reals.
-/
theorem petzSpectral_renyiPowerSum_toReal
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : (alpha : ℝ) ≠ 0) (halpha_one : (alpha : ℝ) ≠ 1)
    (hadmissible : suppLE rho sigma ∨
      ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0)) :
    (renyiPowerSum ⟨(alpha : ℝ),
        lt_of_le_of_ne alpha.property.1 halpha_zero.symm⟩
      (petzSpectralP rho sigma hrho hsigma)
      (petzSpectralQ rho sigma hrho hsigma)).toReal =
        petzTracePower alpha rho sigma hrho hsigma := by
  classical
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  have halpha_pos : 0 < (alpha : ℝ) :=
    lt_of_le_of_ne alpha.property.1 halpha_zero.symm
  have hterm_ne_top : ∀ ij,
      p ij ^ (alpha : ℝ) * q ij ^ (1 - (alpha : ℝ)) ≠ ⊤ := by
    intro ij
    by_cases halpha_lt : (alpha : ℝ) < 1
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg halpha_pos.le (p.apply_ne_top ij))
        (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr halpha_lt.le)
          (q.apply_ne_top ij))
    · have halpha_gt : 1 < (alpha : ℝ) :=
        lt_of_le_of_ne (le_of_not_gt halpha_lt) halpha_one.symm
      have hsupp : suppLE rho sigma := by
        rcases hadmissible with hsupp | hlt
        · exact hsupp
        · exact False.elim (halpha_lt hlt.1)
      have hpq : p.support ⊆ q.support :=
        (petzSpectral_support_subset_iff_suppLE rho sigma hrho hsigma).2 hsupp
      by_cases hpzero : p ij = 0
      · rw [hpzero, ENNReal.zero_rpow_of_pos halpha_pos, zero_mul]
        exact ENNReal.zero_ne_top
      · have hqzero : q ij ≠ 0 :=
          (q.mem_support_iff ij).1 (hpq ((p.mem_support_iff ij).2 hpzero))
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (zero_lt_one.trans halpha_gt).le
            (p.apply_ne_top ij))
          (ENNReal.rpow_ne_top_of_ne_zero hqzero (q.apply_ne_top ij))
  calc
    (renyiPowerSum ⟨(alpha : ℝ), halpha_pos⟩ p q).toReal =
        ∑ ij, (p ij ^ (alpha : ℝ) *
          q ij ^ (1 - (alpha : ℝ))).toReal := by
      rw [renyiPowerSum, ENNReal.toReal_sum]
      intro ij _
      exact hterm_ne_top ij
    _ = ∑ ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (densityEigenvalue rho hrho ij.1) ^ (alpha : ℝ) *
          (densityEigenvalue sigma hsigma ij.2) ^ (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ← ENNReal.toReal_rpow]
      rw [show (p ij).toReal = densityEigenvalue rho hrho ij.1 *
          petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 by
        rw [show p ij = ENNReal.ofReal
            (densityEigenvalue rho hrho ij.1 *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) by
          exact petzSpectralP_apply rho sigma hrho hsigma ij,
          ENNReal.toReal_ofReal]
        exact mul_nonneg (densityEigenvalue_nonneg rho hrho ij.1) (sq_nonneg _),
        show (q ij).toReal = densityEigenvalue sigma hsigma ij.2 *
          petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 by
        rw [show q ij = ENNReal.ofReal
            (densityEigenvalue sigma hsigma ij.2 *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) by
          exact petzSpectralQ_apply rho sigma hrho hsigma ij,
          ENNReal.toReal_ofReal]
        exact mul_nonneg (densityEigenvalue_nonneg sigma hsigma ij.2) (sq_nonneg _)]
      have hoverlap_nonneg :
          0 ≤ petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 :=
        sq_nonneg _
      rw [Real.mul_rpow (densityEigenvalue_nonneg rho hrho ij.1) hoverlap_nonneg,
        Real.mul_rpow (densityEigenvalue_nonneg sigma hsigma ij.2) hoverlap_nonneg]
      calc
        densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^ (alpha : ℝ) *
            (densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^
                (1 - (alpha : ℝ))) =
            densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
                (petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^ (alpha : ℝ) *
                  petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^
                    (1 - (alpha : ℝ))) := by ring
        _ = densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
                petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
          rw [← Real.rpow_add' hoverlap_nonneg (by norm_num :
            (alpha : ℝ) + (1 - (alpha : ℝ)) ≠ 0)]
          norm_num
    _ = petzTracePower alpha rho sigma hrho hsigma :=
      (petzTracePower_eq_spectral_sum alpha rho sigma hrho hsigma).symm

private theorem renyiPowerSum_le_one_of_lt_one
    (alpha : RenyiOrder) (halpha : (alpha : ℝ) < 1)
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    renyiPowerSum alpha p q ≤ 1 := by
  have hraw := classicalFDivSum_nonnegative
    (powerFDivGenerator alpha halpha.ne) p q
  have hc : ((((alpha : ℝ) - 1 : ℝ)) : EReal) ≤ 0 := by
    exact_mod_cast sub_nonpos.mpr halpha.le
  have hterm : ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
      classicalFDivSum (powerFDivGenerator alpha halpha.ne) p q ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc hraw
  have hcoe : (renyiPowerSum alpha p q : EReal) ≤
      ((1 : ℝ≥0∞) : EReal) := by
    rw [renyiPowerSum_eq_one_add_powerFDivSum_of_lt_one alpha halpha p q]
    calc
      1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          classicalFDivSum (powerFDivGenerator alpha halpha.ne) p q ≤
          1 + 0 := by
        simpa only [add_comm] using add_le_add_left hterm 1
      _ = ((1 : ℝ≥0∞) : EReal) := by simp
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hcoe

private theorem renyiLogQuotient_nonneg_of_ne_one
    (alpha : RenyiOrder) (halpha_one : (alpha : ℝ) ≠ 1)
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    0 ≤ renyiLogQuotient alpha p q := by
  rcases lt_or_gt_of_ne halpha_one with halpha | halpha
  · unfold renyiLogQuotient
    apply EReal.mul_nonneg_iff.mpr
    exact Or.inr ⟨EReal.inv_nonpos_of_nonpos (by
        exact_mod_cast sub_nonpos.mpr halpha.le),
      ENNReal.log_le_zero_iff.mpr
        (renyiPowerSum_le_one_of_lt_one alpha halpha p q)⟩
  · unfold renyiLogQuotient
    apply EReal.mul_nonneg
    · apply EReal.inv_nonneg_of_nonneg
      exact_mod_cast sub_nonneg.mpr halpha.le
    · exact ENNReal.zero_le_log_iff.mpr
        (one_le_renyiPowerSum_of_one_lt alpha halpha p q)

/--
**Correspondence with the source.** Gour, *Resources of the Quantum World*, Exercise 6.27 and
Eq. (6.103): a computation of the same form is used as an internal bridge for the endpoint
construction of Definition 6.6.

For \(\alpha\in(0,2]\setminus\{1\}\), the Petz quantum Rényi divergence without the endpoints
equals the classical Rényi divergence, in bits, of the finite distributions
\(p^{XY},q^{XY}\) built from the eigenbases:
\[
 D^{\mathrm P}_{\alpha,\circ}(\rho\Vert\sigma)
 =D^{(2),\mathrm{fin}}_\alpha(p^{XY}\Vert q^{XY}).
\]
The identity is preserved not only on the finite-value branch but also on the branch
\(\alpha<1\) with \(\rho\sigma=0\) and on the \(+\infty\) branch with \(\alpha>1\) where the support
inclusion fails.

**Difference from the source.** This declaration is an internal identification used for the
endpoint construction of Definition 6.6, and is not a declaration representing Exercise 6.27
itself. The values at the orders 0 and 1 themselves are not part of this theorem.

**Finite-dimensional dependence.** Finite eigenbases are used for the construction of the finite
probability distributions, for the equivalence between supports and orthogonality, and for the
representation of the trace power as a double sum over eigenvalues.

The proof splits into cases according to the quantum admissibility condition. On the admissible
branch, the strict positivity of the Petz trace power and the power-sum identification of the
previous lemma show that the classical power sum is neither 0 nor \(+\infty\). Hence its
extended-real logarithm is the finite real number
\[
 \log\sum_{i,j}(p^{XY}_{ij})^\alpha(q^{XY}_{ij})^{1-\alpha}
 =\log Q^{\mathrm P}_\alpha(\rho\Vert\sigma).
\]
The nonnegativity of the classical power \(f\)-divergence shows that the power sum is at most 1 for
\(\alpha<1\) and at least 1 for \(\alpha>1\), which gives the nonnegativity of the logarithmic
quotient. This removes the truncation by `toENNReal`, and after conversion to bits by
\(\log 2>0\) the value agrees with the Petz \(\log_2\) expression.

On the non-admissible branch, if \(\alpha<1\) then \(\rho\sigma=0\), and by the previous lemma the
two classical supports are disjoint. Hence the classical power sum is 0 and both sides are
\(+\infty\). If \(\alpha>1\), the quantum support inclusion fails, and by the support-inclusion
equivalence the classical side also has a support mismatch, so again both sides are \(+\infty\).
-/
theorem petzRenyiPunctured_eq_classicalSpectral
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : (alpha : ℝ) ≠ 0) (halpha_one : (alpha : ℝ) ≠ 1) :
    petzRenyiPunctured alpha rho sigma hrho hsigma
        halpha_zero halpha_one =
      ((classicalRenyiDivBitsFinitePMF
        ⟨(alpha : ℝ), lt_of_le_of_ne alpha.property.1 halpha_zero.symm⟩
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) := by
  classical
  let order : RenyiOrder :=
    ⟨(alpha : ℝ), lt_of_le_of_ne alpha.property.1 halpha_zero.symm⟩
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  let S := renyiPowerSum order p q
  let Q := petzTracePower alpha rho sigma hrho hsigma
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo_zero : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hlogTwo
  have hlogTwo_top : ENNReal.ofReal (Real.log 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  by_cases hadmissible : suppLE rho sigma ∨
      ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0)
  · have hQpos : 0 < Q :=
      (petzTracePower_real_and_pos_of_admissible alpha rho sigma hrho hsigma
        halpha_zero halpha_one hadmissible).2
    have hsumreal : S.toReal = Q := by
      exact petzSpectral_renyiPowerSum_toReal alpha rho sigma hrho hsigma
        halpha_zero halpha_one hadmissible
    have hsumzero : S ≠ 0 := by
      intro hzero
      rw [hzero] at hsumreal
      simp only [ENNReal.toReal_zero] at hsumreal
      exact hQpos.ne' hsumreal.symm
    have hlogQuotient : renyiLogQuotient order p q =
        ((((alpha : ℝ) - 1)⁻¹ * Real.log Q : ℝ) : EReal) := by
      unfold renyiLogQuotient
      rw [ENNReal.log_pos_real' (hsumreal ▸ hQpos), hsumreal]
      rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_inv,
        ← EReal.coe_mul]
    have hclassical : classicalRenyiDivPMF order p q =
        (renyiLogQuotient order p q).toENNReal := by
      by_cases halpha_lt : (alpha : ℝ) < 1
      · have hnot_gt : ¬1 < (alpha : ℝ) := not_lt_of_ge halpha_lt.le
        simp [classicalRenyiDivPMF, order, halpha_one, hnot_gt,
          halpha_lt, S, hsumzero]
      · have halpha_gt : 1 < (alpha : ℝ) :=
          lt_of_le_of_ne (le_of_not_gt halpha_lt) halpha_one.symm
        have hsupp : suppLE rho sigma := by
          rcases hadmissible with hsupp | hlt
          · exact hsupp
          · exact False.elim (halpha_lt hlt.1)
        have hpqsupp : p.support ⊆ q.support := by
          exact (petzSpectral_support_subset_iff_suppLE
            rho sigma hrho hsigma).2 hsupp
        have hnomismatch : ¬renyiSupportMismatch p q :=
          not_not.mpr hpqsupp
        simp [classicalRenyiDivPMF, order, halpha_one, halpha_gt,
          halpha_lt, hnomismatch]
    have hquotient_nonneg : 0 ≤ renyiLogQuotient order p q :=
      renyiLogQuotient_nonneg_of_ne_one order (by simpa [order] using halpha_one) p q
    have hquotient_top : renyiLogQuotient order p q ≠ ⊤ := by
      rw [hlogQuotient]
      exact EReal.coe_ne_top _
    have hnumerator_top :
        (renyiLogQuotient order p q).toENNReal ≠ ⊤ :=
      EReal.toENNReal_ne_top_iff.mpr hquotient_top
    have hbits_top : (renyiLogQuotient order p q).toENNReal /
        ENNReal.ofReal (Real.log 2) ≠ ⊤ :=
      ENNReal.div_ne_top hnumerator_top hlogTwo_zero
    have hpetz : petzRenyiPunctured alpha rho sigma hrho hsigma
        halpha_zero halpha_one =
          ((((alpha : ℝ) - 1)⁻¹ * Real.logb 2 Q : ℝ) : EReal) := by
      simp only [petzRenyiPunctured, dif_pos hadmissible]
      rfl
    rw [hpetz]
    rw [classicalRenyiDivBitsFinitePMF, hclassical]
    rw [← EReal.coe_ennreal_toReal hbits_top]
    norm_cast
    rw [ENNReal.toReal_div,
      EReal.toReal_toENNReal hquotient_nonneg, hlogQuotient,
      EReal.toReal_coe, ENNReal.toReal_ofReal hlogTwo.le]
    rw [Real.logb]
    ring
  · have hpetz : petzRenyiPunctured alpha rho sigma hrho hsigma
        halpha_zero halpha_one = ⊤ := by
      simp only [petzRenyiPunctured, dif_neg hadmissible]
    rw [hpetz]
    symm
    rw [EReal.coe_ennreal_eq_top_iff]
    by_cases halpha_lt : (alpha : ℝ) < 1
    · have hmul : rho * sigma = 0 := by
        by_contra hmul
        exact hadmissible (Or.inr ⟨halpha_lt, hmul⟩)
      have hdisjoint : Disjoint p.support q.support := by
        exact (petzSpectral_disjoint_iff_mul_eq_zero
          rho sigma hrho hsigma).2 hmul
      have hclassical : classicalRenyiDivPMF order p q = ⊤ :=
        classicalRenyiDivPMF_of_lt_one_of_disjoint_support
          order p q (by simpa [order] using halpha_lt) hdisjoint
      rw [classicalRenyiDivBitsFinitePMF, hclassical, ENNReal.top_div,
        if_neg hlogTwo_top]
    · have halpha_gt : 1 < (alpha : ℝ) :=
        lt_of_le_of_ne (le_of_not_gt halpha_lt) halpha_one.symm
      have hmismatch : renyiSupportMismatch p q := by
        intro hpqsupp
        apply hadmissible
        left
        exact (petzSpectral_support_subset_iff_suppLE
          rho sigma hrho hsigma).1 hpqsupp
      have hclassical : classicalRenyiDivPMF order p q = ⊤ :=
        classicalRenyiDivPMF_of_one_lt_of_supportMismatch
          order p q (by simpa [order] using halpha_gt) hmismatch
      rw [classicalRenyiDivBitsFinitePMF, hclassical, ENNReal.top_div,
        if_neg hlogTwo_top]

/-! ## Spectral reduction above order two -/

private theorem petzSupportTracePower_eq_spectral_sum_of_one_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ))
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzSupportTracePower alpha rho sigma =
      ∑ ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (densityEigenvalue rho hrho ij.1) ^ (alpha : ℝ) *
          (densityEigenvalue sigma hsigma ij.2) ^ (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
  classical
  let brho := densityEigenbasis rho hrho
  let bsigma := densityEigenbasis sigma hsigma
  let X : L ℋ := CFC.rpow rho (alpha : ℝ)
  let Y : L ℋ := CFC.rpow sigma (1 - (alpha : ℝ))
  have halpha_zero : (alpha : ℝ) ≠ 0 := ne_of_gt alpha.property
  have halpha_one : (alpha : ℝ) ≠ 1 := ne_of_gt halpha
  have hXsym : X.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive X).mp CFC.rpow_nonneg).isSymmetric
  have hYinner (i : Fin (Module.finrank ℂ ℋ)) :
      inner ℂ (brho i) (Y (brho i)) =
        ∑ j, (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ) := by
    calc
      inner ℂ (brho i) (Y (brho i)) =
          inner ℂ (brho i)
            (Y (∑ j, inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [bsigma.sum_repr']
      _ = ∑ j, inner ℂ (brho i)
          (Y (inner ℂ (bsigma j) (brho i) • bsigma j)) := by
        rw [map_sum, inner_sum]
      _ = ∑ j, (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, show Y (bsigma j) =
            (((densityEigenvalue sigma hsigma j) ^ (1 - (alpha : ℝ)) : ℝ) : ℂ) •
              bsigma j by
          exact rpow_apply_density_eigenbasis sigma hsigma _ j,
          smul_smul, inner_smul_right]
        rw [show inner ℂ (bsigma j) (brho i) =
            starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) from
          (inner_conj_symm (bsigma j) (brho i)).symm]
        change starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) *
            (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) : ℝ) : ℂ) *
              inner ℂ (brho i) (bsigma j) =
          (((densityEigenvalue sigma hsigma j) ^
              (1 - (alpha : ℝ)) *
            ‖inner ℂ (brho i) (bsigma j)‖ ^ 2 : ℝ) : ℂ)
        rw [← Complex.normSq_eq_norm_sq,
          Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        ring
  unfold petzSupportTracePower
  rw [petzSupportRpow_of_ne_zero rho halpha_zero,
    petzSupportRpow_of_ne_zero sigma (sub_ne_zero.mpr halpha_one.symm)]
  rw [show Tr (CFC.rpow rho (alpha : ℝ) *
        CFC.rpow sigma (1 - (alpha : ℝ))) =
      ∑ i, inner ℂ (brho i) ((X * Y) (brho i)) by
    simpa only [X, Y] using
      LinearMap.trace_eq_sum_inner
        (T := CFC.rpow rho (alpha : ℝ) *
          CFC.rpow sigma (1 - (alpha : ℝ))) brho]
  rw [Complex.re_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply]
  rw [show inner ℂ (brho i) (X (Y (brho i))) =
      inner ℂ (X (brho i)) (Y (brho i)) from
    (hXsym (brho i) (Y (brho i))).symm]
  rw [show X (brho i) =
      (((densityEigenvalue rho hrho i) ^ (alpha : ℝ) : ℝ) : ℂ) • brho i by
    exact rpow_apply_density_eigenbasis rho hrho _ i,
    inner_smul_left, Complex.conj_ofReal, hYinner]
  rw [Finset.mul_sum, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem petzSpectral_renyiPowerSum_toReal_of_one_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ))
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupp : suppLE rho sigma) :
    (renyiPowerSum alpha
      (petzSpectralP rho sigma hrho hsigma)
      (petzSpectralQ rho sigma hrho hsigma)).toReal =
        petzSupportTracePower alpha rho sigma := by
  classical
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  have hpq : p.support ⊆ q.support :=
    (petzSpectral_support_subset_iff_suppLE rho sigma hrho hsigma).2 hsupp
  have hterm_ne_top : ∀ ij,
      p ij ^ (alpha : ℝ) * q ij ^ (1 - (alpha : ℝ)) ≠ ⊤ := by
    intro ij
    by_cases hpzero : p ij = 0
    · rw [hpzero, ENNReal.zero_rpow_of_pos alpha.property, zero_mul]
      exact ENNReal.zero_ne_top
    · have hqzero : q ij ≠ 0 :=
        (q.mem_support_iff ij).1 (hpq ((p.mem_support_iff ij).2 hpzero))
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg alpha.property.le (p.apply_ne_top ij))
        (ENNReal.rpow_ne_top_of_ne_zero hqzero (q.apply_ne_top ij))
  calc
    (renyiPowerSum alpha p q).toReal =
        ∑ ij, (p ij ^ (alpha : ℝ) *
          q ij ^ (1 - (alpha : ℝ))).toReal := by
      rw [renyiPowerSum, ENNReal.toReal_sum]
      intro ij _
      exact hterm_ne_top ij
    _ = ∑ ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (densityEigenvalue rho hrho ij.1) ^ (alpha : ℝ) *
          (densityEigenvalue sigma hsigma ij.2) ^ (1 - (alpha : ℝ)) *
            petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ← ENNReal.toReal_rpow]
      rw [show (p ij).toReal = densityEigenvalue rho hrho ij.1 *
          petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 by
        rw [show p ij = ENNReal.ofReal
            (densityEigenvalue rho hrho ij.1 *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) by
          exact petzSpectralP_apply rho sigma hrho hsigma ij,
          ENNReal.toReal_ofReal]
        exact mul_nonneg (densityEigenvalue_nonneg rho hrho ij.1) (sq_nonneg _),
        show (q ij).toReal = densityEigenvalue sigma hsigma ij.2 *
          petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 by
        rw [show q ij = ENNReal.ofReal
            (densityEigenvalue sigma hsigma ij.2 *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) by
          exact petzSpectralQ_apply rho sigma hrho hsigma ij,
          ENNReal.toReal_ofReal]
        exact mul_nonneg (densityEigenvalue_nonneg sigma hsigma ij.2) (sq_nonneg _)]
      have hoverlap_nonneg :
          0 ≤ petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 :=
        sq_nonneg _
      rw [Real.mul_rpow (densityEigenvalue_nonneg rho hrho ij.1) hoverlap_nonneg,
        Real.mul_rpow (densityEigenvalue_nonneg sigma hsigma ij.2) hoverlap_nonneg]
      calc
        densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^ (alpha : ℝ) *
            (densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
              petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^
                (1 - (alpha : ℝ))) =
            densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
                (petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^ (alpha : ℝ) *
                  petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 ^
                    (1 - (alpha : ℝ))) := by ring
        _ = densityEigenvalue rho hrho ij.1 ^ (alpha : ℝ) *
              densityEigenvalue sigma hsigma ij.2 ^ (1 - (alpha : ℝ)) *
                petzSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 := by
          rw [← Real.rpow_add' hoverlap_nonneg (by norm_num :
            (alpha : ℝ) + (1 - (alpha : ℝ)) ≠ 0)]
          norm_num
    _ = petzSupportTracePower alpha rho sigma :=
      (petzSupportTracePower_eq_spectral_sum_of_one_lt
        alpha halpha rho sigma hrho hsigma).symm

/-- Above order one, the support-aware Petz logarithmic formula is the
finite classical Rényi divergence of its two spectral distributions. -/
theorem petzFiniteLogFormula_eq_classicalSpectral_of_one_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ))
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (@ite EReal (suppLE rho sigma) (Classical.propDecidable _)
        ((((alpha : ℝ) - 1)⁻¹ *
          Real.logb 2 (petzSupportTracePower alpha rho sigma) : ℝ) : EReal)
      ⊤) =
      ((classicalRenyiDivBitsFinitePMF alpha
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) := by
  classical
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  let S := renyiPowerSum alpha p q
  let Q := petzSupportTracePower alpha rho sigma
  have halpha_one : (alpha : ℝ) ≠ 1 := ne_of_gt halpha
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo_zero : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hlogTwo
  have hlogTwo_top : ENNReal.ofReal (Real.log 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  by_cases hsupp : suppLE rho sigma
  · rw [if_pos hsupp]
    have hQpos : 0 < Q :=
      petzSupportTracePower_pos_of_suppLE alpha rho sigma hrho hsigma hsupp
    have hsumreal : S.toReal = Q :=
      petzSpectral_renyiPowerSum_toReal_of_one_lt
        alpha halpha rho sigma hrho hsigma hsupp
    have hsumzero : S ≠ 0 := by
      intro hzero
      rw [hzero] at hsumreal
      simp only [ENNReal.toReal_zero] at hsumreal
      exact hQpos.ne' hsumreal.symm
    have hlogQuotient : renyiLogQuotient alpha p q =
        ((((alpha : ℝ) - 1)⁻¹ * Real.log Q : ℝ) : EReal) := by
      unfold renyiLogQuotient
      rw [ENNReal.log_pos_real' (hsumreal ▸ hQpos), hsumreal]
      rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_inv,
        ← EReal.coe_mul]
    have hpqsupp : p.support ⊆ q.support :=
      (petzSpectral_support_subset_iff_suppLE rho sigma hrho hsigma).2 hsupp
    have hnomismatch : ¬renyiSupportMismatch p q := not_not.mpr hpqsupp
    have hclassical : classicalRenyiDivPMF alpha p q =
        (renyiLogQuotient alpha p q).toENNReal := by
      have hnot_lt : ¬(alpha : ℝ) < 1 := not_lt_of_ge halpha.le
      simp [classicalRenyiDivPMF, halpha_one, halpha, hnot_lt, hnomismatch]
    have hquotient_nonneg : 0 ≤ renyiLogQuotient alpha p q :=
      renyiLogQuotient_nonneg_of_ne_one alpha halpha_one p q
    have hquotient_top : renyiLogQuotient alpha p q ≠ ⊤ := by
      rw [hlogQuotient]
      exact EReal.coe_ne_top _
    have hnumerator_top :
        (renyiLogQuotient alpha p q).toENNReal ≠ ⊤ :=
      EReal.toENNReal_ne_top_iff.mpr hquotient_top
    have hbits_top : (renyiLogQuotient alpha p q).toENNReal /
        ENNReal.ofReal (Real.log 2) ≠ ⊤ :=
      ENNReal.div_ne_top hnumerator_top hlogTwo_zero
    rw [classicalRenyiDivBitsFinitePMF, hclassical]
    rw [← EReal.coe_ennreal_toReal hbits_top]
    norm_cast
    rw [ENNReal.toReal_div,
      EReal.toReal_toENNReal hquotient_nonneg, hlogQuotient,
      EReal.toReal_coe, ENNReal.toReal_ofReal hlogTwo.le]
    rw [Real.logb]
    ring
  · rw [if_neg hsupp]
    symm
    rw [EReal.coe_ennreal_eq_top_iff]
    have hmismatch : renyiSupportMismatch p q := by
      intro hpqsupp
      exact hsupp ((petzSpectral_support_subset_iff_suppLE
        rho sigma hrho hsigma).1 hpqsupp)
    have hclassical : classicalRenyiDivPMF alpha p q = ⊤ :=
      classicalRenyiDivPMF_of_one_lt_of_supportMismatch
        alpha p q halpha hmismatch
    rw [classicalRenyiDivBitsFinitePMF, hclassical, ENNReal.top_div,
      if_neg hlogTwo_top]

end OPT
