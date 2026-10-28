/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiOrder.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumEntropy.Common.TraceRe

/-!
# Petz trace powers

This file defines the Petz trace functional and establishes the reality of its
complex trace and strict positivity on Gour's admissible branch.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

universe u

private lemma trace_star_sqrt_mul_self_eq_trace_mul
    {ℋ : Type u} [Qudit ℋ]
    {X Y : L ℋ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y)) = Tr (X * Y) := by
  have hsx_sa : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hsy_sa : IsSelfAdjoint (CFC.sqrt Y) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  calc
    Tr (star (CFC.sqrt X * CFC.sqrt Y) *
        (CFC.sqrt X * CFC.sqrt Y)) =
        Tr ((CFC.sqrt Y * CFC.sqrt X) *
          (CFC.sqrt X * CFC.sqrt Y)) := by
      rw [star_mul, hsx_sa.star_eq, hsy_sa.star_eq]
    _ = Tr (CFC.sqrt Y *
        ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
      simp only [mul_assoc]
    _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by
      rw [CFC.sqrt_mul_sqrt_self X hX]
    _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) :=
      LinearMap.trace_mul_comm ℂ (CFC.sqrt Y) (X * CFC.sqrt Y)
    _ = Tr (X * (CFC.sqrt Y * CFC.sqrt Y)) := by rw [mul_assoc]
    _ = Tr (X * Y) := by rw [CFC.sqrt_mul_sqrt_self Y hY]

private lemma spectrum_real_finite
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) :
    (spectrum ℝ A).Finite := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private lemma rpow_eq_cfc_singular
    {ℋ : Type u} [Qudit ℋ] {A : L ℋ}
    (hA : 0 ≤ A) (p : ℝ) :
    CFC.rpow A p = cfc (fun x : ℝ => x ^ p) A := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hA

private lemma rpow_rpow_inv_singular
    {ℋ : Type u} [Qudit ℋ] {A : L ℋ}
    (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow (CFC.rpow A p) p⁻¹ = A := by
  let f : ℝ → ℝ := fun x => x ^ p
  let g : ℝ → ℝ := fun x => x ^ p⁻¹
  have hspec : (spectrum ℝ A).Finite := spectrum_real_finite A
  have hf : ContinuousOn f (spectrum ℝ A) := hspec.continuousOn f
  have hg : ContinuousOn g (f '' spectrum ℝ A) :=
    (hspec.image f).continuousOn g
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [rpow_eq_cfc_singular (A := CFC.rpow A p) CFC.rpow_nonneg p⁻¹]
  rw [rpow_eq_cfc_singular (A := A) hA p]
  rw [← cfc_comp (p := IsSelfAdjoint) g f A hA_sa hg hf]
  calc
    cfc (g ∘ f) A = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      have hx_nonneg := spectrum_nonneg_of_nonneg hA hx
      change (x ^ p) ^ p⁻¹ = x
      rw [← Real.rpow_mul hx_nonneg, mul_inv_cancel₀ hp, Real.rpow_one]
    _ = A := cfc_id' ℝ A hA_sa

private lemma rpow_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p : ℝ) {v : ℋ} {mu : ℝ}
    (hv : A v = (mu : ℂ) • v) (hmu : mu ∈ spectrum ℝ A) :
    CFC.rpow A p v = ((mu ^ p : ℝ) : ℂ) • v := by
  rw [rpow_eq_cfc_singular hA p]
  exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hA)
    (fun x : ℝ => x ^ p) hv hmu

private lemma ker_rpow_eq_ker
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    LinearMap.ker (CFC.rpow A p) = LinearMap.ker A := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    by_cases hx_zero : x = 0
    · simp [hx_zero]
    have hspec : (0 : ℝ) ∈ spectrum ℝ (CFC.rpow A p) :=
      mem_spectrum_real_of_eigenvector_lm hx_zero (by simpa using hx)
    have happ := rpow_apply_eigenvector CFC.rpow_nonneg p⁻¹
      (show CFC.rpow A p x = ((0 : ℝ) : ℂ) • x by simpa using hx) hspec
    change (CFC.rpow (CFC.rpow A p) p⁻¹) x =
      (((0 : ℝ) ^ p⁻¹ : ℝ) : ℂ) • x at happ
    rw [rpow_rpow_inv_singular hA hp] at happ
    simpa [Real.zero_rpow (inv_ne_zero hp)] using happ
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    by_cases hx_zero : x = 0
    · simp [hx_zero]
    have hspec : (0 : ℝ) ∈ spectrum ℝ A :=
      mem_spectrum_real_of_eigenvector_lm hx_zero (by simpa using hx)
    have happ := rpow_apply_eigenvector hA p
      (show A x = ((0 : ℝ) : ℂ) • x by simpa using hx) hspec
    simpa [Real.zero_rpow hp] using happ

private lemma range_rpow_eq_range
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    LinearMap.range (CFC.rpow A p) = LinearMap.range A := by
  have hpow_symm : (CFC.rpow A p).IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).isSymmetric
  have hA_symm : A.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive _).mp hA).isSymmetric
  calc
    LinearMap.range (CFC.rpow A p) =
        (LinearMap.ker (CFC.rpow A p))ᗮ := by
      rw [LinearMap.orthogonal_ker, hpow_symm.adjoint_eq]
    _ = (LinearMap.ker A)ᗮ :=
      congrArg Submodule.orthogonal (ker_rpow_eq_ker hA hp)
    _ = LinearMap.range A := by
      rw [LinearMap.orthogonal_ker, hA_symm.adjoint_eq]

private lemma mul_eq_zero_of_rpow_mul_rpow_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpow : CFC.rpow A p * CFC.rpow B q = 0) :
    A * B = 0 := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.zero_apply]
  have hv_range : B v ∈ LinearMap.range B := ⟨v, rfl⟩
  rw [← range_rpow_eq_range hB hq] at hv_range
  obtain ⟨w, hw⟩ := hv_range
  have hker_pow : CFC.rpow A p (B v) = 0 := by
    have hw_zero := LinearMap.congr_fun hpow w
    change CFC.rpow A p (CFC.rpow B q w) = 0 at hw_zero
    rw [hw] at hw_zero
    exact hw_zero
  have hker : B v ∈ LinearMap.ker A := by
    rw [← ker_rpow_eq_ker hA hp, LinearMap.mem_ker]
    exact hker_pow
  exact hker

private lemma mul_ne_zero_of_isDensity_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupp : suppLE rho sigma) :
    rho * sigma ≠ 0 := by
  have hrho_nonneg : (0 : L ℋ) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L ℋ) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  have hrho_sa : IsSelfAdjoint rho := IsSelfAdjoint.of_nonneg hrho_nonneg
  have hsigma_sa : IsSelfAdjoint sigma := IsSelfAdjoint.of_nonneg hsigma_nonneg
  have hrho_ne : rho ≠ 0 := by
    intro hrho_zero
    have htrace := hrho.2
    rw [hrho_zero, map_zero] at htrace
    exact zero_ne_one htrace
  intro hmul
  have hrev : sigma * rho = 0 := by
    have hstar := congrArg star hmul
    simpa [star_mul, hrho_sa.star_eq, hsigma_sa.star_eq] using hstar
  have hsquare : rho * rho = 0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply]
    have hv_sigma : sigma (rho v) = 0 := by
      have hv := LinearMap.congr_fun hrev v
      simpa using hv
    have hv_ker_sigma : rho v ∈ LinearMap.ker sigma := hv_sigma
    exact hsupp hv_ker_sigma
  apply hrho_ne
  apply (CStarRing.star_mul_self_eq_zero_iff rho).mp
  simpa [hrho_sa.star_eq] using hsquare

private lemma trace_re_pos_of_mul_of_nonneg_of_ne_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {X Y : L ℋ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X * Y ≠ 0) :
    0 < (Tr (X * Y)).re := by
  let Z : L ℋ := CFC.sqrt X * CFC.sqrt Y
  have hZ_ne : Z ≠ 0 := by
    intro hZ
    apply hXY
    calc
      X * Y = (CFC.sqrt X * CFC.sqrt X) *
          (CFC.sqrt Y * CFC.sqrt Y) := by
        rw [CFC.sqrt_mul_sqrt_self X hX, CFC.sqrt_mul_sqrt_self Y hY]
      _ = CFC.sqrt X * (CFC.sqrt X * CFC.sqrt Y) * CFC.sqrt Y := by
        simp only [mul_assoc]
      _ = 0 := by rw [show CFC.sqrt X * CFC.sqrt Y = 0 from hZ]; simp
  have hstarZ_ne : star Z * Z ≠ 0 :=
    not_congr (CStarRing.star_mul_self_eq_zero_iff Z) |>.mpr hZ_ne
  have htrace_pos := QuantumEntropy.trace_re_pos_of_ne_zero
    (star_mul_self_nonneg Z) hstarZ_ne
  have htrace := trace_star_sqrt_mul_self_eq_trace_mul hX hY
  change Tr (star Z * Z) = Tr (X * Y) at htrace
  rwa [htrace] at htrace_pos

/-- The real-valued Petz trace functional. -/
noncomputable def petzTracePower
    {ℋ : Type u} [Qudit ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (_hrho : IsDensity rho) (_hsigma : IsDensity sigma) : ℝ :=
  (Tr (CFC.rpow rho (alpha : ℝ) *
    CFC.rpow sigma (1 - (alpha : ℝ)))).re

/-- The complex trace underlying the Petz trace functional is real. -/
theorem petzTracePower_trace_im_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (_hrho : IsDensity rho) (_hsigma : IsDensity sigma) :
    (Tr (CFC.rpow rho (alpha : ℝ) *
      CFC.rpow sigma (1 - (alpha : ℝ)))).im = 0 := by
  let X : L ℋ := CFC.rpow rho (alpha : ℝ)
  let Y : L ℋ := CFC.rpow sigma (1 - (alpha : ℝ))
  have htrace : Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y)) = Tr (X * Y) :=
    trace_star_sqrt_mul_self_eq_trace_mul CFC.rpow_nonneg CFC.rpow_nonneg
  have htrace_nonneg :
      0 ≤ Tr (star (CFC.sqrt X * CFC.sqrt Y) *
        (CFC.sqrt X * CFC.sqrt Y)) :=
    ((LinearMap.nonneg_iff_isPositive _).mp
      (star_mul_self_nonneg (CFC.sqrt X * CFC.sqrt Y))).trace_nonneg
  have him : (Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y))).im = 0 :=
    (Complex.nonneg_iff.mp htrace_nonneg).2.symm
  rw [htrace] at him
  exact him

/-- Reality and strict positivity on Gour's admissible branch. -/
theorem petzTracePower_real_and_pos_of_admissible
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : (alpha : ℝ) ≠ 0) (halpha_one : (alpha : ℝ) ≠ 1)
    (hadmissible : suppLE rho sigma ∨
      ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0)) :
    (Tr (CFC.rpow rho (alpha : ℝ) *
      CFC.rpow sigma (1 - (alpha : ℝ)))).im = 0 ∧
      0 < petzTracePower alpha rho sigma hrho hsigma := by
  have hrho_nonneg : (0 : L ℋ) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L ℋ) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  have hone_sub_alpha : 1 - (alpha : ℝ) ≠ 0 :=
    sub_ne_zero.mpr halpha_one.symm
  have hrho_sigma_ne : rho * sigma ≠ 0 := by
    rcases hadmissible with hsupp | ⟨_, hmul⟩
    · exact mul_ne_zero_of_isDensity_of_suppLE hrho hsigma hsupp
    · exact hmul
  have hpow_ne : CFC.rpow rho (alpha : ℝ) *
      CFC.rpow sigma (1 - (alpha : ℝ)) ≠ 0 := by
    intro hpow
    exact hrho_sigma_ne (mul_eq_zero_of_rpow_mul_rpow_eq_zero
      hrho_nonneg hsigma_nonneg halpha_zero hone_sub_alpha hpow)
  refine ⟨petzTracePower_trace_im_eq_zero
    alpha rho sigma hrho hsigma, ?_⟩
  unfold petzTracePower
  exact trace_re_pos_of_mul_of_nonneg_of_ne_zero
    CFC.rpow_nonneg CFC.rpow_nonneg hpow_ne

end OPT

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy

universe u

/--
**Source.** Gilad Gour, *Resources of the Quantum World*, the unnumbered formula of Definition 6.6
(printed page 309, PDF physical page 311).

For any real order \(\alpha\) and operators \(\rho,\sigma\) on a finite-dimensional complex
Hilbert space, the Petz trace power of real order is defined by
\[
  Q^{\mathrm{raw}}_\alpha(\rho\Vert\sigma)
  :=\operatorname{Re}\operatorname{Tr}
    \!\left[\rho^\alpha\sigma^{1-\alpha}\right].
\]

**Difference from the source.** At order zero the source treats \(\rho^0\) as the support
projection, so the value of this total formula at \(\alpha=0\) is not identified with the
source's order-zero value. The case distinction by the domain conditions of the source is not
built into this definition.

**Finite-dimensional dependence.** Used for the matrix trace and for the real powers given by
continuous functional calculus.
-/
noncomputable def petzTracePowerRaw
    {ℋ : Type u} [Qudit ℋ]
    (alpha : ℝ) (rho sigma : L ℋ) : ℝ :=
  (Tr (CFC.rpow rho alpha * CFC.rpow sigma (1 - alpha))).re

/--
**Source.** Gilad Gour, *Resources of the Quantum World*, the remark immediately after
Definition 6.6 (printed page 309, PDF physical page 311).

Let \(\rho,\sigma\) be density operators on a finite-dimensional complex Hilbert space, and let
\(\alpha\) be any real number with \(\alpha\ne0,1\). If
\[
  \operatorname{supp}\rho\subseteq\operatorname{supp}\sigma
  \quad\text{or}\quad
  \bigl(\alpha<1\ \text{and}\ \rho\sigma\ne0\bigr),
\]
then
\[
  \rho^\alpha\sigma^{1-\alpha}\ne0 .
\]

In the proof, positive semidefiniteness of \(\rho,\sigma\) follows from the density property.
In the support-inclusion case, the existing result that the product of two density operators
satisfying support inclusion is nonzero is applied; in the other case \(\rho\sigma\ne0\) is
obtained directly from the hypothesis. From \(\alpha\ne0\) and \(\alpha\ne1\), the two exponents
\(\alpha\) and \(1-\alpha\) are both nonzero. If the product of the powers were zero, the existing
result that nonzero real powers preserve kernels and ranges would give \(\rho\sigma=0\),
contradicting the nonvanishing above.

**Difference from the source.** Orders zero and one are excluded from the statement, and the
endpoint treatment using support projections is outside the scope of this theorem.

**Finite-dimensional dependence.** Used for the finite spectrum and orthogonal-complement arguments
in the invoked kernel and range preservation results.
-/
theorem petzRpowMul_ne_zero_of_admissible
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : alpha ≠ 0) (halpha_one : alpha ≠ 1)
    (hadmissible : suppLE rho sigma ∨
      (alpha < 1 ∧ rho * sigma ≠ 0)) :
    CFC.rpow rho alpha * CFC.rpow sigma (1 - alpha) ≠ 0 := by
  have hrho_nonneg : (0 : L ℋ) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L ℋ) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  have hone_sub_alpha : 1 - alpha ≠ 0 :=
    sub_ne_zero.mpr halpha_one.symm
  have hrho_sigma_ne : rho * sigma ≠ 0 := by
    rcases hadmissible with hsupp | ⟨_, hmul⟩
    · exact mul_ne_zero_of_isDensity_of_suppLE hrho hsigma hsupp
    · exact hmul
  intro hpow
  exact hrho_sigma_ne (mul_eq_zero_of_rpow_mul_rpow_eq_zero
    hrho_nonneg hsigma_nonneg halpha_zero hone_sub_alpha hpow)

/--
**Source.** Gilad Gour, *Resources of the Quantum World*, the remark immediately after
Definition 6.6 (printed page 309, PDF physical page 311).

Let \(\rho,\sigma\) be density operators on a finite-dimensional complex Hilbert space, and let
\(\alpha\) be any real number with \(\alpha\ne0,1\). Assuming support inclusion, or
\(\alpha<1\) and \(\rho\sigma\ne0\),
\[
  Q^{\mathrm{raw}}_\alpha(\rho\Vert\sigma)>0 .
\]

First, the proved result on the nonvanishing of the product of powers gives
\(\rho^\alpha\sigma^{1-\alpha}\ne0\). Both real powers are positive semidefinite. Applying the
existing result that the real part of the trace of a nonzero product of positive semidefinite
operators is strictly positive, and unfolding the Petz trace power defined above, gives the
conclusion.

**Difference from the source.** Positivity at orders zero and one is not part of this theorem,
and the endpoint treatment using support projections is outside the scope of this theorem.

**Finite-dimensional dependence.** Used for faithfulness of the trace on nonzero products of
positive semidefinite operators.
-/
theorem petzTracePowerRaw_pos_of_admissible
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : alpha ≠ 0) (halpha_one : alpha ≠ 1)
    (hadmissible : suppLE rho sigma ∨
      (alpha < 1 ∧ rho * sigma ≠ 0)) :
    0 < petzTracePowerRaw alpha rho sigma := by
  unfold petzTracePowerRaw
  exact trace_re_pos_of_mul_of_nonneg_of_ne_zero
    CFC.rpow_nonneg CFC.rpow_nonneg
    (petzRpowMul_ne_zero_of_admissible alpha rho sigma hrho hsigma
      halpha_zero halpha_one hadmissible)

end OPT
