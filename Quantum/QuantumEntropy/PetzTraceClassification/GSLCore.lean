/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzTracePower.GSLCore
import Quantum.QuantumEntropy.Common.TraceRe

/-!
# Petz trace powers with support-aware zero exponents

This file gives the partial-domain trace expression and its exhaustive
positive, zero, or undefined classification from the remark following Gour's
Definition 6.6.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy

universe u

private lemma petzSpectrumRealFinite
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) :
    (spectrum ℝ A).Finite := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private lemma petzRpowEqCfcSingular
    {ℋ : Type u} [Qudit ℋ] {A : L ℋ}
    (hA : 0 ≤ A) (p : ℝ) :
    CFC.rpow A p = cfc (fun x : ℝ => x ^ p) A := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hA

private lemma petzRpowRpowInvSingular
    {ℋ : Type u} [Qudit ℋ] {A : L ℋ}
    (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow (CFC.rpow A p) p⁻¹ = A := by
  let f : ℝ → ℝ := fun x => x ^ p
  let g : ℝ → ℝ := fun x => x ^ p⁻¹
  have hspec : (spectrum ℝ A).Finite := petzSpectrumRealFinite A
  have hf : ContinuousOn f (spectrum ℝ A) := hspec.continuousOn f
  have hg : ContinuousOn g (f '' spectrum ℝ A) :=
    (hspec.image f).continuousOn g
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [petzRpowEqCfcSingular (A := CFC.rpow A p) CFC.rpow_nonneg p⁻¹]
  rw [petzRpowEqCfcSingular (A := A) hA p]
  rw [← cfc_comp (p := IsSelfAdjoint) g f A hA_sa hg hf]
  calc
    cfc (g ∘ f) A = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      have hx_nonneg := spectrum_nonneg_of_nonneg hA hx
      change (x ^ p) ^ p⁻¹ = x
      rw [← Real.rpow_mul hx_nonneg, mul_inv_cancel₀ hp, Real.rpow_one]
    _ = A := cfc_id' ℝ A hA_sa

private lemma petzRpowApplyEigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p : ℝ) {v : ℋ} {mu : ℝ}
    (hv : A v = (mu : ℂ) • v) (hmu : mu ∈ spectrum ℝ A) :
    CFC.rpow A p v = ((mu ^ p : ℝ) : ℂ) • v := by
  rw [petzRpowEqCfcSingular hA p]
  exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hA)
    (fun x : ℝ => x ^ p) hv hmu

private lemma petzKerRpowEqKer
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
    have happ := petzRpowApplyEigenvector CFC.rpow_nonneg p⁻¹
      (show CFC.rpow A p x = ((0 : ℝ) : ℂ) • x by simpa using hx) hspec
    change (CFC.rpow (CFC.rpow A p) p⁻¹) x =
      (((0 : ℝ) ^ p⁻¹ : ℝ) : ℂ) • x at happ
    rw [petzRpowRpowInvSingular hA hp] at happ
    simpa [Real.zero_rpow (inv_ne_zero hp)] using happ
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    by_cases hx_zero : x = 0
    · simp [hx_zero]
    have hspec : (0 : ℝ) ∈ spectrum ℝ A :=
      mem_spectrum_real_of_eigenvector_lm hx_zero (by simpa using hx)
    have happ := petzRpowApplyEigenvector hA p
      (show A x = ((0 : ℝ) : ℂ) • x by simpa using hx) hspec
    simpa [Real.zero_rpow hp] using happ

private lemma petzRangeRpowEqRange
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
      congrArg Submodule.orthogonal (petzKerRpowEqKer hA hp)
    _ = LinearMap.range A := by
      rw [LinearMap.orthogonal_ker, hA_symm.adjoint_eq]

/-- The support-aware real power, using the orthogonal support projection at exponent zero. -/
noncomputable def petzSupportRpow
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (p : ℝ) : L ℋ :=
  if p = 0 then (LinearMap.range A).starProjection.toLinearMap
  else CFC.rpow A p

@[simp]
theorem petzSupportRpow_zero
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) :
    petzSupportRpow A 0 =
      (LinearMap.range A).starProjection.toLinearMap := by
  simp [petzSupportRpow]

theorem petzSupportRpow_of_ne_zero
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) {p : ℝ} (hp : p ≠ 0) :
    petzSupportRpow A p = CFC.rpow A p := by
  simp [petzSupportRpow, hp]

theorem petzSupportRpow_nonneg
    {ℋ : Type u} [Qudit ℋ] (A : L ℋ) (p : ℝ) :
    0 ≤ petzSupportRpow A p := by
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero]
    exact (LinearMap.nonneg_iff_isPositive _).mpr
      (Submodule.isSymmetricProjection_starProjection
        (LinearMap.range A)).isPositive
  · rw [petzSupportRpow_of_ne_zero A hp]
    exact CFC.rpow_nonneg

private theorem petzSupportRpow_ker_eq
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p : ℝ) :
    LinearMap.ker (petzSupportRpow A p) = LinearMap.ker A := by
  by_cases hp : p = 0
  · subst p
    have hA_symm : A.IsSymmetric :=
      ((LinearMap.nonneg_iff_isPositive _).mp hA).isSymmetric
    rw [petzSupportRpow_zero, Submodule.ker_starProjection,
      LinearMap.orthogonal_range, hA_symm.adjoint_eq]
  · rw [petzSupportRpow_of_ne_zero A hp]
    exact petzKerRpowEqKer hA hp

private theorem petzSupportRpow_range_eq
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p : ℝ) :
    LinearMap.range (petzSupportRpow A p) = LinearMap.range A := by
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero, Submodule.range_starProjection]
  · rw [petzSupportRpow_of_ne_zero A hp]
    exact petzRangeRpowEqRange hA hp

/-- A support-aware power acts on an eigenvector by the ordinary real power
away from zero and by zero on the kernel, including at exponent zero. -/
theorem petzSupportRpow_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p : ℝ) {v : ℋ} {mu : ℝ}
    (hv : A v = (mu : ℂ) • v) (hmu : mu ∈ spectrum ℝ A) :
    petzSupportRpow A p v =
      ((if mu = 0 then 0 else mu ^ p : ℝ) : ℂ) • v := by
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero]
    by_cases hmu0 : mu = 0
    · subst mu
      rw [if_pos rfl]
      simp only [Complex.ofReal_zero, zero_smul]
      apply (Submodule.starProjection_apply_eq_zero_iff
        (K := LinearMap.range A)).mpr
      rw [((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.orthogonal_range]
      exact LinearMap.mem_ker.mpr (by simpa using hv)
    · rw [if_neg hmu0, Real.rpow_zero, Complex.ofReal_one, one_smul]
      apply Submodule.starProjection_eq_self_iff.mpr
      refine ⟨(mu : ℂ)⁻¹ • v, ?_⟩
      rw [map_smul, hv, smul_smul, inv_mul_cancel₀, one_smul]
      exact Complex.ofReal_ne_zero.mpr hmu0
  · rw [petzSupportRpow_of_ne_zero A hp]
    have happ := petzRpowApplyEigenvector hA p hv hmu
    by_cases hmu0 : mu = 0
    · subst mu
      simpa [Real.zero_rpow hp] using happ
    · simpa [hmu0] using happ

/-- Support-aware powers satisfy the exponent-addition law even for singular
operators and even when the sum of the exponents is zero. -/
theorem petzSupportRpow_add
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (p q : ℝ) :
    petzSupportRpow A p * petzSupportRpow A q =
      petzSupportRpow A (p + q) := by
  let hsym : A.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric
  apply (hsym.eigenvectorBasis rfl).toBasis.ext
  intro i
  let mu := hsym.eigenvalues rfl i
  have hmuSpec : mu ∈ spectrum ℝ A := by
    letI : IsScalarTower ℝ ℂ (L ℋ) :=
      RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage]
    exact (hsym.hasEigenvalue_eigenvalues rfl i).mem_spectrum
  have hmuNonneg : 0 ≤ mu := spectrum_nonneg_of_nonneg hA hmuSpec
  have heigen : A (hsym.eigenvectorBasis rfl i) =
      (mu : ℂ) • hsym.eigenvectorBasis rfl i :=
    hsym.apply_eigenvectorBasis rfl i
  change petzSupportRpow A p
      (petzSupportRpow A q (hsym.eigenvectorBasis rfl i)) =
    petzSupportRpow A (p + q) (hsym.eigenvectorBasis rfl i)
  rw [petzSupportRpow_apply_eigenvector hA q heigen hmuSpec,
    map_smul, petzSupportRpow_apply_eigenvector hA p heigen hmuSpec,
    petzSupportRpow_apply_eigenvector hA (p + q) heigen hmuSpec,
    smul_smul]
  congr 1
  by_cases hmu0 : mu = 0
  · simp [hmu0]
  · have hmupos : 0 < mu := lt_of_le_of_ne hmuNonneg (Ne.symm hmu0)
    simp only [hmu0, if_false]
    norm_cast
    rw [Real.rpow_add hmupos, mul_comm]

theorem petzSupportRpow_mul_eq_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p q : ℝ) :
    petzSupportRpow A p * petzSupportRpow B q = 0 ↔ A * B = 0 := by
  simp only [Module.End.mul_eq_comp]
  rw [← LinearMap.range_le_ker_iff, ← LinearMap.range_le_ker_iff,
    petzSupportRpow_range_eq hB q, petzSupportRpow_ker_eq hA p]

private lemma petzTraceStarSqrtMulSelfEqTraceMul
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

private lemma petzTraceRePosOfMulOfNonnegOfNeZero
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
  have htrace := petzTraceStarSqrtMulSelfEqTraceMul hX hY
  change Tr (star Z * Z) = Tr (X * Y) at htrace
  rwa [htrace] at htrace_pos

private lemma petzMulNeZeroOfDensityOfSuppLE
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

/-- The real trace of the product of the two support-aware powers. -/
noncomputable def petzSupportTracePower
    {ℋ : Type u} [Qudit ℋ]
    (alpha : ℝ) (rho sigma : L ℋ) : ℝ :=
  (Tr (petzSupportRpow rho alpha *
    petzSupportRpow sigma (1 - alpha))).re

theorem petzSupportTracePower_eq_raw
    {ℋ : Type u} [Qudit ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (halpha_zero : alpha ≠ 0) (halpha_one : alpha ≠ 1) :
    petzSupportTracePower alpha rho sigma =
      petzTracePowerRaw alpha rho sigma := by
  unfold petzSupportTracePower petzTracePowerRaw
  rw [petzSupportRpow_of_ne_zero rho halpha_zero,
    petzSupportRpow_of_ne_zero sigma (sub_ne_zero.mpr halpha_one.symm)]

/-- The support-aware product is nonzero exactly when the original product is nonzero. -/
theorem petzSupportRpowMul_ne_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzSupportRpow rho alpha * petzSupportRpow sigma (1 - alpha) ≠ 0 ↔
      rho * sigma ≠ 0 := by
  have hrho_nonneg : (0 : L ℋ) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L ℋ) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  exact not_congr (petzSupportRpow_mul_eq_zero_iff
    hrho_nonneg hsigma_nonneg alpha (1 - alpha))

theorem petzSupportTracePower_pos_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupp : suppLE rho sigma) :
    0 < petzSupportTracePower alpha rho sigma := by
  by_cases halpha_zero : alpha = 0
  · have hmul : rho * sigma ≠ 0 :=
      petzMulNeZeroOfDensityOfSuppLE hrho hsigma hsupp
    have hpow : petzSupportRpow rho alpha *
        petzSupportRpow sigma (1 - alpha) ≠ 0 :=
      (petzSupportRpowMul_ne_zero_iff alpha rho sigma hrho hsigma).2 hmul
    unfold petzSupportTracePower
    exact petzTraceRePosOfMulOfNonnegOfNeZero
      (petzSupportRpow_nonneg rho alpha)
      (petzSupportRpow_nonneg sigma (1 - alpha)) hpow
  · by_cases halpha_one : alpha = 1
    · have hmul : rho * sigma ≠ 0 :=
        petzMulNeZeroOfDensityOfSuppLE hrho hsigma hsupp
      have hpow : petzSupportRpow rho alpha *
          petzSupportRpow sigma (1 - alpha) ≠ 0 :=
        (petzSupportRpowMul_ne_zero_iff alpha rho sigma hrho hsigma).2 hmul
      unfold petzSupportTracePower
      exact petzTraceRePosOfMulOfNonnegOfNeZero
        (petzSupportRpow_nonneg rho alpha)
        (petzSupportRpow_nonneg sigma (1 - alpha)) hpow
    · rw [petzSupportTracePower_eq_raw alpha rho sigma
        halpha_zero halpha_one]
      exact petzTracePowerRaw_pos_of_admissible alpha rho sigma
        hrho hsigma halpha_zero halpha_one (Or.inl hsupp)

theorem petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_lt : alpha < 1) (hmul : rho * sigma ≠ 0) :
    0 < petzSupportTracePower alpha rho sigma := by
  by_cases halpha_zero : alpha = 0
  · have hpow : petzSupportRpow rho alpha *
        petzSupportRpow sigma (1 - alpha) ≠ 0 :=
      (petzSupportRpowMul_ne_zero_iff alpha rho sigma hrho hsigma).2 hmul
    unfold petzSupportTracePower
    exact petzTraceRePosOfMulOfNonnegOfNeZero
      (petzSupportRpow_nonneg rho alpha)
      (petzSupportRpow_nonneg sigma (1 - alpha)) hpow
  · have halpha_one : alpha ≠ 1 := ne_of_lt halpha_lt
    rw [petzSupportTracePower_eq_raw alpha rho sigma
      halpha_zero halpha_one]
    exact petzTracePowerRaw_pos_of_admissible alpha rho sigma
      hrho hsigma halpha_zero halpha_one (Or.inr ⟨halpha_lt, hmul⟩)

/-- The Petz trace expression as a partial real value on nonnegative orders. -/
noncomputable def petzTraceExpression
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (_halpha_nonneg : 0 ≤ alpha)
    (_hrho : IsDensity rho) (_hsigma : IsDensity sigma) : Option ℝ :=
  by
    classical
    exact if alpha < 1 ∨ suppLE rho sigma then
      some (petzSupportTracePower alpha rho sigma)
    else none

theorem petzTraceExpression_eq_some_zero_of_lt_one_of_mul_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : ℝ) (rho sigma : L ℋ)
    (halpha_nonneg : 0 ≤ alpha)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_lt : alpha < 1) (hmul : rho * sigma = 0) :
    petzSupportRpow rho alpha * petzSupportRpow sigma (1 - alpha) = 0 ∧
      petzSupportTracePower alpha rho sigma = 0 ∧
      petzTraceExpression alpha rho sigma halpha_nonneg hrho hsigma = some 0 := by
  have hrho_nonneg : (0 : L ℋ) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L ℋ) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  have hpow : petzSupportRpow rho alpha *
      petzSupportRpow sigma (1 - alpha) = 0 :=
    (petzSupportRpow_mul_eq_zero_iff hrho_nonneg hsigma_nonneg
      alpha (1 - alpha)).2 hmul
  have htrace : petzSupportTracePower alpha rho sigma = 0 := by
    unfold petzSupportTracePower
    rw [hpow, map_zero]
    rfl
  refine ⟨hpow, htrace, ?_⟩
  simp [petzTraceExpression, halpha_lt, htrace]

end OPT
