/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.QuantumFDivergence.GSLCore
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCore
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki

open QuantumState TensorProduct
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

/-!
# Petz Rényi divergence at every nonnegative finite order

This file extends the endpoint-complete Petz Rényi divergence from the closed
order interval used by data processing to every finite nonnegative order.  It
establishes support-aware tensor power laws, binary normalization, and tensor
additivity without changing the earlier closed-interval definition.
-/

universe u v

namespace OPT

theorem w26IsDensity_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (rho : L E) (sigma : L F) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    IsDensity (TensorProduct.map rho sigma : L (E ⊗[ℂ] F)) :=
  QuantumEntropy.TensorDensitySupport.isDensity_tensorMap
    rho sigma hrho hsigma

theorem w26SuppLE_tensorMap_iff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    suppLE (TensorProduct.map rho₁ rho₂) (TensorProduct.map sigma₁ sigma₂) ↔
      suppLE rho₁ sigma₁ ∧ suppLE rho₂ sigma₂ :=
  QuantumEntropy.TensorDensitySupport.supportLE_tensorMap_iff
    rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂

theorem w26PetzSupportRpow_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (A : L E) (B : L F) (p : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    petzSupportRpow (TensorProduct.map A B : L (E ⊗[ℂ] F)) p =
      TensorProduct.map (petzSupportRpow A p) (petzSupportRpow B p) := by
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero, petzSupportRpow_zero, petzSupportRpow_zero,
      QuantumEntropy.TensorDensitySupport.starProjection_tensorMap]
  · rw [petzSupportRpow_of_ne_zero _ hp, petzSupportRpow_of_ne_zero _ hp,
      petzSupportRpow_of_ne_zero _ hp]
    exact TensorCFC.rpow_tensorProduct_lm A B p hA hB

private lemma w26TraceMul_im_eq_zero_of_nonneg
    {E : Type u} [Qudit E] {X Y : L E} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (Tr (X * Y)).im = 0 := by
  have hsx : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hsy : IsSelfAdjoint (CFC.sqrt Y) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  have htrace : Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y)) = Tr (X * Y) := by
    calc
      Tr (star (CFC.sqrt X * CFC.sqrt Y) *
          (CFC.sqrt X * CFC.sqrt Y)) =
          Tr ((CFC.sqrt Y * CFC.sqrt X) *
            (CFC.sqrt X * CFC.sqrt Y)) := by
        rw [star_mul, hsx.star_eq, hsy.star_eq]
      _ = Tr (CFC.sqrt Y *
          ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
        simp only [mul_assoc]
      _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by
        rw [CFC.sqrt_mul_sqrt_self X hX]
      _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) :=
        LinearMap.trace_mul_comm ℂ (CFC.sqrt Y) (X * CFC.sqrt Y)
      _ = Tr (X * (CFC.sqrt Y * CFC.sqrt Y)) := by rw [mul_assoc]
      _ = Tr (X * Y) := by rw [CFC.sqrt_mul_sqrt_self Y hY]
  have htrace_nonneg :
      0 ≤ Tr (star (CFC.sqrt X * CFC.sqrt Y) *
        (CFC.sqrt X * CFC.sqrt Y)) :=
    ((LinearMap.nonneg_iff_isPositive _).mp
      (star_mul_self_nonneg (CFC.sqrt X * CFC.sqrt Y))).trace_nonneg
  have him : (Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y))).im = 0 :=
    (Complex.nonneg_iff.mp htrace_nonneg).2.symm
  rwa [htrace] at him

theorem w26PetzSupportTracePower_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (alpha : ℝ) (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : 0 ≤ rho₁) (hsigma₁ : 0 ≤ sigma₁)
    (hrho₂ : 0 ≤ rho₂) (hsigma₂ : 0 ≤ sigma₂) :
    petzSupportTracePower alpha
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂) =
      petzSupportTracePower alpha rho₁ sigma₁ *
        petzSupportTracePower alpha rho₂ sigma₂ := by
  unfold petzSupportTracePower
  rw [w26PetzSupportRpow_tensorMap rho₁ rho₂ alpha hrho₁ hrho₂,
    w26PetzSupportRpow_tensorMap sigma₁ sigma₂ (1 - alpha) hsigma₁ hsigma₂,
    ← TensorProduct.map_mul, LinearMap.trace_tensorProduct']
  have h₁ := w26TraceMul_im_eq_zero_of_nonneg
    (petzSupportRpow_nonneg rho₁ alpha)
    (petzSupportRpow_nonneg sigma₁ (1 - alpha))
  have h₂ := w26TraceMul_im_eq_zero_of_nonneg
    (petzSupportRpow_nonneg rho₂ alpha)
    (petzSupportRpow_nonneg sigma₂ (1 - alpha))
  rw [Complex.mul_re, h₁, h₂]
  ring

/-- Nonnegative finite Petz orders, with no upper cutoff. -/
abbrev W26PetzRenyiFiniteOrder := Set.Ici (0 : ℝ)

private def w26PetzFiniteToClosed
    (alpha : W26PetzRenyiFiniteOrder) (halpha : (alpha : ℝ) ≤ 2) :
    PetzRenyiOrder :=
  ⟨alpha, alpha.property, halpha⟩

private def w26PetzOrderZero : PetzRenyiOrder := ⟨0, by norm_num⟩
private def w26PetzOrderOne : PetzRenyiOrder := ⟨1, by norm_num⟩

noncomputable def w26PetzQuantumRenyiDivergenceFinite
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : W26PetzRenyiFiniteOrder) (rho sigma : L E)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) : EReal := by
  classical
  exact if halpha_zero : (alpha : ℝ) = 0 then
      petzQuantumRenyiDivergence w26PetzOrderZero rho sigma hrho hsigma
    else if halpha_one : (alpha : ℝ) = 1 then
      petzQuantumRenyiDivergence w26PetzOrderOne rho sigma hrho hsigma
    else if hadmissible : suppLE rho sigma ∨
        ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0) then
      let q : {x : ℝ // 0 < x} :=
        ⟨petzSupportTracePower alpha rho sigma,
          hadmissible.elim
            (petzSupportTracePower_pos_of_suppLE alpha rho sigma hrho hsigma)
            (fun h => petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
              alpha rho sigma hrho hsigma h.1 h.2)⟩
      (((((alpha : ℝ) - 1)⁻¹ * Real.logb 2 (q : ℝ) : ℝ) : EReal))
    else ⊤

theorem w26PetzQuantumRenyiDivergenceFinite_compatibility
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : W26PetzRenyiFiniteOrder) (halpha : (alpha : ℝ) ≤ 2)
    (rho sigma : L E) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    w26PetzQuantumRenyiDivergenceFinite alpha rho sigma hrho hsigma =
      petzQuantumRenyiDivergence (w26PetzFiniteToClosed alpha halpha)
        rho sigma hrho hsigma := by
  by_cases hzero : (alpha : ℝ) = 0
  · have horder : w26PetzFiniteToClosed alpha halpha = w26PetzOrderZero := by
      apply Subtype.ext
      exact hzero
    simp only [w26PetzQuantumRenyiDivergenceFinite, dif_pos hzero, horder]
  · by_cases hone : (alpha : ℝ) = 1
    · have horder : w26PetzFiniteToClosed alpha halpha = w26PetzOrderOne := by
        apply Subtype.ext
        exact hone
      simp only [w26PetzQuantumRenyiDivergenceFinite, dif_neg hzero,
        dif_pos hone, horder]
    · have hzero' : ((w26PetzFiniteToClosed alpha halpha : PetzRenyiOrder) : ℝ) ≠ 0 :=
        hzero
      have hone' : ((w26PetzFiniteToClosed alpha halpha : PetzRenyiOrder) : ℝ) ≠ 1 :=
        hone
      rw [w26PetzQuantumRenyiDivergenceFinite, dif_neg hzero, dif_neg hone,
        petzQuantumRenyiDivergence, dif_neg hzero', dif_neg hone',
        petzRenyiPunctured]
      by_cases hadmissible : suppLE rho sigma ∨
          ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0)
      · have hadmissible' : suppLE rho sigma ∨
            (((w26PetzFiniteToClosed alpha halpha : PetzRenyiOrder) : ℝ) < 1 ∧
              rho * sigma ≠ 0) := hadmissible
        rw [dif_pos hadmissible, dif_pos hadmissible']
        dsimp only
        norm_cast
        rw [petzSupportTracePower_eq_raw alpha rho sigma hzero hone]
        rfl
      · have hadmissible' : ¬ (suppLE rho sigma ∨
            (((w26PetzFiniteToClosed alpha halpha : PetzRenyiOrder) : ℝ) < 1 ∧
              rho * sigma ≠ 0)) := hadmissible
        rw [dif_neg hadmissible, dif_neg hadmissible']

private theorem w26PetzAdmissible_tensorMap_iff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (alpha : ℝ) (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    (suppLE (TensorProduct.map rho₁ rho₂) (TensorProduct.map sigma₁ sigma₂) ∨
        (alpha < 1 ∧
          (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F)) *
            TensorProduct.map sigma₁ sigma₂ ≠ 0)) ↔
      (suppLE rho₁ sigma₁ ∨ (alpha < 1 ∧ rho₁ * sigma₁ ≠ 0)) ∧
        (suppLE rho₂ sigma₂ ∨ (alpha < 1 ∧ rho₂ * sigma₂ ≠ 0)) := by
  have hsupp := w26SuppLE_tensorMap_iff rho₁ sigma₁ rho₂ sigma₂
    hrho₁ hsigma₁ hrho₂ hsigma₂
  have hmul :
      (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F)) *
          TensorProduct.map sigma₁ sigma₂ ≠ 0 ↔
        rho₁ * sigma₁ ≠ 0 ∧ rho₂ * sigma₂ ≠ 0 := by
    rw [← TensorProduct.map_mul]
    exact QuantumEntropy.TensorDensitySupport.tensorMap_ne_zero_iff (rho₁ * sigma₁) (rho₂ * sigma₂)
  constructor
  · rintro (hs | ⟨ha, hm⟩)
    · exact ⟨Or.inl (hsupp.mp hs).1, Or.inl (hsupp.mp hs).2⟩
    · exact ⟨Or.inr ⟨ha, (hmul.mp hm).1⟩,
        Or.inr ⟨ha, (hmul.mp hm).2⟩⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with hs₁ | ⟨ha₁, hm₁⟩
    · rcases h₂ with hs₂ | ⟨ha₂, hm₂⟩
      · exact Or.inl (hsupp.mpr ⟨hs₁, hs₂⟩)
      · exact Or.inr ⟨ha₂, hmul.mpr
          ⟨QuantumEntropy.TensorDensitySupport.density_mul_ne_zero_of_supportLE hrho₁ hsigma₁ hs₁,
            hm₂⟩⟩
    · rcases h₂ with hs₂ | ⟨ha₂, hm₂⟩
      · exact Or.inr ⟨ha₁, hmul.mpr
          ⟨hm₁, QuantumEntropy.TensorDensitySupport.density_mul_ne_zero_of_supportLE
            hrho₂ hsigma₂ hs₂⟩⟩
      · exact Or.inr ⟨ha₁, hmul.mpr ⟨hm₁, hm₂⟩⟩

theorem w26PetzQuantumRenyiDivergenceFinite_tensorMap_of_ne_zero_one
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (alpha : W26PetzRenyiFiniteOrder)
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂)
    (halpha_zero : (alpha : ℝ) ≠ 0) (halpha_one : (alpha : ℝ) ≠ 1) :
    w26PetzQuantumRenyiDivergenceFinite alpha
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂)
        (w26IsDensity_tensorMap rho₁ rho₂ hrho₁ hrho₂)
        (w26IsDensity_tensorMap sigma₁ sigma₂ hsigma₁ hsigma₂) =
      w26PetzQuantumRenyiDivergenceFinite alpha rho₁ sigma₁ hrho₁ hsigma₁ +
        w26PetzQuantumRenyiDivergenceFinite alpha rho₂ sigma₂ hrho₂ hsigma₂ := by
  let hadm₁ := suppLE rho₁ sigma₁ ∨
    ((alpha : ℝ) < 1 ∧ rho₁ * sigma₁ ≠ 0)
  let hadm₂ := suppLE rho₂ sigma₂ ∨
    ((alpha : ℝ) < 1 ∧ rho₂ * sigma₂ ≠ 0)
  let hadmT := suppLE
      (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
      (TensorProduct.map sigma₁ sigma₂) ∨
    ((alpha : ℝ) < 1 ∧
      (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F)) *
        TensorProduct.map sigma₁ sigma₂ ≠ 0)
  have hadm_iff : hadmT ↔ hadm₁ ∧ hadm₂ :=
    w26PetzAdmissible_tensorMap_iff alpha rho₁ sigma₁ rho₂ sigma₂
      hrho₁ hsigma₁ hrho₂ hsigma₂
  rw [w26PetzQuantumRenyiDivergenceFinite, dif_neg halpha_zero,
    dif_neg halpha_one, w26PetzQuantumRenyiDivergenceFinite,
    dif_neg halpha_zero, dif_neg halpha_one,
    w26PetzQuantumRenyiDivergenceFinite, dif_neg halpha_zero,
    dif_neg halpha_one]
  by_cases h₁ : hadm₁
  · by_cases h₂ : hadm₂
    · have hT : hadmT := hadm_iff.mpr ⟨h₁, h₂⟩
      rw [dif_pos hT, dif_pos h₁, dif_pos h₂]
      dsimp only
      rw [w26PetzSupportTracePower_tensorMap alpha rho₁ sigma₁ rho₂ sigma₂
        ((LinearMap.nonneg_iff_isPositive _).mpr hrho₁.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₁.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr hrho₂.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₂.1)]
      have hq₁ : 0 < petzSupportTracePower alpha rho₁ sigma₁ :=
        h₁.elim
          (petzSupportTracePower_pos_of_suppLE alpha rho₁ sigma₁ hrho₁ hsigma₁)
          (fun h => petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
            alpha rho₁ sigma₁ hrho₁ hsigma₁ h.1 h.2)
      have hq₂ : 0 < petzSupportTracePower alpha rho₂ sigma₂ :=
        h₂.elim
          (petzSupportTracePower_pos_of_suppLE alpha rho₂ sigma₂ hrho₂ hsigma₂)
          (fun h => petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
            alpha rho₂ sigma₂ hrho₂ hsigma₂ h.1 h.2)
      rw [Real.logb_mul (ne_of_gt hq₁) (ne_of_gt hq₂)]
      norm_cast
      ring
    · have hT : ¬ hadmT := fun h => h₂ (hadm_iff.mp h).2
      rw [dif_neg hT, dif_pos h₁, dif_neg h₂]
      dsimp only
      exact (EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)).symm
  · have hT : ¬ hadmT := fun h => h₁ (hadm_iff.mp h).1
    rw [dif_neg hT, dif_neg h₁]
    by_cases h₂ : hadm₂
    · rw [dif_pos h₂]
      dsimp only
      exact (EReal.top_add_coe _).symm
    · rw [dif_neg h₂, EReal.top_add_top]

private theorem w26Mul_log_tensorMap_of_suppLE
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hsigma₁ : 0 ≤ sigma₁) (hsigma₂ : 0 ≤ sigma₂)
    (hsupp₁ : suppLE rho₁ sigma₁) (hsupp₂ : suppLE rho₂ sigma₂) :
    TensorProduct.map rho₁ rho₂ * CFC.log (TensorProduct.map sigma₁ sigma₂) =
      TensorProduct.map (rho₁ * CFC.log sigma₁) rho₂ +
        TensorProduct.map rho₁ (rho₂ * CFC.log sigma₂) := by
  classical
  have hsigma₁pos : sigma₁.IsPositive :=
    (LinearMap.nonneg_iff_isPositive sigma₁).mp hsigma₁
  have hsigma₂pos : sigma₂.IsPositive :=
    (LinearMap.nonneg_iff_isPositive sigma₂).mp hsigma₂
  have hsigma₁sym : sigma₁.IsSymmetric := hsigma₁pos.isSymmetric
  have hsigma₂sym : sigma₂.IsSymmetric := hsigma₂pos.isSymmetric
  let n₁ := Module.finrank ℂ E
  let n₂ := Module.finrank ℂ F
  let b₁ := hsigma₁sym.eigenvectorBasis (rfl : Module.finrank ℂ E = n₁)
  let b₂ := hsigma₂sym.eigenvectorBasis (rfl : Module.finrank ℂ F = n₂)
  let eig₁ := hsigma₁sym.eigenvalues (rfl : Module.finrank ℂ E = n₁)
  let eig₂ := hsigma₂sym.eigenvalues (rfl : Module.finrank ℂ F = n₂)
  let b₁₂ : Module.Basis (Fin n₁ × Fin n₂) ℂ (E ⊗[ℂ] F) :=
    b₁.toBasis.tensorProduct b₂.toBasis
  have hsigma₁eig : ∀ i, sigma₁ (b₁ i) = ((eig₁ i : ℝ) : ℂ) • b₁ i :=
    hsigma₁sym.apply_eigenvectorBasis _
  have hsigma₂eig : ∀ j, sigma₂ (b₂ j) = ((eig₂ j : ℝ) : ℂ) • b₂ j :=
    hsigma₂sym.apply_eigenvectorBasis _
  have hsigma₁sa : IsSelfAdjoint sigma₁ := hsigma₁pos.isSelfAdjoint
  have hsigma₂sa : IsSelfAdjoint sigma₂ := hsigma₂pos.isSelfAdjoint
  have hsigma₁₂sym : (TensorProduct.map sigma₁ sigma₂).IsSymmetric :=
    QuantumEntropy.TensorDensitySupport.tensorMap_isSymmetric sigma₁ sigma₂ hsigma₁sym hsigma₂sym
  have hsigma₁₂sa : IsSelfAdjoint (TensorProduct.map sigma₁ sigma₂) := by
    rw [isSelfAdjoint_iff, LinearMap.star_eq_adjoint]
    exact hsigma₁₂sym.adjoint_eq
  apply b₁₂.ext
  intro ij
  rcases ij with ⟨i, j⟩
  have hbasis : b₁₂ (i, j) = b₁ i ⊗ₜ[ℂ] b₂ j := by
    simp [b₁₂, b₁, b₂]
  rw [hbasis]
  have hprodEig : TensorProduct.map sigma₁ sigma₂ (b₁ i ⊗ₜ[ℂ] b₂ j) =
      (((eig₁ i * eig₂ j : ℝ) : ℂ)) • (b₁ i ⊗ₜ[ℂ] b₂ j) := by
    rw [TensorProduct.map_tmul, hsigma₁eig i, hsigma₂eig j,
      TensorProduct.smul_tmul_smul, ← Complex.ofReal_mul]
  have hprodNe : b₁ i ⊗ₜ[ℂ] b₂ j ≠ 0 := by
    intro hzero
    exact b₁₂.ne_zero (i, j) (hbasis.trans hzero)
  have hprodSpec : eig₁ i * eig₂ j ∈ spectrum ℝ
      (TensorProduct.map sigma₁ sigma₂) :=
    mem_spectrum_real_of_eigenvector_lm hprodNe hprodEig
  have heig₁spec : eig₁ i ∈ spectrum ℝ sigma₁ :=
    mem_spectrum_real_of_eigenvector_lm (b₁.toBasis.ne_zero i) (hsigma₁eig i)
  have heig₂spec : eig₂ j ∈ spectrum ℝ sigma₂ :=
    mem_spectrum_real_of_eigenvector_lm (b₂.toBasis.ne_zero j) (hsigma₂eig j)
  have hlogprod : CFC.log (TensorProduct.map sigma₁ sigma₂)
      (b₁ i ⊗ₜ[ℂ] b₂ j) =
      ((Real.log (eig₁ i * eig₂ j) : ℝ) : ℂ) •
        (b₁ i ⊗ₜ[ℂ] b₂ j) := by
    exact cfc_real_apply_eigenvector_lm hsigma₁₂sa Real.log hprodEig hprodSpec
  have hlog₁ : CFC.log sigma₁ (b₁ i) =
      ((Real.log (eig₁ i) : ℝ) : ℂ) • b₁ i := by
    exact cfc_real_apply_eigenvector_lm hsigma₁sa Real.log (hsigma₁eig i) heig₁spec
  have hlog₂ : CFC.log sigma₂ (b₂ j) =
      ((Real.log (eig₂ j) : ℝ) : ℂ) • b₂ j := by
    exact cfc_real_apply_eigenvector_lm hsigma₂sa Real.log (hsigma₂eig j) heig₂spec
  simp only [LinearMap.add_apply, Module.End.mul_apply, hlogprod, map_smul,
    TensorProduct.map_tmul, hlog₁, hlog₂]
  by_cases hi : eig₁ i = 0
  · have hkerSigma : b₁ i ∈ LinearMap.ker sigma₁ := by
      rw [LinearMap.mem_ker, hsigma₁eig i, hi]
      simp
    have hrho : rho₁ (b₁ i) = 0 := LinearMap.mem_ker.mp (hsupp₁ hkerSigma)
    rw [hrho]
    simp
  · by_cases hj : eig₂ j = 0
    · have hkerSigma : b₂ j ∈ LinearMap.ker sigma₂ := by
        rw [LinearMap.mem_ker, hsigma₂eig j, hj]
        simp
      have hrho : rho₂ (b₂ j) = 0 := LinearMap.mem_ker.mp (hsupp₂ hkerSigma)
      rw [hrho]
      simp
    · rw [Real.log_mul hi hj, Complex.ofReal_add, add_smul,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul]

private theorem w26UmegakiNorm_tensorMap_of_suppLE
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : 0 ≤ rho₁) (hsigma₁ : 0 ≤ sigma₁)
    (hrho₂ : 0 ≤ rho₂) (hsigma₂ : 0 ≤ sigma₂)
    (hTrRho₁ : Tr rho₁ = 1) (hTrRho₂ : Tr rho₂ = 1)
    (hsupp₁ : suppLE rho₁ sigma₁) (hsupp₂ : suppLE rho₂ sigma₂) :
    umegakiNorm (TensorProduct.map rho₁ rho₂) (TensorProduct.map sigma₁ sigma₂) =
      umegakiNorm rho₁ sigma₁ + umegakiNorm rho₂ sigma₂ := by
  have hself := w26Mul_log_tensorMap_of_suppLE
    rho₁ rho₁ rho₂ rho₂ hrho₁ hrho₂ (le_refl _) (le_refl _)
  have hcross := w26Mul_log_tensorMap_of_suppLE
    rho₁ sigma₁ rho₂ sigma₂ hsigma₁ hsigma₂ hsupp₁ hsupp₂
  unfold umegakiNorm
  rw [mul_sub, hself, hcross, map_sub, Complex.sub_re,
    map_add, map_add, LinearMap.trace_tensorProduct',
    LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct',
    LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct',
    hTrRho₁, hTrRho₂]
  norm_num
  simp only [mul_sub, map_sub, Complex.sub_re]
  ring

theorem w26UmegakiRelEntropyNN_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    umegakiRelEntropyNN
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂) =
      umegakiRelEntropyNN rho₁ sigma₁ +
        umegakiRelEntropyNN rho₂ sigma₂ := by
  have hsupp := w26SuppLE_tensorMap_iff rho₁ sigma₁ rho₂ sigma₂
    hrho₁ hsigma₁ hrho₂ hsigma₂
  by_cases hs₁ : suppLE rho₁ sigma₁
  · by_cases hs₂ : suppLE rho₂ sigma₂
    · have hsT := hsupp.mpr ⟨hs₁, hs₂⟩
      simp only [umegakiRelEntropyNN, hs₁, hs₂, hsT, if_true]
      rw [← EReal.coe_add]
      exact congrArg Real.toEReal
        (w26UmegakiNorm_tensorMap_of_suppLE rho₁ sigma₁ rho₂ sigma₂
          ((LinearMap.nonneg_iff_isPositive _).mpr hrho₁.1)
          ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₁.1)
          ((LinearMap.nonneg_iff_isPositive _).mpr hrho₂.1)
          ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₂.1)
          hrho₁.2 hrho₂.2 hs₁ hs₂)
    · have hsT : ¬ suppLE
          (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
          (TensorProduct.map sigma₁ sigma₂) := fun h => hs₂ (hsupp.mp h).2
      simp only [umegakiRelEntropyNN, hs₁, hs₂, hsT, if_true, if_false]
      exact (EReal.coe_add_top _).symm
  · have hsT : ¬ suppLE
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂) := fun h => hs₁ (hsupp.mp h).1
    by_cases hs₂ : suppLE rho₂ sigma₂
    · simp only [umegakiRelEntropyNN, hs₁, hs₂, hsT, if_true, if_false]
      exact (EReal.top_add_coe _).symm
    · simp only [umegakiRelEntropyNN, hs₁, hs₂, hsT, if_false]
      exact EReal.top_add_top.symm

theorem w26PetzQuantumRenyiDivergenceFinite_tensorMap_one
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    w26PetzQuantumRenyiDivergenceFinite ⟨1, by norm_num⟩
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂)
        (w26IsDensity_tensorMap rho₁ rho₂ hrho₁ hrho₂)
        (w26IsDensity_tensorMap sigma₁ sigma₂ hsigma₁ hsigma₂) =
      w26PetzQuantumRenyiDivergenceFinite ⟨1, by norm_num⟩
          rho₁ sigma₁ hrho₁ hsigma₁ +
        w26PetzQuantumRenyiDivergenceFinite ⟨1, by norm_num⟩
          rho₂ sigma₂ hrho₂ hsigma₂ := by
  have hone : ((⟨1, by norm_num⟩ : W26PetzRenyiFiniteOrder) : ℝ) = 1 := rfl
  rw [w26PetzQuantumRenyiDivergenceFinite, dif_neg one_ne_zero,
    dif_pos hone, w26PetzQuantumRenyiDivergenceFinite, dif_neg one_ne_zero,
    dif_pos hone, w26PetzQuantumRenyiDivergenceFinite, dif_neg one_ne_zero,
    dif_pos hone]
  change petzQuantumRenyiDivergence petzRenyiOrderOne
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂) _ _ =
    petzQuantumRenyiDivergence petzRenyiOrderOne rho₁ sigma₁ hrho₁ hsigma₁ +
      petzQuantumRenyiDivergence petzRenyiOrderOne rho₂ sigma₂ hrho₂ hsigma₂
  rw [petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
    petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
    petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
    w26UmegakiRelEntropyNN_tensorMap rho₁ sigma₁ rho₂ sigma₂
      hrho₁ hsigma₁ hrho₂ hsigma₂]
  exact EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (by positivity)) (EReal.coe_ne_top _) _ _

private theorem w26ClassicalSupportOverlap_ne_top
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    classicalSupportOverlapPMF p q ≠ ⊤ := by
  classical
  unfold classicalSupportOverlapPMF
  rw [ENNReal.sum_ne_top]
  intro i _
  split_ifs <;> simp [q.apply_ne_top]

private theorem w26ClassicalSupportOverlap_le_one
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    classicalSupportOverlapPMF p q ≤ 1 := by
  classical
  have hsum : ∑ i, q i = 1 := by
    simpa only [tsum_fintype] using q.tsum_coe
  unfold classicalSupportOverlapPMF
  calc
    (∑ i, if i ∈ p.support then q i else 0) ≤ ∑ i, q i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp
    _ = 1 := hsum

theorem w26PetzQuantumRenyiDivergenceFinite_zero_eq_supportTracePower
    {E : Type u} [Qudit E] [Nontrivial E]
    (rho sigma : L E) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    w26PetzQuantumRenyiDivergenceFinite ⟨0, by norm_num⟩
        rho sigma hrho hsigma =
      if petzSupportTracePower 0 rho sigma = 0 then ⊤
      else ((-Real.logb 2 (petzSupportTracePower 0 rho sigma) : ℝ) : EReal) := by
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  let s := classicalSupportOverlapPMF p q
  let Q := petzSupportTracePower 0 rho sigma
  have hbridge : s.toReal = Q := by
    exact classicalSupportOverlapPMF_petzSpectral_toReal_eq
      rho sigma hrho hsigma
  have hstop : s ≠ ⊤ := w26ClassicalSupportOverlap_ne_top p q
  have hsle : s ≤ 1 := w26ClassicalSupportOverlap_le_one p q
  have hzero : s = 0 ↔ Q = 0 := by
    constructor
    · intro hs
      rw [← hbridge, hs, ENNReal.toReal_zero]
    · intro hQ
      have hsreal : s.toReal = 0 := hbridge.trans hQ
      exact (ENNReal.toReal_eq_zero_iff s).mp hsreal |>.resolve_right hstop
  have hQnonneg : 0 ≤ Q := by
    rw [← hbridge]
    exact ENNReal.toReal_nonneg
  have hQle : Q ≤ 1 := by
    rw [← hbridge]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hsle
  have hlog_nonneg : 0 ≤ -Real.logb 2 Q := by
    exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num) hQnonneg hQle)
  rw [w26PetzQuantumRenyiDivergenceFinite, dif_pos rfl,
    petzQuantumRenyiDivergence]
  simp only [w26PetzOrderZero, Subtype.coe_mk, ↓reduceDIte]
  rw [(petzRenyiEndpointValues_eq_classicalSpectral
    rho sigma hrho hsigma).1]
  unfold classicalMinRelativeEntropyBitsPMF
  change (↑(if s = 0 then (⊤ : ENNReal) else
      ENNReal.ofReal (-Real.logb 2 s.toReal)) : EReal) =
    if Q = 0 then ⊤ else ((-Real.logb 2 Q : ℝ) : EReal)
  by_cases hs : s = 0
  · have hQ : Q = 0 := hzero.mp hs
    simp [hs, hQ]
  · have hQ : Q ≠ 0 := fun h => hs (hzero.mpr h)
    simp only [if_neg hs, if_neg hQ]
    rw [hbridge, EReal.coe_ennreal_ofReal, max_eq_left hlog_nonneg]

theorem w26PetzQuantumRenyiDivergenceFinite_tensorMap_zero
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    w26PetzQuantumRenyiDivergenceFinite ⟨0, by norm_num⟩
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂)
        (w26IsDensity_tensorMap rho₁ rho₂ hrho₁ hrho₂)
        (w26IsDensity_tensorMap sigma₁ sigma₂ hsigma₁ hsigma₂) =
      w26PetzQuantumRenyiDivergenceFinite ⟨0, by norm_num⟩
          rho₁ sigma₁ hrho₁ hsigma₁ +
        w26PetzQuantumRenyiDivergenceFinite ⟨0, by norm_num⟩
          rho₂ sigma₂ hrho₂ hsigma₂ := by
  rw [w26PetzQuantumRenyiDivergenceFinite_zero_eq_supportTracePower,
    w26PetzQuantumRenyiDivergenceFinite_zero_eq_supportTracePower,
    w26PetzQuantumRenyiDivergenceFinite_zero_eq_supportTracePower,
    w26PetzSupportTracePower_tensorMap 0 rho₁ sigma₁ rho₂ sigma₂
      ((LinearMap.nonneg_iff_isPositive _).mpr hrho₁.1)
      ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₁.1)
      ((LinearMap.nonneg_iff_isPositive _).mpr hrho₂.1)
      ((LinearMap.nonneg_iff_isPositive _).mpr hsigma₂.1)]
  let Q₁ := petzSupportTracePower 0 rho₁ sigma₁
  let Q₂ := petzSupportTracePower 0 rho₂ sigma₂
  change (if Q₁ * Q₂ = 0 then ⊤
      else ((-Real.logb 2 (Q₁ * Q₂) : ℝ) : EReal)) =
    (if Q₁ = 0 then ⊤ else ((-Real.logb 2 Q₁ : ℝ) : EReal)) +
      if Q₂ = 0 then ⊤ else ((-Real.logb 2 Q₂ : ℝ) : EReal)
  by_cases h₁ : Q₁ = 0
  · by_cases h₂ : Q₂ = 0
    · simp [h₁, h₂, EReal.top_add_top]
    · simp only [h₁, h₂, zero_mul, if_true, if_false]
      exact (EReal.top_add_coe _).symm
  · by_cases h₂ : Q₂ = 0
    · simp only [h₁, h₂, mul_zero, if_true, if_false]
      exact (EReal.coe_add_top _).symm
    · simp only [mul_ne_zero h₁ h₂, if_false, h₁, h₂]
      rw [Real.logb_mul h₁ h₂, ← EReal.coe_add]
      congr 1
      ring

theorem w26PetzQuantumRenyiDivergenceFinite_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (alpha : W26PetzRenyiFiniteOrder)
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    w26PetzQuantumRenyiDivergenceFinite alpha
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂)
        (w26IsDensity_tensorMap rho₁ rho₂ hrho₁ hrho₂)
        (w26IsDensity_tensorMap sigma₁ sigma₂ hsigma₁ hsigma₂) =
      w26PetzQuantumRenyiDivergenceFinite alpha rho₁ sigma₁ hrho₁ hsigma₁ +
        w26PetzQuantumRenyiDivergenceFinite alpha rho₂ sigma₂ hrho₂ hsigma₂ := by
  by_cases halpha_zero : (alpha : ℝ) = 0
  · have halpha : alpha = (⟨0, by norm_num⟩ : W26PetzRenyiFiniteOrder) := by
      apply Subtype.ext
      exact halpha_zero
    subst alpha
    exact w26PetzQuantumRenyiDivergenceFinite_tensorMap_zero
      rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂
  · by_cases halpha_one : (alpha : ℝ) = 1
    · have halpha : alpha = (⟨1, by norm_num⟩ : W26PetzRenyiFiniteOrder) := by
        apply Subtype.ext
        exact halpha_one
      subst alpha
      exact w26PetzQuantumRenyiDivergenceFinite_tensorMap_one
        rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂
    · exact w26PetzQuantumRenyiDivergenceFinite_tensorMap_of_ne_zero_one
        alpha rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂
        halpha_zero halpha_one

/-- A pair of orthogonal rank-one density projections resolving the identity. -/
structure PetzBinaryPurePair (E : Type u) [Qudit E] where
  pure₀ : L E
  pure₁ : L E
  pure₀_density : IsDensity pure₀
  pure₁_density : IsDensity pure₁
  pure₀_idempotent : IsIdempotentElem pure₀
  pure₁_idempotent : IsIdempotentElem pure₁
  orthogonal : pure₀ * pure₁ = 0
  resolution : pure₀ + pure₁ = 1

/-- The equal mixture associated with a binary orthogonal pure pair. -/
noncomputable def PetzBinaryPurePair.uniform
    {E : Type u} [Qudit E] (_pair : PetzBinaryPurePair E) : L E :=
  ((2 : ℂ)⁻¹) • (1 : L E)

theorem PetzBinaryPurePair.uniform_density
    {E : Type u} [Qudit E] (pair : PetzBinaryPurePair E) :
    IsDensity pair.uniform := by
  have htrace_one : Tr (1 : L E) = 2 := by
    calc
      Tr (1 : L E) = Tr (pair.pure₀ + pair.pure₁) :=
        congrArg Tr pair.resolution.symm
      _ = Tr pair.pure₀ + Tr pair.pure₁ := by rw [map_add]
      _ = 2 := by rw [pair.pure₀_density.2, pair.pure₁_density.2]; norm_num
  constructor
  · apply (LinearMap.nonneg_iff_isPositive _).mp
    rw [PetzBinaryPurePair.uniform]
    rw [show (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num]
    exact smul_nonneg (Complex.zero_le_real.mpr
      (show 0 ≤ (2 : ℝ)⁻¹ by norm_num))
      (show (0 : L E) ≤ 1 from zero_le_one)
  · rw [PetzBinaryPurePair.uniform, map_smul, htrace_one]
    norm_num

private theorem w26PetzSupportRpow_pureProjection
    {E : Type u} [Qudit E] [Nontrivial E]
    (P : L E) (hP : IsDensity P) (hPid : IsIdempotentElem P) (p : ℝ) :
    petzSupportRpow P p = P := by
  have hPnonneg : (0 : L E) ≤ P :=
    (LinearMap.nonneg_iff_isPositive P).mpr hP.1
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero]
    have hprojection : P.IsSymmetricProjection :=
      ⟨hPid, hP.1.isSymmetric⟩
    obtain ⟨_, hstar⟩ :=
      LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hprojection
    exact hstar.symm
  · rw [petzSupportRpow_of_ne_zero P hp,
      CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hPnonneg]
    calc
      cfc (fun x : ℝ => x ^ p) P = cfc (fun x : ℝ => x) P := by
        apply cfc_congr
        intro x hx
        have hx01 : x ∈ ({0, 1} : Set ℝ) :=
          (isIdempotentElem_iff_spectrum_subset ℝ P
            (IsSelfAdjoint.of_nonneg hPnonneg)).mp hPid hx
        rcases hx01 with hx0 | hx1
        · rw [Set.mem_singleton_iff.mp hx0]
          exact Real.zero_rpow hp
        · rw [Set.mem_singleton_iff.mp hx1]
          exact Real.one_rpow p
      _ = P := cfc_id' ℝ P

private theorem w26AlgebraMapNNReal_eq_smul_one
    {E : Type u} [Qudit E] (x : NNReal) :
    algebraMap NNReal (L E) x = (((x : ℝ) : ℂ) • (1 : L E)) := by
  calc
    algebraMap NNReal (L E) x = algebraMap NNReal (L E) x * 1 := by rw [mul_one]
    _ = x • (1 : L E) := (Algebra.smul_def x (1 : L E)).symm
    _ = (((x : ℝ) : ℂ) • (1 : L E)) := rfl

private theorem w26PetzSupportRpow_binaryUniform
    {E : Type u} [Qudit E] [Nontrivial E]
    (pair : PetzBinaryPurePair E) (p : ℝ) :
    petzSupportRpow pair.uniform p =
      algebraMap NNReal (L E) ((2 : NNReal)⁻¹ ^ p) := by
  have huniform : pair.uniform = algebraMap NNReal (L E) (2 : NNReal)⁻¹ := by
    rw [w26AlgebraMapNNReal_eq_smul_one]
    norm_num [PetzBinaryPurePair.uniform]
  by_cases hp : p = 0
  · subst p
    rw [petzSupportRpow_zero]
    have hrange : LinearMap.range pair.uniform = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine ⟨(2 : ℂ) • x, ?_⟩
      simp [PetzBinaryPurePair.uniform]
    have hstar : (LinearMap.range pair.uniform).starProjection.toLinearMap =
        (1 : L E) := by
      ext x
      exact Submodule.starProjection_eq_self_iff.mpr (by
        rw [hrange]
        trivial)
    rw [hstar, w26AlgebraMapNNReal_eq_smul_one]
    ext x
    simp
  · rw [petzSupportRpow_of_ne_zero pair.uniform hp, huniform,
      CFC.rpow_eq_pow, CFC.rpow_algebraMap]

theorem PetzBinaryPurePair.supportTracePower_pure_uniform
    {E : Type u} [Qudit E] [Nontrivial E]
    (pair : PetzBinaryPurePair E) (alpha : ℝ) :
    petzSupportTracePower alpha pair.pure₀ pair.uniform =
      (2 : ℝ)⁻¹ ^ (1 - alpha) := by
  unfold petzSupportTracePower
  rw [w26PetzSupportRpow_pureProjection pair.pure₀ pair.pure₀_density
      pair.pure₀_idempotent alpha,
    w26PetzSupportRpow_binaryUniform pair (1 - alpha)]
  have hmul : pair.pure₀ *
      algebraMap NNReal (L E) ((2 : NNReal)⁻¹ ^ (1 - alpha)) =
      ((((2 : NNReal)⁻¹ ^ (1 - alpha) : NNReal) : ℝ) : ℂ) • pair.pure₀ := by
    rw [w26AlgebraMapNNReal_eq_smul_one]
    ext x
    simp
  rw [hmul, map_smul, pair.pure₀_density.2, smul_eq_mul,
    mul_one, Complex.ofReal_re, NNReal.coe_rpow]
  congr 1

private theorem w26AlgebraMapReal_eq_smul_one
    {E : Type u} [Qudit E] (x : ℝ) :
    algebraMap ℝ (L E) x = (((x : ℝ) : ℂ) • (1 : L E)) := by
  calc
    algebraMap ℝ (L E) x = algebraMap ℝ (L E) x * 1 := by rw [mul_one]
    _ = x • (1 : L E) := (Algebra.smul_def x (1 : L E)).symm
    _ = (((x : ℝ) : ℂ) • (1 : L E)) := rfl

private theorem w26PetzBinaryPurePair_suppLE_uniform
    {E : Type u} [Qudit E] [Nontrivial E]
    (pair : PetzBinaryPurePair E) : suppLE pair.pure₀ pair.uniform := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hxzero : x = 0 := by
    simpa [PetzBinaryPurePair.uniform] using hx
  simp [hxzero]

private theorem w26CFCLog_pureProjection_eq_zero
    {E : Type u} [Qudit E] [Nontrivial E]
    (P : L E) (hP : IsDensity P) (hPid : IsIdempotentElem P) :
    CFC.log P = 0 := by
  have hPnonneg : (0 : L E) ≤ P :=
    (LinearMap.nonneg_iff_isPositive P).mpr hP.1
  change cfc Real.log P = 0
  calc
    cfc Real.log P = cfc (fun _x : ℝ => 0) P := by
      apply cfc_congr
      intro x hx
      have hx01 : x ∈ ({0, 1} : Set ℝ) :=
        (isIdempotentElem_iff_spectrum_subset ℝ P
          (IsSelfAdjoint.of_nonneg hPnonneg)).mp hPid hx
      rcases hx01 with hx0 | hx1
      · rw [Set.mem_singleton_iff.mp hx0]
        simp
      · rw [Set.mem_singleton_iff.mp hx1]
        simp
    _ = 0 := by simp

theorem PetzBinaryPurePair.umegakiNorm_pure_uniform
    {E : Type u} [Qudit E] [Nontrivial E]
    (pair : PetzBinaryPurePair E) :
    umegakiNorm pair.pure₀ pair.uniform = Real.log 2 := by
  have huniform : pair.uniform = algebraMap ℝ (L E) (2 : ℝ)⁻¹ := by
    rw [w26AlgebraMapReal_eq_smul_one]
    norm_num [PetzBinaryPurePair.uniform]
  unfold umegakiNorm
  rw [w26CFCLog_pureProjection_eq_zero pair.pure₀ pair.pure₀_density
      pair.pure₀_idempotent,
    huniform, CFC.log_algebraMap, w26AlgebraMapReal_eq_smul_one]
  have hmul : pair.pure₀ *
      (0 - (((Real.log (2 : ℝ)⁻¹ : ℝ) : ℂ) • (1 : L E))) =
      ((-(Real.log (2 : ℝ)⁻¹) : ℝ) : ℂ) • pair.pure₀ := by
    ext x
    simp
  rw [hmul, map_smul, pair.pure₀_density.2, smul_eq_mul,
    mul_one, Complex.ofReal_re, Real.log_inv]
  norm_num

theorem PetzBinaryPurePair.umegakiRelEntropyNN_pure_uniform
    {E : Type u} [Qudit E] [Nontrivial E]
    (pair : PetzBinaryPurePair E) :
    umegakiRelEntropyNN pair.pure₀ pair.uniform =
      ((Real.log 2 : ℝ) : EReal) := by
  unfold umegakiRelEntropyNN
  rw [if_pos (w26PetzBinaryPurePair_suppLE_uniform pair),
    pair.umegakiNorm_pure_uniform]

theorem w26PetzQuantumRenyiDivergenceFinite_binary_normalization
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : W26PetzRenyiFiniteOrder) (pair : PetzBinaryPurePair E) :
    w26PetzQuantumRenyiDivergenceFinite alpha pair.pure₀ pair.uniform
      pair.pure₀_density pair.uniform_density = 1 := by
  by_cases halpha_zero : (alpha : ℝ) = 0
  · have halpha : alpha = (⟨0, by norm_num⟩ : W26PetzRenyiFiniteOrder) := by
      apply Subtype.ext
      exact halpha_zero
    subst alpha
    have hlogHalf : Real.logb 2 (2 : ℝ)⁻¹ = -1 := by
      rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    have hlogHalf' : Real.logb 2 ((1 : ℝ) / 2) = -1 := by
      convert hlogHalf using 1
      norm_num
    rw [w26PetzQuantumRenyiDivergenceFinite_zero_eq_supportTracePower,
      pair.supportTracePower_pure_uniform]
    norm_num [Real.rpow_one, hlogHalf']
  · by_cases halpha_one : (alpha : ℝ) = 1
    · have halpha : alpha = (⟨1, by norm_num⟩ : W26PetzRenyiFiniteOrder) := by
        apply Subtype.ext
        exact halpha_one
      subst alpha
      have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      rw [w26PetzQuantumRenyiDivergenceFinite, dif_neg one_ne_zero,
        dif_pos rfl]
      change petzQuantumRenyiDivergence petzRenyiOrderOne
        pair.pure₀ pair.uniform pair.pure₀_density pair.uniform_density = 1
      rw [petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
        pair.umegakiRelEntropyNN_pure_uniform, ← EReal.coe_mul]
      norm_cast
      exact one_div_mul_cancel hlogTwo
    · rw [w26PetzQuantumRenyiDivergenceFinite, dif_neg halpha_zero,
        dif_neg halpha_one, dif_pos
          (Or.inl (w26PetzBinaryPurePair_suppLE_uniform pair))]
      dsimp only
      rw [pair.supportTracePower_pure_uniform,
        Real.logb_rpow_eq_mul_logb_of_pos (by positivity),
        Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
      norm_cast
      rw [show ((Int.negSucc 0 : ℤ) : ℝ) = -1 by norm_num]
      calc
        ((alpha : ℝ) - 1)⁻¹ * ((1 - (alpha : ℝ)) * (-1)) =
            ((alpha : ℝ) - 1)⁻¹ * ((alpha : ℝ) - 1) := by ring
        _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr halpha_one)

/-! ## Public finite-order interface -/

/-- Every nonnegative real number, viewed as a finite Petz Rényi order. -/
abbrev PetzRenyiFiniteOrder := W26PetzRenyiFiniteOrder

/-- A finite Petz order at most two, viewed as an order in the closed interval `[0, 2]`
(`PetzRenyiOrder`). -/
def PetzRenyiFiniteOrder.toClosed
    (alpha : PetzRenyiFiniteOrder) (halpha : (alpha : ℝ) ≤ 2) :
    PetzRenyiOrder :=
  ⟨alpha, alpha.property, halpha⟩

/-- The Petz quantum Rényi divergence in bits at an arbitrary finite
nonnegative order.  At orders zero and one it reuses the uniquely extended
endpoint values of the closed-interval definition. -/
noncomputable def petzQuantumRenyiDivergenceFinite
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : PetzRenyiFiniteOrder) (rho sigma : L E)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) : EReal :=
  w26PetzQuantumRenyiDivergenceFinite alpha rho sigma hrho hsigma

/-- The all-finite-order definition agrees with the closed-interval definition on
the whole closed interval `[0, 2]`. -/
theorem petzQuantumRenyiDivergenceFinite_compatibility
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : PetzRenyiFiniteOrder) (halpha : (alpha : ℝ) ≤ 2)
    (rho sigma : L E) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzQuantumRenyiDivergenceFinite alpha rho sigma hrho hsigma =
      petzQuantumRenyiDivergence (PetzRenyiFiniteOrder.toClosed alpha halpha)
        rho sigma hrho hsigma := by
  exact w26PetzQuantumRenyiDivergenceFinite_compatibility
    alpha halpha rho sigma hrho hsigma

/-- Tensor products of density operators are density operators. -/
theorem isDensity_tensorProduct
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (rho : L E) (sigma : L F) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    IsDensity (TensorProduct.map rho sigma : L (E ⊗[ℂ] F)) :=
  w26IsDensity_tensorMap rho sigma hrho hsigma

/-- Binary pure-versus-uniform normalization is one bit at every finite
nonnegative order. -/
theorem petzQuantumRenyiDivergenceFinite_binary_normalization
    {E : Type u} [Qudit E] [Nontrivial E]
    (alpha : PetzRenyiFiniteOrder) (pair : PetzBinaryPurePair E) :
    petzQuantumRenyiDivergenceFinite alpha pair.pure₀ pair.uniform
      pair.pure₀_density pair.uniform_density = 1 :=
  w26PetzQuantumRenyiDivergenceFinite_binary_normalization alpha pair

/-- Petz Rényi divergence is additive on density tensor pairs at every
finite nonnegative order. -/
theorem petzQuantumRenyiDivergenceFinite_tensorProduct
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (alpha : PetzRenyiFiniteOrder)
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    petzQuantumRenyiDivergenceFinite alpha
        (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F))
        (TensorProduct.map sigma₁ sigma₂)
        (isDensity_tensorProduct rho₁ rho₂ hrho₁ hrho₂)
        (isDensity_tensorProduct sigma₁ sigma₂ hsigma₁ hsigma₂) =
      petzQuantumRenyiDivergenceFinite alpha rho₁ sigma₁ hrho₁ hsigma₁ +
        petzQuantumRenyiDivergenceFinite alpha rho₂ sigma₂ hrho₂ hsigma₂ :=
  w26PetzQuantumRenyiDivergenceFinite_tensorMap alpha
    rho₁ sigma₁ rho₂ sigma₂ hrho₁ hsigma₁ hrho₂ hsigma₂

end OPT
