/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.BlockExtensionOrder
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionSpectrum

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionLimit

/-!
Finite-dimensional block-extension limiting argument for Proposition 5.1.5.

This module carries the heavy finite-span CFC limiting payload used by the
finite-dimensional monotonicity and convexity bridge surfaces.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology MatrixOrder CStarAlgebra
open Filter
open HansenPedersen.Internal

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem blockExtension_normal_of_selfAdjoint_subtype
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [U.HasOrthogonalProjection] [CompleteSpace ↥Uᗮ]
    {A : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) :
    IsStarNormal (blockExtensionDiag (U := U) A t₀) := by
  letI : CompleteSpace U := instCompleteSpaceSortFromSubtype (U := U)
  letI : CompleteSpace Uᗮ := instCompleteSpaceSortFromSubtype (U := Uᗮ)
  simpa [blockExtensionDiag] using
    (block_extension_normal_of_selfAdjoint (ℋ := ℋ) (U := U) (A := A) (t₀ := t₀) hA)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem blockExtension_normal_pair_of_selfAdjoint_subtype
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [U.HasOrthogonalProjection] [CompleteSpace ↥Uᗮ]
    {A B : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsStarNormal (blockExtensionDiag (U := U) A t₀) ∧
      IsStarNormal (blockExtensionDiag (U := U) B t₀) := by
  constructor
  · exact
      blockExtension_normal_of_selfAdjoint_subtype
        (ℋ := ℋ) (U := U) (A := A) (t₀ := t₀) hA
  · exact
      blockExtension_normal_of_selfAdjoint_subtype
        (ℋ := ℋ) (U := U) (A := B) (t₀ := t₀) hB

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem hilbertFiniteSpan_blockExtension_normal_pair
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) {A B : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    ∀ s : Finset ι,
      IsStarNormal
          (blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) A t₀) ∧
        IsStarNormal
          (blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) B t₀) := by
  intro s
  exact
    blockExtension_normal_pair_of_selfAdjoint_subtype
      (ℋ := ℋ) (U := hilbertFiniteSpan (ℋ := ℋ) b s) (A := A) (B := B) (t₀ := t₀) hA hB

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem hilbertFiniteSpan_blockExtension_normal_named
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) {A : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) :
    ∀ s : Finset ι,
      IsStarNormal
        (((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) * A *
          ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) +
          (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) := by
  intro s
  simpa [blockExtensionDiag] using
    (blockExtension_normal_of_selfAdjoint_subtype
      (ℋ := ℋ) (U := hilbertFiniteSpan (ℋ := ℋ) b s) (A := A) (t₀ := t₀) hA)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem hilbertFiniteSpan_blockExtension_normal_family
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) {A : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) :
    ∀ s : Finset ι,
      IsStarNormal (blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) A t₀) := by
  intro s
  exact
    blockExtension_normal_of_selfAdjoint_subtype
      (ℋ := ℋ) (U := hilbertFiniteSpan (ℋ := ℋ) b s) (A := A) (t₀ := t₀) hA

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem hilbertFiniteSpan_blockExtension_normal_family_pair
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) {A B : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (∀ s : Finset ι,
        IsStarNormal
          (((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) * A *
            ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) +
            (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection))) ∧
      ∀ s : Finset ι,
        IsStarNormal
          (((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) * B *
            ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) +
            (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) := by
  constructor
  · intro s
    exact hilbertFiniteSpan_blockExtension_normal_named (ℋ := ℋ) b (A := A) (t₀ := t₀) hA s
  · intro s
    exact hilbertFiniteSpan_blockExtension_normal_named (ℋ := ℋ) b (A := B) (t₀ := t₀) hB s

omit [Nontrivial (L ℋ)] in
private theorem hilbertFiniteSpan_block_extension_complex_spectrum_subset_pair_named
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {Ω : Set ℂ}
    (hΩ : Ω = Complex.ofReal '' Set.Icc α β)
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    ∀ s : Finset ι,
      spectrum ℂ (blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) A t₀) ⊆ Ω ∧
        spectrum ℂ
          (blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) B t₀) ⊆ Ω := by
  subst hΩ
  intro s
  constructor
  · simpa [blockExtensionDiag] using
      (hilbertFiniteSpan_block_extension_complex_spectrum_subset
        (ℋ := ℋ) b (A := A) (hA := hA) (hA_bounds := hA_bounds) (ht₀ := ht₀) s)
  · simpa [blockExtensionDiag] using
      (hilbertFiniteSpan_block_extension_complex_spectrum_subset
        (ℋ := ℋ) b (A := B) (hA := hB) (hA_bounds := hB_bounds) (ht₀ := ht₀) s)

private theorem hilbertFiniteSpan_block_extension_cfc_pair_tendsto
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hAγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀) A)
    (hBγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀) B) :
    SOTTendsto (ℋ := ℋ)
        (hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g A t₀)
        (cfcNormal (ℋ := ℋ) g A) ∧
      SOTTendsto (ℋ := ℋ)
        (hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g B t₀)
        (cfcNormal (ℋ := ℋ) g B) := by
  have hABblock_normal :=
    hilbertFiniteSpan_blockExtension_normal_family_pair
      (ℋ := ℋ) b (A := A) (B := B) (t₀ := t₀) hA hB
  have ht₀Icc : t₀ ∈ Set.Icc α β := hHull (Or.inr (by simp))
  have hσABtilde :=
    hilbertFiniteSpan_block_extension_complex_spectrum_subset_pair_named
      (ℋ := ℋ) b (A := A) (B := B) (α := α) (β := β) (t₀ := t₀)
      (Ω := Complex.ofReal '' Set.Icc α β) rfl
      hA hA_bounds hB hB_bounds ht₀Icc
  have hσABΩ :=
    complex_spectrum_subset_pair_of_real_hull (K := ℋ) (t₀ := t₀) hA hB hHull
  exact
    SOTTendsto.cfcNormal_pair (Ω := Complex.ofReal '' Set.Icc α β) (f := g)
      (Aγ := hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀)
      (Bγ := hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀)
      hΩ hABblock_normal.1 hABblock_normal.2
      (hA.isStarNormal) (hB.isStarNormal)
      (fun s => (hσABtilde s).1)
      (fun s => (hσABtilde s).2)
      hσABΩ hgΩ hAγ_tendsto hBγ_tendsto

@[reducible] private noncomputable def hilbertFiniteSpanBlockExtensionCfcPairTendstoDef
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hAγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀) A)
    (hBγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀) B) :
    SOTTendsto (ℋ := ℋ)
        (hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g A t₀)
        (cfcNormal (ℋ := ℋ) g A) ∧
      SOTTendsto (ℋ := ℋ)
        (hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g B t₀)
        (cfcNormal (ℋ := ℋ) g B) :=
  hilbertFiniteSpan_block_extension_cfc_pair_tendsto
    (ℋ := ℋ) b (A := A) (B := B) (α := α) (β := β) (t₀ := t₀) (g := g)
    hΩ hgΩ hA hA_bounds hB hB_bounds hHull hAγ_tendsto hBγ_tendsto

private theorem hilbertFiniteSpan_block_extension_cfc_sub_tendsto_eval
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hAγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀) A)
    (hBγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀) B)
    (x : ℋ) :
    Tendsto
      (fun s : Finset ι =>
        (cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀ s) -
          cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s)) x)
      atTop
      (𝓝 ((cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A) x)) := by
  have hcfAB :=
    hilbertFiniteSpanBlockExtensionCfcPairTendstoDef
      (ℋ := ℋ) b hΩ hgΩ hA hA_bounds hB hB_bounds hHull hAγ_tendsto hBγ_tendsto
  simpa [hilbertFiniteSpanBlockCfcFamily, hilbertFiniteSpanBlockFamily,
    sub_eq_add_neg, ContinuousLinearMap.sub_apply] using ((hcfAB.2 x).sub (hcfAB.1 x))

@[reducible] private noncomputable def
    hilbertFiniteSpanBlockExtensionCfcSubTendstoDef
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hAγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀) A)
    (hBγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀) B) :
    ∀ x : ℋ,
      Tendsto
        (fun s : Finset ι =>
          (cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀ s) -
            cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s)) x)
        atTop
        (𝓝 ((cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A) x)) :=
  fun x =>
    hilbertFiniteSpan_block_extension_cfc_sub_tendsto_eval
      (ℋ := ℋ) b hΩ hgΩ hA hA_bounds hB hB_bounds hHull hAγ_tendsto hBγ_tendsto x

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem cfcNormal_le_of_blockCfcFamily
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {t₀ : ℝ} {g : ℂ → ℂ}
    (hself_target :
      IsSelfAdjoint
        (cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A))
    (hblock_cfc :
      ∀ s : Finset ι,
        hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g A t₀ s ≤
          hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g B t₀ s)
    (hsub_tendsto :
      ∀ x : ℋ,
        Tendsto
          (fun s : Finset ι =>
            (cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀ s) -
              cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s)) x)
          atTop
          (𝓝 ((cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A) x))) :
    cfcNormal (ℋ := ℋ) g A ≤ cfcNormal (ℋ := ℋ) g B := by
  exact
    le_of_sub_clm_tendsto_of_pointwise_le (ℋ := ℋ)
      (Aγ := hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g A t₀)
      (Bγ := hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g B t₀)
      (A := cfcNormal (ℋ := ℋ) g A) (B := cfcNormal (ℋ := ℋ) g B)
      hself_target hblock_cfc hsub_tendsto

private theorem cfcNormal_le_of_hilbertFiniteSpanBlockFamily
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {f : ℝ → ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hblock :
      ∀ s : Finset ι,
        cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s) ≤
          cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀ s))
    (hAγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀) A)
    (hBγ_tendsto :
      SOTTendsto (ℋ := ℋ) (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀) B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    cfcNormal (ℋ := ℋ) g A ≤ cfcNormal (ℋ := ℋ) g B := by
  have hself_target :
      IsSelfAdjoint
        (cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A) := by
    exact isSelfAdjointCfcNormalSubPairHilbertDef (f := f) (g := g) (A := A) (B := B) hA hB hg
  have hblock_cfc :
      ∀ s : Finset ι,
        hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g A t₀ s ≤
          hilbertFiniteSpanBlockCfcFamily (ℋ := ℋ) b g B t₀ s := by
    simpa [hilbertFiniteSpanBlockCfcFamily] using hblock
  exact
    cfcNormal_le_of_blockCfcFamily
      (ℋ := ℋ) (b := b) (A := A) (B := B) (t₀ := t₀) (g := g)
      hself_target hblock_cfc
      (hilbertFiniteSpanBlockExtensionCfcSubTendstoDef
        (ℋ := ℋ) b hΩ hgΩ hA hA_bounds hB hB_bounds hHull hAγ_tendsto hBγ_tendsto)

@[reducible] private noncomputable def
    cfcNormalLeOfHilbertFiniteSpanBlockFamilyHilbertFromBlockTendstoDef
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A B : L ℋ} {α β t₀ : ℝ} {f : ℝ → ℝ} {g : ℂ → ℂ}
    (hΩ : IsCompact (Complex.ofReal '' Set.Icc α β))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB : IsSelfAdjoint B)
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β)
    (hblock :
      ∀ s : Finset ι,
        cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s) ≤
          cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b B t₀ s))
    (hAtilde_tendsto :
      SOTTendsto (ℋ := ℋ)
        (fun s : Finset ι =>
          (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * A *
              (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
            (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) A)
    (hBtilde_tendsto :
      SOTTendsto (ℋ := ℋ)
        (fun s : Finset ι =>
          (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * B *
              (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
            (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    cfcNormal (ℋ := ℋ) g A ≤ cfcNormal (ℋ := ℋ) g B :=
  cfcNormal_le_of_hilbertFiniteSpanBlockFamily
    b hΩ hgΩ hA hA_bounds hB hB_bounds hHull hblock
    (by
      change
        SOTTendsto (ℋ := ℋ)
          (fun s : Finset ι =>
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * A *
                (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
              (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) A
      exact hAtilde_tendsto)
    (by
      change
        SOTTendsto (ℋ := ℋ)
          (fun s : Finset ι =>
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * B *
                (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
              (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) B
      exact hBtilde_tendsto)
    hg

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Reformulation of Proposition 5.1.5(1): matrix monotonicity implies
`H`-operator monotonicity for every complex Hilbert space.
Source: Hiai--Yanagi, Proposition 5.1.5(1). -/
def MatrixMonotoneImpliesAllHOperatorMonotone : Prop :=
  ∀ {J : Set ℝ} {f : ℝ → ℝ},
    Convex ℝ J →
    ContinuousOn f J →
    _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval J f →
    AllHOperatorMonotoneOnInterval.{u} J f

namespace BlockExtensionInternal

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Nonnegative-spectrum class for endomorphisms of a complete submodule
(`Sort`-coercion spelling), extracted from the finite-span compression proof of
Proposition 5.1.5 (1) so that the associated scalar-action instance searches
elaborate once. -/
theorem nonnegSpectrumClass_submoduleEndSort
    (U : Submodule ℂ ℋ) (hUSortComplete : CompleteSpace U) :
    NonnegSpectrumClass ℝ (U →L[ℂ] U) := by
  exact @ContinuousLinearMap.instNonnegSpectrumClassRealId ℂ U _ _ _ hUSortComplete _
    (instIsScalarTowerRealComplexSubmoduleEndSort (U := U))

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The block-CFC comparison on one nonzero finite-dimensional subspace `V`; the finite-span
statement below specialises it to `V = hilbertFiniteSpan b s`. -/
private theorem blockExtension_cfcNormal_le_of_finiteDimensional
    {J : Set ℝ} {f : ℝ → ℝ} {α β t₀ : ℝ}
    (hfJ : ContinuousOn f J)
    (hmat : _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval J f)
    (hIccJ : Set.Icc α β ⊆ J)
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hgΩ : ContinuousOn (fun z : ℂ => (f z.re : ℂ)) (Complex.ofReal '' Set.Icc α β))
    (V : Submodule ℂ ℋ) [FiniteDimensional ℂ V] [Nontrivial V]
    (hscalar :
      spectrum ℂ ((t₀ : ℂ) • (1 : ↥Vᗮ →L[ℂ] ↥Vᗮ)) ⊆ Complex.ofReal '' Set.Icc α β) :
    cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        (V.starProjection * A * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection)) ≤
      cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        (V.starProjection * B * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection)) := by
  let g : ℂ → ℂ := fun z => (f z.re : ℂ)
  let A_sub : V →L[ℂ] V := V.orthogonalProjection ∘L A ∘L V.subtypeL
  let B_sub : V →L[ℂ] V := V.orthogonalProjection ∘L B ∘L V.subtypeL
  have hUSubComplete : CompleteSpace ↥V := instCompleteSpaceSubtypeFromSort (U := V)
  have hUorthSubComplete : CompleteSpace ↥(Vᗮ) :=
    instCompleteSpaceSubtypeFromSort (U := Vᗮ)
  have hUSortComplete : CompleteSpace V := instCompleteSpaceSortFromSubtype (U := V)
  have hUorthSortComplete : CompleteSpace (Vᗮ) :=
    instCompleteSpaceSortFromSubtype (U := Vᗮ)
  letI : CompleteSpace ↥V := hUSubComplete
  letI : CompleteSpace ↥(Vᗮ) := hUorthSubComplete
  letI : CompleteSpace V := hUSortComplete
  letI : CompleteSpace (Vᗮ) := hUorthSortComplete
  letI : StarOrderedRing (V →L[ℂ] V) :=
    show StarOrderedRing (V →L[ℂ] V) from
      @ContinuousLinearMap.instStarOrderedRing V _ _ hUSortComplete
  letI : CStarAlgebra (V →L[ℂ] V) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace V _ _ hUSortComplete
  have hUNonnegSub : NonnegSpectrumClass ℝ (↥V →L[ℂ] ↥V) :=
    nonnegSpectrumClass_submoduleEndSubtype (ℋ := ℋ) V hUSubComplete
  letI : NonnegSpectrumClass ℝ (↥V →L[ℂ] ↥V) := hUNonnegSub
  letI : ContinuousFunctionalCalculus ℂ (V →L[ℂ] V) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI hRealCfc : ContinuousFunctionalCalculus ℝ (↥V →L[ℂ] ↥V) IsSelfAdjoint := by
    infer_instance
  /- Step 2: Make the compressed restrictions self-adjoint so their real CFCs are available. -/
  have hA_sub_sa : IsSelfAdjoint A_sub := by
    have hsym :
        ((A_sub : ↥V →L[ℂ] ↥V) :
          ↥V →ₗ[ℂ] ↥V).IsSymmetric := by
      intro x y
      simpa [A_sub, compressionCLM, Submodule.subtypeL_apply] using
        hA.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ ↥V _ _ _ hUSubComplete A_sub hsym
  have hB_sub_sa : IsSelfAdjoint B_sub := by
    have hsym :
        ((B_sub : ↥V →L[ℂ] ↥V) :
          ↥V →ₗ[ℂ] ↥V).IsSymmetric := by
      intro x y
      simpa [B_sub, compressionCLM, Submodule.subtypeL_apply] using
        hB.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ ↥V _ _ _ hUSubComplete B_sub hsym
  have hUOrth : V.HasOrthogonalProjection := inferInstance
  /- Step 3: Inherit spectral bounds and A_sub <= B_sub from the ambient operators. -/
  have hA_sub_Icc : spectrum ℝ A_sub ⊆ Set.Icc α β :=
    (@compression_spectrum_subset_Icc ℋ _ _ _ V hUSubComplete hUOrth
      (instStarOrderedRingSubtypeSubmoduleEnd (U := V))
      (show AddRightMono (↥V →L[ℂ] ↥V) from inferInstance)
      hUNonnegSub
      hRealCfc
      A α β hA hA_bounds.1 hA_bounds.2)
  have hB_sub_Icc : spectrum ℝ B_sub ⊆ Set.Icc α β :=
    (@compression_spectrum_subset_Icc ℋ _ _ _ V hUSubComplete hUOrth
      (instStarOrderedRingSubtypeSubmoduleEnd (U := V))
      (show AddRightMono (↥V →L[ℂ] ↥V) from inferInstance)
      hUNonnegSub
      hRealCfc
      B α β hB hB_bounds.1 hB_bounds.2)
  have hsub_le : A_sub ≤ B_sub := compression_le_of_le (U := V) hAB
  /- Step 4: Apply finite-dimensional matrix monotonicity to the compressed operators. -/
  have hsub_fc :
      cfc (R := ℝ) f A_sub ≤ cfc (R := ℝ) f B_sub :=
    by
      exact
        @matrixOperatorMonotoneOnInterval_of_finiteDimensional
          ↥V _ _ hUSubComplete _
          hRealCfc
          (by infer_instance : Nontrivial (↥V →L[ℂ] ↥V))
          J f hfJ hmat A_sub B_sub hA_sub_sa hB_sub_sa
          (by intro x hx; exact hIccJ (hA_sub_Icc hx))
          (by intro x hx; exact hIccJ (hB_sub_Icc hx))
          hsub_le
  /- Step 5: Transport the compressed CFC inequality through the block model. -/
  have hblock_s :
      cfcNormal (ℋ := ℋ) g
          (V.starProjection * A * V.starProjection +
            (t₀ : ℂ) • (1 - V.starProjection)) ≤
        cfcNormal (ℋ := ℋ) g
          (V.starProjection * B * V.starProjection +
            (t₀ : ℂ) • (1 - V.starProjection)) := by
    exact
      blockExtensionDiagCfcMonoFromSubtypeIntervalPacked
        (U := V) (f := f) (g := g) (A := A) (B := B) (α := α) (β := β) (t₀ := t₀)
        hUNonnegSub
        (subtypeSubmoduleEndStarNormalCfcDef (U := V))
        (subtypeSubmoduleEndStarNormalCfcDef (U := Vᗮ))
        (subtypeSubmodulePairEndStarNormalCfcDef (U := V))
        hRealCfc
      rfl hgΩ hA_sub_sa hA_sub_Icc hB_sub_sa hB_sub_Icc hscalar hsub_fc
  exact hblock_s

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Per-block CFC comparison for the finite-span compression step of
Proposition 5.1.5 (1): on a nonempty finite span `hilbertFiniteSpan b s`, the
compressed operator inequality transports through the block-extension normal
CFC.  Extracted from `matrixMonotoneImpliesOperatorMonotone_core` so that the
heavy subspace instance elaboration and the packed block-CFC comparison
elaborate in their own declaration. -/
private theorem hilbertFiniteSpan_blockExtension_cfcNormal_le
    {J : Set ℝ} {f : ℝ → ℝ} {α β t₀ : ℝ}
    (hfJ : ContinuousOn f J)
    (hmat : _root_.Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval J f)
    (hIccJ : Set.Icc α β ⊆ J)
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hgΩ : ContinuousOn (fun z : ℂ => (f z.re : ℂ)) (Complex.ofReal '' Set.Icc α β))
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (s : Finset ι) (hs0 : s ≠ ∅)
    (hscalar :
      spectrum ℂ
          ((t₀ : ℂ) •
            (1 : ↥((hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ) →L[ℂ]
              ↥((hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ))) ⊆
        Complex.ofReal '' Set.Icc α β) :
    cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * A *
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
          (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) ≤
      cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * B *
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
          (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) := by
  haveI : Nontrivial (hilbertFiniteSpan (ℋ := ℋ) b s) :=
    nontrivial_hilbertFiniteSpan_of_ne_empty (ℋ := ℋ) b hs0
  exact blockExtension_cfcNormal_le_of_finiteDimensional (ℋ := ℋ) hfJ hmat hIccJ hA hB hAB
    hA_bounds hB_bounds hgΩ (hilbertFiniteSpan (ℋ := ℋ) b s) hscalar

/-- Core proof of Proposition 5.1.5(1): matrix monotonicity on a convex
interval implies operator monotonicity on the ambient Hilbert space.  The proof
approximates by finite Hilbert-basis spans, applies the finite-dimensional
matrix bridge on each compression, and passes to the strong-operator limit.
Source: Hiai--Yanagi, Proposition 5.1.5(1). -/
theorem matrixMonotoneImpliesOperatorMonotone_core :
    MatrixMonotoneImpliesOperatorMonotone (ℋ := ℋ) := by
  intro J f hJ hfJ hmat A B hA hB hσA hσB hAB
  /- Step 1: Exclude the empty interval and choose the complement base point. -/
  by_cases hJempty : J = ∅
  · exfalso
    have hσAempty : spectrum ℝ A ⊆ (∅ : Set ℝ) := by simpa [hJempty] using hσA
    have hsA := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
    exact Set.not_nonempty_empty (hsA.mono hσAempty)
  · have hJne : J.Nonempty := by
      by_contra hJnone
      exact hJempty ((Set.not_nonempty_iff_eq_empty).mp hJnone)
    obtain ⟨t₀, ht₀⟩ := hJne
    obtain ⟨α, β, hHull, hIccJ⟩ :=
      exists_compact_interval_subset_of_spectra (ℋ := ℋ) hσA hσB ht₀ hJ
    /- Step 2: Enclose the spectra in one compact interval and lift f to normal CFC. -/
    let g : ℂ → ℂ := fun z => (f z.re : ℂ)
    let Ω : Set ℂ := Complex.ofReal '' Set.Icc α β
    have hΩ : IsCompact Ω := by
      simpa [Ω] using (isCompact_Icc.image Complex.continuous_ofReal)
    have hgΩ : ContinuousOn g Ω := by
      have hMaps : Set.MapsTo (fun w : ℂ => w.re) Ω J := by
        intro w hw
        rcases hw with ⟨r, hr, rfl⟩
        exact hIccJ hr
      have hfre : ContinuousOn (fun w : ℂ => f (w.re)) Ω :=
        hfJ.comp Complex.continuous_re.continuousOn hMaps
      simpa [g] using Complex.continuous_ofReal.comp_continuousOn' hfre
    have hA_bounds :
        (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ) := by
      apply order_bounds_of_spectrum_subset_Icc (ℋ := ℋ) hA
      intro x hx
      exact hHull (Or.inl (Or.inl hx))
    have hB_bounds :
        (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ) := by
      apply order_bounds_of_spectrum_subset_Icc (ℋ := ℋ) hB
      intro x hx
      exact hHull (Or.inl (Or.inr hx))
    /- Step 3: Build finite Hilbert-span block extensions that approximate A and B. -/
    obtain ⟨ι, b, hb⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := ℋ)
    let U : Finset ι → Submodule ℂ ℋ := hilbertFiniteSpan (ℋ := ℋ) b
    let P : Finset ι → L ℋ := fun s => (U s).starProjection
    let A_sub : (s : Finset ι) → (U s →L[ℂ] U s) :=
      fun s => (U s).orthogonalProjection ∘L A ∘L (U s).subtypeL
    let B_sub : (s : Finset ι) → (U s →L[ℂ] U s) :=
      fun s => (U s).orthogonalProjection ∘L B ∘L (U s).subtypeL
    let Atilde : Finset ι → L ℋ :=
      fun s => P s * A * P s + (t₀ : ℂ) • (1 - P s)
    let Btilde : Finset ι → L ℋ :=
      fun s => P s * B * P s + (t₀ : ℂ) • (1 - P s)
    have hP : SOTTendsto (ℋ := ℋ) P 1 := by
      intro x
      simpa [P, U] using hilbertFiniteSpan_starProjection_tendsto_self (ℋ := ℋ) b x
    have hPbound : ∀ s, ‖P s‖ ≤ 1 := by
      simpa [P, U] using hilbertFiniteSpan_starProjection_uniformBound (ℋ := ℋ) b
    /- Step 4: Keep the scalar complement block inside the same compact spectral window. -/
    have hScalar_Icc :
        ∀ s : Finset ι,
          spectrum ℂ (((t₀ : ℂ) • (1 : (U s)ᗮ →L[ℂ] (U s)ᗮ))) ⊆ Ω := by
      intro s
      let V : Type _ := ↥((U s)ᗮ)
      letI : CompleteSpace V := by
        dsimp [V]
        infer_instance
      change spectrum ℂ (((t₀ : ℂ) • (1 : V →L[ℂ] V))) ⊆ Ω
      classical
      rcases subsingleton_or_nontrivial (V →L[ℂ] V) with hV | hV
      · letI : Subsingleton (V →L[ℂ] V) := hV
        simp [Ω]
      · letI : Nontrivial (V →L[ℂ] V) := hV
        intro z hz
        have hz' : z ∈ ({(t₀ : ℂ)} : Set ℂ) := by
          have hz'' : z ∈ spectrum ℂ ((algebraMap ℂ (V →L[ℂ] V)) t₀) := by
            simpa [Algebra.algebraMap_eq_smul_one] using hz
          rw [spectrum.scalar_eq (𝕜 := ℂ) (A := V →L[ℂ] V) (k := t₀)] at hz''
          simpa using hz''
        rcases Set.mem_singleton_iff.mp hz' with rfl
        exact ⟨t₀, hHull (Or.inr (by simp)), by simp⟩
    /- Step 5: Prove the CFC inequality on each finite block, treating the empty span separately. -/
    have hblock :
        ∀ s : Finset ι,
          cfcNormal (ℋ := ℋ) g (Atilde s) ≤
            cfcNormal (ℋ := ℋ) g (Btilde s) := by
      intro s
      by_cases hs0 : s = ∅
      · have hP0 : P s = 0 := by
          subst hs0
          simp [P, U, hilbertFiniteSpan]
        simp [Atilde, Btilde, hP0]
      · exact
          hilbertFiniteSpan_blockExtension_cfcNormal_le (ℋ := ℋ)
            hfJ hmat hIccJ hA hB hAB hA_bounds hB_bounds hgΩ b s hs0 (hScalar_Icc s)
    /- Step 6: Pass finite block inequalities to the SOT limit and return to real CFC. -/
    have hAtilde_tendsto : SOTTendsto (ℋ := ℋ) Atilde A := by
      change
        SOTTendsto (ℋ := ℋ)
          (fun s => P s * A * P s + (t₀ : ℂ) • (1 - P s)) A
      exact block_extension_tendsto_self (ℋ := ℋ) (A := A) (t₀ := t₀) hP hPbound
    have hBtilde_tendsto : SOTTendsto (ℋ := ℋ) Btilde B := by
      change
        SOTTendsto (ℋ := ℋ)
          (fun s => P s * B * P s + (t₀ : ℂ) • (1 - P s)) B
      exact block_extension_tendsto_self (ℋ := ℋ) (A := B) (t₀ := t₀) hP hPbound
    have hnormal : cfcNormal (ℋ := ℋ) g A ≤ cfcNormal (ℋ := ℋ) g B :=
      cfcNormalLeOfHilbertFiniteSpanBlockFamilyHilbertFromBlockTendstoDef
        (ℋ := ℋ) (ι := ι) b (A := A) (B := B) (α := α) (β := β) (t₀ := t₀)
        (f := f) (g := g) hΩ hgΩ hA hA_bounds hB hB_bounds hHull hblock
        hAtilde_tendsto hBtilde_tendsto rfl
    have hrealA : cfcR (ℋ := ℋ) f A = cfcNormal (ℋ := ℋ) g A :=
      realCfc_eq_normalCfc_of_selfAdjoint (K := ℋ) (f := f) hA
    have hrealB : cfcR (ℋ := ℋ) f B = cfcNormal (ℋ := ℋ) g B :=
      realCfc_eq_normalCfc_of_selfAdjoint (K := ℋ) (f := f) hB
    rw [hrealA, hrealB]
    exact hnormal

end BlockExtensionInternal

end NormalCFC514

end HansenPedersen
