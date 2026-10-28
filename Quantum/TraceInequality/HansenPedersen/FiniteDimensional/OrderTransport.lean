/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.CFCTransport
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.CFCTransport
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.OrderTransport

/-!
# Order transport through finite-dimensional compressions

This module provides the order, spectrum, and convergence lemmas used to pass
finite-dimensional functional-calculus inequalities to the ambient Hilbert
space.  It builds the directed net of finite spans of a Hilbert basis, controls
block extensions under strong-operator convergence, and transports CFC
comparisons from compressed submodule operators back to the ambient space.

## Main results

* `hilbertFiniteSpan` and its projection convergence lemmas: finite-dimensional
  subspaces approximating the identity strongly.
* `blockExtensionDiag_cfc_mono_from_subtype_interval`: lifts a compressed
  real-CFC comparison to ambient block extensions.
* `compression_spectrum_subset_Icc` and `compression_le_of_le`: spectrum and
  order control for compressions.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
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

/-- Pair version of `complex_spectrum_subset_of_real_Icc`. -/
theorem complex_spectrum_subset_of_real_Icc_pair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {A B : K →L[ℂ] K} {α β : ℝ}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Icc α β)
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Icc α β) :
    spectrum ℂ A ⊆ Complex.ofReal '' Set.Icc α β ∧
      spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc α β := by
  constructor
  · exact complex_spectrum_subset_of_real_Icc (ℋ := K) hA hσA
  · exact complex_spectrum_subset_of_real_Icc (ℋ := K) hB hσB

/-- If the spectra of two self-adjoint operators and the scalar `t₀` lie in a
real interval, then both complex spectra lie in its complex image. -/
theorem complex_spectrum_subset_pair_of_real_hull
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {A B : K →L[ℂ] K} {α β t₀ : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hHull : spectrum ℝ A ∪ spectrum ℝ B ∪ ({t₀} : Set ℝ) ⊆ Set.Icc α β) :
    spectrum ℂ A ⊆ Complex.ofReal '' Set.Icc α β ∧
      spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc α β := by
  exact complex_spectrum_subset_of_real_Icc_pair (K := K) hA
    (by
      intro x hx
      exact hHull (Or.inl (Or.inl hx)))
    hB
    (by
      intro x hx
      exact hHull (Or.inl (Or.inr hx)))

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
/-- Pair form of normal continuous functional calculus continuity for strong-operator convergence.
Source: Hiai–Yanagi, Lemma 5.1.4. -/
protected theorem SOTTendsto.cfcNormal_pair
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)] {Ω : Set ℂ} {f : ℂ → ℂ}
    {A B : L ℋ} {Aγ Bγ : ι → L ℋ}
    (hΩ : IsCompact Ω)
    (hAγ : ∀ i, IsStarNormal (Aγ i)) (hBγ : ∀ i, IsStarNormal (Bγ i))
    (hA : IsStarNormal A) (hB : IsStarNormal B)
    (hσAγ : ∀ i, spectrum ℂ (Aγ i) ⊆ Ω) (hσBγ : ∀ i, spectrum ℂ (Bγ i) ⊆ Ω)
    (hσAB : spectrum ℂ A ⊆ Ω ∧ spectrum ℂ B ⊆ Ω)
    (hf : ContinuousOn f Ω)
    (hconvA : SOTTendsto (ℋ := ℋ) Aγ A) (hconvB : SOTTendsto (ℋ := ℋ) Bγ B) :
    SOTTendsto (ℋ := ℋ)
        (fun i => cfcNormal (ℋ := ℋ) f (Aγ i)) (cfcNormal (ℋ := ℋ) f A) ∧
      SOTTendsto (ℋ := ℋ)
        (fun i => cfcNormal (ℋ := ℋ) f (Bγ i)) (cfcNormal (ℋ := ℋ) f B) := by
  constructor
  · exact SOTTendsto.cfcNormal (ℋ := ℋ) hΩ hAγ hA hσAγ hσAB.1 hf hconvA
  · exact SOTTendsto.cfcNormal (ℋ := ℋ) hΩ hBγ hB hσBγ hσAB.2 hf hconvB

/-- Pair form of the equality between real CFC of `f` and complex normal CFC
of the extension `z ↦ f z.re` on self-adjoint operators. -/
theorem realCfc_eq_normalCfc_of_selfAdjoint_pair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : K →L[ℂ] K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    cfc (R := ℝ) f A = cfcNormal (ℋ := K) g A ∧
      cfc (R := ℝ) f B = cfcNormal (ℋ := K) g B := by
  subst hg
  constructor
  · exact realCfc_eq_normalCfc_of_selfAdjoint (K := K) (f := f) hA
  · exact realCfc_eq_normalCfc_of_selfAdjoint (K := K) (f := f) hB

/-- Reducible wrapper for `realCfc_eq_normalCfc_of_selfAdjoint_pair`, used to
avoid repeatedly unfolding the same pair conversion. -/
@[reducible] noncomputable def realCfcEqNormalPairDef
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : K →L[ℂ] K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    cfc (R := ℝ) f A = cfcNormal (ℋ := K) g A ∧
      cfc (R := ℝ) f B = cfcNormal (ℋ := K) g B :=
  realCfc_eq_normalCfc_of_selfAdjoint_pair
    (K := K) (f := f) (g := g) (A := A) (B := B) hA hB hg

/-- The difference of two normal CFC values coming from a real-valued function
on self-adjoint operators is self-adjoint. -/
theorem isSelfAdjoint_cfcNormal_sub_of_selfAdjoint_pair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : K →L[ℂ] K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    IsSelfAdjoint (cfcNormal (ℋ := K) g B - cfcNormal (ℋ := K) g A) := by
  have hrealAB :=
    realCfcEqNormalPairDef (K := K) (f := f) (g := g) (A := A) (B := B) hA hB hg
  rw [← hrealAB.2, ← hrealAB.1]
  simpa [cfcR] using
    (IsSelfAdjoint.cfc (R := ℝ) (A := K →L[ℂ] K) (f := f) (a := B)).sub
      (IsSelfAdjoint.cfc (R := ℝ) (A := K →L[ℂ] K) (f := f) (a := A))

/-- Reducible wrapper for the self-adjointness of a pairwise normal-CFC
difference. -/
@[reducible] noncomputable def isSelfAdjointCfcNormalSubPairDef
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : K →L[ℂ] K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    IsSelfAdjoint (cfcNormal (ℋ := K) g B - cfcNormal (ℋ := K) g A) :=
  isSelfAdjoint_cfcNormal_sub_of_selfAdjoint_pair
    (K := K) (f := f) (g := g) (A := A) (B := B) hA hB hg

/-- Hilbert-space-specialized wrapper for
`isSelfAdjointCfcNormalSubPairDef`. -/
@[reducible] noncomputable def isSelfAdjointCfcNormalSubPairHilbertDef
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hg : g = fun z : ℂ => (f z.re : ℂ)) :
    IsSelfAdjoint (cfcNormal (ℋ := ℋ) g B - cfcNormal (ℋ := ℋ) g A) :=
  isSelfAdjointCfcNormalSubPairDef
    (K := ℋ) (f := f) (g := g) (A := A) (B := B) hA hB hg

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Pointwise Loewner inequalities imply nonnegativity of the quadratic forms
of the differences `S i - T i`. -/
theorem quadratic_form_nonneg_of_pointwise_le
    {ι : Type*} {T S : ι → L ℋ} (hTS : ∀ i, T i ≤ S i) (x : ℋ) :
    ∀ i, 0 ≤ RCLike.re (inner ℂ ((S i - T i) x) x) := by
  intro i
  have hpos : (S i - T i).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp (hTS i)
  exact (ContinuousLinearMap.isPositive_iff_complex _).1 hpos x |>.2

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Taking the real part of the inner product with a fixed vector preserves
ordinary vector convergence. -/
theorem real_inner_tendsto_of_clm_tendsto
    {ι : Type*} {F : ι → ℋ} {v : ℋ} {l : Filter ι}
    (hF : Tendsto F l (𝓝 v)) (x : ℋ) :
    Tendsto (fun i => Complex.re (inner ℂ (F i) x)) l (𝓝 (Complex.re (inner ℂ v x))) := by
  have hinner :
      Tendsto (fun i => inner ℂ (F i) x) l (𝓝 (inner ℂ v x)) := by
    exact ((continuous_id.inner continuous_const).continuousAt.tendsto.comp hF)
  exact Complex.continuous_re.continuousAt.tendsto.comp hinner

/-- Restrict continuity on a complex set to the union of two spectra contained
in that set. -/
@[fun_prop] theorem continuousOn_union_of_spectrum_subsets
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {g : ℂ → ℂ} {Ω : Set ℂ}
    {A : K →L[ℂ] K} {B : L' →L[ℂ] L'}
    (hgΩ : ContinuousOn g Ω)
    (hσA : spectrum ℂ A ⊆ Ω) (hσB : spectrum ℂ B ⊆ Ω) :
    ContinuousOn g (spectrum ℂ A ∪ spectrum ℂ B) := by
  exact hgΩ.mono <| by
    intro z hz
    rcases hz with hzA | hzB
    · exact hσA hzA
    · exact hσB hzB

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Interval-based lifting of a compressed real-CFC comparison to a comparison
between ambient block-extension normal CFCs. -/
theorem blockExtensionDiag_cfc_mono_from_subtype_interval
    {U : Submodule ℂ ℋ} [Nontrivial ↥U] [U.HasOrthogonalProjection]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [StarOrderedRing (↥U →L[ℂ] ↥U)] [AddRightMono (↥U →L[ℂ] ↥U)]
    [NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U)]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : L ℋ} {α β t₀ : ℝ}
    (hg : g = fun z : ℂ => (f z.re : ℂ))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA_sa : IsSelfAdjoint (U.orthogonalProjection ∘L A ∘L U.subtypeL))
    (hA_Icc : spectrum ℝ (U.orthogonalProjection ∘L A ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hB_sa : IsSelfAdjoint (U.orthogonalProjection ∘L B ∘L U.subtypeL))
    (hB_Icc : spectrum ℝ (U.orthogonalProjection ∘L B ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hσt₀ :
      spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) ⊆
        Complex.ofReal '' Set.Icc α β)
    (hsub_fc :
      cfc (R := ℝ) f (U.orthogonalProjection ∘L A ∘L U.subtypeL) ≤
        cfc (R := ℝ) f (U.orthogonalProjection ∘L B ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) A t₀) ≤
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) B t₀) := by
  exact
    blockExtensionDiag_cfc_mono_from_subtype
      (U := U) (g := g) (A := A) (B := B) (t₀ := t₀)
      (hgΩ.mono (Set.union_subset
        (@complex_spectrum_subset_of_real_Icc ↥U _ _ (by assumption) _ _ _ hA_sa hA_Icc) hσt₀))
      (hgΩ.mono (Set.union_subset
        (@complex_spectrum_subset_of_real_Icc ↥U _ _ (by assumption) _ _ _ hB_sa hB_Icc) hσt₀))
      hA_sa.isStarNormal hB_sa.isStarNormal
      (@realCfc_monotone_bridge_sort_named ↥U _ _ (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (by assumption) _ _ _ _
        hg hA_sa hB_sa hsub_fc)

/-- Reducible wrapper for
`blockExtensionDiag_cfc_mono_from_subtype_interval`, keeping the interval
transport proof available as a definitional facade. -/
@[reducible] noncomputable def blockExtensionDiagCfcMonoFromSubtypeIntervalDef
    {U : Submodule ℂ ℋ} [Nontrivial ↥U] [U.HasOrthogonalProjection]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [StarOrderedRing (↥U →L[ℂ] ↥U)] [AddRightMono (↥U →L[ℂ] ↥U)]
    [NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U)]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : L ℋ} {α β t₀ : ℝ}
    (hg : g = fun z : ℂ => (f z.re : ℂ))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA_sa : IsSelfAdjoint (U.orthogonalProjection ∘L A ∘L U.subtypeL))
    (hA_Icc : spectrum ℝ (U.orthogonalProjection ∘L A ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hB_sa : IsSelfAdjoint (U.orthogonalProjection ∘L B ∘L U.subtypeL))
    (hB_Icc : spectrum ℝ (U.orthogonalProjection ∘L B ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hσt₀ :
      spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) ⊆
        Complex.ofReal '' Set.Icc α β)
    (hsub_fc :
      cfc (R := ℝ) f (U.orthogonalProjection ∘L A ∘L U.subtypeL) ≤
        cfc (R := ℝ) f (U.orthogonalProjection ∘L B ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) A t₀) ≤
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) B t₀) :=
  blockExtensionDiag_cfc_mono_from_subtype_interval
    (U := U) (f := f) (g := g) (A := A) (B := B) (α := α) (β := β) (t₀ := t₀)
    hg hgΩ hA_sa hA_Icc hB_sa hB_Icc hσt₀ hsub_fc

/-- Packed-instance version of
`blockExtensionDiagCfcMonoFromSubtypeIntervalDef`, taking the CFC and
nonnegative-spectrum structures explicitly before installing them locally. -/
@[reducible] noncomputable def blockExtensionDiagCfcMonoFromSubtypeIntervalPacked
    {U : Submodule ℂ ℋ} [Nontrivial ↥U] [U.HasOrthogonalProjection]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [StarOrderedRing (↥U →L[ℂ] ↥U)] [AddRightMono (↥U →L[ℂ] ↥U)]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : L ℋ} {α β t₀ : ℝ}
    (hUNonneg : NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U))
    (hCfcU : ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal)
    (hCfcUorth : ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal)
    (hCfcPair :
      ContinuousFunctionalCalculus ℂ
        ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal)
    (hRealCfcU : ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint)
    (hg : g = fun z : ℂ => (f z.re : ℂ))
    (hgΩ : ContinuousOn g (Complex.ofReal '' Set.Icc α β))
    (hA_sa : IsSelfAdjoint (U.orthogonalProjection ∘L A ∘L U.subtypeL))
    (hA_Icc : spectrum ℝ (U.orthogonalProjection ∘L A ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hB_sa : IsSelfAdjoint (U.orthogonalProjection ∘L B ∘L U.subtypeL))
    (hB_Icc : spectrum ℝ (U.orthogonalProjection ∘L B ∘L U.subtypeL) ⊆ Set.Icc α β)
    (hσt₀ :
      spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) ⊆
        Complex.ofReal '' Set.Icc α β)
    (hsub_fc :
      cfc (R := ℝ) f (U.orthogonalProjection ∘L A ∘L U.subtypeL) ≤
        cfc (R := ℝ) f (U.orthogonalProjection ∘L B ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) A t₀) ≤
      cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) B t₀) := by
  letI : NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U) := hUNonneg
  letI : ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal := hCfcU
  letI : ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal := hCfcUorth
  letI :
      ContinuousFunctionalCalculus ℂ
        ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal :=
    hCfcPair
  letI : ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint := hRealCfcU
  exact
    blockExtensionDiagCfcMonoFromSubtypeIntervalDef
      (U := U) (f := f) (g := g) (A := A) (B := B) (α := α) (β := β) (t₀ := t₀)
      hg hgΩ hA_sa hA_Icc hB_sa hB_Icc hσt₀ hsub_fc

/-- Directed family of block extensions along the finite spans of a Hilbert
basis. -/
@[reducible] noncomputable def hilbertFiniteSpanBlockFamily
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (A : L ℋ) (t₀ : ℝ) :
    Finset ι → L ℋ :=
  fun s => blockExtensionDiag (U := hilbertFiniteSpan (ℋ := ℋ) b s) A t₀

/-- Directed family obtained by applying complex normal CFC to
`hilbertFiniteSpanBlockFamily`. -/
@[reducible] noncomputable def hilbertFiniteSpanBlockCfcFamily
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (g : ℂ → ℂ) (A : L ℋ) (t₀ : ℝ) :
    Finset ι → L ℋ :=
  fun s => cfcNormal (ℋ := ℋ) g (hilbertFiniteSpanBlockFamily (ℋ := ℋ) b A t₀ s)

/-- Real scalar multiples of the identity are self-adjoint. -/
theorem isSelfAdjoint_smul_one_real
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (t : ℝ) :
    IsSelfAdjoint (((t : ℂ) • (1 : K →L[ℂ] K))) := by
  have ht : IsSelfAdjoint (t : ℂ) := by
    simp [isSelfAdjoint_iff]
  simpa using ht.smul (IsSelfAdjoint.one (K →L[ℂ] K))

/-- Real scalar multiples of the identity are star-normal. -/
theorem isStarNormal_smul_one_real
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (t : ℝ) :
    IsStarNormal (((t : ℂ) • (1 : K →L[ℂ] K))) :=
  (isSelfAdjoint_smul_one_real (K := K) t).isStarNormal

end NormalCFC514

end HansenPedersen
