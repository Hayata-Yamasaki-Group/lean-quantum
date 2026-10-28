/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.CFCTransport
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space

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
/-- Finite-dimensional subspace spanned by the vectors of a Hilbert basis with
indices in a finite set. -/
noncomputable def hilbertFiniteSpan {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    (s : Finset ι) : Submodule ℂ ℋ :=
  Submodule.span ℂ (b '' (s : Set ι))

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- The finite-span construction is monotone with respect to inclusion of
finite index sets. -/
lemma hilbertFiniteSpan_mono {ι : Type*} (b : HilbertBasis ι ℂ ℋ) :
    Monotone (hilbertFiniteSpan (ℋ := ℋ) b) := by
  intro s t hst
  exact Submodule.span_mono (by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact ⟨i, Set.mem_of_mem_of_subset hi (show (s : Set ι) ⊆ t from hst), rfl⟩)

attribute [gcongr] hilbertFiniteSpan_mono

/-- Each finite span of a Hilbert basis is finite-dimensional. -/
instance hilbertFiniteSpan_finiteDimensional {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    (s : Finset ι) : FiniteDimensional ℂ (hilbertFiniteSpan (ℋ := ℋ) b s) := by
  classical
  refine FiniteDimensional.span_of_finite ℂ ?_
  exact s.finite_toSet.image b

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- The closed supremum of all finite Hilbert-basis spans is the whole Hilbert
space. -/
lemma top_le_closure_iSup_hilbertFiniteSpan {ι : Type*} (b : HilbertBasis ι ℂ ℋ) :
    (⊤ : Submodule ℂ ℋ) ≤
      (⨆ s : Finset ι, hilbertFiniteSpan (ℋ := ℋ) b s).topologicalClosure := by
  classical
  have hdense := HilbertBasis.finite_spans_dense (b := b)
  simpa [hilbertFiniteSpan] using hdense.ge

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Orthogonal projections onto the finite Hilbert-basis spans converge
strongly to the identity on each vector. -/
theorem hilbertFiniteSpan_starProjection_tendsto_self {ι : Type*}
    (b : HilbertBasis ι ℂ ℋ) (x : ℋ) :
    Tendsto
      (fun s : Finset ι => (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection x)
      atTop (𝓝 x) :=
  Submodule.starProjection_tendsto_self
    (U := fun s : Finset ι => hilbertFiniteSpan (ℋ := ℋ) b s)
    (hU := hilbertFiniteSpan_mono (ℋ := ℋ) b) x
    (hU' := top_le_closure_iSup_hilbertFiniteSpan (ℋ := ℋ) b)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Constant nets converge in the strong-operator topology. -/
lemma SOTTendsto_const {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)] (A : L ℋ) :
    SOTTendsto (ℋ := ℋ) (fun _ : ι => A) A := by
  intro x
  simp

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Orthogonal projections onto finite Hilbert-basis spans are uniformly
bounded by one. -/
theorem hilbertFiniteSpan_starProjection_uniformBound
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) :
    ∀ s : Finset ι, ‖(hilbertFiniteSpan (ℋ := ℋ) b s).starProjection‖ ≤ 1 := by
  intro s
  simpa using Submodule.starProjection_norm_le (hilbertFiniteSpan (ℋ := ℋ) b s)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- If projections converge strongly to the identity and are uniformly bounded,
then the block extensions `Pᵢ A Pᵢ + t₀ (1 - Pᵢ)` converge strongly to `A`. -/
theorem block_extension_tendsto_self
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {P : ι → L ℋ} {A : L ℋ} {t₀ : ℝ}
    (hP : SOTTendsto (ℋ := ℋ) P 1) (hPbound : ∀ i, ‖P i‖ ≤ 1) :
    SOTTendsto (ℋ := ℋ)
      (fun i => P i * A * P i + (t₀ : ℂ) • (1 - P i)) A := by
  have hPA_bound : ∃ M > 0, ∀ i, ‖P i * A‖ ≤ M := by
    refine ⟨‖A‖ + 1, by positivity, ?_⟩
    intro i
    calc
      ‖P i * A‖ ≤ ‖P i‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ 1 * ‖A‖ := by
        exact mul_le_mul_of_nonneg_right (hPbound i) (norm_nonneg A)
      _ ≤ ‖A‖ + 1 := by nlinarith [norm_nonneg A]
  have hPA :
      SOTTendsto (ℋ := ℋ) (fun i => P i * A) A := by
    simpa using
      HansenPedersen.SOTTendsto_mul_of_uniformBound (ℋ := ℋ) hP
        (SOTTendsto_const (ℋ := ℋ) A) ⟨1, zero_lt_one, hPbound⟩
  have hPAP :
      SOTTendsto (ℋ := ℋ) (fun i => (P i * A) * P i) A := by
    simpa [mul_assoc] using
      HansenPedersen.SOTTendsto_mul_of_uniformBound (ℋ := ℋ) hPA hP hPA_bound
  have hOneSubP :
      SOTTendsto (ℋ := ℋ) (fun i => 1 - P i) 0 := by
    simpa using
      HansenPedersen.SOTTendsto_sub (ℋ := ℋ) (SOTTendsto_const (ℋ := ℋ) (1 : L ℋ)) hP
  have hScalar :
      SOTTendsto (ℋ := ℋ) (fun i => (t₀ : ℂ) • (1 - P i)) 0 := by
    simpa using HansenPedersen.SOTTendsto_smul (ℋ := ℋ) (t₀ : ℂ) hOneSubP
  simpa [zero_add] using HansenPedersen.SOTTendsto_add (ℋ := ℋ) hPAP hScalar

omit [Nontrivial (L ℋ)] in
/-- Given two spectra and one scalar inside a convex real set, choose a compact
interval contained in the set and containing all three pieces. -/
theorem exists_compact_interval_subset_of_spectra
    {J : Set ℝ} {A B : L ℋ} {t₀ : ℝ}
    (hσA : spectrum ℝ A ⊆ J) (hσB : spectrum ℝ B ⊆ J)
    (ht₀ : t₀ ∈ J) (hJ : Convex ℝ J) :
    ∃ α β : ℝ,
      spectrum ℝ A ∪ spectrum ℝ B ∪ {t₀} ⊆ Set.Icc α β ∧ Set.Icc α β ⊆ J := by
  let S : Set ℝ := spectrum ℝ A ∪ spectrum ℝ B ∪ {t₀}
  have hScompact : IsCompact S := by
    simpa [S] using
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) A).union
        ((ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) B).union isCompact_singleton)
  have hSne : S.Nonempty := by
    simp [S]
  have hSbddBelow : BddBelow S := hScompact.bddBelow
  have hSbddAbove : BddAbove S := hScompact.bddAbove
  refine ⟨sInf S, sSup S, subset_Icc_csInf_csSup hSbddBelow hSbddAbove, ?_⟩
  have hsInf_mem : sInf S ∈ S := hScompact.sInf_mem hSne
  have hsSup_mem : sSup S ∈ S := hScompact.sSup_mem hSne
  have hSJ : S ⊆ J := by
    intro x hx
    rcases hx with hxAB | hxT
    · rcases hxAB with hxA | hxB
      · exact hσA hxA
      · exact hσB hxB
    · simpa [Set.mem_singleton_iff.mp hxT] using ht₀
  exact hJ.ordConnected.out (hSJ hsInf_mem) (hSJ hsSup_mem)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- A real spectral bound for a self-adjoint operator gives the corresponding
complex spectral bound in the image of the same interval. -/
theorem complex_spectrum_subset_of_real_Icc
    {T : L ℋ} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Icc α β) :
    spectrum ℂ T ⊆ Complex.ofReal '' Set.Icc α β := by
  intro z hz
  rw [← hT.spectrumRestricts.algebraMap_image] at hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hσ hx, rfl⟩

/-- Triple version of `complex_spectrum_subset_of_real_Icc`. -/
theorem complex_spectrum_subset_of_real_Icc_triple
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {A B M : K →L[ℂ] K} {α β : ℝ}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Icc α β)
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Icc α β)
    (hM : IsSelfAdjoint M) (hσM : spectrum ℝ M ⊆ Set.Icc α β) :
    spectrum ℂ A ⊆ Complex.ofReal '' Set.Icc α β ∧
      spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc α β ∧
      spectrum ℂ M ⊆ Complex.ofReal '' Set.Icc α β := by
  refine ⟨complex_spectrum_subset_of_real_Icc (ℋ := K) hA hσA, ?_, ?_⟩
  · exact complex_spectrum_subset_of_real_Icc (ℋ := K) hB hσB
  · exact complex_spectrum_subset_of_real_Icc (ℋ := K) hM hσM

/-- Restrict continuity on a complex set to the union of two subsets. -/
@[fun_prop] theorem continuousOn_union_of_subsets
    {Ω S T : Set ℂ} {g : ℂ → ℂ}
    (hgΩ : ContinuousOn g Ω)
    (hS : S ⊆ Ω) (hT : T ⊆ Ω) :
    ContinuousOn g (S ∪ T) :=
  hgΩ.mono <| by
    intro z hz
    rcases hz with hzS | hzT
    · exact hS hzS
    · exact hT hzT

omit [Nontrivial (L ℋ)] in
/-- A real spectral inclusion in `Icc α β` yields scalar lower and upper
Loewner bounds for a self-adjoint ambient operator. -/
theorem order_bounds_of_spectrum_subset_Icc
    {T : L ℋ} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Icc α β) :
    (α : ℂ) • (1 : L ℋ) ≤ T ∧ T ≤ (β : ℂ) • (1 : L ℋ) :=
  order_bounds_of_spectrum_subset_Icc_clm hT hσ

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Compressing a scalar multiple of the ambient identity to a submodule gives
the same scalar multiple of the submodule identity. -/
theorem compression_scalar_eq
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace U]
    {r : ℝ} :
    U.orthogonalProjection ∘L ((r : ℂ) • (1 : L ℋ)) ∘L U.subtypeL =
      (r : ℂ) • (1 : U →L[ℂ] U) := by
  ext x
  simp only [Complex.coe_smul, ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL',
    Submodule.coe_subtype, Function.comp_apply, Submodule.coe_orthogonalProjection_apply]
  exact congrArg Subtype.val
    (Submodule.orthogonalProjection_mem_subspace_eq_self (K := U) ((r : ℂ) • x))

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Compression of `A - r • 1` is the compressed operator minus the compressed
scalar identity. -/
theorem compression_sub_scalar_eq
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace U]
    {A : L ℋ} {r : ℝ} :
    U.orthogonalProjection ∘L (A - (r : ℂ) • (1 : L ℋ)) ∘L U.subtypeL =
      (U.orthogonalProjection ∘L A ∘L U.subtypeL) - (r : ℂ) • (1 : U →L[ℂ] U) := by
  calc
    U.orthogonalProjection ∘L (A - (r : ℂ) • (1 : L ℋ)) ∘L U.subtypeL
        = (U.orthogonalProjection ∘L A ∘L U.subtypeL) -
            (U.orthogonalProjection ∘L ((r : ℂ) • (1 : L ℋ)) ∘L U.subtypeL) := by
            rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    _ =
        (U.orthogonalProjection ∘L A ∘L U.subtypeL) -
          (r : ℂ) • (1 : ↥U →L[ℂ] ↥U) := by
          rw [compression_scalar_eq (U := U) (r := r)]

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Compression of `r • 1 - A` is the compressed scalar identity minus the
compressed operator. -/
theorem scalar_sub_compression_eq
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace U]
    {A : L ℋ} {r : ℝ} :
    U.orthogonalProjection ∘L ((r : ℂ) • (1 : L ℋ) - A) ∘L U.subtypeL =
      (r : ℂ) • (1 : U →L[ℂ] U) - (U.orthogonalProjection ∘L A ∘L U.subtypeL) := by
  calc
    U.orthogonalProjection ∘L ((r : ℂ) • (1 : L ℋ) - A) ∘L U.subtypeL
        = (U.orthogonalProjection ∘L ((r : ℂ) • (1 : L ℋ)) ∘L U.subtypeL) -
            (U.orthogonalProjection ∘L A ∘L U.subtypeL) := by
            rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    _ =
        (r : ℂ) • (1 : ↥U →L[ℂ] ↥U) -
          (U.orthogonalProjection ∘L A ∘L U.subtypeL) := by
          rw [compression_scalar_eq (U := U) (r := r)]

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- If an ambient self-adjoint operator is bounded between scalar identities,
then every submodule compression has real spectrum in the same interval. -/
theorem compression_spectrum_subset_Icc
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [U.HasOrthogonalProjection]
    [StarOrderedRing (↥U →L[ℂ] ↥U)] [AddRightMono (↥U →L[ℂ] ↥U)]
    [NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U)]
    [ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint]
    {A : L ℋ} {α β : ℝ}
    (hA : IsSelfAdjoint A)
    (hlow : (α : ℂ) • (1 : L ℋ) ≤ A)
    (hupp : A ≤ (β : ℂ) • (1 : L ℋ)) :
    spectrum ℝ (compressionCLM (U := U) A) ⊆
      Set.Icc α β := by
  letI : CompleteSpace ↥U := ‹CompleteSpace ↥U›
  letI : CompleteSpace U := instCompleteSpaceSortFromSubtype (U := U)
  let Acomp : U →L[ℂ] U := compressionCLM (U := U) A
  have hAcomp : IsSelfAdjoint Acomp := by
    have hsym : (Acomp : U →ₗ[ℂ] U).IsSymmetric := by
      intro x y
      simpa [Acomp, compressionCLM, Submodule.subtypeL_apply] using
        hA.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ U _ _ _ (instCompleteSpaceSortFromSubtype (U := U))
        Acomp hsym
  have hlowPos : ((A - (α : ℂ) • (1 : L ℋ))).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp hlow
  have huppPos : ((((β : ℂ) • (1 : L ℋ)) - A)).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp hupp
  have hlowComp :
    (α : ℂ) • (1 : ↥U →L[ℂ] ↥U) ≤ Acomp := by
    refine (ContinuousLinearMap.le_def _ _).2 ?_
    change
      ((U.orthogonalProjection ∘L A ∘L U.subtypeL) -
        (α : ℂ) • (1 : ↥U →L[ℂ] ↥U)).IsPositive
    have hlowCompPos :
        (U.orthogonalProjection ∘L (A - (α : ℂ) • (1 : L ℋ)) ∘L U.subtypeL).IsPositive :=
      hlowPos.orthogonalProjection_comp U
    rw [compression_sub_scalar_eq (U := U) (A := A) (r := α)] at hlowCompPos
    simpa [Acomp] using hlowCompPos
  have huppComp :
    Acomp ≤ (β : ℂ) • (1 : ↥U →L[ℂ] ↥U) := by
    refine (ContinuousLinearMap.le_def _ _).2 ?_
    change
      (((β : ℂ) • (1 : ↥U →L[ℂ] ↥U)) -
        (U.orthogonalProjection ∘L A ∘L U.subtypeL)).IsPositive
    have huppCompPos :
        (U.orthogonalProjection ∘L (((β : ℂ) • (1 : L ℋ)) - A) ∘L
          U.subtypeL).IsPositive :=
      huppPos.orthogonalProjection_comp U
    rw [scalar_sub_compression_eq (U := U) (A := A) (r := β)] at huppCompPos
    simpa [Acomp] using huppCompPos
  intro x hx
  refine ⟨?_, ?_⟩
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := ↥U →L[ℂ] ↥U) (p := IsSelfAdjoint)
      (r := α) (a := Acomp) (ha := hAcomp)).1 hlowComp x hx
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := ↥U →L[ℂ] ↥U) (p := IsSelfAdjoint)
      (r := β) (a := Acomp) (ha := hAcomp)).1 huppComp x hx

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Compression to a closed submodule is monotone for the Loewner order. -/
theorem compression_le_of_le
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection]
    {A B : L ℋ} (hAB : A ≤ B) :
    compressionCLM (U := U) A ≤ compressionCLM (U := U) B := by
  refine (ContinuousLinearMap.le_def _ _).2 ?_
  simpa [sub_eq_add_neg, ContinuousLinearMap.comp_assoc] using
    ((ContinuousLinearMap.le_def _ _).mp hAB).orthogonalProjection_comp U

attribute [gcongr] compression_le_of_le

end NormalCFC514

end HansenPedersen
