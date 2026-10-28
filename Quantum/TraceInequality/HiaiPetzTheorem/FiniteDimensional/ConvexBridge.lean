/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionLimit

/-!
# Finite-dimensional convex bridge

This file proves the convexity half of Proposition 5.1.5 for the
finite-dimensional bridge.  It compresses to finite spans, applies matrix
operator convexity on those finite-dimensional subspaces, transports the real
CFC comparison through normal CFC for block extensions, and passes to the
strong-operator limit.

## Main results

* `BlockExtensionInternal.matrixConvexImpliesOperatorMidpointConvex_core`: the
  fixed-Hilbert-space bridge from matrix operator convexity to operator
  midpoint convexity.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Proposition 5.1.5.
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

namespace BlockExtensionInternal

/- Instance caches: the scalar-action classes on submodule endomorphism spaces
(`↥U →L[ℂ] ↥U`) trigger deep `synthInstance` derivations through the restricted
real structure, exceeding the default budget when searched outside the `letI`
walls of the block proofs.  Section-level reducible local instances turn each
search into a head-match (same pattern as the HiaiPetz transport files). -/

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real module structure on submodule
endomorphisms used in finite-span compression calculations. -/
@[reducible, local instance] noncomputable def instModuleRealSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    Module ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for distributive real scalar multiplication on
submodule endomorphisms used by midpoint block algebra. -/
@[reducible, local instance] noncomputable def instDistribSMulRealSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    DistribSMul ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for real scalar multiplication on the ambient
operator algebra `L ℋ` used in the finite-dimensional bridge. -/
@[reducible, local instance] noncomputable def instSMulRealLHScopedCB :
    SMul ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real module structure on `L ℋ` used by
finite-span midpoint and limit calculations. -/
@[reducible, local instance] noncomputable def instModuleRealLHScopedCB :
    Module ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for distributive real scalar multiplication on `L ℋ`
used in block extension algebra. -/
@[reducible, local instance] noncomputable def instDistribSMulRealLHScopedCB :
    DistribSMul ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real multiplicative action on `L ℋ` used in
scalar-action expressions inside the bridge proof. -/
@[reducible, local instance] noncomputable def instMulActionRealLHScopedCB :
    MulAction ℝ (L ℋ) :=
  inferInstance

-- Explicit derivation: the raw `SMul ℝ` search dead-ends through the huge
-- population of non-algebra `SMul` candidates before reaching
-- `Algebra.toSMul` (times out even at 20x the default budget); naming the
-- head directly leaves only the cheap `Algebra ℝ` subgoal
-- (`Algebra.complexToReal`, found within the default budget).
/-- Local reducible cache for real scalar multiplication on submodule
endomorphisms used by restricted CFC comparisons. -/
@[reducible, local instance] noncomputable def instSMulRealSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    SMul ℝ (↥U →L[ℂ] ↥U) :=
  Algebra.toSMul

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real multiplicative action on submodule
endomorphisms used in midpoint compression formulas. -/
@[reducible, local instance] noncomputable def instMulActionRealSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    MulAction ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real algebra structure on `L ℋ` used in
real-to-complex CFC bridge calculations. -/
@[reducible, local instance] noncomputable def instAlgebraRealLHScopedCB :
    Algebra ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the complex algebra structure on `L ℋ` used by
normal CFC and block-extension comparisons. -/
@[reducible, local instance] noncomputable def instAlgebraComplexLHScopedCB :
    Algebra ℂ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the real algebra structure on submodule
endomorphisms used in finite-dimensional restricted CFC. -/
@[reducible, local instance] noncomputable def instAlgebraRealSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    Algebra ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible cache for the complex algebra structure on submodule
endomorphisms used by normal CFC on finite spans. -/
@[reducible, local instance] noncomputable def instAlgebraComplexSubmoduleEndScopedCB
    {U : Submodule ℂ ℋ} :
    Algebra ℂ (↥U →L[ℂ] ↥U) :=
  inferInstance

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Pointwise form of `blockConjDiagMap`: the `U`-block acts on the projection to `U` and
the complement block on the projection to `Uᗮ`. -/
private theorem blockConjDiagMap_apply_split
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    (a : U →L[ℂ] U) (b : Uᗮ →L[ℂ] Uᗮ) (x : ℋ) :
    blockConjDiagMap (U := U) (a := a) (b := b) x =
      U.subtypeL (a (U.orthogonalProjection x)) +
        (Uᗮ).subtypeL (b ((Uᗮ).orthogonalProjection x)) :=
  orthogonalDecomposition_symm_diagMapCLM_apply (U := U) (a := a) (b := b) x

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Midpoint linearity of the block conjugated diagonal map in its upper-left
block: averaging two blocks and then embedding agrees with embedding the
average.  Extracted from `matrixConvexImpliesOperatorMidpointConvex_core` so
that the pointwise block algebra elaborates in its own declaration. -/
private theorem blockConjDiagMap_midpoint
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    (p q : U →L[ℂ] U) (r : Uᗮ →L[ℂ] Uᗮ) :
    (1 / 2 : ℝ) •
        (blockConjDiagMap (U := U) (a := p) (b := r) +
          blockConjDiagMap (U := U) (a := q) (b := r)) =
      blockConjDiagMap (U := U) (a := ((1 / 2 : ℝ) • (p + q))) (b := r) := by
  ext x
  change
    (1 / 2 : ℝ) •
        (blockConjDiagMap (U := U) (a := p) (b := r) x +
          blockConjDiagMap (U := U) (a := q) (b := r) x) =
      blockConjDiagMap (U := U) (a := ((1 / 2 : ℝ) • (p + q))) (b := r) x
  rw [blockConjDiagMap_apply_split, blockConjDiagMap_apply_split, blockConjDiagMap_apply_split]
  change
    (1 / 2 : ℝ) •
        (((p (U.orthogonalProjection x) : ℋ) + (r ((Uᗮ).orthogonalProjection x) : ℋ)) +
          ((q (U.orthogonalProjection x) : ℋ) + (r ((Uᗮ).orthogonalProjection x) : ℋ))) =
      (1 / 2 : ℝ) • ((p (U.orthogonalProjection x) : ℋ) + (q (U.orthogonalProjection x) : ℋ)) +
        (r ((Uᗮ).orthogonalProjection x) : ℋ)
  module

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Star-normality of the block extension of a self-adjoint operator over a
finite span, extracted from `matrixConvexImpliesOperatorMidpointConvex_core`
(used for `A`, `B` and the midpoint). -/
private theorem hilbertFiniteSpan_blockExtension_isStarNormal
    {t₀ : ℝ} {T : L ℋ} (hT : IsSelfAdjoint T)
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (s : Finset ι) :
    IsStarNormal
      ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * T *
          (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
        (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) := by
  letI : CompleteSpace (hilbertFiniteSpan (ℋ := ℋ) b s) :=
    instCompleteSpaceSortFromSubtype (U := hilbertFiniteSpan (ℋ := ℋ) b s)
  letI : CompleteSpace ((hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ) :=
    instCompleteSpaceSortFromSubtype (U := (hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ)
  exact block_extension_normal_of_selfAdjoint (ℋ := ℋ) (U := hilbertFiniteSpan (ℋ := ℋ) b s)
    (A := T) (t₀ := t₀) hT

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Complex-spectrum localization of the block extension of a self-adjoint
operator over a finite span, extracted from
`matrixConvexImpliesOperatorMidpointConvex_core` (used for `A`, `B` and the
midpoint). -/
private theorem hilbertFiniteSpan_blockExtension_spectrum_subset_ofReal_Icc
    {α β t₀ : ℝ} (ht₀Icc : t₀ ∈ Set.Icc α β)
    {T : L ℋ} (hT : IsSelfAdjoint T)
    (hT_bounds : (α : ℂ) • (1 : L ℋ) ≤ T ∧ T ≤ (β : ℂ) • (1 : L ℋ))
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (s : Finset ι) :
    spectrum ℂ
        ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * T *
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
          (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) ⊆
      Complex.ofReal '' Set.Icc α β := by
  by_cases hs0 : s = ∅
  · have hP0 : (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection = 0 := by
      subst hs0
      simp [hilbertFiniteSpan]
    intro z hz
    have hzscalar : z ∈ spectrum ℂ ((algebraMap ℂ (L ℋ)) (t₀ : ℂ)) := by
      simpa [hP0, Algebra.algebraMap_eq_smul_one] using hz
    have hz' : z ∈ ({(t₀ : ℂ)} : Set ℂ) :=
      (CFC.spectrum_algebraMap_subset (R := ℂ) (A := L ℋ) (t₀ : ℂ)) hzscalar
    rcases Set.mem_singleton_iff.mp hz' with rfl
    exact ⟨t₀, ht₀Icc, by simp⟩
  · haveI : Nontrivial (hilbertFiniteSpan (ℋ := ℋ) b s) :=
      nontrivial_hilbertFiniteSpan_of_ne_empty (ℋ := ℋ) b hs0
    simpa using
      (hilbertFiniteSpan_block_extension_complex_spectrum_subset
        (ℋ := ℋ) (b := b) (A := T) (hA := hT) (hA_bounds := hT_bounds) (t₀ := t₀)
        (ht₀ := ht₀Icc) s)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Block-extension step of the midpoint comparison: a midpoint inequality between the complex
CFCs of the compressions to `V` transports to the block extensions with scalar complement `t₀`. -/
private theorem blockExtension_cfcNormal_midpoint_le_of_compressed
    {V : Submodule ℂ ℋ} [V.HasOrthogonalProjection] [CompleteSpace ↥V] [CompleteSpace ↥Vᗮ]
    [CompleteSpace (WithLp 2 (↥V × ↥Vᗮ))]
    [ContinuousFunctionalCalculus ℂ (↥V →L[ℂ] ↥V) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Vᗮ →L[ℂ] ↥Vᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ ((↥V →L[ℂ] ↥V) × (↥Vᗮ →L[ℂ] ↥Vᗮ)) IsStarNormal]
    {g : ℂ → ℂ} {A B : L ℋ} {t₀ : ℝ}
    (hcontA :
      ContinuousOn g (spectrum ℂ (V.orthogonalProjection ∘L A ∘L V.subtypeL) ∪
        spectrum ℂ ((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ))))
    (hcontB :
      ContinuousOn g (spectrum ℂ (V.orthogonalProjection ∘L B ∘L V.subtypeL) ∪
        spectrum ℂ ((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ))))
    (hcontM :
      ContinuousOn g
        (spectrum ℂ (V.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L V.subtypeL) ∪
          spectrum ℂ ((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ))))
    (hA_norm : IsStarNormal (V.orthogonalProjection ∘L A ∘L V.subtypeL))
    (hB_norm : IsStarNormal (V.orthogonalProjection ∘L B ∘L V.subtypeL))
    (hM_norm : IsStarNormal (V.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L V.subtypeL))
    (hsub :
      cfc (R := ℂ) g (V.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L V.subtypeL) ≤
        (1 / 2 : ℝ) •
          (cfc (R := ℂ) g (V.orthogonalProjection ∘L A ∘L V.subtypeL) +
            cfc (R := ℂ) g (V.orthogonalProjection ∘L B ∘L V.subtypeL))) :
    cfcNormal (ℋ := ℋ) g
        (V.starProjection * ((1 / 2 : ℝ) • (A + B)) * V.starProjection +
          (t₀ : ℂ) • (1 - V.starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfcNormal (ℋ := ℋ) g
            (V.starProjection * A * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection)) +
          cfcNormal (ℋ := ℋ) g
            (V.starProjection * B * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection))) := by
  let M : L ℋ := (1 / 2 : ℝ) • (A + B)
  let b_s : Vᗮ →L[ℂ] Vᗮ := cfc (R := ℂ) g ((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ))
  change
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := V) M t₀) ≤
      (1 / 2 : ℝ) •
        (cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := V) A t₀) +
          cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := V) B t₀))
  rw [cfcNormal_blockExtensionDiag_eq_blockConjDiagMap (U := V) (g := g) (X := M) t₀ hcontM hM_norm,
    cfcNormal_blockExtensionDiag_eq_blockConjDiagMap (U := V) (g := g) (X := A) t₀ hcontA hA_norm,
    cfcNormal_blockExtensionDiag_eq_blockConjDiagMap (U := V) (g := g) (X := B) t₀ hcontB hB_norm]
  change
    blockConjDiagMap (U := V)
        (a := cfc (R := ℂ) g (V.orthogonalProjection ∘L M ∘L V.subtypeL)) (b := b_s) ≤
      (1 / 2 : ℝ) •
        (blockConjDiagMap (U := V)
            (a := cfc (R := ℂ) g (V.orthogonalProjection ∘L A ∘L V.subtypeL)) (b := b_s) +
          blockConjDiagMap (U := V)
            (a := cfc (R := ℂ) g (V.orthogonalProjection ∘L B ∘L V.subtypeL)) (b := b_s))
  rw [blockConjDiagMap_midpoint (ℋ := ℋ) (U := V)]
  exact blockConjDiagMap_mono (U := V) hsub

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The midpoint block-CFC comparison on one nonzero finite-dimensional subspace `V`; the
finite-span statement below specialises it to `V = hilbertFiniteSpan b s`. -/
private theorem blockExtension_cfcNormal_midpoint_le_of_finiteDimensional
    {J : Set ℝ} {f : ℝ → ℝ} {α β t₀ : ℝ}
    (hJ : Convex ℝ J)
    (hfJ : ContinuousOn f J)
    (hmat : MatrixOperatorMidpointConvexOnInterval J f)
    (hIccJ : Set.Icc α β ⊆ J)
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hM_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (A + B)))
    (hM_bounds :
      (α : ℂ) • (1 : L ℋ) ≤ (1 / 2 : ℝ) • (A + B) ∧
        (1 / 2 : ℝ) • (A + B) ≤ (β : ℂ) • (1 : L ℋ))
    (hgΩ : ContinuousOn (fun z : ℂ => (f z.re : ℂ)) (Complex.ofReal '' Set.Icc α β))
    (V : Submodule ℂ ℋ) [FiniteDimensional ℂ V] [Nontrivial V]
    (hscalar :
      spectrum ℂ ((t₀ : ℂ) • (1 : ↥Vᗮ →L[ℂ] ↥Vᗮ)) ⊆ Complex.ofReal '' Set.Icc α β) :
    cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        (V.starProjection * ((1 / 2 : ℝ) • (A + B)) * V.starProjection +
          (t₀ : ℂ) • (1 - V.starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
            (V.starProjection * A * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection)) +
          cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
            (V.starProjection * B * V.starProjection + (t₀ : ℂ) • (1 - V.starProjection))) := by
  let g : ℂ → ℂ := fun z => (f z.re : ℂ)
  let Ω : Set ℂ := Complex.ofReal '' Set.Icc α β
  let M : L ℋ := (1 / 2 : ℝ) • (A + B)
  let P : L ℋ := V.starProjection
  let A_sub : V →L[ℂ] V := V.orthogonalProjection ∘L A ∘L V.subtypeL
  let B_sub : V →L[ℂ] V := V.orthogonalProjection ∘L B ∘L V.subtypeL
  let M_sub : V →L[ℂ] V := V.orthogonalProjection ∘L M ∘L V.subtypeL
  let Atilde : L ℋ := P * A * P + (t₀ : ℂ) • (1 - P)
  let Btilde : L ℋ := P * B * P + (t₀ : ℂ) • (1 - P)
  let Mtilde : L ℋ := P * M * P + (t₀ : ℂ) • (1 - P)
  change
    cfcNormal (ℋ := ℋ) g Mtilde ≤
      (1 / 2 : ℝ) • (cfcNormal (ℋ := ℋ) g Atilde + cfcNormal (ℋ := ℋ) g Btilde)
  have hM_sa' : IsSelfAdjoint M := hM_sa
  have hM_bounds' :
      (α : ℂ) • (1 : L ℋ) ≤ M ∧ M ≤ (β : ℂ) • (1 : L ℋ) := hM_bounds
  /- Step 2: Install finite-span CFC and order instances for matrix convexity. -/
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
    @ContinuousLinearMap.instStarOrderedRing V _ _ hUSortComplete
  have hUNonnegSub : NonnegSpectrumClass ℝ (↥V →L[ℂ] ↥V) :=
    nonnegSpectrumClass_submoduleEndSubtype (ℋ := ℋ) V hUSubComplete
  letI : NonnegSpectrumClass ℝ (↥V →L[ℂ] ↥V) := hUNonnegSub
  letI hCfcV : ContinuousFunctionalCalculus ℂ (↥V →L[ℂ] ↥V) IsStarNormal :=
    subtypeSubmoduleEndStarNormalCfcDef (U := V)
  letI : ContinuousFunctionalCalculus ℂ (↥Vᗮ →L[ℂ] ↥Vᗮ) IsStarNormal :=
    subtypeSubmoduleEndStarNormalCfcDef (U := Vᗮ)
  letI hRealCfc : ContinuousFunctionalCalculus ℝ (↥V →L[ℂ] ↥V) IsSelfAdjoint := by
    infer_instance
  /- Step 3: Transfer self-adjointness and spectral bounds to the compressions. -/
  have hA_sub_sa : IsSelfAdjoint (A_sub) := by
    have hsym :
        ((A_sub : ↥V →L[ℂ] ↥V) :
          ↥V →ₗ[ℂ] ↥V).IsSymmetric := by
      intro x y
      simpa [A_sub, compressionCLM, Submodule.subtypeL_apply] using
        hA.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ ↥V _ _ _ hUSubComplete (A_sub) hsym
  have hB_sub_sa : IsSelfAdjoint (B_sub) := by
    have hsym :
        ((B_sub : ↥V →L[ℂ] ↥V) :
          ↥V →ₗ[ℂ] ↥V).IsSymmetric := by
      intro x y
      simpa [B_sub, compressionCLM, Submodule.subtypeL_apply] using
        hB.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ ↥V _ _ _ hUSubComplete (B_sub) hsym
  have hM_sub_sa : IsSelfAdjoint (M_sub) := by
    have hsym :
        ((M_sub : ↥V →L[ℂ] ↥V) :
          ↥V →ₗ[ℂ] ↥V).IsSymmetric := by
      intro x y
      simpa [M_sub, compressionCLM, Submodule.subtypeL_apply] using
        hM_sa'.isSymmetric (x : ℋ) (y : ℋ)
    exact
      @LinearMap.IsSymmetric.isSelfAdjoint ℂ ↥V _ _ _ hUSubComplete (M_sub) hsym
  have hA_sub_norm : IsStarNormal (A_sub) := hA_sub_sa.isStarNormal
  have hB_sub_norm : IsStarNormal (B_sub) := hB_sub_sa.isStarNormal
  have hM_sub_norm : IsStarNormal (M_sub) := hM_sub_sa.isStarNormal
  have hUOrth : V.HasOrthogonalProjection := inferInstance
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
  have hM_sub_Icc : spectrum ℝ M_sub ⊆ Set.Icc α β :=
    (@compression_spectrum_subset_Icc ℋ _ _ _ V hUSubComplete hUOrth
      (instStarOrderedRingSubtypeSubmoduleEnd (U := V))
      (show AddRightMono (↥V →L[ℂ] ↥V) from inferInstance)
      hUNonnegSub
      hRealCfc
      M α β hM_sa' hM_bounds'.1 hM_bounds'.2)
  /- Step 4: Apply finite-dimensional matrix convexity and identify the compressed midpoint. -/
  have hsub_fc :
      cfc (R := ℝ) f ((1 / 2 : ℝ) • (A_sub + B_sub)) ≤
        (1 / 2 : ℝ) • (cfc (R := ℝ) f (A_sub) + cfc (R := ℝ) f (B_sub)) :=
    @matrixOperatorConvexOnInterval_of_finiteDimensional
      ↥V _ _ hUSubComplete _
      hRealCfc
      (by infer_instance : Nontrivial (↥V →L[ℂ] ↥V))
      J f hJ hfJ hmat (A_sub) (B_sub) hA_sub_sa hB_sub_sa
      (by intro x hx; exact hIccJ (hA_sub_Icc hx))
      (by intro x hx; exact hIccJ (hB_sub_Icc hx))
  have hM_sub_eq : M_sub = (1 / 2 : ℝ) • (A_sub + B_sub) := by
    calc
      M_sub =
          V.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L
            V.subtypeL := by
        rfl
      _ = (1 / 2 : ℝ) •
            ((V.orthogonalProjection ∘L A ∘L V.subtypeL) +
              (V.orthogonalProjection ∘L B ∘L V.subtypeL)) := by
            exact compression_midpoint_eq (U := V) (A := A) (B := B)
      _ = (1 / 2 : ℝ) • (A_sub + B_sub) := by
            rfl
  have hsub_fc' :
      cfc (R := ℝ) f (M_sub) ≤
        (1 / 2 : ℝ) • (cfc (R := ℝ) f (A_sub) + cfc (R := ℝ) f (B_sub)) := by
    rw [hM_sub_eq]
    exact hsub_fc
  let mU : ↥V →L[ℂ] ↥V := M_sub
  let aU : ↥V →L[ℂ] ↥V := A_sub
  let bU : ↥V →L[ℂ] ↥V := B_sub
  let gm : ↥V →L[ℂ] ↥V :=
    @complexCfcCLM ↥V _ _ hUSubComplete _ _
      hCfcV g mU
  let ga : ↥V →L[ℂ] ↥V :=
    @complexCfcCLM ↥V _ _ hUSubComplete _ _
      hCfcV g aU
  let gb : ↥V →L[ℂ] ↥V :=
    @complexCfcCLM ↥V _ _ hUSubComplete _ _
      hCfcV g bU
  /- Step 5: Bridge the real compressed CFC inequality to the complex normal CFC model. -/
  have hsub_fcC :
      gm ≤ (1 / 2 : ℝ) • (ga + gb) := by
    have hsub_fcR :
        cfc (R := ℝ) f mU ≤
          (1 / 2 : ℝ) • (cfc (R := ℝ) f aU + cfc (R := ℝ) f bU) := by
      exact hsub_fc'
    change
      cfc (R := ℂ) g mU ≤
        (1 / 2 : ℝ) • (cfc (R := ℂ) g aU + cfc (R := ℂ) g bU)
    exact
      @realCfc_midpoint_convex_bridge_sort_named
        ↥V _ _ hUSubComplete
        (instStarOrderedRingSubtypeSubmoduleEnd (U := V))
        (show AddRightMono (↥V →L[ℂ] ↥V) from inferInstance)
        hUNonnegSub
        hCfcV
        hRealCfc
        f g mU aU bU
        rfl hM_sub_sa hA_sub_sa hB_sub_sa hsub_fcR
  have hsub_cx :
      spectrum ℂ (A_sub) ⊆ Ω ∧
        spectrum ℂ (B_sub) ⊆ Ω ∧
        spectrum ℂ (M_sub) ⊆ Ω := by
    exact
      (@complex_spectrum_subset_of_real_Icc_triple
        ↥V _ _ hUSubComplete
        hRealCfc
        (by infer_instance : Nontrivial (↥V →L[ℂ] ↥V))
        aU bU mU α β
        hA_sub_sa hA_sub_Icc hB_sub_sa hB_sub_Icc hM_sub_sa hM_sub_Icc)
  have hA_sub_cx : spectrum ℂ (A_sub) ⊆ Ω := hsub_cx.1
  have hB_sub_cx : spectrum ℂ (B_sub) ⊆ Ω := hsub_cx.2.1
  have hM_sub_cx : spectrum ℂ (M_sub) ⊆ Ω := hsub_cx.2.2
  have hcontA :
      ContinuousOn g (spectrum ℂ (A_sub) ∪
        spectrum ℂ (((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ)))) :=
    continuousOn_union_of_subsets hgΩ hA_sub_cx hscalar
  have hcontB :
      ContinuousOn g (spectrum ℂ (B_sub) ∪
        spectrum ℂ (((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ)))) :=
    continuousOn_union_of_subsets hgΩ hB_sub_cx hscalar
  have hcontM :
      ContinuousOn g (spectrum ℂ (M_sub) ∪
        spectrum ℂ (((t₀ : ℂ) • (1 : Vᗮ →L[ℂ] Vᗮ)))) :=
    continuousOn_union_of_subsets hgΩ hM_sub_cx hscalar
  letI : ContinuousFunctionalCalculus ℂ ((↥V →L[ℂ] ↥V) × (↥Vᗮ →L[ℂ] ↥Vᗮ)) IsStarNormal :=
    subtypeSubmodulePairEndStarNormalCfcDef (U := V)
  exact blockExtension_cfcNormal_midpoint_le_of_compressed (ℋ := ℋ) hcontA hcontB hcontM
    hA_sub_norm hB_sub_norm hM_sub_norm hsub_fcC

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Per-block midpoint-convexity CFC comparison for the finite-span compression
step of Proposition 5.1.5 (2): on a nonempty finite span `hilbertFiniteSpan b s`,
the compressed midpoint inequality transports through the block-extension normal
CFC.  Extracted from `matrixConvexImpliesOperatorMidpointConvex_core` so that
the heavy subspace instance elaboration and the block-CFC comparison elaborate
in their own declaration. -/
private theorem hilbertFiniteSpan_blockExtension_cfcNormal_midpoint_le
    {J : Set ℝ} {f : ℝ → ℝ} {α β t₀ : ℝ}
    (hJ : Convex ℝ J)
    (hfJ : ContinuousOn f J)
    (hmat : MatrixOperatorMidpointConvexOnInterval J f)
    (hIccJ : Set.Icc α β ⊆ J)
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (hB_bounds : (α : ℂ) • (1 : L ℋ) ≤ B ∧ B ≤ (β : ℂ) • (1 : L ℋ))
    (hM_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (A + B)))
    (hM_bounds :
      (α : ℂ) • (1 : L ℋ) ≤ (1 / 2 : ℝ) • (A + B) ∧
        (1 / 2 : ℝ) • (A + B) ≤ (β : ℂ) • (1 : L ℋ))
    (hgΩ : ContinuousOn (fun z : ℂ => (f z.re : ℂ)) (Complex.ofReal '' Set.Icc α β))
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ) (s : Finset ι) (hs0 : s ≠ ∅)
    (hscalar :
      spectrum ℂ
          ((t₀ : ℂ) • (1 :
            ↥((hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ) →L[ℂ]
              ↥((hilbertFiniteSpan (ℋ := ℋ) b s)ᗮ))) ⊆
        Complex.ofReal '' Set.Icc α β) :
    cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
        ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * ((1 / 2 : ℝ) • (A + B)) *
            (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
          (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
            ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * A *
                (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
              (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) +
          cfcNormal (ℋ := ℋ) (fun z : ℂ => (f z.re : ℂ))
            ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection * B *
                (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection +
              (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection))) := by
  haveI : Nontrivial (hilbertFiniteSpan (ℋ := ℋ) b s) :=
    nontrivial_hilbertFiniteSpan_of_ne_empty (ℋ := ℋ) b hs0
  exact blockExtension_cfcNormal_midpoint_le_of_finiteDimensional (ℋ := ℋ) hJ hfJ hmat hIccJ
    hA hB hA_bounds hB_bounds hM_sa hM_bounds hgΩ (hilbertFiniteSpan (ℋ := ℋ) b s) hscalar

/-- Convexity half of the finite-dimensional bridge in Proposition 5.1.5.
Matrix operator convexity on every finite-dimensional matrix algebra implies
operator midpoint convexity on the ambient Hilbert space, via finite-span
compression, block-extension CFC, and a strong-operator limit.
Source: Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixConvexImpliesOperatorMidpointConvex_core :
    MatrixConvexImpliesOperatorMidpointConvex (ℋ := ℋ) := by
  intro J f hJ hfJ hmat A B hA hB hσA hσB
  /- Step 1: Exclude the empty interval before choosing a block-extension base point. -/
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
    /- Step 2: Put A, B, and their midpoint in one compact interval and lift f to normal CFC. -/
    let g : ℂ → ℂ := fun z => (f z.re : ℂ)
    let Ω : Set ℂ := Complex.ofReal '' Set.Icc α β
    let M : L ℋ := (1 / 2 : ℝ) • (A + B)
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
    have hM_sa : IsSelfAdjoint M := by
      change star M = M
      calc
        star M = (1 / 2 : ℝ) • (star A + star B) := by
          simp [M, smul_add]
        _ = (1 / 2 : ℝ) • (A + B) := by rw [hA, hB]
        _ = M := by simp [M]
    have hM_bounds : (α : ℂ) • (1 : L ℋ) ≤ M ∧ M ≤ (β : ℂ) • (1 : L ℋ) :=
      midpoint_order_bounds (K := ℋ) hA_bounds hB_bounds
    /- Step 3: Choose finite block extensions converging to A, B, and the midpoint. -/
    obtain ⟨ι, b, hb⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := ℋ)
    let U : Finset ι → Submodule ℂ ℋ := hilbertFiniteSpan (ℋ := ℋ) b
    let P : Finset ι → L ℋ := fun s => (U s).starProjection
    let A_sub : (s : Finset ι) → (U s →L[ℂ] U s) :=
      fun s => (U s).orthogonalProjection ∘L A ∘L (U s).subtypeL
    let B_sub : (s : Finset ι) → (U s →L[ℂ] U s) :=
      fun s => (U s).orthogonalProjection ∘L B ∘L (U s).subtypeL
    let M_sub : (s : Finset ι) → (U s →L[ℂ] U s) :=
      fun s => (U s).orthogonalProjection ∘L M ∘L (U s).subtypeL
    let Atilde : Finset ι → L ℋ :=
      fun s => P s * A * P s + (t₀ : ℂ) • (1 - P s)
    let Btilde : Finset ι → L ℋ :=
      fun s => P s * B * P s + (t₀ : ℂ) • (1 - P s)
    let Mtilde : Finset ι → L ℋ :=
      fun s => P s * M * P s + (t₀ : ℂ) • (1 - P s)
    have hP : SOTTendsto (ℋ := ℋ) P 1 := by
      intro x
      simpa [P, U] using hilbertFiniteSpan_starProjection_tendsto_self (ℋ := ℋ) b x
    have hPbound : ∀ s, ‖P s‖ ≤ 1 := by
      simpa [P, U] using hilbertFiniteSpan_starProjection_uniformBound (ℋ := ℋ) b
    /- Step 4: Keep the scalar complement blocks in the same compact spectral window. -/
    have hScalar_Icc :
        ∀ s : Finset ι,
          spectrum ℂ (((t₀ : ℂ) • (1 : (U s)ᗮ →L[ℂ] (U s)ᗮ))) ⊆ Ω := by
      intro s
      have hUorthSubComplete : CompleteSpace ↥((U s)ᗮ) :=
        instCompleteSpaceSubtypeFromSort (U := (U s)ᗮ)
      have hUorthSortComplete : CompleteSpace ((U s)ᗮ) :=
        instCompleteSpaceSortFromSubtype (U := (U s)ᗮ)
      exact
        @scalar_block_complex_spectrum_subset ((U s)ᗮ) _ _ hUorthSortComplete α β t₀
          (hHull (Or.inr (by simp)))
    /- Step 5: Establish midpoint convexity on every finite block. -/
    have hblock :
        ∀ s : Finset ι,
          cfcNormal (ℋ := ℋ) g (Mtilde s) ≤
            (1 / 2 : ℝ) •
              (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s)) := by
      intro s
      by_cases hs0 : s = ∅
      · have hP0 : P s = 0 := by
          subst hs0
          simp [P, U, hilbertFiniteSpan]
        let T : L ℋ := cfcNormal (ℋ := ℋ) g ((t₀ : ℂ) • (1 : L ℋ))
        have hhalf : (1 / 2 : ℝ) • (T + T) = T := by
          calc
            (1 / 2 : ℝ) • (T + T) = (1 / 2 : ℝ) • ((2 : ℝ) • T) := by
              rw [two_smul]
            _ = ((1 / 2 : ℝ) * (2 : ℝ)) • T := by rw [smul_smul]
            _ = T := by norm_num
        have hle : T ≤ (1 / 2 : ℝ) • (T + T) := by
          rw [hhalf]
        simpa [Atilde, Btilde, Mtilde, M, hP0, T] using hle
      · exact
          hilbertFiniteSpan_blockExtension_cfcNormal_midpoint_le (ℋ := ℋ)
            hJ hfJ hmat hIccJ hA hB hA_bounds hB_bounds hM_sa hM_bounds hgΩ b s hs0
            (hScalar_Icc s)
    /- Step 6: Use SOT and normal CFC continuity to get the CFC limits. -/
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
    have hMtilde_tendsto : SOTTendsto (ℋ := ℋ) Mtilde M := by
      change
        SOTTendsto (ℋ := ℋ)
          (fun s => P s * M * P s + (t₀ : ℂ) • (1 - P s)) M
      exact block_extension_tendsto_self (ℋ := ℋ) (A := M) (t₀ := t₀) hP hPbound
    have hAtilde_normal : ∀ s : Finset ι, IsStarNormal (Atilde s) := fun s =>
      hilbertFiniteSpan_blockExtension_isStarNormal (ℋ := ℋ) hA b s
    have hBtilde_normal : ∀ s : Finset ι, IsStarNormal (Btilde s) := fun s =>
      hilbertFiniteSpan_blockExtension_isStarNormal (ℋ := ℋ) hB b s
    have hMtilde_normal : ∀ s : Finset ι, IsStarNormal (Mtilde s) := fun s =>
      hilbertFiniteSpan_blockExtension_isStarNormal (ℋ := ℋ) hM_sa b s
    have hσAtilde : ∀ s : Finset ι, spectrum ℂ (Atilde s) ⊆ Ω := fun s =>
      hilbertFiniteSpan_blockExtension_spectrum_subset_ofReal_Icc (ℋ := ℋ)
        (hHull (Or.inr (by simp))) hA hA_bounds b s
    have hσBtilde : ∀ s : Finset ι, spectrum ℂ (Btilde s) ⊆ Ω := fun s =>
      hilbertFiniteSpan_blockExtension_spectrum_subset_ofReal_Icc (ℋ := ℋ)
        (hHull (Or.inr (by simp))) hB hB_bounds b s
    have hσMtilde : ∀ s : Finset ι, spectrum ℂ (Mtilde s) ⊆ Ω := fun s =>
      hilbertFiniteSpan_blockExtension_spectrum_subset_ofReal_Icc (ℋ := ℋ)
        (hHull (Or.inr (by simp))) hM_sa hM_bounds b s
    have hσAΩ : spectrum ℂ A ⊆ Ω :=
      complex_spectrum_subset_of_real_Icc (ℋ := ℋ) hA <|
        spectrum_subset_Icc_of_order_bounds_clm (K := ℋ) hA hA_bounds.1 hA_bounds.2
    have hσBΩ : spectrum ℂ B ⊆ Ω :=
      complex_spectrum_subset_of_real_Icc (ℋ := ℋ) hB <|
        spectrum_subset_Icc_of_order_bounds_clm (K := ℋ) hB hB_bounds.1 hB_bounds.2
    have hσMΩ : spectrum ℂ M ⊆ Ω :=
      complex_spectrum_subset_of_real_Icc (ℋ := ℋ) hM_sa <|
        spectrum_subset_Icc_of_order_bounds_clm (K := ℋ) hM_sa hM_bounds.1 hM_bounds.2
    have hcfA := SOTTendsto.cfcNormal (ℋ := ℋ) (Ω := Ω) (f := g) (A := A) (Aγ := Atilde)
      hΩ hAtilde_normal hA.isStarNormal hσAtilde hσAΩ hgΩ hAtilde_tendsto
    have hcfB := SOTTendsto.cfcNormal (ℋ := ℋ) (Ω := Ω) (f := g) (A := B) (Aγ := Btilde)
      hΩ hBtilde_normal hB.isStarNormal hσBtilde hσBΩ hgΩ hBtilde_tendsto
    have hcfM := SOTTendsto.cfcNormal (ℋ := ℋ) (Ω := Ω) (f := g) (A := M) (Aγ := Mtilde)
      hΩ hMtilde_normal hM_sa.isStarNormal hσMtilde hσMΩ hgΩ hMtilde_tendsto
    /- Step 7: Return to real CFC and pass positivity through quadratic-form limits. -/
    have hrealA : cfcR (ℋ := ℋ) f A = cfcNormal (ℋ := ℋ) g A :=
      realCfc_eq_normalCfc_of_selfAdjoint (K := ℋ) (f := f) hA
    have hrealB : cfcR (ℋ := ℋ) f B = cfcNormal (ℋ := ℋ) g B :=
      realCfc_eq_normalCfc_of_selfAdjoint (K := ℋ) (f := f) hB
    have hrealM : cfcR (ℋ := ℋ) f M = cfcNormal (ℋ := ℋ) g M :=
      realCfc_eq_normalCfc_of_selfAdjoint (K := ℋ) (f := f) hM_sa
    rw [hrealM, hrealA, hrealB]
    have hself_target :
        IsSelfAdjoint
          ((1 / 2 : ℝ) • (cfcNormal (ℋ := ℋ) g A + cfcNormal (ℋ := ℋ) g B) -
            cfcNormal (ℋ := ℋ) g M) := by
      rw [← hrealA, ← hrealB, ← hrealM]
      have hsum_sa :
          IsSelfAdjoint (cfcR (ℋ := ℋ) f A + cfcR (ℋ := ℋ) f B) := by
        exact (IsSelfAdjoint.cfc (R := ℝ) (A := L ℋ) (f := f) (a := A)).add
          (IsSelfAdjoint.cfc (R := ℝ) (A := L ℋ) (f := f) (a := B))
      have hABsa :
          IsSelfAdjoint
            ((1 / 2 : ℝ) • (cfcR (ℋ := ℋ) f A + cfcR (ℋ := ℋ) f B)) := by
        have hhalf : IsSelfAdjoint ((1 / 2 : ℝ)) := by
          simp [isSelfAdjoint_iff]
        exact hhalf.smul hsum_sa
      exact hABsa.sub (IsSelfAdjoint.cfc (R := ℝ) (A := L ℋ) (f := f) (a := M))
    refine le_of_quadratic_form_nonneg (ℋ := ℋ) hself_target ?_
    intro x
    have hquad_s :
        ∀ s : Finset ι,
          0 ≤ RCLike.re
            (inner ℂ
              (((1 / 2 : ℝ) •
                  (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s)) -
                cfcNormal (ℋ := ℋ) g (Mtilde s)) x) x) := by
      intro s
      have hspos :
          (((1 / 2 : ℝ) •
              (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s))) -
            cfcNormal (ℋ := ℋ) g (Mtilde s)).IsPositive :=
        (ContinuousLinearMap.le_def _ _).mp (hblock s)
      exact (ContinuousLinearMap.isPositive_iff_complex _).1 hspos x |>.2
    have hmid_eval :
        Tendsto
          (fun s : Finset ι =>
            (((1 / 2 : ℝ) •
                (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s))) -
              cfcNormal (ℋ := ℋ) g (Mtilde s)) x)
          atTop
          (𝓝
            ((((1 / 2 : ℝ) •
                (cfcNormal (ℋ := ℋ) g A + cfcNormal (ℋ := ℋ) g B)) -
              cfcNormal (ℋ := ℋ) g M) x)) := by
      change Tendsto
          (fun s : Finset ι =>
            ((((1 / 2 : ℝ) •
                (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s))) -
              cfcNormal (ℋ := ℋ) g (Mtilde s)) x))
          atTop
          (𝓝
            ((((1 / 2 : ℝ) •
                (cfcNormal (ℋ := ℋ) g A + cfcNormal (ℋ := ℋ) g B)) -
              cfcNormal (ℋ := ℋ) g M) x))
      have hsum_eval :=
        ((((hcfA x).add (hcfB x)).const_smul (1 / 2 : ℝ)).sub (hcfM x))
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] using hsum_eval
    have hinner_eval :
        Tendsto
          (fun s : Finset ι =>
            Complex.re
              (inner ℂ
                ((((1 / 2 : ℝ) •
                    (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s))) -
                  cfcNormal (ℋ := ℋ) g (Mtilde s)) x) x))
          atTop
          (𝓝
            (Complex.re
              (inner ℂ
                ((((1 / 2 : ℝ) •
                    (cfcNormal (ℋ := ℋ) g A + cfcNormal (ℋ := ℋ) g B)) -
                  cfcNormal (ℋ := ℋ) g M) x) x))) := by
      have hinner :
          Tendsto
            (fun s : Finset ι =>
              inner ℂ
                ((((1 / 2 : ℝ) •
                    (cfcNormal (ℋ := ℋ) g (Atilde s) + cfcNormal (ℋ := ℋ) g (Btilde s))) -
                  cfcNormal (ℋ := ℋ) g (Mtilde s)) x) x)
            atTop
            (𝓝
              (inner ℂ
                ((((1 / 2 : ℝ) •
                    (cfcNormal (ℋ := ℋ) g A + cfcNormal (ℋ := ℋ) g B)) -
                  cfcNormal (ℋ := ℋ) g M) x) x)) := by
        exact ((continuous_id.inner continuous_const).continuousAt.tendsto.comp hmid_eval)
      exact Complex.continuous_re.continuousAt.tendsto.comp hinner
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    simpa [Set.mem_Ici] using
      hclosed.mem_of_tendsto hinner_eval (Filter.Eventually.of_forall hquad_s)

end BlockExtensionInternal

end NormalCFC514

end HansenPedersen
