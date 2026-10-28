/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.OrderTransport
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Spectrum and normality facts for finite-dimensional block extensions.

This module isolates the block-extension spectrum payload used by the
finite-dimensional Hansen--Pedersen functional-calculus bridge.
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

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- A nonempty finite span of a Hilbert basis is nontrivial. -/
theorem nontrivial_hilbertFiniteSpan_of_ne_empty {ι : Type*}
    (b : HilbertBasis ι ℂ ℋ) {s : Finset ι}
    (hs : s ≠ ∅) :
    Nontrivial (hilbertFiniteSpan (ℋ := ℋ) b s) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  let x : hilbertFiniteSpan (ℋ := ℋ) b s :=
    ⟨b i, Submodule.subset_span ⟨i, by simpa using hi, rfl⟩⟩
  refine ⟨⟨0, x, ?_⟩⟩
  intro hx
  have : (b i : ℋ) = 0 := by
    simpa [x] using (congrArg Subtype.val hx).symm
  exact b.orthonormal.ne_zero i this
/-- The spectrum of a real scalar block is contained in the complex image of
any real interval containing that scalar. -/
theorem scalar_block_complex_spectrum_subset
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {α β t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc α β) :
    spectrum ℂ (((t₀ : ℂ) • (1 : K →L[ℂ] K))) ⊆ Complex.ofReal '' Set.Icc α β := by
  classical
  rcases subsingleton_or_nontrivial (K →L[ℂ] K) with hK | hK
  · letI : Subsingleton (K →L[ℂ] K) := hK
    simp
  · letI : Nontrivial (K →L[ℂ] K) := hK
    letI : ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus (A := K →L[ℂ] K)
    intro z hz
    have hz' : z ∈ ({(t₀ : ℂ)} : Set ℂ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (CFC.spectrum_algebraMap_subset (R := ℂ) (A := K →L[ℂ] K) (t₀ : ℂ) hz)
    rcases Set.mem_singleton_iff.mp hz' with rfl
    exact ⟨t₀, ht₀, by simp⟩

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private theorem blockConjDiagMap_mono_both
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    {a₁ a₂ : U →L[ℂ] U} {b₁ b₂ : Uᗮ →L[ℂ] Uᗮ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    blockConjDiagMap (U := U) (a := a₁) (b := b₁) ≤
      blockConjDiagMap (U := U) (a := a₂) (b := b₂) := by
  refine (ContinuousLinearMap.le_def _ _).2 ?_
  letI : CompleteSpace U := by
    simpa using (inferInstance : CompleteSpace ↥U)
  letI : CompleteSpace Uᗮ := by
    simpa using (inferInstance : CompleteSpace ↥Uᗮ)
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) :=
    instWithLpSubmodulePairCompleteSpaceSortCoe (U := U)
  let S : WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] ℋ :=
    U.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let R : ℋ →L[ℂ] WithLp 2 (↥U × ↥Uᗮ) :=
    U.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap
  have hdiag_pos : (diagMapCLM a₂ b₂ - diagMapCLM a₁ b₁).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp <|
      @HansenPedersen.Internal.diagMapCLM_mono
        ↥U _ _ ‹CompleteSpace ↥U›
        ↥Uᗮ _ _ ‹CompleteSpace ↥Uᗮ›
        a₁ a₂ b₁ b₂ ha hb
  have hpush_pos :
      (S ∘L (diagMapCLM a₂ b₂ - diagMapCLM a₁ b₁) ∘L R).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    let M : WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] WithLp 2 (↥U × ↥Uᗮ) :=
      diagMapCLM a₂ b₂ - diagMapCLM a₁ b₁
    have hM_pos : M.IsPositive := by
      simpa [M] using hdiag_pos
    have hx : S (R x) = x := by
      change
        U.orthogonalDecomposition.toContinuousLinearEquiv.symm
            (U.orthogonalDecomposition.toContinuousLinearEquiv x) = x
      exact U.orthogonalDecomposition.toContinuousLinearEquiv.symm_apply_apply x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have hinner :
        inner ℂ (S (M (R x))) x = inner ℂ (M (R x)) (R x) := by
      calc
        inner ℂ (S (M (R x))) x = inner ℂ (S (M (R x))) (S (R x)) := by
          exact congrArg (fun z => inner ℂ (S (M (R x))) z) hx.symm
        _ = inner ℂ (M (R x)) (R x) := by
          simpa [S] using
            (U.orthogonalDecomposition.symm.inner_map_map (M (R x)) (R x))
    have hxM := (ContinuousLinearMap.isPositive_iff_complex _).1 hM_pos (R x)
    have hprod :
        inner ℂ (M (R x)) (R x) =
          inner ℂ ↑(M (R x)).fst ↑(R x).fst + inner ℂ ↑(M (R x)).snd ↑(R x).snd := by
      simp [WithLp.prod_inner_apply]
    have hM_real : ↑(inner ℂ (M (R x)) (R x)).re = inner ℂ (M (R x)) (R x) := by
      simpa [hprod] using hxM.1
    have hM_nonneg : 0 ≤ (inner ℂ (M (R x)) (R x)).re := by
      simpa [hprod] using hxM.2
    refine ⟨?_, ?_⟩
    · calc
        ↑(inner ℂ (S (M (R x))) x).re = ↑(inner ℂ (M (R x)) (R x)).re := by
          simp [hinner]
        _ = inner ℂ (M (R x)) (R x) := hM_real
        _ = inner ℂ (S (M (R x))) x := hinner.symm
    · calc
        0 ≤ (inner ℂ (M (R x)) (R x)).re := hM_nonneg
        _ = (inner ℂ (S (M (R x))) x).re := by
          simp [hinner]
  change ((S ∘L diagMapCLM a₂ b₂ ∘L R) - (S ∘L diagMapCLM a₁ b₁ ∘L R)).IsPositive
  have hpush_eq :
      ((S ∘L diagMapCLM a₂ b₂ ∘L R) - (S ∘L diagMapCLM a₁ b₁ ∘L R)) =
        S ∘L (diagMapCLM a₂ b₂ - diagMapCLM a₁ b₁) ∘L R := by
    ext x
    change
      S ((diagMapCLM a₂ b₂) (R x)) - S ((diagMapCLM a₁ b₁) (R x)) =
        S (((diagMapCLM a₂ b₂) (R x)) - ((diagMapCLM a₁ b₁) (R x)))
    rw [map_sub]
  exact hpush_eq.symm ▸ hpush_pos

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Loewner comparison of real scalar multiples of the identity, extracted from
`block_extension_real_spectrum_subset_Icc` (used for both scalar-block bounds). -/
private theorem coe_smul_one_le_coe_smul_one_of_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {c d : ℝ} (hcd : c ≤ d) :
    (c : ℂ) • (1 : V →L[ℂ] V) ≤ (d : ℂ) • (1 : V →L[ℂ] V) := by
  refine (ContinuousLinearMap.le_def _ _).2 ?_
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hsub :
      (d : ℂ) • (1 : V →L[ℂ] V) - (c : ℂ) • (1 : V →L[ℂ] V) =
        (((d - c : ℝ) : ℂ)) • (1 : V →L[ℂ] V) := by
    ext y
    simp [sub_eq_add_neg, add_smul]
  refine ⟨?_, ?_⟩
  · have hsym :
        ((((d - c : ℝ) : ℂ)) • (1 : V →L[ℂ] V) : V →ₗ[ℂ] V).IsSymmetric := by
      intro x y
      change inner ℂ (((((d - c : ℝ) : ℂ)) • x : V)) y =
        inner ℂ x (((((d - c : ℝ) : ℂ)) • y : V))
      calc
        inner ℂ (((((d - c : ℝ) : ℂ)) • x : V)) y =
            (starRingEnd ℂ) (((d - c : ℝ) : ℂ)) * inner ℂ x y := by
            rw [inner_smul_left]
        _ = (((d - c : ℝ) : ℂ)) * inner ℂ x y := by simp
        _ = inner ℂ x (((((d - c : ℝ) : ℂ)) • y : V)) := by
            rw [inner_smul_right]
    have hsymm :
        ((d : ℂ) • (1 : V →L[ℂ] V) -
          (c : ℂ) • (1 : V →L[ℂ] V)).toLinearMap.IsSymmetric := by
      rw [hsub]
      simpa using hsym
    exact Complex.conj_eq_iff_re.mp
      ((LinearMap.isSymmetric_iff_inner_map_self_real _).mp hsymm x)
  · have hsub_apply :
        ((d : ℂ) • (1 : V →L[ℂ] V) - (c : ℂ) • (1 : V →L[ℂ] V)) x =
          (((d - c : ℝ) : ℂ)) • x := by
      change ((d : ℂ) • x - (c : ℂ) • x) = (((d - c : ℝ) : ℂ)) • x
      rw [← sub_smul]
      simp
    have hxx : 0 ≤ RCLike.re (inner ℂ x x) := by
      simpa using (inner_self_nonneg : 0 ≤ RCLike.re (inner ℂ x x))
    have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
    have hinner :
        RCLike.re
          (inner ℂ
            (((d : ℂ) • (1 : V →L[ℂ] V) -
              (c : ℂ) • (1 : V →L[ℂ] V)) x) x) =
          (d - c) * RCLike.re (inner ℂ x x) := by
      rw [hsub_apply, inner_smul_left]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    exact hinner.symm ▸ (mul_nonneg hdc hxx)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- The conjugated block-diagonal form of a real scalar multiple of the identity
is the scalar itself, extracted from `block_extension_real_spectrum_subset_Icc`
(used for both interval endpoints). -/
private theorem blockExtensionConjDiag_smul_one
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    (r : ℝ) :
    blockExtensionConjDiag (U := U) ((r : ℂ) • (1 : L ℋ)) r = (r : ℂ) • (1 : L ℋ) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  letI : CompleteSpace ↥Uᗮ := instCompleteSpaceSubtypeFromSort (U := Uᗮ)
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := instWithLpSubmodulePairCompleteSpace (U := U)
  rw [block_extension_eq_conj_diag (U := U) ((r : ℂ) • (1 : L ℋ)) r]
  have hmul :
      U.starProjection * ((r : ℂ) • (1 : L ℋ)) * U.starProjection =
        (r : ℂ) • U.starProjection := by
    ext x
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, Submodule.starProjection_apply]
    rw [map_smul]
    have hp :
        ↑(U.orthogonalProjection (U.starProjection x)) = U.starProjection x := by
      exact congrArg Subtype.val <|
        Submodule.orthogonalProjection_mem_subspace_eq_self
          ⟨U.starProjection x, Submodule.starProjection_apply_mem U x⟩
    change r • ↑(U.orthogonalProjection (U.starProjection x)) = r • U.starProjection x
    rw [hp]
  unfold blockExtensionDiag
  rw [hmul]
  ext x
  simp [sub_eq_add_neg]

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Self-adjointness of the block extension `P A P + t₀ (1 - P)` of a
self-adjoint operator, extracted from the block-extension spectrum proofs. -/
private theorem blockExtension_isSelfAdjoint_of_isSelfAdjoint
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection]
    {A : L ℋ} {t₀ : ℝ} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint
      (U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection)) := by
  have hprojA_sa : IsSelfAdjoint (U.starProjection * A * U.starProjection) := by
    have hP :
        ContinuousLinearMap.adjoint U.starProjection = U.starProjection := by
      have hPsa : IsSelfAdjoint U.starProjection := isSelfAdjoint_starProjection U
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hPsa
      exact hPsa
    have hconj :
        IsSelfAdjoint
          ((ContinuousLinearMap.adjoint U.starProjection).comp
            (ContinuousLinearMap.comp A U.starProjection)) := by
      simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
        (hA.adjoint_conj U.starProjection)
    simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, hP] using hconj
  have hcompl_sa : IsSelfAdjoint ((1 : L ℋ) - U.starProjection) := by
    exact IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_starProjection U)
  have ht₀_sa : IsSelfAdjoint (t₀ : ℂ) := by
    simp [isSelfAdjoint_iff]
  have hscalar_sa_ambient :
      IsSelfAdjoint ((t₀ : ℂ) • ((1 : L ℋ) - U.starProjection)) := by
    exact ht₀_sa.smul hcompl_sa
  simpa [blockExtensionDiag] using hprojA_sa.add hscalar_sa_ambient

/- Instance caches: the real scalar action and algebra structure on submodule
endomorphism spaces (`↥U →L[ℂ] ↥U`) and on `L ℋ` trigger deep `synthInstance`
derivations through the restricted real structure, re-run at many use sites of
the block-extension spectrum proof below.  Section-level reducible local instances turn
each search into a head-match (same pattern as `ConvexBridge.lean`). -/

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real scalar action on ambient operators used
in block-extension spectrum estimates. -/
@[reducible, local instance] noncomputable def instSMulRealLHScopedBES :
    SMul ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real module structure on ambient operators. -/
@[reducible, local instance] noncomputable def instModuleRealLHScopedBES :
    Module ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real algebra structure on ambient
operators. -/
@[reducible, local instance] noncomputable def instAlgebraRealLHScopedBES :
    Algebra ℝ (L ℋ) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
-- Direct `SMul` search times out through non-algebra candidates; naming
-- `Algebra.toSMul` leaves only the cheap `Algebra ℝ _` subgoal.
/-- Reducible local cache for real scalar multiplication on submodule
endomorphisms. -/
@[reducible, local instance] noncomputable def instSMulRealSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    SMul ℝ (↥U →L[ℂ] ↥U) :=
  Algebra.toSMul

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real module structure on submodule
endomorphisms. -/
@[reducible, local instance] noncomputable def instModuleRealSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    Module ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for distributed real scalar multiplication on
submodule endomorphisms. -/
@[reducible, local instance] noncomputable def instDistribSMulRealSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    DistribSMul ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real multiplicative action on submodule
endomorphisms. -/
@[reducible, local instance] noncomputable def instMulActionRealSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    MulAction ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the real algebra structure on submodule
endomorphisms. -/
@[reducible, local instance] noncomputable def instAlgebraRealSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    Algebra ℝ (↥U →L[ℂ] ↥U) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible local cache for the complex algebra structure on submodule
endomorphisms. -/
@[reducible, local instance] noncomputable def instAlgebraComplexSubmoduleEndScopedBES
    {U : Submodule ℂ ℋ} :
    Algebra ℂ (↥U →L[ℂ] ↥U) :=
  inferInstance

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Ambient lower bound for the block extension, extracted from
`block_extension_real_spectrum_subset_Icc`. -/
private theorem blockExtension_lower_bound
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    {A : L ℋ} {α t₀ : ℝ}
    (hA_lower : (α : ℂ) • (1 : L ℋ) ≤ A)
    (hαt : α ≤ t₀) :
    (α : ℂ) • (1 : L ℋ) ≤
      U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  letI : CompleteSpace ↥Uᗮ := instCompleteSpaceSubtypeFromSort (U := Uᗮ)
  letI : StarOrderedRing (U →L[ℂ] U) :=
    show StarOrderedRing (U →L[ℂ] U) from
      @ContinuousLinearMap.instStarOrderedRing U _ _
        (instCompleteSpaceSortFromSubtype (U := U))
  letI : AddRightMono (U →L[ℂ] U) := by infer_instance
  letI : StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) :=
    show StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) from
      @ContinuousLinearMap.instStarOrderedRing Uᗮ _ _
        (instCompleteSpaceSortFromSubtype (U := Uᗮ))
  letI : AddRightMono (Uᗮ →L[ℂ] Uᗮ) := by infer_instance
  letI : StarOrderedRing (↥U →L[ℂ] ↥U) := instStarOrderedRingSubtypeSubmoduleEnd (U := U)
  letI : AddRightMono (↥U →L[ℂ] ↥U) := by infer_instance
  letI : StarOrderedRing (↥Uᗮ →L[ℂ] ↥Uᗮ) :=
    instStarOrderedRingSubtypeSubmoduleEnd (U := Uᗮ)
  letI : AddRightMono (↥Uᗮ →L[ℂ] ↥Uᗮ) := by infer_instance
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) :=
    instWithLpSubmodulePairCompleteSpaceSortCoe (U := U)
  let Acomp : ↥U →L[ℂ] ↥U := compressionCLM (U := U) A
  let Scalar : ↥Uᗮ →L[ℂ] ↥Uᗮ := ((t₀ : ℂ) • (1 : ↥Uᗮ →L[ℂ] ↥Uᗮ))
  have hAcomp_lower0 : 0 ≤ Acomp - (α : ℂ) • (1 : ↥U →L[ℂ] ↥U) := by
    have hcomp :=
      (compression_le_of_le (U := U) (show 0 ≤ A - (α : ℂ) • (1 : L ℋ) by
        simpa [sub_eq_add_neg] using sub_nonneg.mpr hA_lower))
    have hcomp' :
        0 ≤ U.orthogonalProjection ∘L (A - (α : ℂ) • (1 : L ℋ)) ∘L U.subtypeL := by
      simpa [compressionCLM] using hcomp
    have hcomp'' :
        0 ≤
          (U.orthogonalProjection ∘L A ∘L U.subtypeL) -
            (α : ℂ) • (1 : ↥U →L[ℂ] ↥U) := by
      rw [compression_sub_scalar_eq (U := U) (A := A) (r := α)] at hcomp'
      exact hcomp'
    simpa [Acomp] using hcomp''
  have hAcomp_lower : (α : ℂ) • (1 : ↥U →L[ℂ] ↥U) ≤ Acomp :=
    sub_nonneg.mp hAcomp_lower0
  have hScalar_lower :
      (α : ℂ) • (1 : ↥Uᗮ →L[ℂ] ↥Uᗮ) ≤ Scalar :=
    @coe_smul_one_le_coe_smul_one_of_le ↥Uᗮ _ _
      (instCompleteSpaceSubtypeFromSort (U := Uᗮ)) α t₀ hαt
  have hscalar_block_alpha :
      (α : ℂ) • (1 : L ℋ) =
        blockExtensionConjDiag (U := U) ((α : ℂ) • (1 : L ℋ)) α :=
    (blockExtensionConjDiag_smul_one (U := U) α).symm
  change (α : ℂ) • (1 : L ℋ) ≤ blockExtensionDiag (U := U) A t₀
  rw [← block_extension_eq_conj_diag (U := U) A t₀, hscalar_block_alpha]
  change
    blockExtensionConjDiag (U := U) ((α : ℂ) • (1 : L ℋ)) α ≤
      blockExtensionConjDiag (U := U) A t₀
  change
    blockConjDiagMap (U := U)
        (a := U.orthogonalProjection ∘L ((α : ℂ) • (1 : L ℋ)) ∘L U.subtypeL)
        (b := ((α : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) ≤
      blockConjDiagMap (U := U) (a := Acomp) (b := Scalar)
  have hscalarComp :
      U.orthogonalProjection ∘L ((α : ℂ) • (1 : L ℋ)) ∘L U.subtypeL =
        ((α : ℂ) • (1 : U →L[ℂ] U)) := by
    simpa using (compression_scalar_eq (U := U) (r := α))
  rw [hscalarComp]
  exact blockConjDiagMap_mono_both (U := U) hAcomp_lower hScalar_lower

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Ambient upper bound for the block extension, extracted from
`block_extension_real_spectrum_subset_Icc`. -/
private theorem blockExtension_upper_bound
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    {A : L ℋ} {β t₀ : ℝ}
    (hA_upper : A ≤ (β : ℂ) • (1 : L ℋ))
    (htβ : t₀ ≤ β) :
    U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection) ≤
      (β : ℂ) • (1 : L ℋ) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  letI : CompleteSpace ↥Uᗮ := instCompleteSpaceSubtypeFromSort (U := Uᗮ)
  letI : StarOrderedRing (U →L[ℂ] U) :=
    show StarOrderedRing (U →L[ℂ] U) from
      @ContinuousLinearMap.instStarOrderedRing U _ _
        (instCompleteSpaceSortFromSubtype (U := U))
  letI : AddRightMono (U →L[ℂ] U) := by infer_instance
  letI : StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) :=
    show StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) from
      @ContinuousLinearMap.instStarOrderedRing Uᗮ _ _
        (instCompleteSpaceSortFromSubtype (U := Uᗮ))
  letI : AddRightMono (Uᗮ →L[ℂ] Uᗮ) := by infer_instance
  letI : StarOrderedRing (↥U →L[ℂ] ↥U) := instStarOrderedRingSubtypeSubmoduleEnd (U := U)
  letI : AddRightMono (↥U →L[ℂ] ↥U) := by infer_instance
  letI : StarOrderedRing (↥Uᗮ →L[ℂ] ↥Uᗮ) :=
    instStarOrderedRingSubtypeSubmoduleEnd (U := Uᗮ)
  letI : AddRightMono (↥Uᗮ →L[ℂ] ↥Uᗮ) := by infer_instance
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) :=
    instWithLpSubmodulePairCompleteSpaceSortCoe (U := U)
  let Acomp : ↥U →L[ℂ] ↥U := compressionCLM (U := U) A
  let Scalar : ↥Uᗮ →L[ℂ] ↥Uᗮ := ((t₀ : ℂ) • (1 : ↥Uᗮ →L[ℂ] ↥Uᗮ))
  have hAcomp_upper0 : 0 ≤ (β : ℂ) • (1 : ↥U →L[ℂ] ↥U) - Acomp := by
    have hcomp :=
      (compression_le_of_le (U := U) (show 0 ≤ (β : ℂ) • (1 : L ℋ) - A by
        simpa [sub_eq_add_neg] using sub_nonneg.mpr hA_upper))
    have hcomp' :
        0 ≤ U.orthogonalProjection ∘L ((β : ℂ) • (1 : L ℋ) - A) ∘L U.subtypeL := by
      simpa [compressionCLM] using hcomp
    have hcomp'' :
        0 ≤
          (β : ℂ) • (1 : ↥U →L[ℂ] ↥U) -
            (U.orthogonalProjection ∘L A ∘L U.subtypeL) := by
      rw [scalar_sub_compression_eq (U := U) (A := A) (r := β)] at hcomp'
      exact hcomp'
    simpa [Acomp] using hcomp''
  have hAcomp_upper : Acomp ≤ (β : ℂ) • (1 : ↥U →L[ℂ] ↥U) :=
    sub_nonneg.mp hAcomp_upper0
  have hScalar_upper :
      Scalar ≤ (β : ℂ) • (1 : ↥Uᗮ →L[ℂ] ↥Uᗮ) :=
    @coe_smul_one_le_coe_smul_one_of_le ↥Uᗮ _ _
      (instCompleteSpaceSubtypeFromSort (U := Uᗮ)) t₀ β htβ
  have hscalar_block_beta :
      blockExtensionConjDiag (U := U) ((β : ℂ) • (1 : L ℋ)) β =
        (β : ℂ) • (1 : L ℋ) :=
    blockExtensionConjDiag_smul_one (U := U) β
  change blockExtensionDiag (U := U) A t₀ ≤ (β : ℂ) • (1 : L ℋ)
  rw [← block_extension_eq_conj_diag (U := U) A t₀, ← hscalar_block_beta]
  change
    blockExtensionConjDiag (U := U) A t₀ ≤
      blockExtensionConjDiag (U := U) ((β : ℂ) • (1 : L ℋ)) β
  change
    blockConjDiagMap (U := U) (a := Acomp) (b := Scalar) ≤
      blockConjDiagMap (U := U)
        (a := U.orthogonalProjection ∘L ((β : ℂ) • (1 : L ℋ)) ∘L U.subtypeL)
        (b := ((β : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))
  have hscalarComp :
      U.orthogonalProjection ∘L ((β : ℂ) • (1 : L ℋ)) ∘L U.subtypeL =
        ((β : ℂ) • (1 : U →L[ℂ] U)) := by
    simpa using (compression_scalar_eq (U := U) (r := β))
  rw [hscalarComp]
  exact blockConjDiagMap_mono_both (U := U) hAcomp_upper hScalar_upper

omit [Nontrivial (L ℋ)] in
private theorem block_extension_real_spectrum_subset_Icc
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection]
    [CompleteSpace Uᗮ]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal]
    [Nontrivial (U →L[ℂ] U)]
    {A : L ℋ} {α β t₀ : ℝ}
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    spectrum ℝ
        (U.starProjection * A * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) ⊆
      Set.Icc α β := by
  have hU_nontriv : Nontrivial U := by
    by_cases hUsub : Subsingleton U
    · letI : Subsingleton U := hUsub
      have hEndSub : Subsingleton (U →L[ℂ] U) := inferInstance
      exact False.elim
        ((not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial (U →L[ℂ] U))) hEndSub)
    · exact not_subsingleton_iff_nontrivial.mp hUsub
  have hℋ_nontriv : Nontrivial ℋ := by
    rcases hU_nontriv.exists_pair_ne with ⟨u, v, huv⟩
    exact ⟨⟨(u : ℋ), (v : ℋ), fun h => huv (Subtype.ext h)⟩⟩
  letI : Nontrivial ℋ := hℋ_nontriv
  letI : Nontrivial (L ℋ) := by infer_instance
  have hT_sa :
      IsSelfAdjoint
        (U.starProjection * A * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) :=
    blockExtension_isSelfAdjoint_of_isSelfAdjoint (U := U) hA
  have hT_lower :
      (α : ℂ) • (1 : L ℋ) ≤
        U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection) :=
    blockExtension_lower_bound (U := U) hA_bounds.1 ht₀.1
  have hT_upper :
      U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection) ≤
        (β : ℂ) • (1 : L ℋ) :=
    blockExtension_upper_bound (U := U) hA_bounds.2 ht₀.2
  have hT_Icc :
      spectrum ℝ
          (U.starProjection * A * U.starProjection +
            (t₀ : ℂ) • (1 - U.starProjection)) ⊆
        Set.Icc α β := by
    intro x hx
    constructor
    · have hlowspec := (algebraMap_le_iff_le_spectrum (R := ℝ)
        (A := L ℋ) (p := IsSelfAdjoint) (r := α)
        (a := U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection))
        (ha := hT_sa)).1 hT_lower
      exact hlowspec x hx
    · have huppspec := (le_algebraMap_iff_spectrum_le (R := ℝ)
        (A := L ℋ) (p := IsSelfAdjoint) (r := β)
        (a := U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection))
        (ha := hT_sa)).1 hT_upper
      exact huppspec x hx
  exact hT_Icc

omit [Nontrivial (L ℋ)] in
private theorem block_extension_complex_spectrum_subset
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal]
    [Nontrivial (U →L[ℂ] U)]
  {A : L ℋ} {α β t₀ : ℝ}
  (hA : IsSelfAdjoint A)
  (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
  (ht₀ : t₀ ∈ Set.Icc α β) :
  spectrum ℂ
      (U.starProjection * A * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection)) ⊆
      Complex.ofReal '' Set.Icc α β := by
  have hT_sa :
      IsSelfAdjoint
        (U.starProjection * A * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) :=
    blockExtension_isSelfAdjoint_of_isSelfAdjoint (U := U) hA
  have hT_Icc :=
    block_extension_real_spectrum_subset_Icc (ℋ := ℋ) (U := U) hA hA_bounds ht₀
  intro z hz
  rw [← hT_sa.spectrumRestricts.algebraMap_image] at hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hT_Icc hx, rfl⟩

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- A block extension of a self-adjoint operator by a real scalar complement is
star-normal. -/
theorem block_extension_normal_of_selfAdjoint
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    {A : L ℋ} {t₀ : ℝ}
    (hA : IsSelfAdjoint A) :
    IsStarNormal
      (U.starProjection * A * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection)) :=
  by
    have hblock_sa :
        IsSelfAdjoint
          (U.starProjection * A * U.starProjection +
            (t₀ : ℂ) • (1 - U.starProjection)) := by
      have hprojA_sa : IsSelfAdjoint (U.starProjection * A * U.starProjection) := by
        have hP :
            ContinuousLinearMap.adjoint U.starProjection = U.starProjection := by
          have hPsa : IsSelfAdjoint U.starProjection := isSelfAdjoint_starProjection U
          rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hPsa
          exact hPsa
        have hconj :
            IsSelfAdjoint
              ((ContinuousLinearMap.adjoint U.starProjection).comp
                (ContinuousLinearMap.comp A U.starProjection)) := by
          simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
            (hA.adjoint_conj U.starProjection)
        simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, hP] using hconj
      have hcompl_sa : IsSelfAdjoint ((1 : L ℋ) - U.starProjection) := by
        exact IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_starProjection U)
      have ht₀_sa : IsSelfAdjoint (t₀ : ℂ) := by
        simp [isSelfAdjoint_iff]
      have hscalar_sa_ambient :
          IsSelfAdjoint ((t₀ : ℂ) • ((1 : L ℋ) - U.starProjection)) := by
        exact ht₀_sa.smul hcompl_sa
      simpa [blockExtensionDiag] using hprojA_sa.add hscalar_sa_ambient
    exact hblock_sa.isStarNormal
omit [Nontrivial (L ℋ)] in
private theorem block_extension_complex_spectrum_subset_of_bounds
    {U : Submodule ℂ ℋ} [CompleteSpace U] [U.HasOrthogonalProjection] [CompleteSpace Uᗮ]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal]
    [Nontrivial (U →L[ℂ] U)]
    {A : L ℋ} {α β t₀ : ℝ}
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    spectrum ℂ
        (U.starProjection * A * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) ⊆
      Complex.ofReal '' Set.Icc α β :=
  block_extension_complex_spectrum_subset (ℋ := ℋ) (U := U) (A := A)
    (hA := hA) (hA_bounds := hA_bounds) (ht₀ := ht₀)

omit [Nontrivial (L ℋ)] in
/-- Along every finite Hilbert-basis span, the block extension has complex
spectrum inside the complex image of the ambient real interval bounds. -/
theorem hilbertFiniteSpan_block_extension_complex_spectrum_subset
    {ι : Type*} (b : HilbertBasis ι ℂ ℋ)
    {A : L ℋ} {α β t₀ : ℝ}
    (hA : IsSelfAdjoint A)
    (hA_bounds : (α : ℂ) • (1 : L ℋ) ≤ A ∧ A ≤ (β : ℂ) • (1 : L ℋ))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    ∀ s : Finset ι,
      spectrum ℂ
          (((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) * A *
              ((hilbertFiniteSpan (ℋ := ℋ) b s).starProjection) +
            (t₀ : ℂ) • (1 - (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection)) ⊆
        Complex.ofReal '' Set.Icc α β := by
  intro s
  by_cases hs0 : s = ∅
  · have hP0 : (hilbertFiniteSpan (ℋ := ℋ) b s).starProjection = 0 := by
      subst hs0
      simp [hilbertFiniteSpan]
    intro z hz
    have hzscalar : z ∈ spectrum ℂ ((t₀ : ℂ) • (1 : L ℋ)) := by
      rw [hP0, zero_mul, mul_zero, sub_zero, zero_add] at hz
      simpa using hz
    exact scalar_block_complex_spectrum_subset (K := ℋ)
      (α := α) (β := β) (t₀ := t₀) ht₀ hzscalar
  · let U : Submodule ℂ ℋ := hilbertFiniteSpan (ℋ := ℋ) b s
    haveI : Nontrivial U := nontrivial_hilbertFiniteSpan_of_ne_empty (ℋ := ℋ) b hs0
    letI : CompleteSpace U := by
      simpa [U] using (inferInstance : CompleteSpace ↥U)
    letI : CompleteSpace Uᗮ := by
      simpa [U] using (inferInstance : CompleteSpace ↥Uᗮ)
    letI : CStarAlgebra (U →L[ℂ] U) :=
      @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace U _ _
        (instCompleteSpaceSortFromSubtype (U := U))
    letI : CStarAlgebra (Uᗮ →L[ℂ] Uᗮ) :=
      @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace Uᗮ _ _
        (instCompleteSpaceSortFromSubtype (U := Uᗮ))
    letI : ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    simpa [U] using
      (block_extension_complex_spectrum_subset_of_bounds (ℋ := ℋ) (U := U) (A := A)
        (hA := hA) (hA_bounds := hA_bounds) (ht₀ := ht₀))


end NormalCFC514

end HansenPedersen
