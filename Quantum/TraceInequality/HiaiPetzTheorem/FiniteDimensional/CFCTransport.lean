/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Instances
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.MatrixModel
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Functional-calculus transport for block extensions

This module transports complex normal functional calculus across the diagonal
block map and the orthogonal decomposition of a closed submodule.  It provides
the block-extension models and monotonicity transport used by the
finite-dimensional approximation layer.

## Main results

* `cfcNormal_diagMapCLM_union`: complex CFC of a diagonal block is diagonal CFC.
* `blockExtensionConjDiag` and `blockExtensionDiag`: two equivalent models of
  the block extension `P A P + t₀ (1 - P)`.
* `blockExtensionDiag_cfc_mono_from_subtype`: CFC monotonicity for compressed
  submodule operators lifts to the ambient block extensions.

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

/-- Complex continuous functional calculus commutes with a continuous star-algebra
homomorphism out of a product of C⋆-algebras (stated over abstract C⋆-algebras so that the
instance search stays cheap). -/
private theorem cfc_map_prod_starAlgHom_complex
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (φ : (A × B) →⋆ₐ[ℂ] C) (hφ : Continuous φ) {g : ℂ → ℂ} {a : A} {b : B}
    (hf : ContinuousOn g (spectrum ℂ a ∪ spectrum ℂ b))
    (ha : IsStarNormal a) (hb : IsStarNormal b) :
    cfc g (φ (a, b)) = φ (cfc g a, cfc g b) := by
  letI : ContinuousFunctionalCalculus ℂ (A × B) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hab : IsStarNormal (a, b) := ⟨Commute.prod ha.star_comm_self hb.star_comm_self⟩
  have hmap := StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) φ g (a, b)
    (hf := by rwa [Prod.spectrum_eq]) (hφ := hφ) (ha := hab) (hφa := hab.map φ)
  have hprod : cfc g (a, b) = (cfc g a, cfc g b) :=
    cfc_map_prod (R := ℂ) (S := ℂ) (A := A) (B := B) g a b (hf := hf) (hab := hab)
      (ha := ha) (hb := hb)
  rw [hprod] at hmap
  exact hmap.symm

/-- The diagonal block star-algebra homomorphism is continuous. -/
private theorem continuous_diagStarAlgHom_local
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    Continuous (diagStarAlgHom (K := K) (L' := L')) := by
  let e : WithLp 2 (K × L') ≃L[ℂ] K × L' := WithLp.prodContinuousLinearEquiv 2 ℂ K L'
  let pre :
      ((K × L') →L[ℂ] (K × L')) →L[ℂ]
        ((WithLp 2 (K × L')) →L[ℂ] (K × L')) :=
    ((ContinuousLinearMap.compL ℂ (WithLp 2 (K × L')) (K × L') (K × L')).flip
      (e : WithLp 2 (K × L') →L[ℂ] K × L'))
  let post :
      ((WithLp 2 (K × L')) →L[ℂ] (K × L')) →L[ℂ]
        ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    ContinuousLinearMap.compL ℂ (WithLp 2 (K × L')) (K × L') (WithLp 2 (K × L'))
      (e.symm : K × L' →L[ℂ] WithLp 2 (K × L'))
  have hdiag : Continuous fun p : (K →L[ℂ] K) × (L' →L[ℂ] L') =>
      diagMapCLM p.1 p.2 := by
    have hprod :
        Continuous fun p : (K →L[ℂ] K) × (L' →L[ℂ] L') =>
          p.1.prodMap p.2 := by
      simpa using
        (ContinuousLinearMap.prodMapL ℂ K K L' L').continuous.comp
          (continuous_fst.prodMk continuous_snd)
    simpa [diagMapCLM, e, pre, post] using post.continuous.comp (pre.continuous.comp hprod)
  exact hdiag

-- pair-hom instance synthesis for complex CFC is heavy
/-- Complex normal CFC of a diagonal block operator is the diagonal block of
the CFC values of its two entries, assuming continuity on the union of their
spectra. -/
theorem cfcNormal_diagMapCLM_union
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (L' →L[ℂ] L') IsStarNormal]
    [ContinuousFunctionalCalculus ℂ ((K →L[ℂ] K) × (L' →L[ℂ] L')) IsStarNormal]
    {g : ℂ → ℂ} {a : K →L[ℂ] K} {b : L' →L[ℂ] L'}
    (hf : ContinuousOn g (spectrum ℂ a ∪ spectrum ℂ b))
    (ha : IsStarNormal a) (hb : IsStarNormal b) :
    cfc (R := ℂ) g (diagMapCLM a b) =
      diagMapCLM (cfc (R := ℂ) g a) (cfc (R := ℂ) g b) :=
  cfc_map_prod_starAlgHom_complex (diagStarAlgHom (K := K) (L' := L'))
    continuous_diagStarAlgHom_local hf ha hb

/-- The complex spectrum of a diagonal block operator is contained in the union
of the spectra of its two diagonal entries. -/
theorem spectrum_diagMapCLM_subset_union
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : K →L[ℂ] K} {b : L' →L[ℂ] L'} :
    spectrum ℂ (diagMapCLM a b) ⊆ spectrum ℂ a ∪ spectrum ℂ b := by
  letI : CompleteSpace (WithLp 2 (K × L')) :=
    WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
  let hCstar :
      CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (WithLp 2 (K × L')) _ _
      ‹CompleteSpace (WithLp 2 (K × L'))›
  letI : CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar
  letI : Semiring ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Star ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : StarRing ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Algebra ℂ ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar.toAlgebra
  let Φ :
      ((K →L[ℂ] K) × (L' →L[ℂ] L')) →⋆ₐ[ℂ]
        ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    @HansenPedersen.Internal.diagStarAlgHom K inferInstance inferInstance inferInstance
      L' inferInstance inferInstance inferInstance
  intro z hz
  have hz' : z ∈ spectrum ℂ (a, b) := by
    exact AlgHom.spectrum_apply_subset Φ (a, b) hz
  simpa [Φ, Prod.spectrum_eq] using hz'

/-- A diagonal block operator is star-normal when both diagonal entries are
star-normal. -/
theorem isStarNormal_diagMapCLM_local
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : K →L[ℂ] K} {b : L' →L[ℂ] L'}
    (ha : IsStarNormal a) (hb : IsStarNormal b) :
    IsStarNormal (diagMapCLM a b) := by
  letI : CompleteSpace (WithLp 2 (K × L')) :=
    WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
  let hCstar :
      CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (WithLp 2 (K × L')) _ _
      ‹CompleteSpace (WithLp 2 (K × L'))›
  letI : CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar
  letI : Semiring ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Star ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : StarRing ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Algebra ℂ ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar.toAlgebra
  let Φ :
      ((K →L[ℂ] K) × (L' →L[ℂ] L')) →⋆ₐ[ℂ]
        ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    @HansenPedersen.Internal.diagStarAlgHom K inferInstance inferInstance inferInstance
      L' inferInstance inferInstance inferInstance
  have hab : IsStarNormal (a, b) := by
    exact ⟨Commute.prod ha.star_comm_self hb.star_comm_self⟩
  simpa [Φ] using hab.map Φ

-- orthogonal decomposition transport needs explicit pair-space instance search
-- expanding the concrete diagonal map application is still elaboration-heavy
omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Evaluation of a diagonal block through the orthogonal decomposition:
conjugating back to `ℋ` applies the first entry on `U` and the second entry on
`Uᗮ`. -/
theorem orthogonalDecomposition_symm_diagMapCLM_apply
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    {a : U →L[ℂ] U} {b : Uᗮ →L[ℂ] Uᗮ} (x : ℋ) :
    U.orthogonalDecomposition.symm (diagMapCLM a b (U.orthogonalDecomposition x)) =
      U.subtypeL (a (U.orthogonalProjection x)) +
        Uᗮ.subtypeL (b (Uᗮ.orthogonalProjection x)) := by
  rw [Submodule.orthogonalDecomposition_apply]
  simp [diagMapCLM]
  rfl

/-- Real scalar multiples of the identity are self-adjoint. -/
theorem isSelfAdjoint_smul_one_real_local
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (t : ℝ) :
    IsSelfAdjoint (((t : ℂ) • (1 : K →L[ℂ] K))) := by
  have ht : IsSelfAdjoint (t : ℂ) := by
    simp [isSelfAdjoint_iff]
  simpa using ht.smul (IsSelfAdjoint.one (K →L[ℂ] K))

/-- Real scalar multiples of the identity are star-normal. -/
theorem isStarNormal_smul_one_real_local
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (t : ℝ) :
    IsStarNormal (((t : ℂ) • (1 : K →L[ℂ] K))) :=
  (isSelfAdjoint_smul_one_real_local (K := K) t).isStarNormal

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Block extension written by conjugating a diagonal operator on
`U × Uᗮ` through the orthogonal decomposition of `ℋ`. -/
noncomputable def blockExtensionConjDiag
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    (A : L ℋ) (t₀ : ℝ) : L ℋ := by
  letI : CompleteSpace ↥U := inferInstance
  letI : CompleteSpace ↥Uᗮ := inferInstance
  exact
    (U.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
      diagMapCLM (U.orthogonalProjection ∘L A ∘L U.subtypeL)
        ((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) ∘L
      U.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Ambient formula for the block extension `P A P + t₀ (1 - P)`, where `P`
is the orthogonal projection onto `U`. -/
noncomputable def blockExtensionDiag
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    (A : L ℋ) (t₀ : ℝ) : L ℋ :=
  U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- The conjugated diagonal model and the ambient projection formula for the
block extension are equal. -/
theorem block_extension_eq_conj_diag
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    (A : L ℋ) (t₀ : ℝ) :
    blockExtensionConjDiag (U := U) A t₀ =
      blockExtensionDiag (U := U) A t₀ := by
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := instWithLpSubmodulePairCompleteSpace
  unfold blockExtensionConjDiag
  calc
    (U.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
        diagMapCLM (U.orthogonalProjection ∘L A ∘L U.subtypeL)
          ((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) ∘L
        U.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap =
        U.subtypeL ∘L (U.orthogonalProjection ∘L A ∘L U.subtypeL) ∘L
            U.orthogonalProjection +
          Uᗮ.subtypeL ∘L (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) ∘L
            Uᗮ.orthogonalProjection :=
      by
        ext x
        simpa using
          (orthogonalDecomposition_symm_diagMapCLM_apply (U := U)
            (a := U.orthogonalProjection ∘L A ∘L U.subtypeL)
            (b := ((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) x)
    _ = U.starProjection * A * U.starProjection +
          Uᗮ.starProjection * ((t₀ : ℂ) • (1 : L ℋ)) := by
      ext x
      have hfst :
          (U.starProjection * A * U.starProjection) x =
            U.subtypeL (U.orthogonalProjection (A (U.subtypeL (U.orthogonalProjection x)))) := by
        rfl
      have hsnd :
          (Uᗮ.starProjection * ((t₀ : ℂ) • (1 : L ℋ))) x =
            (t₀ : ℂ) • Uᗮ.subtypeL (Uᗮ.orthogonalProjection x) := by
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, Submodule.starProjection_apply]
        rw [map_smul]
        rfl
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      rw [hfst, hsnd]
      rfl
    _ = blockExtensionDiag (U := U) A t₀ := by
      have hmul :
          Uᗮ.starProjection * ((t₀ : ℂ) • (1 : L ℋ)) =
            (t₀ : ℂ) • Uᗮ.starProjection := by
        ext x
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
          Submodule.starProjection_apply]
        rw [map_smul]
        rfl
      unfold blockExtensionDiag
      rw [hmul, Submodule.starProjection_orthogonal]
      rfl

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Conjugated diagonal model of the complex CFC of a block extension.  The
first block is the CFC of the compression of `A`, and the second block is the
CFC of the scalar complement. -/
noncomputable def blockExtensionConjDiagCfc
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    {g : ℂ → ℂ} (A : L ℋ) (t₀ : ℝ) : L ℋ := by
  exact
    (U.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
      diagMapCLM
        (cfc (R := ℂ) (A := ↥U →L[ℂ] ↥U) g
          (U.orthogonalProjection ∘L A ∘L U.subtypeL))
        (cfc (R := ℂ) (A := ↥Uᗮ →L[ℂ] ↥Uᗮ) g
          (((t₀ : ℂ) • (1 : ↥Uᗮ →L[ℂ] ↥Uᗮ)))) ∘L
      U.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Ambient operator obtained by conjugating an arbitrary diagonal block
`diag(a, b)` through the orthogonal decomposition of `ℋ`. -/
noncomputable def blockConjDiagMap
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    {a : U →L[ℂ] U} {b : Uᗮ →L[ℂ] Uᗮ} : L ℋ :=
  (U.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
    diagMapCLM a b ∘L
    U.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Compression of an ambient operator to the closed submodule `U`. -/
noncomputable def compressionCLM
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] (A : L ℋ) :
    U →L[ℂ] U :=
  U.orthogonalProjection ∘L A ∘L U.subtypeL

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Monotonicity of the conjugated diagonal block map in its first diagonal
entry, with the second entry fixed. -/
theorem blockConjDiagMap_mono
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    {a1 a2 : U →L[ℂ] U} {b : Uᗮ →L[ℂ] Uᗮ}
    (ha : a1 ≤ a2) :
    blockConjDiagMap (U := U) (a := a1) (b := b) ≤
      blockConjDiagMap (U := U) (a := a2) (b := b) := by
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
  have hdiag_pos : (diagMapCLM a2 b - diagMapCLM a1 b).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp <|
      @HansenPedersen.Internal.diagMapCLM_mono
        ↥U _ _ ‹CompleteSpace ↥U›
        ↥Uᗮ _ _ ‹CompleteSpace ↥Uᗮ›
        a1 a2 b b ha le_rfl
  have hpush_pos :
      (S ∘L (diagMapCLM a2 b - diagMapCLM a1 b) ∘L R).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    let M : WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] WithLp 2 (↥U × ↥Uᗮ) :=
      diagMapCLM a2 b - diagMapCLM a1 b
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
  change ((S ∘L diagMapCLM a2 b ∘L R) - (S ∘L diagMapCLM a1 b ∘L R)).IsPositive
  have hpush_eq :
      ((S ∘L diagMapCLM a2 b ∘L R) - (S ∘L diagMapCLM a1 b ∘L R)) =
        S ∘L (diagMapCLM a2 b - diagMapCLM a1 b) ∘L R := by
    ext x
    change
      S ((diagMapCLM a2 b) (R x)) - S ((diagMapCLM a1 b) (R x)) =
        S (((diagMapCLM a2 b) (R x)) - ((diagMapCLM a1 b) (R x)))
    rw [map_sub]
  exact hpush_eq.symm ▸ hpush_pos

attribute [gcongr] blockConjDiagMap_mono

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Complex normal CFC commutes with conjugation by a linear isometry
equivalence. -/
theorem cfcNormal_conjStarAlgEquiv
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    {g : ℂ → ℂ} (e : ℋ ≃ₗᵢ[ℂ] K) {A : K →L[ℂ] K}
    (hcont : ContinuousOn g (spectrum ℂ A))
    (hnorm : IsStarNormal A) :
    cfcNormal (ℋ := ℋ) g
        ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          A ∘L e.toContinuousLinearEquiv.toContinuousLinearMap) =
      (e.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
        cfc (R := ℂ) g A ∘L
        e.toContinuousLinearEquiv.toContinuousLinearMap := by
  let Φ₀ := e.symm.conjStarAlgEquiv
  let Φop : (K →L[ℂ] K) →⋆ₐ[ℂ] L ℋ :=
    { Φ₀.toAlgEquiv.toAlgHom with
      map_star' := by
        intro T
        simpa [Φ₀] using Φ₀.map_star' T }
  have hφa : IsStarNormal (Φop A) := by
    simpa [Φ₀, Φop, LinearIsometryEquiv.conjStarAlgEquiv_apply] using hnorm.map Φop
  have hφ : Continuous Φop := by
    let e' : K ≃L[ℂ] ℋ := e.symm.toContinuousLinearEquiv
    let pre :
        ((K →L[ℂ] K) →L[ℂ] (ℋ →L[ℂ] K)) :=
      ((ContinuousLinearMap.compL ℂ ℋ K K).flip
        (e'.symm : ℋ →L[ℂ] K))
    let post :
        ((ℋ →L[ℂ] K) →L[ℂ] (ℋ →L[ℂ] ℋ)) :=
      ContinuousLinearMap.compL ℂ ℋ K ℋ
        (e' : K →L[ℂ] ℋ)
    simpa [Φ₀, Φop, e', pre, post, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_assoc] using
      post.continuous.comp pre.continuous
  have hmap := StarAlgHomClass.map_cfc Φop g A
    (hf := hcont) (hφ := hφ) (ha := hnorm) (hφa := hφa)
  simpa [cfcNormal, Φ₀, Φop, LinearIsometryEquiv.conjStarAlgEquiv_apply,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_assoc] using
    hmap.symm

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Complex normal CFC of a diagonal block operator conjugated by a linear isometry
equivalence onto the pair space is the conjugated diagonal of the two blockwise CFCs. -/
private theorem cfcNormal_conj_diagMapCLM
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [hK : CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [hL : CompleteSpace L']
    (e : ℋ ≃ₗᵢ[ℂ] WithLp 2 (K × L')) {g : ℂ → ℂ} {a : K →L[ℂ] K} {b : L' →L[ℂ] L'}
    (hf : ContinuousOn g (spectrum ℂ a ∪ spectrum ℂ b))
    (ha : IsStarNormal a) (hb : IsStarNormal b) :
    cfcNormal (ℋ := ℋ) g
        ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          diagMapCLM a b ∘L e.toContinuousLinearEquiv.toContinuousLinearMap) =
      (e.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
        diagMapCLM (cfc (R := ℂ) g a) (cfc (R := ℂ) g b) ∘L
        e.toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [cfcNormal_conjStarAlgEquiv e (hf.mono spectrum_diagMapCLM_subset_union)
      (isStarNormal_diagMapCLM_local ha hb),
    cfcNormal_diagMapCLM_union hf ha hb]

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Complex normal CFC of the ambient block extension equals the conjugated
diagonal CFC model. -/
theorem cfcNormal_blockExtensionDiag_eq_blockConjDiagMap
    {U : Submodule ℂ ℋ} [U.HasOrthogonalProjection] [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ (↥Uᗮ →L[ℂ] ↥Uᗮ) IsStarNormal]
    [ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal]
    {g : ℂ → ℂ} (X : L ℋ) (t₀ : ℝ)
    (hXcont :
      ContinuousOn g
        (spectrum ℂ (U.orthogonalProjection ∘L X ∘L U.subtypeL) ∪
          spectrum ℂ (((t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))))
    (hXnorm : IsStarNormal (U.orthogonalProjection ∘L X ∘L U.subtypeL)) :
    cfcNormal (ℋ := ℋ) g (blockExtensionDiag (U := U) X t₀) =
      blockExtensionConjDiagCfc (U := U) (g := g) X t₀ := by
  /- Replace the ambient block extension by its conjugated diagonal representative, then
  transport the CFC through the orthogonal decomposition and split it blockwise. -/
  rw [← block_extension_eq_conj_diag (U := U) X t₀]
  exact cfcNormal_conj_diagMapCLM (hK := ‹CompleteSpace ↥U›) (hL := ‹CompleteSpace ↥Uᗮ›)
    U.orthogonalDecomposition hXcont hXnorm
    (@isStarNormal_smul_one_real_local ↥Uᗮ _ _ ‹CompleteSpace ↥Uᗮ› t₀)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Complex normal CFC instance for endomorphisms of a complete submodule,
transported from the subtype spelling. -/
theorem subtypeSubmoduleEndStarNormalCfc
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal := by
  let hU : CompleteSpace U := instCompleteSpaceSortFromSubtype (U := U)
  letI : CompleteSpace U := hU
  letI : CStarAlgebra (U →L[ℂ] U) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace U _ _ hU
  letI : ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus (A := U →L[ℂ] U)
  exact instContinuousFunctionalCalculusSubtypeSubmoduleEnd (U := U)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Complex normal CFC instance for the product of a complete submodule and its
orthogonal-complement endomorphism algebra. -/
theorem subtypeSubmodulePairEndStarNormalCfc
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal := by
  let hU : CompleteSpace U := instCompleteSpaceSortFromSubtype (U := U)
  let hUorth : CompleteSpace Uᗮ := instCompleteSpaceSortFromSubtype (U := Uᗮ)
  letI : CompleteSpace U := hU
  letI : CompleteSpace Uᗮ := hUorth
  letI : CStarAlgebra (U →L[ℂ] U) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace U _ _ hU
  letI : CStarAlgebra (Uᗮ →L[ℂ] Uᗮ) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace Uᗮ _ _ hUorth
  letI :
      ContinuousFunctionalCalculus ℂ ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
      (A := (U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ))
  exact instContinuousFunctionalCalculusSubtypeSubmodulePairEnd (U := U)

/-- Reducible wrapper exposing `subtypeSubmoduleEndStarNormalCfc` as an
instance-valued definition for later packed arguments. -/
@[reducible] noncomputable def subtypeSubmoduleEndStarNormalCfcDef
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal :=
  subtypeSubmoduleEndStarNormalCfc (U := U)

/-- Reducible wrapper exposing the pair CFC instance for later packed block
extension arguments. -/
@[reducible] noncomputable def subtypeSubmodulePairEndStarNormalCfcDef
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal :=
  subtypeSubmodulePairEndStarNormalCfc (U := U)

end NormalCFC514

end HansenPedersen
