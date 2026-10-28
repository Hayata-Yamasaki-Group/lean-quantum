/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.OperatorCore

import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Instance bridges for finite-dimensional block extensions

This file provides the typeclass bridges needed by the finite-dimensional
Hansen–Pedersen block-extension arguments.  Most declarations transfer
structure between the operator abbreviation `L K`, explicit continuous
endomorphism spaces, submodule sorts, coerced subtypes, and `WithLp` products.

## Main results

* `inst...L`: star, order, C*-algebra, and CFC instances for `L K`.
* `inst...Submodule...`: bridges between `U` and `↥U` endomorphism spaces.
* `inst...WithLp...`: completeness, additive, order, and star instances for
  doubled `WithLp` spaces used by block matrices.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Proposition 5.1.5.
-/

namespace HansenPedersen

universe u

open CFC
open scoped CStarAlgebra

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- Explicit Loewner-order cache for `L K`; retaining the completeness premise
keeps downstream section-variable interfaces stable. -/
noncomputable scoped instance instPartialOrderL
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    PartialOrder (L K) :=
  ContinuousLinearMap.instLoewnerPartialOrder

section SubmoduleInstances

/-- Completeness of the doubled `WithLp` space follows from completeness of a
submodule and its orthogonal complement, viewed as coerced subtypes. -/
noncomputable scoped instance instWithLpSubmodulePairCompleteSpace
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ] :
    CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) :=
  WithLp.instProdCompleteSpace (p := 2) (α := ↥U) (β := ↥Uᗮ)

/-- The coerced subtype `↥U` is complete whenever the submodule sort `U` is
complete. -/
noncomputable scoped instance instCompleteSpaceSubtypeFromSort
    {U : Submodule ℂ ℋ} [CompleteSpace U] :
    CompleteSpace ↥U := by
  simpa using (inferInstance : CompleteSpace U)

/-- The submodule sort `U` is complete whenever its coerced subtype `↥U` is
complete. -/
noncomputable scoped instance instCompleteSpaceSortFromSubtype
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    CompleteSpace U := by
  simpa using (inferInstance : CompleteSpace ↥U)

/-- Continuous addition on the doubled `WithLp` pair is transported through the
product continuous linear equivalence. -/
scoped instance instContinuousAddWithLpSubmodulePair
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ] :
    ContinuousAdd (WithLp 2 (↥U × ↥Uᗮ)) where
  continuous_add := by
    let e : WithLp 2 (↥U × ↥Uᗮ) ≃L[ℂ] ↥U × ↥Uᗮ :=
      WithLp.prodContinuousLinearEquiv 2 ℂ ↥U ↥Uᗮ
    have hcont :
        Continuous fun p : WithLp 2 (↥U × ↥Uᗮ) × WithLp 2 (↥U × ↥Uᗮ) =>
          e.symm (e p.1 + e p.2) := by
      exact e.symm.continuous.comp
        ((e.continuous.comp continuous_fst).add
          (e.continuous.comp continuous_snd))
    simpa using hcont

/-- Adjoint star on continuous endomorphisms of the coerced submodule
`↥U`. -/
noncomputable scoped instance instStarSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    Star (↥U →L[ℂ] ↥U) :=
  HansenPedersen.Internal.instStarSubmoduleEnd (U := U)

/-- Involutivity of the adjoint star on endomorphisms of the coerced submodule
`↥U`. -/
noncomputable scoped instance instInvolutiveStarSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    InvolutiveStar (↥U →L[ℂ] ↥U) :=
  HansenPedersen.Internal.instInvolutiveStarSubmoduleEnd (U := U)

/-- Multiplicative compatibility of the adjoint star on endomorphisms of
`↥U`. -/
noncomputable scoped instance instStarMulSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    StarMul (↥U →L[ℂ] ↥U) :=
  HansenPedersen.Internal.instStarMulSubmoduleEnd (U := U)

/-- Star-ring structure on continuous endomorphisms of the coerced submodule
`↥U`. -/
noncomputable scoped instance instStarRingSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    StarRing (↥U →L[ℂ] ↥U) :=
  HansenPedersen.Internal.instStarRingSubmoduleEnd (U := U)

/-- Loewner partial order on continuous endomorphisms of the coerced submodule
`↥U`. -/
noncomputable scoped instance instPartialOrderSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    PartialOrder (↥U →L[ℂ] ↥U) :=
  ContinuousLinearMap.instLoewnerPartialOrder

/-- Completeness of the doubled `WithLp` pair for the submodule sort and its
orthogonal complement. -/
noncomputable scoped instance instWithLpSubmodulePairCompleteSpaceSort
    {U : Submodule ℂ ℋ} [CompleteSpace U] [CompleteSpace Uᗮ] :
    CompleteSpace (WithLp 2 (U × Uᗮ)) :=
  WithLp.instProdCompleteSpace (p := 2) (α := U) (β := Uᗮ)

/-- Completeness of `WithLp 2 (↥U × ↥Uᗮ)` transported from the corresponding
submodule-sort product. -/
noncomputable scoped instance instWithLpSubmodulePairCompleteSpaceSortCoe
    {U : Submodule ℂ ℋ} [CompleteSpace U] [CompleteSpace Uᗮ] :
    CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := by
  simpa using (instWithLpSubmodulePairCompleteSpaceSort (U := U))

/-- Star-ordered-ring structure transported from endomorphisms of the
submodule sort `U` to endomorphisms of the coerced subtype `↥U`. -/
noncomputable scoped instance instStarOrderedRingSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace U]
    [StarOrderedRing (U →L[ℂ] U)] :
    StarOrderedRing (↥U →L[ℂ] ↥U) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  simpa using (inferInstance : StarOrderedRing (U →L[ℂ] U))

/-- Nonnegative-spectrum class transported from endomorphisms of `U` to
endomorphisms of the coerced subtype `↥U`. -/
noncomputable scoped instance instNonnegSpectrumClassSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace U]
    [NonnegSpectrumClass ℝ (U →L[ℂ] U)] :
    NonnegSpectrumClass ℝ (↥U →L[ℂ] ↥U) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  simpa using (inferInstance : NonnegSpectrumClass ℝ (U →L[ℂ] U))

/-- Real scalars act through complex scalars on continuous endomorphisms of
the submodule sort `U`. -/
noncomputable scoped instance instIsScalarTowerRealComplexSubmoduleEndSort
    {U : Submodule ℂ ℋ} :
    IsScalarTower ℝ ℂ (U →L[ℂ] U) :=
  IsScalarTower.of_algebraMap_smul fun r f => by
    ext x
    rfl

/-- Real-to-complex scalar-tower compatibility on endomorphisms of the coerced
submodule subtype `↥U`. -/
noncomputable scoped instance instIsScalarTowerRealComplexSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} :
    IsScalarTower ℝ ℂ (↥U →L[ℂ] ↥U) := by
  simpa using (inferInstance : IsScalarTower ℝ ℂ (U →L[ℂ] U))

/-- C*-algebra structure transported from endomorphisms of `U` to
endomorphisms of the coerced subtype `↥U`. -/
noncomputable scoped instance instCStarAlgebraSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace U]
    [CStarAlgebra (U →L[ℂ] U)] :
    CStarAlgebra (↥U →L[ℂ] ↥U) := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  simpa using (inferInstance : CStarAlgebra (U →L[ℂ] U))

/-- Loewner partial order on continuous endomorphisms of the submodule sort
`U`. -/
noncomputable scoped instance instPartialOrderSubmoduleEndSort
    {U : Submodule ℂ ℋ} [CompleteSpace ↥U] :
    PartialOrder (U →L[ℂ] U) :=
  ContinuousLinearMap.instLoewnerPartialOrder

/-- Complex continuous functional calculus transported from endomorphisms of
`U` to endomorphisms of the coerced subtype `↥U`. -/
noncomputable scoped instance instContinuousFunctionalCalculusSubtypeSubmoduleEnd
    {U : Submodule ℂ ℋ} [CompleteSpace U]
    [ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal] :
    ContinuousFunctionalCalculus ℂ (↥U →L[ℂ] ↥U) IsStarNormal := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  simpa using
    (inferInstance : ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal)

/-- Real continuous functional calculus transported from endomorphisms of `U`
to endomorphisms of the coerced subtype `↥U`. -/
noncomputable scoped instance instContinuousFunctionalCalculusSubtypeSubmoduleEndReal
    {U : Submodule ℂ ℋ} [CompleteSpace U]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint] :
    ContinuousFunctionalCalculus ℝ (↥U →L[ℂ] ↥U) IsSelfAdjoint := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  simpa using
    (inferInstance : ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint)

/-- Complex continuous functional calculus for pairs of submodule
endomorphisms, transported to the corresponding coerced subtype pair. -/
noncomputable scoped instance instContinuousFunctionalCalculusSubtypeSubmodulePairEnd
    {U : Submodule ℂ ℋ} [CompleteSpace U] [CompleteSpace Uᗮ]
    [ContinuousFunctionalCalculus ℂ ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) IsStarNormal] :
    ContinuousFunctionalCalculus ℂ
      ((↥U →L[ℂ] ↥U) × (↥Uᗮ →L[ℂ] ↥Uᗮ)) IsStarNormal := by
  letI : CompleteSpace ↥U := instCompleteSpaceSubtypeFromSort (U := U)
  letI : CompleteSpace ↥Uᗮ := instCompleteSpaceSubtypeFromSort (U := Uᗮ)
  simpa using
    (inferInstance :
      ContinuousFunctionalCalculus ℂ ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) IsStarNormal)

/-- Adjoint star on endomorphisms of a doubled `WithLp` product Hilbert
space. -/
noncomputable scoped instance instStarWithLpProdEnd
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    Star ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) where
  star A :=
    letI : CompleteSpace (WithLp 2 (K × L')) :=
      WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
    (@ContinuousLinearMap.adjoint ℂ (WithLp 2 (K × L')) (WithLp 2 (K × L')) _ _ _ _ _
      ‹CompleteSpace (WithLp 2 (K × L'))› ‹CompleteSpace (WithLp 2 (K × L'))›) A

/-- Involutivity of the adjoint star on endomorphisms of a doubled `WithLp`
product Hilbert space. -/
noncomputable scoped instance instInvolutiveStarWithLpProdEnd
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    InvolutiveStar ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) where
  star_involutive A := by
    letI : CompleteSpace (WithLp 2 (K × L')) :=
      WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
    simp

/-- Multiplicative compatibility of the adjoint star on doubled `WithLp`
product endomorphisms. -/
noncomputable scoped instance instStarMulWithLpProdEnd
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    StarMul ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) where
  star_mul A B := by
    letI : CompleteSpace (WithLp 2 (K × L')) :=
      WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
    simp

/-- Star-ring structure on endomorphisms of a doubled `WithLp` product Hilbert
space. -/
noncomputable scoped instance instStarRingWithLpProdEnd
    {K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    StarRing ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) where
  star_add A B := by
    letI : CompleteSpace (WithLp 2 (K × L')) :=
      WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
    exact map_add
      (@ContinuousLinearMap.adjoint ℂ (WithLp 2 (K × L')) (WithLp 2 (K × L')) _ _ _ _ _
        ‹CompleteSpace (WithLp 2 (K × L'))› ‹CompleteSpace (WithLp 2 (K × L'))›) A B


end SubmoduleInstances

end HansenPedersen
