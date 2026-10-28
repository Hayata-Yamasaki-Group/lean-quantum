/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.Analysis.CStar.FiniteDimensionalStructure.ProductAssembly
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Classification
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrderRetained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransportRetained
-- An instance name below is an indivisible token longer than the style limit.
set_option linter.style.longLine false

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 classification providers

Carlen 2022 Theorem 1.45 (AH1): non-unital CStarMatrix classification
provider assembly, finite C*-algebra block models, and endpoint-transport
classification-provider variants.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra
open scoped Topology
open Filter
open Matrix

universe u

section PositiveRayEndpointQuotientCFC

attribute [local instance]
    instContinuousFunctionalCalculusRealContinuousLinearMapComplexIdEuclideanSpaceFinIsSelfAdjointOfNontrivial_quantum_7

attribute [local instance]
    instNonnegSpectrumClassRealContinuousLinearMapComplexIdEuclideanSpaceFinOfNontrivial_quantum_7

/--
Transport the endpoint-quotient monotonicity from a finite product of
`CStarMatrix` blocks back to a finite-dimensional non-unital C*-algebra once a
block-product model of that algebra is supplied.

Such a model exists for every finite-dimensional non-unital C*-algebra: combine
`finiteCStarMatrixBlockModel_of_starAlgEquiv` with the classification theorem
`exists_starAlgEquiv_pi_cstarMatrix`.  The resulting unconditional theorem is
`positiveRay_cfcₙ_sub_endpoint_le`.
-/
theorem
    positiveRay_cfcₙ_sub_endpoint_le_of_blockModelWitness
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (model : FiniteCStarMatrixBlockModel A)
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b := by
  letI : Fintype model.ι := model.instFintype
  haveI : ∀ i : model.ι, Nontrivial (EuclideanSpace ℂ (Fin (model.n i))) :=
    model.instNontrivial
  haveI : ∀ i : model.ι,
      StarOrderedRing (CStarMatrix (Fin (model.n i)) (Fin (model.n i)) ℂ) :=
    fun _ => CStarMatrix.instStarOrderedRing
  let F : ℝ → ℝ := positiveCayleyPullback (positiveRayEndpointQuotient h d)
  let f : ℝ → ℝ := fun x : ℝ => F x - F 0
  have hf0 : f 0 = 0 := by simp [f]
  have hφa : IsSelfAdjoint (model.toBlocks a) := ha.map model.toBlocks
  have hφb : IsSelfAdjoint (model.toBlocks b) := hb.map model.toBlocks
  have hφaq : quasispectrum ℝ (model.toBlocks a) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hsubset :
        quasispectrum ℝ (model.toBlocks a) ⊆ quasispectrum ℝ a := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ model.toBlocks a
    exact haq (hsubset hx)
  have hφbq : quasispectrum ℝ (model.toBlocks b) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hsubset :
        quasispectrum ℝ (model.toBlocks b) ⊆ quasispectrum ℝ b := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ model.toBlocks b
    exact hbq (hsubset hx)
  have hφab : model.toBlocks a ≤ model.toBlocks b := by
    exact model.toBlocks_le hab
  have hblock :
      cfcₙ f (model.toBlocks a) ≤ cfcₙ f (model.toBlocks b) := by
    simpa [F, f] using
      piCStarMatrix_endpointQuotient_positiveCayleyPullback_cfcₙ_sub_endpoint_le_of_order
        (h := h) (d := d) hclosed hlin hφa hφb hφaq hφbq hφab
  have hback :
      model.fromBlocks (cfcₙ f (model.toBlocks a)) ≤
        model.fromBlocks (cfcₙ f (model.toBlocks b)) := by
    exact model.fromBlocks_le hblock
  have hfinφa : (quasispectrum ℝ (model.toBlocks a)).Finite := by
    have hfin : (quasispectrum ℝ a).Finite :=
      positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex a
    have hsubset :
        quasispectrum ℝ (model.toBlocks a) ⊆ quasispectrum ℝ a := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ model.toBlocks a
    exact hfin.subset hsubset
  have hfinφb : (quasispectrum ℝ (model.toBlocks b)).Finite := by
    have hfin : (quasispectrum ℝ b).Finite :=
      positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex b
    have hsubset :
        quasispectrum ℝ (model.toBlocks b) ⊆ quasispectrum ℝ b := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ model.toBlocks b
    exact hfin.subset hsubset
  have hmapa :
      model.fromBlocks (cfcₙ f (model.toBlocks a)) = cfcₙ f a := by
    have hψφa : IsSelfAdjoint (model.fromBlocks (model.toBlocks a)) := by
      simpa [model.left_inv a] using ha
    have hcf := model.fromBlocks.map_cfcₙ f (model.toBlocks a)
      (hf := hfinφa.continuousOn f) (hf₀ := hf0)
      (ha := hφa) (hφa := hψφa)
    exact hcf.trans (congrArg (fun x : A => cfcₙ f x) (model.left_inv a))
  have hmapb :
      model.fromBlocks (cfcₙ f (model.toBlocks b)) = cfcₙ f b := by
    have hψφb : IsSelfAdjoint (model.fromBlocks (model.toBlocks b)) := by
      simpa [model.left_inv b] using hb
    have hcf := model.fromBlocks.map_cfcₙ f (model.toBlocks b)
      (hf := hfinφb.continuousOn f) (hf₀ := hf0)
      (ha := hφb) (hφa := hψφb)
    exact hcf.trans (congrArg (fun x : A => cfcₙ f x) (model.left_inv b))
  simpa [hmapa, hmapb] using hback

/--
If every finite-dimensional non-unital C*-algebra has a block-product model,
then the endpoint-quotient monotonicity transports to every such algebra.

This packages the previous block-model transport into the theorem-facing
universal form.  The block model itself is supplied by the classification theorem
`exists_starAlgEquiv_pi_cstarMatrix`; the unconditional theorem is
`positiveRay_cfcₙ_sub_endpoint_le`.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_blockModel
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hmodel :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [FiniteDimensional ℂ B],
        FiniteCStarMatrixBlockModel B)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_blockModelWitness
    (A := A) (h := h) (d := d) (a := a) (b := b) hclosed hlin
    (hmodel (B := A)) ha hb haq hbq hab

/--
If every finite-dimensional non-unital C*-algebra is supplied with a non-unital
star algebra equivalence to a finite product of `CStarMatrix` blocks, then the
endpoint-quotient monotonicity transports to every such algebra.

The star block equivalence provider `hdecomp` is supplied by the classification
theorem `exists_starAlgEquiv_pi_cstarMatrix`; the unconditional theorem is
`positiveRay_cfcₙ_sub_endpoint_le`.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_starAlgEquiv
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hdecomp :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
        [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (B ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_blockModel
    (h := h) (d := d) hclosed hlin
    (finiteCStarMatrixBlockModelProvider_of_starAlgEquivProvider hdecomp)
    ha hb haq hbq hab

/--
The same finite-dimensional transport theorem with the block classification
provider stated in the natural C*-algebra form: every finite-dimensional
non-unital C*-algebra admits a non-unital star algebra equivalence to a finite
product of `CStarMatrix` blocks.

The order assumptions on the target algebra are only needed by the transport
theorem; the classification provider itself depends only on the non-unital
C*-algebra and finite-dimensional vector-space structure.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_nonUnitalStarAlgEquiv
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hdecomp :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (B ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_starAlgEquiv
    (h := h) (d := d) hclosed hlin
    (fun {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B]
        [StarOrderedRing B] [FiniteDimensional ℂ B] =>
      hdecomp (B := B))
    ha hb haq hbq hab

/--
Given the unital finite-dimensional C*-algebra Wedderburn-Artin
star-compatibility upgrade, the non-unital C*-classification constructed above
supplies the finite-dimensional endpoint-quotient transport.  The upgrade is
`finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv` in
`ProductAssembly.lean`, and the unconditional transport theorem is
`positiveRay_cfcₙ_sub_endpoint_le`.

This theorem composes the following results:
unital star-compatible WA upgrade → non-unital C*-classification → existing
finite-dimensional transport wrapper.  It does not require a separate
`hdecomp` input.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_unitalStarCompatibilityUpgrade
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hupgradeUnital :
      ∀ {B : Type u} [CStarAlgebra B] [FiniteDimensional ℂ B]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              B ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) })
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_nonUnitalStarAlgEquiv
    (h := h) (d := d) hclosed hlin
    (exists_starAlgEquiv_pi_cstarMatrix_of_unitalStarCompatibilityUpgrade
      hupgradeUnital)
    ha hb haq hbq hab

/-! ### Classification-provider variants for endpoint transport -/
/--
Actual finite-dimensional C*-algebra transport theorem.  The finite-dimensional
non-unital C*-classification has already been closed above, so this theorem is
the thin wrapper that passes that classification provider to the existing block
transport theorem.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_nonUnitalStarAlgEquiv
    (h := h) (d := d) hclosed hlin
    exists_starAlgEquiv_pi_cstarMatrix
    ha hb haq hbq hab

/--
If unitization-level star block decompositions are available and the image
subalgebras inside finite `CStarMatrix` products can be classified again by
finite `CStarMatrix` products, then the endpoint-quotient monotonicity
transports to arbitrary finite-dimensional non-unital C*-algebras.

The unconditional form, which uses the classification theorem
`exists_starAlgEquiv_pi_cstarMatrix` instead of these two hypotheses, is
`positiveRay_cfcₙ_sub_endpoint_le`.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_unitizationBlockImageSubalgebra
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hunit :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (Unitization ℂ B ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hsub :
      ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
        ∀ (S : NonUnitalStarSubalgebra ℂ
          (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
          ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
            (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
            Nonempty (S ≃⋆ₐ[ℂ]
              ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_starAlgEquiv
    (h := h) (d := d) hclosed hlin
    (starAlgEquivProvider_of_unitizationBlockImageSubalgebra
      hunit hsub)
    ha hb haq hbq hab

/--
If the unitization admits star-compatible algebraic block decompositions and
the resulting image subalgebras inside finite `CStarMatrix` products can be
classified again by finite `CStarMatrix` products, then the endpoint-quotient
monotonicity transports to arbitrary finite-dimensional non-unital
C*-algebras.

This combines the unitization star-block packaging step with the
image-subalgebra transport theorem.  The unconditional form, which uses the classification
theorem `exists_starAlgEquiv_pi_cstarMatrix` instead of the hypotheses `hstar` and `hsub`, is
`positiveRay_cfcₙ_sub_endpoint_le`.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibleAlgBlock
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hstar :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (N : ℕ) (n : Fin N → ℕ), (∀ i, NeZero (n i)) ∧
          Nonempty
            { e :
                Unitization ℂ B ≃ₐ[ℂ]
                  ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
              ∀ x, e (star x) = star (e x) })
    (hsub :
      ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
        ∀ (S : NonUnitalStarSubalgebra ℂ
          (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
          ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
            (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
            Nonempty (S ≃⋆ₐ[ℂ]
              ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_unitizationBlockImageSubalgebra
    (h := h) (d := d) hclosed hlin
    (unitizationStarAlgEquivProvider_of_starCompatibleAlgBlock
      hstar)
    hsub ha hb haq hbq hab

/--
Semisimplicity of unitizations, a star-compatibility upgrade for the resulting
algebraic Wedderburn-Artin decompositions, and classification of the image
subalgebras inside finite `CStarMatrix` products together supply the
finite-dimensional endpoint-quotient transport.

This node removes the explicit star-compatible block provider hypothesis from
the preceding transport theorem.  The three provider hypotheses are proved for
all finite-dimensional C*-algebras; the unconditional theorem is
`positiveRay_cfcₙ_sub_endpoint_le` above.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_semisimpleStarCompatibilitySubalgebra
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hsemi :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        IsSemisimpleRing (Unitization ℂ B))
    (hupgrade :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ B ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) })
    (hsub :
      ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
        ∀ (S : NonUnitalStarSubalgebra ℂ
          (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
          ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
            (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
            Nonempty (S ≃⋆ₐ[ℂ]
              ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibleAlgBlock
    (h := h) (d := d) hclosed hlin
    (starCompatibleAlgBlockProvider_of_semisimple_of_starCompatibilityUpgrade
      hsemi hupgrade)
    hsub ha hb haq hbq hab

/--
The same transport theorem with the semisimplicity input expressed as trivial
Jacobson radical of the finite-dimensional unitization.

This reduces the C*-specific semisimplicity input to the standard
Banach/C*-algebra fact that finite-dimensional unitizations have zero
Jacobson radical, proved as
`finiteDimensionalNonUnitalCStarAlgebra_unitization_jacobson_eq_bot` in
`BlockDecomposition.lean`.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_jacobsonStarCompatibilitySubalgebra
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hjac :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        Ring.jacobson (Unitization ℂ B) = ⊥)
    (hupgrade :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ B ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) })
    (hsub :
      ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
        ∀ (S : NonUnitalStarSubalgebra ℂ
          (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
          ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
            (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
            Nonempty (S ≃⋆ₐ[ℂ]
              ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_semisimpleStarCompatibilitySubalgebra
    (h := h) (d := d) hclosed hlin
    (finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider_of_jacobson_eq_bot
      hjac)
    hupgrade hsub ha hb haq hbq hab

/--
The same transport theorem with the image-subalgebra classification supplied
by a universal finite-dimensional non-unital C*-algebra star-block
classification theorem.

This replaces the ad hoc `CStarMatrix`-subalgebra provider by the more natural
classification input for arbitrary finite-dimensional non-unital C*-algebras.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_jacobsonStarCompatibilityCStarAlgEquiv
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hjac :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        Ring.jacobson (Unitization ℂ B) = ⊥)
    (hupgrade :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ B ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) })
    (hdecomp :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (B ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_jacobsonStarCompatibilitySubalgebra
    (h := h) (d := d) hclosed hlin hjac hupgrade
    (nonUnitalStarSubalgebraProvider_of_nonUnitalCStarStarAlgEquiv
      hdecomp)
    ha hb haq hbq hab

/--
A star-compatible unitization block provider and the universal finite-dimensional
non-unital C*-algebra block classification provider together supply the
finite-dimensional endpoint-quotient transport.

This is the forward composition used after semisimplicity of the unitization has
already been supplied.  The theorem-level inputs are exactly the two
classification providers: star-compatible unitization blocks and non-unital
`CStarMatrix` block classification.  Both are proved; the unconditional theorem is
`positiveRay_cfcₙ_sub_endpoint_le` above.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibleAlgBlock_and_nonUnitalStarAlgEquiv
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hstar :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (N : ℕ) (n : Fin N → ℕ), (∀ i, NeZero (n i)) ∧
          Nonempty
            { e :
                Unitization ℂ B ≃ₐ[ℂ]
                  ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
              ∀ x, e (star x) = star (e x) })
    (hdecomp :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (B ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibleAlgBlock
    (h := h) (d := d) hclosed hlin hstar
    (nonUnitalStarSubalgebraProvider_of_nonUnitalCStarStarAlgEquiv
      hdecomp)
    ha hb haq hbq hab

/--
The same transport theorem after the finite-dimensional C*-algebra radical
calculation has supplied the zero-Jacobson-radical provider.

The global inputs are the star-compatible upgrade of the unitization
Wedderburn-Artin decomposition and the finite-dimensional non-unital C*-algebra
classification by `CStarMatrix` blocks.  Both are proved; the unconditional
theorem is `positiveRay_cfcₙ_sub_endpoint_le` above.
-/
theorem positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibilityCStarAlgEquiv
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hupgrade :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ B ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) })
    (hdecomp :
      ∀ {B : Type u} [NonUnitalCStarAlgebra B] [FiniteDimensional ℂ B],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (B ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hbq : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) a ≤
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) b :=
  positiveRay_cfcₙ_sub_endpoint_le_of_starCompatibleAlgBlock_and_nonUnitalStarAlgEquiv
    (h := h) (d := d) hclosed hlin
    (starCompatibleAlgBlockProvider_of_starCompatibilityUpgrade
      hupgrade)
    hdecomp ha hb haq hbq hab

/--
The same block-model provider gives Lean's normalized finite-dimensional CFC
monotonicity predicate.

This is not the classification theorem: it only states that, given block models
for all finite-dimensional non-unital C*-algebras, the previous transport
theorem supplies the `UnitIntervalFiniteMatrixMonotone` field.  Such block models
exist by `finiteCStarMatrixBlockModel_of_starAlgEquiv` and
`exists_starAlgEquiv_pi_cstarMatrix`.
-/
theorem unitIntervalFiniteMatrixMonotone_of_blockModel
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (hmodel :
      ∀ {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
        [FiniteDimensional ℂ A],
        FiniteCStarMatrixBlockModel A) :
    UnitIntervalFiniteMatrixMonotone.{0}
      (positiveCayleyPullback (positiveRayEndpointQuotient h d)) where
  cfc_monotone_finite := by
    intro A _ _ _ _ a ha b hb hab
    exact
      positiveRay_cfcₙ_sub_endpoint_le_of_blockModel
        (h := h) (d := d) hclosed hlin hmodel ha.1 hb.1 ha.2 hb.2 hab

/--
The theorem-facing bridge from the concrete finite-dimensional Hilbert-space
endpoint-quotient monotonicity to Lean's normalized finite-dimensional CFC
monotonicity predicate.

The finite-dimensional C*-algebra transport itself is kept as an explicit
hypothesis: this node only packages the already proved concrete matrix theorem
into the `UnitIntervalFiniteMatrixMonotone` target once that transport principle
is supplied.
-/
theorem unitIntervalFiniteMatrixMonotone_endpointQuotient_of_concreteTransport
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (htransport :
      (∀ {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
          {A B : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))},
          IsSelfAdjoint A → IsSelfAdjoint B →
          spectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1 →
          spectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1 →
          A ≤ B →
          LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n))
              (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A ≤
            LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n))
              (positiveCayleyPullback (positiveRayEndpointQuotient h d)) B) →
        UnitIntervalFiniteMatrixMonotone.{0}
          (positiveCayleyPullback (positiveRayEndpointQuotient h d))) :
    UnitIntervalFiniteMatrixMonotone.{0}
      (positiveCayleyPullback (positiveRayEndpointQuotient h d)) := by
  refine htransport ?_
  intro n _ A B hA hB hAspec hBspec hAB
  exact positiveRayEuclidean_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
    (h := h) (d := d) hclosed hlin (n := n) hA hB hAspec hBspec hAB

/-- W version: matrix monotonicity from the concrete endpoint-quotient transport (a verbatim copy of
the old declaration with only the predicate replaced). -/
theorem unitIntervalMatrixMonotone_endpointQuotient_of_concreteTransport
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    (htransport :
      (∀ {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
          {A B : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))},
          IsSelfAdjoint A → IsSelfAdjoint B →
          spectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1 →
          spectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1 →
          A ≤ B →
          LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n))
              (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A ≤
            LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n))
              (positiveCayleyPullback (positiveRayEndpointQuotient h d)) B) →
        UnitIntervalMatrixMonotone
          (positiveCayleyPullback (positiveRayEndpointQuotient h d))) :
    UnitIntervalMatrixMonotone
      (positiveCayleyPullback (positiveRayEndpointQuotient h d)) := by
  refine htransport ?_
  intro n _ A B hA hB hAspec hBspec hAB
  exact positiveRayEuclidean_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
    (h := h) (d := d) hclosed hlin (n := n) hA hB hAspec hBspec hAB

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
