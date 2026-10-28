/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.Analysis.CStar.FiniteDimensionalStructure.ProductAssembly

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

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    ContinuousFunctionalCalculus ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative bounded operators on `EuclideanSpace ℂ (Fin n)` have nonnegative real spectrum. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    NonnegSpectrumClass ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := inferInstance

/-! ### Non-unital CStarMatrix classification provider assembly -/
/--
Any two subsingleton non-unital star algebras are star-algebra equivalent.

This small packaging lemma is used for the zero-algebra case of the
finite-dimensional non-unital C*-classification `exists_starAlgEquiv_pi_cstarMatrix` below.
-/
noncomputable def starAlgEquivOfSubsingleton
    {A B : Type u} [Zero A] [Add A] [Mul A] [SMul ℂ A] [Star A] [Subsingleton A]
    [Zero B] [Add B] [Mul B] [SMul ℂ B] [Star B] [Subsingleton B] :
    A ≃⋆ₐ[ℂ] B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  map_star' _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

/--
The zero case of the finite-dimensional non-unital C*-classification
(`exists_starAlgEquiv_pi_cstarMatrix` below):
a subsingleton finite-dimensional non-unital C*-algebra is star-algebra
equivalent to the empty product of `CStarMatrix` blocks.

The block-size condition is vacuous because the index type is empty.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_starAlgEquivProvider_of_subsingleton
    {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] [Subsingleton A] :
    ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
      (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
      Nonempty (A ≃⋆ₐ[ℂ]
        ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  refine ⟨PEmpty, inferInstance, (fun i => PEmpty.elim i), ?_, ?_⟩
  · intro i
    exact PEmpty.elim i
  · exact
      ⟨starAlgEquivOfSubsingleton (A := A)
        (B := ∀ i : PEmpty,
          CStarMatrix (Fin ((fun j : PEmpty => PEmpty.elim j) i))
            (Fin ((fun j : PEmpty => PEmpty.elim j) i)) ℂ)⟩

/--
To prove the full finite-dimensional non-unital C*-classification provider it
is enough to prove it for nontrivial algebras.

The subsingleton case is the empty block product proved above.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_starAlgEquivProvider_of_nontrivialProvider
    (hnontrivial :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
        [Nontrivial A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (A ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  intro A _ _
  by_cases hsub : Subsingleton A
  · haveI : Subsingleton A := hsub
    exact finiteDimensionalNonUnitalCStarAlgebra_starAlgEquivProvider_of_subsingleton
      (A := A)
  · haveI : Nontrivial A := (not_subsingleton_iff_nontrivial).mp hsub
    exact hnontrivial (A := A)

/--
Finite products of `CStarMatrix` blocks classify themselves.

This is the identity case of the finite-dimensional non-unital
C*-classification: once an algebra has already been written as a
finite `CStarMatrix` product, the required star-block provider is just the
identity star algebra equivalence.
-/
theorem finiteCStarMatrixProduct_starAlgEquivProvider
    {ι : Type u} [Finite ι] {n : ι → ℕ}
    [∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))] :
    ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
      (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
      Nonempty ((∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) ≃⋆ₐ[ℂ]
        ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ) := by
  refine ⟨ι, Fintype.ofFinite ι, n, ?_, ?_⟩
  · intro i
    infer_instance
  · exact ⟨StarAlgEquiv.refl⟩

/--
The finite `CStarMatrix` block classification provider pulls back along a
star algebra equivalence.

This is the formal step that lets a concrete block model for a star-equivalent
algebra be reused as a classification provider for the original algebra.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_starAlgEquivProvider_of_starAlgEquiv
    {A B : Type u} [Add A] [Mul A] [SMul ℂ A] [Star A]
    [Add B] [Mul B] [SMul ℂ B] [Star B]
    (e : A ≃⋆ₐ[ℂ] B)
    (hB :
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (B ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
      (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
      Nonempty (A ≃⋆ₐ[ℂ]
        ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  rcases hB with ⟨ι, instι, n, hn, ⟨g⟩⟩
  exact ⟨ι, instι, n, hn, ⟨e.trans g⟩⟩

/--
If unitization-level star block decompositions are available and every
finite-dimensional non-unital star subalgebra of a finite `CStarMatrix` product
is itself star-equivalent to a finite `CStarMatrix` product, then arbitrary
finite-dimensional non-unital C*-algebras admit the star block equivalence
provider needed downstream.

This reduces the classification to subalgebras of finite products of concrete
matrix C*-algebras; the full classification is `exists_starAlgEquiv_pi_cstarMatrix`
below.
-/
noncomputable def starAlgEquivProvider_of_unitizationBlockImageSubalgebra
    (hunit :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (Unitization ℂ A ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hsub :
      ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
        ∀ (S : NonUnitalStarSubalgebra ℂ
          (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
          ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
            (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
            Nonempty (S ≃⋆ₐ[ℂ]
              ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ)) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      [FiniteDimensional ℂ A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (A ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  intro A _ _ _ _
  classical
  rcases hunit (A := A) with ⟨ι, instι, n, hn, ⟨e⟩⟩
  letI : Fintype ι := instι
  haveI : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))) := hn
  let S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    NonUnitalStarAlgHom.range (unitizationBlockImageHom (A := A) (n := n) e)
  rcases hsub (ι := ι) (n := n) hn S with ⟨κ, instκ, m, hm, ⟨g⟩⟩
  let eA : A ≃⋆ₐ[ℂ] S :=
    Classical.choice
      (nonUnitalCStarAlgebra_starAlgEquiv_unitizationBlockImageRange
        (A := A) (n := n) e)
  exact ⟨κ, instκ, m, hm, ⟨eA.trans g⟩⟩

/--
If every finite-dimensional non-unital C*-algebra has a unitization-level
`CStarMatrix` star-block decomposition, then every such non-unital algebra is
itself star-algebra equivalent to a finite product of `CStarMatrix` blocks.

The image of the algebra inside the unitization block product is a two-sided
star ideal, so the finite-product ideal coordinate decomposition applies
directly; no classification of arbitrary product subalgebras is needed here.
-/
theorem exists_starAlgEquiv_pi_cstarMatrix_of_unitizationStarAlgEquiv
    (hunit :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (Unitization ℂ A ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  intro A _ _
  classical
  rcases hunit (A := A) with ⟨ι, instι, n, hn, ⟨e⟩⟩
  letI : Fintype ι := instι
  haveI : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))) := hn
  let S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    NonUnitalStarAlgHom.range (unitizationBlockImageHom (A := A) (n := n) e)
  have hSideal : IsTwoSidedStarIdeal S :=
    unitizationBlockImageRange_isTwoSidedStarIdeal (A := A) (n := n) e
  rcases piCStarMatrix_twoSidedStarIdeal_coordinateProduct hn S hSideal with
    ⟨κ, instκ, m, hm, ⟨g⟩⟩
  let eA : A ≃⋆ₐ[ℂ] S :=
    Classical.choice
      (nonUnitalCStarAlgebra_starAlgEquiv_unitizationBlockImageRange
        (A := A) (n := n) e)
  exact ⟨κ, instκ, m, hm, ⟨eA.trans g⟩⟩

/--
The unital star-compatibility upgrade is the only global input of this theorem
for the finite-dimensional non-unital C*-algebra `CStarMatrix` block
classification.  It is proved as
`finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv` in
`ProductAssembly.lean`, which gives `exists_starAlgEquiv_pi_cstarMatrix` below.
The unitization semisimplicity, star-block packaging, and two-sided ideal
coordinate decomposition are supplied by the preceding theorems.
-/
theorem exists_starAlgEquiv_pi_cstarMatrix_of_unitalStarCompatibilityUpgrade
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
            ∀ x, e (star x) = star (e x) }) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
  exists_starAlgEquiv_pi_cstarMatrix_of_unitizationStarAlgEquiv
    (unitizationStarAlgEquivProvider_of_unitalStarCompatibilityUpgrade
      hupgradeUnital)

/--
Actual finite-dimensional non-unital C*-algebra classification by finite
products of `CStarMatrix` blocks.
-/
theorem exists_starAlgEquiv_pi_cstarMatrix :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
  exists_starAlgEquiv_pi_cstarMatrix_of_unitalStarCompatibilityUpgrade
    finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv

/-! ### Block models for finite C*-algebra transport -/
/--
A finite-dimensional non-unital C*-algebra modelled by a finite product of
`CStarMatrix` blocks.

Mathlib currently provides the non-unital star homomorphisms needed to move CFC
through a representation, but not a packaged `NonUnitalAlgEquiv`.  This
structure records the two inverse non-unital star homomorphisms expected from a
finite-dimensional C*-algebra block decomposition theorem, together with the
order preservation needed for the monotonicity transport.
-/
structure FiniteCStarMatrixBlockModel (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] where
  ι : Type*
  instFintype : Fintype ι
  n : ι → ℕ
  instNontrivial : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))
  toBlocks : A →⋆ₙₐ[ℂ] (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
  fromBlocks : (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) →⋆ₙₐ[ℂ] A
  toBlocks_le : ∀ {a b : A}, a ≤ b → toBlocks a ≤ toBlocks b
  fromBlocks_le : ∀ {x y}, x ≤ y → fromBlocks x ≤ fromBlocks y
  left_inv : ∀ a : A, fromBlocks (toBlocks a) = a
  right_inv : ∀ x, toBlocks (fromBlocks x) = x

/--
A star algebra equivalence from a non-unital C*-algebra to a finite product of
`CStarMatrix` blocks supplies the block-model package used by the finite
transport theorem.

This definition does not itself classify finite-dimensional C*-algebras; for every
finite-dimensional non-unital C*-algebra, the required star algebra equivalence is supplied
by `exists_starAlgEquiv_pi_cstarMatrix` above.
-/
noncomputable def finiteCStarMatrixBlockModel_of_starAlgEquiv
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    [∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))]
    (e : A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    FiniteCStarMatrixBlockModel A := by
  classical
  haveI : ∀ i : ι,
      StarOrderedRing (CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    fun _ => CStarMatrix.instStarOrderedRing
  letI : OrderIsoClass
      (A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      A (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    StarRingEquivClass.instOrderIsoClass
  letI : OrderIsoClass
      ((∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) ≃⋆ₐ[ℂ] A)
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) A :=
    StarRingEquivClass.instOrderIsoClass
  exact
  { ι := ι
    instFintype := inferInstance
    n := n
    instNontrivial := inferInstance
    toBlocks := starAlgEquivToNonUnitalStarAlgHom e
    fromBlocks := starAlgEquivToNonUnitalStarAlgHom e.symm
    toBlocks_le := by
      intro a b hab
      exact OrderHomClass.mono e hab
    fromBlocks_le := by
      intro x y hxy
      exact OrderHomClass.mono e.symm hxy
    left_inv := by
      intro a
      exact e.symm_apply_apply a
    right_inv := by
      intro x
      exact e.apply_symm_apply x }

/--
A provider of non-unital star algebra block equivalences supplies the block-model
provider needed by the finite-dimensional transport theorem.

For arbitrary finite-dimensional non-unital C*-algebras, the star block equivalences are
supplied by the classification theorem `exists_starAlgEquiv_pi_cstarMatrix` above.
-/
noncomputable def finiteCStarMatrixBlockModelProvider_of_starAlgEquivProvider
    (hdecomp :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
        [FiniteDimensional ℂ A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
        [FiniteDimensional ℂ A],
        FiniteCStarMatrixBlockModel A := by
  intro A _ _ _ _
  classical
  let hA := hdecomp (A := A)
  let ι : Type u := Classical.choose hA
  have hι :
      ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    Classical.choose_spec hA
  let instι : Fintype ι := Classical.choose hι
  have hnexists :
      ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    Classical.choose_spec hι
  let n : ι → ℕ := Classical.choose hnexists
  have hpayload :
      (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (A ≃⋆ₐ[ℂ] ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    Classical.choose_spec hnexists
  letI : Fintype ι := instι
  haveI : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))) := hpayload.1
  exact finiteCStarMatrixBlockModel_of_starAlgEquiv (A := A)
    (Classical.choice hpayload.2)

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
