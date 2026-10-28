/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransport
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.Trace

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 block decomposition

Carlen 2022 Theorem 1.45 (AH1): finite-dimensional C*-algebra
classification infrastructure stage for Wedderburn decomposition,
star-compatible block providers, and coordinate central idempotents.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra
open scoped Topology
open Filter
open Matrix

universe u v

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

/-! ### Unitization semisimplicity and star-compatible block providers -/

/--
The algebraic Wedderburn-Artin input applied to the unitization of a finite
dimensional non-unital C*-algebra, once semisimplicity of the unitization is
available.

This is still only an algebra equivalence for the unitization.  The required
semisimplicity is `finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider`
below, and the upgrade to a star-compatible non-unital block equivalence for the
original algebra is the classification theorem `exists_starAlgEquiv_pi_cstarMatrix`
in `Classification.lean`.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitization_exists_algEquiv_pi_matrix
    (A : Type*) [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
    [IsSemisimpleRing (Unitization ℂ A)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (Unitization ℂ A ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (Unitization ℂ A)

/--
If semisimplicity of the unitization is available for all finite-dimensional
non-unital C*-algebras, then their unitizations admit algebraic block
decompositions uniformly.

This still does not identify the original non-unital algebra with a coordinate
block ideal, nor does it prove star compatibility of the algebraic equivalence.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitizationAlgBlockProvider_of_semisimpleProvider
    (hsemi :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        IsSemisimpleRing (Unitization ℂ A)) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
        Nonempty (Unitization ℂ A ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  intro A _ _
  haveI : IsSemisimpleRing (Unitization ℂ A) := hsemi (A := A)
  exact finiteDimensionalNonUnitalCStarAlgebra_unitization_exists_algEquiv_pi_matrix A

/--
The unitization of a finite-dimensional non-unital C*-algebra is Artinian.

This is the ring-theoretic input for the C*-specific proof that the Jacobson
radical of the unitization is zero
(`finiteDimensionalNonUnitalCStarAlgebra_unitization_jacobson_eq_bot` below).
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitization_isArtinianRing
    {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] :
    IsArtinianRing (Unitization ℂ A) := by
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  exact IsArtinianRing.of_finite ℂ (Unitization ℂ A)

/--
In a finite-dimensional algebra over `ℂ`, any element with a left inverse is a
unit.

The proof uses left multiplication by the element. A left inverse makes this
linear map injective; finite dimensionality makes it surjective, giving a right
inverse. The two inverses then coincide.
-/
theorem finiteDimensionalAlgebra_isUnit_of_exists_left_inverse
    {A : Type u} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    {r z : A} (hz : z * r = 1) :
    IsUnit r := by
  let L : A →ₗ[ℂ] A := LinearMap.mulLeft ℂ r
  have hinj : Function.Injective L := by
    intro a b hab
    have h := congrArg (fun x => z * x) hab
    calc
      a = 1 * a := by rw [one_mul]
      _ = (z * r) * a := by rw [hz]
      _ = z * (r * a) := by rw [mul_assoc]
      _ = z * (r * b) := by simpa [L, LinearMap.mulLeft_apply] using h
      _ = (z * r) * b := by rw [mul_assoc]
      _ = 1 * b := by rw [hz]
      _ = b := by rw [one_mul]
  have hsurj : Function.Surjective L := LinearMap.surjective_of_injective hinj
  rcases hsurj 1 with ⟨w, hw⟩
  have hrw : r * w = 1 := by
    simpa [L, LinearMap.mulLeft_apply] using hw
  have hwz : w = z := by
    exact (left_inv_eq_right_inv hz hrw).symm
  have hwr : w * r = 1 := by
    simpa [hwz] using hz
  exact isUnit_iff_exists.mpr ⟨w, hrw, hwr⟩

/--
For a finite-dimensional algebra over `ℂ`, an element of the Jacobson radical
gives units of the form `y * x + 1`.

This is the noncommutative replacement for the commutative
`Ideal.mem_jacobson_bot` criterion used in radical arguments. The raw
noncommutative Jacobson criterion gives only a left inverse; finite
dimensionality upgrades it to a two-sided unit.
-/
theorem finiteDimensionalAlgebra_isUnit_mul_jacobson_add_one
    {A : Type u} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    {x y : A} (hx : x ∈ Ring.jacobson A) :
    IsUnit (y * x + 1) := by
  have hx' : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
    simpa [Ideal.jacobson_bot] using hx
  rcases (Ideal.mem_jacobson_iff.mp hx') y with ⟨z, hz⟩
  have hleft : z * (y * x + 1) = 1 := by
    have hz0 : z * y * x + z - 1 = 0 := by
      simpa using hz
    have hz1 : z * y * x + z = 1 := by
      exact sub_eq_zero.mp hz0
    calc
      z * (y * x + 1) = z * y * x + z := by
        rw [mul_add, mul_one, mul_assoc]
      _ = 1 := hz1
  exact finiteDimensionalAlgebra_isUnit_of_exists_left_inverse hleft

/--
In a nontrivial C*-algebra, a self-adjoint nilpotent element is zero.

The proof uses the spectral mapping inclusion for powers: every real spectral
value of a self-adjoint nilpotent element has a positive power equal to zero,
so the real spectrum is contained in `{0}`, and the continuous functional
calculus identifies the element with zero.
-/
theorem cstarAlgebra_selfAdjoint_eq_zero_of_isNilpotent
    {A : Type u} [CStarAlgebra A] [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a) (hnil : IsNilpotent a) :
    a = 0 := by
  rcases hnil with ⟨n, hn⟩
  have hpow : a ^ (n + 1) = 0 := by
    rw [pow_succ, hn, zero_mul]
  have hspec : spectrum ℝ a ⊆ ({0} : Set ℝ) := by
    intro x hx
    have hxpow : x ^ (n + 1) ∈ spectrum ℝ (a ^ (n + 1)) := by
      exact spectrum.pow_mem_pow a (n + 1) hx
    have hxpow0 : x ^ (n + 1) = 0 := by
      simpa [hpow, spectrum.zero_eq] using hxpow
    have hx0 : x = 0 := by
      exact eq_zero_of_pow_eq_zero hxpow0
    simp [hx0]
  exact CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) (a := a) hspec ha

/--
In a finite-dimensional nontrivial C*-algebra, a self-adjoint element of the
Jacobson radical is zero.

The Artinian theorem makes the Jacobson radical nilpotent. Hence a radical
element is nilpotent, and the preceding C*-algebraic spectral lemma applies to
self-adjoint elements.
-/
theorem finiteDimensionalCStarAlgebra_selfAdjoint_eq_zero_of_mem_jacobson
    {A : Type u} [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a) (hjac : a ∈ Ring.jacobson A) :
    a = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  have hnilJ : IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) :=
    IsArtinianRing.isNilpotent_jacobson_bot
  rcases hnilJ with ⟨n, hJpow⟩
  have hmem : a ∈ Ideal.jacobson (⊥ : Ideal A) := by
    simpa [Ideal.jacobson_bot] using hjac
  have hanil : a ^ n = 0 := by
    exact Ideal.pow_eq_zero_of_mem hJpow (Nat.le_refl n) hmem
  exact cstarAlgebra_selfAdjoint_eq_zero_of_isNilpotent ha ⟨n, hanil⟩

/--
The Jacobson radical of a finite-dimensional nontrivial C*-algebra is zero.

If `x` lies in the radical, then `x⋆ * x` lies in the radical because the
radical is a left ideal. This element is self-adjoint, hence zero by the
previous theorem. The C*-identity then gives `x = 0`.
-/
theorem finiteDimensionalCStarAlgebra_jacobson_eq_bot
    {A : Type u} [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A] :
    Ring.jacobson A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxstarx : star x * x ∈ Ring.jacobson A := by
    exact (Ring.jacobson A).mul_mem_left (star x) hx
  have hsa : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hzero : star x * x = 0 :=
    finiteDimensionalCStarAlgebra_selfAdjoint_eq_zero_of_mem_jacobson hsa hxstarx
  exact (CStarRing.star_mul_self_eq_zero_iff x).mp hzero

/--
The unitization of a finite-dimensional non-unital C*-algebra has zero
Jacobson radical.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitization_jacobson_eq_bot
    {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] :
    Ring.jacobson (Unitization ℂ A) = ⊥ := by
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  exact finiteDimensionalCStarAlgebra_jacobson_eq_bot (A := Unitization ℂ A)

/--
Uniform provider form of the zero-radical statement for finite-dimensional
unitizations.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitizationJacobsonEqBotProvider :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      Ring.jacobson (Unitization ℂ A) = ⊥ := by
  intro A _ _
  exact finiteDimensionalNonUnitalCStarAlgebra_unitization_jacobson_eq_bot (A := A)

/--
For finite-dimensional unitizations, trivial Jacobson radical is exactly the
ring-theoretic input needed for semisimplicity.

The zero-radical input is supplied below by the finite-dimensional C*-algebra
radical calculation.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider_of_jacobson_eq_bot
    (hjac :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        Ring.jacobson (Unitization ℂ A) = ⊥) :
  ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      IsSemisimpleRing (Unitization ℂ A) := by
  intro A _ _
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  have hart : IsArtinianRing (Unitization ℂ A) :=
    IsArtinianRing.of_finite ℂ (Unitization ℂ A)
  exact (@IsArtinianRing.isSemisimpleRing_iff_jacobson
    (Unitization ℂ A) _ hart).mpr (hjac (A := A))

/--
Finite-dimensional unitizations of non-unital C*-algebras are semisimple.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider :
  ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      IsSemisimpleRing (Unitization ℂ A) := by
  exact finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider_of_jacobson_eq_bot
    finiteDimensionalNonUnitalCStarAlgebra_unitizationJacobsonEqBotProvider

/--
Semisimplicity of all finite-dimensional unitizations gives algebraic block
decompositions, and a star-compatibility upgrade for such algebraic
decompositions turns this into the star-compatible algebraic block
decomposition provider.

This isolates the analytic classification work in proving that the
Wedderburn-Artin decomposition of a finite-dimensional C*-algebra unitization
can be chosen star-compatible; that upgrade is
`finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade` in
`ProductAssembly.lean`.
-/
theorem starCompatibleAlgBlockProvider_of_semisimple_of_starCompatibilityUpgrade
    (hsemi :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        IsSemisimpleRing (Unitization ℂ A))
    (hupgrade :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ A ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ A ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) }) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (N : ℕ) (n : Fin N → ℕ), (∀ i, NeZero (n i)) ∧
        Nonempty
          { e :
              Unitization ℂ A ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) } := by
  intro A _ _
  rcases
    finiteDimensionalNonUnitalCStarAlgebra_unitizationAlgBlockProvider_of_semisimpleProvider
      hsemi (A := A)
    with ⟨N, n, hn, he⟩
  exact ⟨N, n, hn, hupgrade (A := A) hn he⟩

/--
The actual semisimplicity theorem for finite-dimensional unitizations discharges
the semisimplicity input in the star-compatible unitization block provider.

After this reduction, the only hypothesis is the C*-algebraic upgrade that an
algebraic Wedderburn-Artin block decomposition of the unitization can be chosen
star-compatible with the same block sizes.  This upgrade is
`finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade` in
`ProductAssembly.lean`.
-/
theorem
  starCompatibleAlgBlockProvider_of_starCompatibilityUpgrade
    (hupgrade :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
        {N : ℕ} {n : Fin N → ℕ},
        (∀ i, NeZero (n i)) →
        Nonempty
          (Unitization ℂ A ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ) →
        Nonempty
          { e :
              Unitization ℂ A ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) }) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (N : ℕ) (n : Fin N → ℕ), (∀ i, NeZero (n i)) ∧
        Nonempty
          { e :
              Unitization ℂ A ≃ₐ[ℂ]
                ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
            ∀ x, e (star x) = star (e x) } :=
  starCompatibleAlgBlockProvider_of_semisimple_of_starCompatibilityUpgrade
    finiteDimensionalNonUnitalCStarAlgebra_unitizationSemisimpleProvider hupgrade

/-! ### Central idempotents and coordinate block projections -/
/--
In a C*-algebra, a central idempotent is self-adjoint.

This is one of the local C*-algebraic inputs for upgrading an algebraic
Wedderburn-Artin block decomposition to a star-compatible one: central block
idempotents become star projections.
-/
theorem central_idempotent_isSelfAdjoint_of_cstar
    {B : Type u} [CStarAlgebra B] {p : B}
    (hp : p * p = p) (hcentral : ∀ x : B, p * x = x * p) :
    IsSelfAdjoint p := by
  have hidem : IsIdempotentElem p := by
    exact hp
  have hnormal : IsStarNormal p := by
    refine ⟨?_⟩
    exact (hcentral (star p)).symm
  exact (IsIdempotentElem.isSelfAdjoint_iff_isStarNormal hidem).mpr hnormal

/--
The same central idempotent lemma in the projection form used by the
star-compatible block decomposition argument.
-/
theorem central_idempotent_isStarProjection_of_cstar
    {B : Type u} [CStarAlgebra B] {p : B}
    (hp : p * p = p) (hcentral : ∀ x : B, p * x = x * p) :
    IsStarProjection p where
  isIdempotentElem := hp
  isSelfAdjoint :=
    (central_idempotent_isSelfAdjoint_of_cstar hp hcentral).star_eq

/--
The central idempotent of a coordinate block, pulled back along an algebraic
Wedderburn-Artin product decomposition.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) : B :=
  e.symm (Pi.single i (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ))

/--
The coordinate block idempotent pulled back from a product of matrix algebras is
idempotent in the original C*-algebra.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_isIdempotent
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    IsIdempotentElem (algEquivPiMatrixCoordinateCentralIdempotent n e i) := by
  rw [IsIdempotentElem]
  apply e.injective
  ext j a b
  by_cases hj : j = i
  · subst j
    simp [algEquivPiMatrixCoordinateCentralIdempotent]
  · simp [algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hj]

/--
The coordinate block idempotent pulled back from a product of matrix algebras is
central in the original C*-algebra.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_central
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    ∀ x : B,
      algEquivPiMatrixCoordinateCentralIdempotent n e i * x =
        x * algEquivPiMatrixCoordinateCentralIdempotent n e i := by
  intro x
  apply e.injective
  ext j a b
  by_cases hj : j = i
  · subst j
    simp [algEquivPiMatrixCoordinateCentralIdempotent]
  · simp [algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hj]

/--
The pulled-back coordinate block idempotent is multiplicatively central in the
sense required by Mathlib's complete orthogonal idempotent decomposition API.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_isMulCentral
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    IsMulCentral (algEquivPiMatrixCoordinateCentralIdempotent n e i) where
  comm x := by
    rw [commute_iff_eq]
    exact algEquivPiMatrixCoordinateCentralIdempotent_central n e i x
  left_assoc x y := by
    rw [mul_assoc]
  right_assoc x y := by
    rw [mul_assoc]

/--
Thus every algebraic coordinate block idempotent in a finite-dimensional
C*-algebra Wedderburn-Artin product decomposition is a star projection.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    IsStarProjection (algEquivPiMatrixCoordinateCentralIdempotent n e i) :=
  central_idempotent_isStarProjection_of_cstar
    (algEquivPiMatrixCoordinateCentralIdempotent_isIdempotent n e i)
    (algEquivPiMatrixCoordinateCentralIdempotent_central n e i)

/--
Distinct coordinate block idempotents in an algebraic product decomposition are
orthogonal after pulling back to the original C*-algebra.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_mul_eq_zero_of_ne
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    {i j : ι} (hij : i ≠ j) :
    algEquivPiMatrixCoordinateCentralIdempotent n e i *
        algEquivPiMatrixCoordinateCentralIdempotent n e j = 0 := by
  apply e.injective
  ext k a b
  by_cases hki : k = i
  · subst k
    simp [algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hij]
  · simp [algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hki]

/--
For a finite product decomposition, the pulled-back coordinate block
idempotents sum to the unit.
-/
theorem sum_algEquivPiMatrixCoordinateCentralIdempotent_eq_one
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    (∑ i : ι, algEquivPiMatrixCoordinateCentralIdempotent n e i) = 1 := by
  apply e.injective
  ext k a b
  have hsum :
      (∑ i : ι,
          (Pi.single i (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
            ∀ j : ι, Matrix (Fin (n j)) (Fin (n j)) ℂ) k a b) =
        (1 : Matrix (Fin (n k)) (Fin (n k)) ℂ) a b := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _hi hik
      simp [Pi.single_eq_of_ne' hik]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  calc
    e (∑ i : ι, algEquivPiMatrixCoordinateCentralIdempotent n e i) k a b =
        (∑ i : ι,
          (Pi.single i (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
            ∀ j : ι, Matrix (Fin (n j)) (Fin (n j)) ℂ) k a b) := by
          simp only [algEquivPiMatrixCoordinateCentralIdempotent, map_sum,
            AlgEquiv.apply_symm_apply, Finset.sum_apply]
          rw [Matrix.sum_apply]
    _ = (1 : Matrix (Fin (n k)) (Fin (n k)) ℂ) a b := by
        exact hsum
    _ = e (1 : B) k a b := by
        simp

/--
The coordinate block idempotents pulled back from a finite algebraic
Wedderburn-Artin product decomposition form a complete orthogonal family.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    CompleteOrthogonalIdempotents
      (fun i : ι => algEquivPiMatrixCoordinateCentralIdempotent n e i) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro i j hij
    exact algEquivPiMatrixCoordinateCentralIdempotent_mul_eq_zero_of_ne n e hij
  · exact sum_algEquivPiMatrixCoordinateCentralIdempotent_eq_one n e

/--
The complete orthogonal central block idempotents induce the standard ring
equivalence from the original algebra to the product of their corners.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    B ≃+* ∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner :=
  (algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).ringEquivOfIsMulCentral
    (fun i => algEquivPiMatrixCoordinateCentralIdempotent_isMulCentral n e i)


end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
