/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerNormalization

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 product assembly

Carlen 2022 Theorem 1.45 (AH1): product assembly, unitization star-block
providers, two-sided star ideals, block images, and active-coordinate product
ideal decomposition.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra
open scoped Topology
open Filter
open Matrix

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

/-! ### Product assembly and unitization star-block providers -/
/--
If every star-invariant coordinate corner has already been normalized to the
standard `CStarMatrix` involution on the corresponding block size, then the
coordinatewise product of these normalizations is a star algebra equivalence
from the corner product to the `CStarMatrix` product.
-/
noncomputable def
    algEquivPiMatrixCoordinateCentralIdempotent_cornerProductCStarMatrixStarAlgEquiv.{u, v}
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (φ : ∀ i : ι,
      letI : Algebra ℂ
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        algebraCornerOfIsIdempotentElem
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
      letI : StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
        ≃⋆ₐ[ℂ]
        CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    letI : ∀ i : ι,
        Algebra ℂ
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      fun i =>
        algebraCornerOfIsIdempotentElem
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : ∀ i : ι,
        StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      fun i =>
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    letI : Algebra ℂ (∀ i : ι,
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      Pi.algebra ι
        (fun i : ι =>
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner)
    (∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner)
      ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  classical
  letI : ∀ i : ι,
      Algebra ℂ
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    fun i =>
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  letI : ∀ i : ι,
      StarRing
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    fun i =>
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
  letI : Algebra ℂ (∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    Pi.algebra ι
      (fun i : ι =>
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner)
  refine StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.piCongrRight (R := ℂ) (fun i => (φ i).toAlgEquiv)) ?_
  intro x
  funext i
  exact map_star (φ i) (x i)

/--
Combining the star-compatible corner decomposition of `B` with coordinatewise
normalizations of all corners gives a star algebra equivalence from `B` to the
same indexed product of concrete `CStarMatrix` blocks.
-/
noncomputable def
    algEquivPiMatrixCoordinateCentralIdempotent_piCStarMatrixStarAlgEquiv_of_cornerEquivs.{u, v}
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (φ : ∀ i : ι,
      letI : Algebra ℂ
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        algebraCornerOfIsIdempotentElem
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
      letI : StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
        ≃⋆ₐ[ℂ]
        CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    B ≃⋆ₐ[ℂ] (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  classical
  letI : ∀ i : ι,
      Semiring
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    fun _ => inferInstance
  letI : ∀ i : ι,
      Algebra ℂ
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    fun i =>
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  letI : Algebra ℂ (∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      Pi.algebra ι
        (fun i : ι =>
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner)
  letI : ∀ i : ι,
      StarRing
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    fun i =>
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
  exact
    (algEquivPiMatrixCoordinateCentralIdempotent_cornerStarAlgEquiv n e).trans
      (algEquivPiMatrixCoordinateCentralIdempotent_cornerProductCStarMatrixStarAlgEquiv n e φ)

/--
Left multiplication by a central star projection is a non-unital star algebra
endomorphism.  In the block decomposition argument this is the algebraic
projection onto the summand cut out by the central block projection.
-/
def central_starProjection_leftMul_nonUnitalStarAlgHom.{u}
    {B : Type u} [CStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hcentral : ∀ x : B, p * x = x * p) :
    B →⋆ₙₐ[ℂ] B where
  toFun x := p * x
  map_zero' := by
    simp
  map_add' := by
    intro x y
    rw [mul_add]
  map_mul' := by
    intro x y
    have hpxp : (p * x) * p = p * x := by
      calc
        (p * x) * p = p * (x * p) := by rw [mul_assoc]
        _ = p * (p * x) := by rw [hcentral x]
        _ = (p * p) * x := by rw [mul_assoc]
        _ = p * x := by rw [hp.isIdempotentElem]
    calc
      p * (x * y) = (p * x) * y := by rw [mul_assoc]
      _ = ((p * x) * p) * y := by rw [hpxp]
      _ = (p * x) * (p * y) := by rw [mul_assoc]
  map_smul' := by
    intro c x
    simp
  map_star' := by
    intro x
    calc
      p * star x = star x * p := hcentral (star x)
      _ = star x * star p := by rw [hp.isSelfAdjoint]
      _ = star (p * x) := (star_mul p x).symm

/--
The range of the central star-projection map `x ↦ p * x` is exactly the
summand fixed by `p`.
-/
theorem central_starProjection_leftMul_mem_range_iff.{u}
    {B : Type u} [CStarAlgebra B] {p x : B}
    (hp : IsStarProjection p) (hcentral : ∀ y : B, p * y = y * p) :
    x ∈ NonUnitalStarAlgHom.range
      (central_starProjection_leftMul_nonUnitalStarAlgHom hp hcentral) ↔
      p * x = x := by
  constructor
  · intro hx
    rcases (NonUnitalStarAlgHom.mem_range
        (central_starProjection_leftMul_nonUnitalStarAlgHom hp hcentral)).mp hx
      with ⟨y, rfl⟩
    calc
      p * (p * y) = (p * p) * y := by rw [mul_assoc]
      _ = p * y := by rw [hp.isIdempotentElem]
  · intro hx
    refine (NonUnitalStarAlgHom.mem_range
        (central_starProjection_leftMul_nonUnitalStarAlgHom hp hcentral)).mpr ?_
    exact ⟨x, hx⟩

/--
A unital finite-dimensional C*-algebra star-compatibility upgrade supplies the
corresponding upgrade for unitizations of finite-dimensional non-unital
C*-algebras.

This is the thin wrapper separating the unital Wedderburn-Artin
star-compatibility upgrade, proved below as
`finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv`, from the
unitization-specific provider shape used below.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade_of_unital.{u}
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
          ∀ x, e (star x) = star (e x) } := by
  intro A _ _ N n hn h
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  exact hupgradeUnital (B := Unitization ℂ A) hn h

universe v
universe u

/--
The entrywise identification of ordinary matrix blocks with `CStarMatrix`
blocks, bundled over a product as a star algebra equivalence.
-/
noncomputable def piMatrixCStarMatrixStarAlgEquiv
    {ι : Type v} (n : ι → ℕ) :
    (∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  classical
  refine StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.piCongrRight (R := ℂ)
      (fun i => (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin (n i))).toAlgEquiv))
    ?_
  intro x
  ext i a b
  rfl

/--
Once the coordinate corners have been normalized to the standard
`CStarMatrix` involutions, the resulting star algebra equivalence can be
returned to the original `Matrix` product target.  This is the theorem-facing
assembly form of the unital Wedderburn-Artin star-compatibility upgrade,
conditional only on the per-corner normalization step, which is
`cornerCStarMatrixStarAlgEquiv` in `CornerNormalization.lean`.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_starCompatibleAlgEquiv_of_cornerEquivs
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (φ : ∀ i : ι,
      letI : Algebra ℂ
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        algebraCornerOfIsIdempotentElem
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
      letI : StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
        ≃⋆ₐ[ℂ]
        CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    { e' : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ //
      ∀ x, e' (star x) = star (e' x) } := by
  classical
  let ψ : B ≃⋆ₐ[ℂ] (∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :=
    (algEquivPiMatrixCoordinateCentralIdempotent_piCStarMatrixStarAlgEquiv_of_cornerEquivs
      n e φ).trans
      (piMatrixCStarMatrixStarAlgEquiv n).symm
  exact ⟨ψ.toAlgEquiv, fun x => map_star ψ x⟩

/--
Nonempty provider form of the preceding assembly hook.  It turns a family of
per-corner `CStarMatrix` normalizations into the existence statement used by
the star-compatible Wedderburn-Artin upgrade.
-/
theorem
    algEquivPiMatrixCoordinateCentralIdempotent_exists_starCompatibleAlgEquiv_of_cornerEquivProvider
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Finite ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (hφ :
      letI : Fintype ι := Fintype.ofFinite ι
      ∀ i : ι,
      letI : Algebra ℂ
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        algebraCornerOfIsIdempotentElem
          ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
      letI : StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
      Nonempty
        ((((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner)
          ≃⋆ₐ[ℂ]
          CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    Nonempty
      { e' : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ //
        ∀ x, e' (star x) = star (e' x) } := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact
    ⟨algEquivPiMatrixCoordinateCentralIdempotent_starCompatibleAlgEquiv_of_cornerEquivs
      n e (fun i => Classical.choice (hφ i))⟩

/--
Unital finite-dimensional C*-algebra version of the star-compatible
Wedderburn-Artin upgrade.  A fixed algebraic product decomposition is not made
star-preserving; rather, using the same indexed target product and the same
block sizes, we choose a new algebra equivalence which is star-compatible.
-/
theorem finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv
    {B : Type u} [CStarAlgebra B] [FiniteDimensional ℂ B]
    {N : ℕ} {n : Fin N → ℕ}
    (hn : ∀ i, NeZero (n i))
    (h :
      Nonempty
        (B ≃ₐ[ℂ]
          ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ)) :
    Nonempty
      { e :
          B ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
        ∀ x, e (star x) = star (e x) } := by
  classical
  rcases h with ⟨e⟩
  exact
    algEquivPiMatrixCoordinateCentralIdempotent_exists_starCompatibleAlgEquiv_of_cornerEquivProvider
    n e
    (by
      intro i
      haveI : NeZero (n i) := hn i
      exact ⟨cornerCStarMatrixStarAlgEquiv n e i⟩)

/--
Unitization version of the star-compatible Wedderburn-Artin upgrade.  This is
the non-unital corollary of the unital finite-dimensional C*-algebra upgrade.
-/
theorem finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade
    {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
    {N : ℕ} {n : Fin N → ℕ}
    (hn : ∀ i, NeZero (n i))
    (h :
      Nonempty
        (Unitization ℂ A ≃ₐ[ℂ]
          ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ)) :
    Nonempty
      { e :
          Unitization ℂ A ≃ₐ[ℂ]
            ∀ i : Fin N, Matrix (Fin (n i)) (Fin (n i)) ℂ //
        ∀ x, e (star x) = star (e x) } :=
  finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade_of_unital
    finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv
    hn h

/--
A star-compatible algebraic block decomposition of the unitization gives a star
algebra equivalence from the unitization to a product of `CStarMatrix` blocks.

This still does not prove that the Wedderburn-Artin equivalence is
star-compatible, nor does it identify the original non-unital algebra inside
the unitization.
-/
noncomputable def unitizationStarAlgEquiv_piCStarMatrix_of_starCompatibleAlgEquiv
    {A : Type u} [NonUnitalCStarAlgebra A]
    {ι : Type v} (n : ι → ℕ)
    (e : Unitization ℂ A ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (hstar : ∀ x, e (star x) = star (e x)) :
    Unitization ℂ A ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
  (StarAlgEquiv.ofAlgEquiv e hstar).trans (piMatrixCStarMatrixStarAlgEquiv n)

/--
Existential form of the preceding bridge: if the unitization has an algebraic
block decomposition whose equivalence is known to preserve star, then it has a
`CStarMatrix`-valued star algebra block decomposition.
-/
theorem unitization_exists_starAlgEquiv_pi_cstarMatrix_of_starCompatible_algEquiv
    {A : Type u} [NonUnitalCStarAlgebra A]
    (h :
      ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
        Nonempty
          { e :
              Unitization ℂ A ≃ₐ[ℂ]
                ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ //
            ∀ x, e (star x) = star (e x) }) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty
        (Unitization ℂ A ≃⋆ₐ[ℂ]
          ∀ i : Fin n, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) := by
  rcases h with ⟨n, d, hd, ⟨e⟩⟩
  exact
    ⟨n, d, hd,
      ⟨unitizationStarAlgEquiv_piCStarMatrix_of_starCompatibleAlgEquiv
        (A := A) (n := d) e.1 e.2⟩⟩

/-- Reindex a finite `CStarMatrix` product from `Fin N` to its universe lift. -/
noncomputable def piCStarMatrixULiftStarAlgEquiv
    {N : ℕ} (d : Fin N → ℕ) :
    (∀ i : Fin N, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ i : ULift.{u} (Fin N),
        CStarMatrix (Fin (d i.down)) (Fin (d i.down)) ℂ) := by
  refine StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.piCongrLeft' ℂ
      (fun i : Fin N => CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
      (Equiv.ulift.symm)) ?_
  intro x
  ext i
  cases i
  rfl

/--
A uniform star-compatible algebraic block decomposition provider for
unitizations supplies the unitization-level star block decomposition provider.
-/
theorem unitizationStarAlgEquivProvider_of_starCompatibleAlgBlock
    (h :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
          Nonempty
            { e :
                Unitization ℂ A ≃ₐ[ℂ]
                  ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ //
              ∀ x, e (star x) = star (e x) }) :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (Unitization ℂ A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  intro A _ _
  classical
  rcases
    unitization_exists_starAlgEquiv_pi_cstarMatrix_of_starCompatible_algEquiv
      (A := A) (h (A := A))
    with ⟨N, d, hd, ⟨e⟩⟩
  refine
    ⟨ULift (Fin N), inferInstance, (fun i : ULift (Fin N) => d i.down), ?_,
      ⟨e.trans (piCStarMatrixULiftStarAlgEquiv d)⟩⟩
  intro i
  haveI : NeZero (d i.down) := hd i.down
  infer_instance

/--
The unital star-compatibility upgrade alone supplies the unitization-level
`CStarMatrix` star-block provider, after the already-proved finite-dimensional
unitization semisimplicity and algebraic Wedderburn-Artin inputs.
-/
theorem unitizationStarAlgEquivProvider_of_unitalStarCompatibilityUpgrade
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
        Nonempty (Unitization ℂ A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
  unitizationStarAlgEquivProvider_of_starCompatibleAlgBlock
    (
  starCompatibleAlgBlockProvider_of_starCompatibilityUpgrade
    (finiteDimensionalNonUnitalCStarAlgebra_unitization_starCompatibilityUpgrade_of_unital
      hupgradeUnital))

/--
Actual unitization star block decomposition provider, with the unital
star-compatible Wedderburn-Artin upgrade already supplied by
`finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv`.
-/
theorem unitizationStarAlgEquivProvider :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
      ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
        (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
        Nonempty (Unitization ℂ A ≃⋆ₐ[ℂ]
          ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
  unitizationStarAlgEquivProvider_of_unitalStarCompatibilityUpgrade
    finiteDimensionalCStarAlgebra_starCompatibleAlgEquiv_pi_matrix_of_algEquiv

/--
The original non-unital C*-algebra is star-algebra equivalent to its canonical
range inside the unitization.

This is the first extraction step from a unitization-level decomposition back
to the original non-unital algebra.
-/
theorem nonUnitalCStarAlgebra_starAlgEquiv_unitization_inrRange
    (A : Type*) [NonUnitalCStarAlgebra A] :
    Nonempty
      (A ≃⋆ₐ[ℂ]
        NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom ℂ A)) :=
  ⟨Unitization.inrRangeEquiv ℂ A⟩

/-! ### Two-sided star ideals and unitization block images -/
/--
A non-unital star subalgebra is a two-sided star ideal when it is closed under
left and right multiplication by arbitrary ambient elements.  Star-closure is
already part of `NonUnitalStarSubalgebra`.
-/
def IsTwoSidedStarIdeal {R A : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (S : NonUnitalStarSubalgebra R A) : Prop :=
  (∀ b x : A, x ∈ S → b * x ∈ S) ∧
    (∀ b x : A, x ∈ S → x * b ∈ S)

/--
The range cut out by a central star projection is a two-sided star ideal.
-/
theorem central_starProjection_leftMul_range_isTwoSidedStarIdeal
    {B : Type u} [CStarAlgebra B] {p : B}
    (hp : IsStarProjection p) (hcentral : ∀ y : B, p * y = y * p) :
    IsTwoSidedStarIdeal
      (NonUnitalStarAlgHom.range
        (central_starProjection_leftMul_nonUnitalStarAlgHom hp hcentral)) := by
  constructor
  · intro b x hx
    have hxfix :
        p * x = x :=
      (central_starProjection_leftMul_mem_range_iff (x := x) hp hcentral).mp hx
    exact
      (central_starProjection_leftMul_mem_range_iff (x := b * x) hp hcentral).mpr
        (by
          calc
            p * (b * x) = (p * b) * x := by rw [mul_assoc]
            _ = (b * p) * x := by rw [hcentral b]
            _ = b * (p * x) := by rw [mul_assoc]
            _ = b * x := by rw [hxfix])
  · intro b x hx
    have hxfix :
        p * x = x :=
      (central_starProjection_leftMul_mem_range_iff (x := x) hp hcentral).mp hx
    exact
      (central_starProjection_leftMul_mem_range_iff (x := x * b) hp hcentral).mpr
        (by
          calc
            p * (x * b) = (p * x) * b := by rw [mul_assoc]
            _ = x * b := by rw [hxfix])

/--
For an algebraic Wedderburn-Artin product decomposition, the range of the
coordinate block projection pulled back to the C*-algebra is a two-sided star
ideal.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_leftMul_range_isTwoSidedStarIdeal
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    IsTwoSidedStarIdeal
      (NonUnitalStarAlgHom.range
        (central_starProjection_leftMul_nonUnitalStarAlgHom
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
          (algEquivPiMatrixCoordinateCentralIdempotent_central n e i))) :=
  central_starProjection_leftMul_range_isTwoSidedStarIdeal
    (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    (algEquivPiMatrixCoordinateCentralIdempotent_central n e i)

/--
If a two-sided star ideal in one concrete `CStarMatrix` block contains a
matrix with a nonzero entry, then it contains every standard matrix unit.
-/
private theorem cstarMatrix_single_mem_of_nonzero_mem_twoSidedStarIdeal
    {n : ℕ} (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) ℂ))
    (hS : IsTwoSidedStarIdeal S)
    {X : CStarMatrix (Fin n) (Fin n) ℂ} (hX : X ∈ S)
    {p q : Fin n} (hpq : X p q ≠ 0) (i j : Fin n) :
    CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) ∈ S := by
  have hleft : CStarMatrix.ofMatrix (Matrix.single i p ((X p q)⁻¹)) * X ∈ S :=
    hS.1 (CStarMatrix.ofMatrix (Matrix.single i p ((X p q)⁻¹))) X hX
  have hboth :
      (CStarMatrix.ofMatrix (Matrix.single i p ((X p q)⁻¹)) * X) *
          CStarMatrix.ofMatrix (Matrix.single q j (1 : ℂ)) ∈ S :=
    hS.2 (CStarMatrix.ofMatrix (Matrix.single q j (1 : ℂ)))
      (CStarMatrix.ofMatrix (Matrix.single i p ((X p q)⁻¹)) * X) hleft
  have hprod :
      CStarMatrix.ofMatrix (Matrix.single i p ((X p q)⁻¹)) * X *
          CStarMatrix.ofMatrix (Matrix.single q j (1 : ℂ)) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) := by
    change CStarMatrix.ofMatrix
        (Matrix.single i p ((X p q)⁻¹) * CStarMatrix.ofMatrix.symm X *
          Matrix.single q j (1 : ℂ)) =
      CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ))
    rw [Matrix.single_mul_mul_single]
    simp [hpq]
  simpa [hprod] using hboth

/--
If a non-unital star subalgebra of one concrete `CStarMatrix` block contains
all standard matrix units, then it is the whole block.
-/
private theorem cstarMatrix_mem_of_matrix_units_mem
    {n : ℕ} (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) ℂ))
    (hunits : ∀ i j : Fin n, CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) ∈ S)
    (M : CStarMatrix (Fin n) (Fin n) ℂ) : M ∈ S := by
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
          CStarMatrix.ofMatrix (Matrix.single i j (M i j))) ∈ S := by
    refine Submodule.sum_mem S.toSubmodule ?_
    intro i _hi
    refine Submodule.sum_mem S.toSubmodule ?_
    intro j _hj
    have hunit := hunits i j
    have hsmul : (M i j) • CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)) ∈ S := by
      exact SMulMemClass.smul_mem (M i j) hunit
    simpa [NonUnitalSubalgebra.mem_toSubmodule, Matrix.smul_single] using hsmul
  have hM : M = ∑ i : Fin n, ∑ j : Fin n,
      CStarMatrix.ofMatrix (Matrix.single i j (M i j)) := by
    exact congrArg CStarMatrix.ofMatrix
      (Matrix.matrix_eq_sum_single (CStarMatrix.ofMatrix.symm M))
  simpa [NonUnitalSubalgebra.mem_toSubmodule, ← hM] using hsum

/--
A two-sided star ideal in one concrete `CStarMatrix` block is either zero or
the whole block, stated in membership form.
-/
theorem cstarMatrix_isTwoSidedStarIdeal_zero_or_univ
    {n : ℕ}
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) ℂ))
    (hS : IsTwoSidedStarIdeal S) :
    (∀ X : CStarMatrix (Fin n) (Fin n) ℂ, X ∈ S → X = 0) ∨
      (∀ M : CStarMatrix (Fin n) (Fin n) ℂ, M ∈ S) := by
  classical
  by_cases hzero : ∀ X : CStarMatrix (Fin n) (Fin n) ℂ, X ∈ S → X = 0
  · exact Or.inl hzero
  · right
    push_neg at hzero
    rcases hzero with ⟨X, hX, hXne⟩
    have hentry : ¬ ∀ p q : Fin n, X p q = 0 := by
      intro hzero_entries
      apply hXne
      ext p q
      exact hzero_entries p q
    push_neg at hentry
    rcases hentry with ⟨p, q, hpq⟩
    intro M
    apply cstarMatrix_mem_of_matrix_units_mem S
    intro i j
    exact cstarMatrix_single_mem_of_nonzero_mem_twoSidedStarIdeal S hS hX hpq i j

/--
The canonical image of a non-unital C*-algebra inside its unitization is a
two-sided star ideal.
-/
theorem unitization_inrRange_isTwoSidedStarIdeal
    (A : Type u) [NonUnitalCStarAlgebra A] :
    IsTwoSidedStarIdeal
      (NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom ℂ A)) := by
  constructor
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (Unitization.inrNonUnitalStarAlgHom ℂ A)).mp hx with ⟨a, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (Unitization.inrNonUnitalStarAlgHom ℂ A)).mpr ?_
    refine ⟨b.fst • a + b.snd * a, ?_⟩
    ext <;> simp [Unitization.fst_mul, Unitization.snd_mul]
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (Unitization.inrNonUnitalStarAlgHom ℂ A)).mp hx with ⟨a, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (Unitization.inrNonUnitalStarAlgHom ℂ A)).mpr ?_
    refine ⟨b.fst • a + a * b.snd, ?_⟩
    ext <;> simp [Unitization.fst_mul, Unitization.snd_mul]

/--
The standard embedding of a non-unital C*-algebra into its unitization, followed
by a unitization-level star block decomposition.
-/
noncomputable def unitizationBlockImageHom
    {A : Type u} [NonUnitalCStarAlgebra A]
    {ι : Type v} (n : ι → ℕ)
    (e : Unitization ℂ A ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    A →⋆ₙₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) where
  toFun a := e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a)
  map_zero' := by simp
  map_add' := by
    intro x y
    simp [map_add]
  map_mul' := by
    intro x y
    calc
      e ((Unitization.inrNonUnitalStarAlgHom ℂ A) (x * y))
          = e (((Unitization.inrNonUnitalStarAlgHom ℂ A) x) *
              ((Unitization.inrNonUnitalStarAlgHom ℂ A) y)) := by
            rw [map_mul]
      _ = e ((Unitization.inrNonUnitalStarAlgHom ℂ A) x) *
          e ((Unitization.inrNonUnitalStarAlgHom ℂ A) y) := by
            rw [map_mul]
  map_smul' := by
    intro c x
    simp [map_smul]
  map_star' := by
    intro x
    simp [map_star]

/--
The image of a non-unital C*-algebra under a unitization-level star block
decomposition is a two-sided star ideal in the finite block product.
-/
theorem unitizationBlockImageRange_isTwoSidedStarIdeal
    {A : Type u} [NonUnitalCStarAlgebra A]
    {ι : Type v} (n : ι → ℕ)
    (e : Unitization ℂ A ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    IsTwoSidedStarIdeal
      (NonUnitalStarAlgHom.range
        (unitizationBlockImageHom (A := A) (n := n) e)) := by
  constructor
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (unitizationBlockImageHom (A := A) (n := n) e)).mp hx with ⟨a, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (unitizationBlockImageHom (A := A) (n := n) e)).mpr ?_
    refine ⟨(e.symm b).fst • a + (e.symm b).snd * a, ?_⟩
    change
      e ((Unitization.inrNonUnitalStarAlgHom ℂ A) ((e.symm b).fst • a + (e.symm b).snd * a)) =
        b * e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a)
    calc
      e ((Unitization.inrNonUnitalStarAlgHom ℂ A)
          ((e.symm b).fst • a + (e.symm b).snd * a))
          = e ((e.symm b) * ((Unitization.inrNonUnitalStarAlgHom ℂ A) a)) := by
            congr 1
            ext <;> simp [Unitization.fst_mul, Unitization.snd_mul]
      _ = e (e.symm b) * e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a) := by
            rw [map_mul]
      _ = b * e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a) := by
            simp
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (unitizationBlockImageHom (A := A) (n := n) e)).mp hx with ⟨a, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (unitizationBlockImageHom (A := A) (n := n) e)).mpr ?_
    refine ⟨(e.symm b).fst • a + a * (e.symm b).snd, ?_⟩
    change
      e ((Unitization.inrNonUnitalStarAlgHom ℂ A) ((e.symm b).fst • a + a * (e.symm b).snd)) =
        e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a) * b
    calc
      e ((Unitization.inrNonUnitalStarAlgHom ℂ A)
          ((e.symm b).fst • a + a * (e.symm b).snd))
          = e (((Unitization.inrNonUnitalStarAlgHom ℂ A) a) * (e.symm b)) := by
            congr 1
            ext <;> simp [Unitization.fst_mul, Unitization.snd_mul]
      _ = e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a) * e (e.symm b) := by
            rw [map_mul]
      _ = e ((Unitization.inrNonUnitalStarAlgHom ℂ A) a) * b := by
            simp

/--
After a unitization-level star block decomposition is fixed, the original
non-unital algebra is star-algebra equivalent to its image inside the block
product.

This still does not identify that image with a coordinate block product.
-/
theorem nonUnitalCStarAlgebra_starAlgEquiv_unitizationBlockImageRange
    {A : Type u} [NonUnitalCStarAlgebra A]
    {ι : Type v} (n : ι → ℕ)
    (e : Unitization ℂ A ≃⋆ₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    Nonempty
      (A ≃⋆ₐ[ℂ]
        NonUnitalStarAlgHom.range
          (unitizationBlockImageHom (A := A) (n := n) e)) := by
  classical
  refine
    ⟨StarAlgEquiv.ofInjective'
      (unitizationBlockImageHom (A := A) (n := n) e) ?_⟩
  intro x y hxy
  have hunit :
      (Unitization.inrNonUnitalStarAlgHom ℂ A) x =
        (Unitization.inrNonUnitalStarAlgHom ℂ A) y := by
    apply e.injective
    exact hxy
  exact (Unitization.inrRangeEquiv ℂ A).injective (Subtype.ext hunit)

/-! ### Active-coordinate product ideal decomposition -/
/--
A coordinate of a two-sided star ideal in a finite product of `CStarMatrix`
blocks is active if some element of the ideal has a nonzero value there.
-/
private def piCStarMatrixIdealActive
    {ι : Type u} {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (i : ι) : Prop :=
  ∃ X : ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ, X ∈ S ∧ X i ≠ 0

/-- Evaluate a product-subalgebra element at one coordinate. -/
private noncomputable def piCStarMatrix_coordinateEval
    {ι : Type u} {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (i : ι) :
    S →⋆ₙₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ where
  toFun X := X.1 i
  map_zero' := rfl
  map_add' := by
    intro x y
    rfl
  map_mul' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl
  map_star' := by
    intro x
    rfl

/--
The coordinate image of a two-sided star ideal in a finite product is again a
two-sided star ideal in the corresponding block.
-/
private theorem piCStarMatrix_coordinateImage_isTwoSidedStarIdeal
    {ι : Type u} {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hS : IsTwoSidedStarIdeal S)
    (i : ι) :
    IsTwoSidedStarIdeal
      (NonUnitalStarAlgHom.range (piCStarMatrix_coordinateEval S i)) := by
  classical
  constructor
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mp hx with ⟨X, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mpr ?_
    let L : ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ := Pi.single i b
    refine ⟨⟨L * X.1, hS.1 L X.1 X.2⟩, ?_⟩
    ext r s
    change (L * X.1) i r s = (b * X.1 i) r s
    simp [L]
  · intro b x hx
    rcases (NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mp hx with ⟨X, rfl⟩
    refine (NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mpr ?_
    let R : ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ := Pi.single i b
    refine ⟨⟨X.1 * R, hS.2 R X.1 X.2⟩, ?_⟩
    ext r s
    change (X.1 * R) i r s = (X.1 i * b) r s
    simp [R]

/--
If one coordinate of a finite-product two-sided star ideal is active, then the
ideal contains every element supported only at that coordinate.
-/
private theorem piCStarMatrix_single_mem_of_active_twoSidedStarIdeal
    {ι : Type u} [DecidableEq ι] {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hS : IsTwoSidedStarIdeal S)
    {i : ι} (hi : piCStarMatrixIdealActive S i)
    (M : CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    Pi.single i M ∈ S := by
  have hcoord := cstarMatrix_isTwoSidedStarIdeal_zero_or_univ
    (NonUnitalStarAlgHom.range (piCStarMatrix_coordinateEval S i))
    (piCStarMatrix_coordinateImage_isTwoSidedStarIdeal S hS i)
  rcases hi with ⟨X, hX, hXi⟩
  rcases hcoord with hzero | huniv
  · have hXi_zero : X i = 0 := hzero (X i)
      ((NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mpr ⟨⟨X, hX⟩, rfl⟩)
    exact (hXi hXi_zero).elim
  · have hMrange : M ∈ NonUnitalStarAlgHom.range
        (piCStarMatrix_coordinateEval S i) := huniv M
    rcases (NonUnitalStarAlgHom.mem_range
        (piCStarMatrix_coordinateEval S i)).mp hMrange with ⟨Y, hY⟩
    change Y.1 i = M at hY
    let P : ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ :=
      Pi.single i (1 : CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
    have hPY : P * Y.1 ∈ S := hS.1 P Y.1 Y.2
    have hEq : P * Y.1 = Pi.single i M := by
      ext k r s
      by_cases hk : k = i
      · subst k
        have hleft :
            (P * Y.1) i =
              (1 : CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) * M := by
          ext a b
          simp [P, hY]
        have hright :
            ((Pi.single i M :
              ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ) i) = M := by
          simp
        calc
          (P * Y.1) i r s =
              ((1 : CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) * M) r s :=
                congrFun₂ hleft r s
          _ = M r s := congrFun₂ (one_mul M) r s
          _ = ((Pi.single i M :
                ∀ k : ι, CStarMatrix (Fin (n k)) (Fin (n k)) ℂ) i) r s :=
              (congrFun₂ hright r s).symm
      · simp [P, Pi.single_eq_of_ne hk]
    simpa [hEq] using hPY

/--
Membership in a finite-product two-sided star ideal is equivalent to vanishing
on all inactive coordinates.
-/
private theorem piCStarMatrix_mem_iff_inactive_coord_zero_of_twoSidedStarIdeal
    {ι : Type u} [Finite ι] {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hS : IsTwoSidedStarIdeal S)
    (M : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :
    M ∈ S ↔ ∀ i : ι, ¬ piCStarMatrixIdealActive S i → M i = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hM i hi
    by_contra hne
    exact hi ⟨M, hM, hne⟩
  · intro hM
    have hsum : (∑ i : ι, Pi.single i (M i)) ∈ S := by
      refine Submodule.sum_mem S.toSubmodule ?_
      intro i _hi
      by_cases hactive : piCStarMatrixIdealActive S i
      · exact piCStarMatrix_single_mem_of_active_twoSidedStarIdeal S hS hactive (M i)
      · have hMi : M i = 0 := hM i hactive
        simp [hMi]
    have hdecomp : M = ∑ i : ι, Pi.single i (M i) := by
      ext i
      simp
    simpa [NonUnitalSubalgebra.mem_toSubmodule, ← hdecomp] using hsum

/-- Restrict a finite-product two-sided star ideal to its active coordinates. -/
private noncomputable def piCStarMatrix_twoSidedStarIdeal_coordinateRestriction
    {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    S →⋆ₙₐ[ℂ]
      (∀ j : {i : ι // piCStarMatrixIdealActive S i},
        CStarMatrix (Fin (n j.1)) (Fin (n j.1)) ℂ) where
  toFun x j := x.1 j.1
  map_zero' := by
    ext j
    rfl
  map_add' := by
    intro x y
    ext j
    rfl
  map_mul' := by
    intro x y
    ext j
    rfl
  map_smul' := by
    intro c x
    ext j
    rfl
  map_star' := by
    intro x
    ext j
    rfl

/-- The active-coordinate restriction is bijective. -/
private theorem piCStarMatrix_twoSidedStarIdeal_coordinateRestriction_bijective
    {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hS : IsTwoSidedStarIdeal S) :
    Function.Bijective (piCStarMatrix_twoSidedStarIdeal_coordinateRestriction S) := by
  classical
  constructor
  · intro x y hxy
    apply Subtype.ext
    ext i r s
    by_cases hi : piCStarMatrixIdealActive S i
    · exact congrFun₂ (congrFun hxy ⟨i, hi⟩) r s
    · have hx0 : x.1 i = 0 :=
        (piCStarMatrix_mem_iff_inactive_coord_zero_of_twoSidedStarIdeal
          S hS x.1).mp x.2 i hi
      have hy0 : y.1 i = 0 :=
        (piCStarMatrix_mem_iff_inactive_coord_zero_of_twoSidedStarIdeal
          S hS y.1).mp y.2 i hi
      rw [hx0, hy0]
  · intro y
    let X : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ :=
      ∑ j : {i : ι // piCStarMatrixIdealActive S i}, Pi.single j.1 (y j)
    have hX : X ∈ S := by
      refine Submodule.sum_mem S.toSubmodule ?_
      intro j _hj
      exact piCStarMatrix_single_mem_of_active_twoSidedStarIdeal S hS j.2 (y j)
    refine ⟨⟨X, hX⟩, ?_⟩
    ext j r s
    change X j.1 r s = y j r s
    have hsum_apply :
        (∑ c : {i : ι // piCStarMatrixIdealActive S i},
          ((Pi.single c.1 (y c) :
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) j.1)) = y j := by
      rw [Fintype.sum_eq_single j]
      · simp
      · intro c hne
        have hcne : c.1 ≠ j.1 := by
          intro hval
          exact hne (Subtype.ext hval)
        exact
          (Pi.single_eq_of_ne
            (M := fun i : ι => CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
            (Ne.symm hcne) (y c))
    simpa [X] using congrFun₂ hsum_apply r s

/--
A two-sided star ideal in a finite product of concrete `CStarMatrix` blocks is
star-algebra equivalent to the product over its active coordinates.
-/
theorem piCStarMatrix_twoSidedStarIdeal_coordinateProduct
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    (hn : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))))
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ))
    (hS : IsTwoSidedStarIdeal S) :
    ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
      (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
      Nonempty (S ≃⋆ₐ[ℂ]
        ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ) := by
  classical
  let κ : Type u := {i : ι // piCStarMatrixIdealActive S i}
  let m : κ → ℕ := fun k => n k.1
  refine ⟨κ, inferInstance, m, ?_, ?_⟩
  · intro k
    exact hn k.1
  · exact ⟨StarAlgEquiv.ofBijective
      (piCStarMatrix_twoSidedStarIdeal_coordinateRestriction S)
      (piCStarMatrix_twoSidedStarIdeal_coordinateRestriction_bijective S hS)⟩

/--
Every non-unital star subalgebra of a finite product of finite `CStarMatrix`
blocks is a closed finite-dimensional complex subspace.

This is only the first structural input for classifying such subalgebras: it does
not by itself identify the subalgebra with another finite product of matrix
C*-algebras.  That identification follows from
`nonUnitalStarSubalgebraProvider_of_nonUnitalCStarStarAlgEquiv` below together with
the classification theorem `exists_starAlgEquiv_pi_cstarMatrix` in `Classification.lean`.
-/
theorem finiteCStarMatrixProduct_nonUnitalStarSubalgebra_closed_and_finiteDimensional
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    [∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))]
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    IsClosed (S : Set (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) ∧
      FiniteDimensional ℂ S := by
  haveI : FiniteDimensional ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
    change FiniteDimensional ℂ
      (∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    infer_instance
  have hSsub_finite : FiniteDimensional ℂ S.toSubmodule := by
    infer_instance
  have hclosed :
      IsClosed (S : Set (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) := by
    haveI : FiniteDimensional ℂ S.toSubmodule := hSsub_finite
    simpa [NonUnitalSubalgebra.coe_toSubmodule]
      using (Submodule.closed_of_finiteDimensional (s := S.toSubmodule))
  have hfinite : FiniteDimensional ℂ S := by
    haveI : FiniteDimensional ℂ S.toNonUnitalSubalgebra.toSubmodule := by
      infer_instance
    exact LinearEquiv.finiteDimensional S.toNonUnitalSubalgebra.toSubmoduleEquiv
  exact ⟨hclosed, hfinite⟩

/--
Every non-unital star subalgebra of a finite product of finite `CStarMatrix`
blocks inherits the structure of a finite-dimensional non-unital C*-algebra.

This still does not classify the subalgebra by a finite product of matrix
blocks; it only supplies the C*-algebra structure needed to state and apply a
classification theorem to the subalgebra itself.
-/
@[reducible]
noncomputable def finiteCStarMatrixProduct_nonUnitalStarSubalgebra_nonUnitalCStarAlgebra
    {ι : Type u} [Fintype ι] {n : ι → ℕ}
    [∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))]
    (S : NonUnitalStarSubalgebra ℂ
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    NonUnitalCStarAlgebra S := by
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  haveI : (i : ι) →
      NonUnitalCStarAlgebra (CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
    intro i
    exact CStarMatrix.instNonUnitalCStarAlgebra
  haveI :
      NonUnitalCStarAlgebra
        (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
    infer_instance
  letI : StarMul
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    StarRing.toStarMul
  letI : StarAddMonoid
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    StarRing.toStarAddMonoid
  have hclosed :
      IsClosed (S : Set (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :=
    (finiteCStarMatrixProduct_nonUnitalStarSubalgebra_closed_and_finiteDimensional
      S).1
  exact
  { toCompleteSpace := hclosed.completeSpace_coe
    star_mul := by
      intro x y
      apply Subtype.ext
      change star
          ((x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) * y) =
        star (y : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) *
          star (x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      exact star_mul (x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) y
    star_add := by
      intro x y
      apply Subtype.ext
      change star
          ((x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) + y) =
        star (x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) +
          star (y : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      exact StarRing.star_add
        (x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) y
    norm_mul_self_le := by
      intro x
      exact CStarRing.norm_star_mul_self
        (x := (x : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) |>.symm.le }

/--
If every finite-dimensional non-unital C*-algebra admits a finite
`CStarMatrix` star-block decomposition, then the same classification applies
to every non-unital star subalgebra of a finite `CStarMatrix` product.

The preceding closedness and inherited C*-algebra structure lemmas are exactly
the inputs needed to view such a subalgebra as an instance of the universal
finite-dimensional classification statement.
-/
theorem nonUnitalStarSubalgebraProvider_of_nonUnitalCStarStarAlgEquiv
    (hdecomp :
      ∀ {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A],
        ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (n : ι → ℕ),
          (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) ∧
          Nonempty (A ≃⋆ₐ[ℂ]
            ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)) :
    ∀ {ι : Type u} [Fintype ι] {n : ι → ℕ},
      (∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i)))) →
      ∀ (S : NonUnitalStarSubalgebra ℂ
        (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)),
        ∃ (κ : Type u), ∃ (_ : Fintype κ), ∃ (m : κ → ℕ),
          (∀ k : κ, Nontrivial (EuclideanSpace ℂ (Fin (m k)))) ∧
          Nonempty (S ≃⋆ₐ[ℂ]
            ∀ k : κ, CStarMatrix (Fin (m k)) (Fin (m k)) ℂ) := by
  intro ι _ n hn S
  haveI : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))) := hn
  letI : NonUnitalCStarAlgebra S :=
    finiteCStarMatrixProduct_nonUnitalStarSubalgebra_nonUnitalCStarAlgebra S
  haveI : FiniteDimensional ℂ S :=
    (finiteCStarMatrixProduct_nonUnitalStarSubalgebra_closed_and_finiteDimensional
      S).2
  exact hdecomp (A := S)

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
