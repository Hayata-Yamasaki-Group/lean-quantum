/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.Analysis.CStar.FiniteDimensionalStructure.TraceRepair

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 corner normalization

Carlen 2022 Theorem 1.45 (AH1): normalization of star-invariant corners to
standard CStarMatrix blocks and the provider variants used by product assembly.
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

/-! ### Corner normalization to standard CStarMatrix blocks -/
/--
The corner--matrix algebra equivalence sends the restricted corner star to the
transported matrix-block involution.  This plain form avoids competing with
the standard `Matrix` star instance while retaining the exact normalization
target needed downstream.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv_map_star_transported
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (x : ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv n e i) (star x) =
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
        ((algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv n e i) x) := by
  classical
  letI : Algebra ℂ
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    algebraCornerOfIsIdempotentElem
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  letI : StarRing
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    instStarRingCornerOfIsStarProjection
      (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
  let φ := algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv n e i
  change φ (star x) = φ (star (φ.symm (φ x)))
  simp

/--
A matrix-block algebra automorphism that intertwines the transported
involution with the standard matrix adjoint normalizes the corresponding
corner to the standard `CStarMatrix` block.
-/
noncomputable def
    cornerCStarMatrixStarAlgEquiv_of_transportNormalizer
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (β : Matrix (Fin (n i)) (Fin (n i)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (hβ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      β (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M) =
        star (β M)) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  letI : Algebra ℂ
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    algebraCornerOfIsIdempotentElem
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  letI : StarRing
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    instStarRingCornerOfIsStarProjection
      (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
  let φ := algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv n e i
  let γ :
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
        ≃ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ :=
    (φ.trans β).trans
      (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin (n i))).toAlgEquiv
  refine StarAlgEquiv.ofAlgEquiv γ ?_
  intro x
  have hφ :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv_map_star_transported
      n e i x
  have hmat : β (φ (star x)) = star (β (φ x)) := by
    calc
      β (φ (star x)) =
          β (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar
            n e i (φ x)) := by
            rw [hφ]
      _ = star (β (φ x)) := hβ (φ x)
  change (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin (n i))).toAlgEquiv
      (β (φ (star x))) =
    star ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin (n i))).toAlgEquiv
      (β (φ x)))
  simpa using congrArg
    ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin (n i))).toAlgEquiv) hmat

/--
Positive-normalized matrix implementation of the transported corner involution
is enough to normalize that corner to the standard `CStarMatrix` block.  For the
coordinate corners of a C*-algebra, an implementer with this positive-definiteness
property is produced in the unconditional normalization
`cornerCStarMatrixStarAlgEquiv` below.
-/
noncomputable def
    cornerCStarMatrixStarAlgEquiv_of_transportConjPosDef
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hPpos : (star P).PosDef) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  let hβex := matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_posDef
      (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
      P hτ hPpos
  let β := Classical.choose hβex
  have hβ := Classical.choose_spec hβex
  exact
    cornerCStarMatrixStarAlgEquiv_of_transportNormalizer
      n e i β hβ

/--
Existence form of the positive-normalized transported-star implementation for a
corner.  This is the theorem-facing hook for the C*-normalization:
once the transported corner involution has some implementation whose adjoint is
positive definite, the corner is normalized to the standard `CStarMatrix` block.
The unconditional normalization is `cornerCStarMatrixStarAlgEquiv` below.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_exists_transportConjPosDef
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (hP : ∃ P : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∃ _hP : Invertible P,
      (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
        algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
          star (P * M * ⅟P)) ∧ (star P).PosDef) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  let P := Classical.choose hP
  let hPtail := Classical.choose_spec hP
  let hPinv := Classical.choose hPtail
  let hPrest := Classical.choose_spec hPtail
  letI : Invertible P := hPinv
  exact cornerCStarMatrixStarAlgEquiv_of_transportConjPosDef
    n e i P hPrest.1 hPrest.2


/--
Self-adjoint, sign-semidefinite implementation of the transported corner star
is already enough to normalize that corner to the standard `CStarMatrix` block.
The C*-positive-cone argument producing the sign-semidefinite alternative is
carried out, for the coordinate corners of a C*-algebra, in the unconditional
normalization `cornerCStarMatrixStarAlgEquiv` below.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportSelfAdjointSignSemidef
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hself : IsSelfAdjoint P)
    (hsemidef : P.PosSemidef ∨ (-P).PosSemidef) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  have hPpos :
      ∃ Pnew : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∃ _hPnew : Invertible Pnew,
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Pnew * M * ⅟Pnew)) ∧ (star Pnew).PosDef :=
    matrixBlockTransportedStar_exists_posDef_implementer_of_selfAdjoint_signSemidef
      (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
      P hτ hself hsemidef
  exact cornerCStarMatrixStarAlgEquiv_of_exists_transportConjPosDef
    n e i hPpos


/--
For a nonzero transported coordinate block, an arbitrary inner implementer plus
a sign-semidefinite provider is enough to normalize the coordinate corner to the
standard `CStarMatrix` block.  The unconditional normalization
`cornerCStarMatrixStarAlgEquiv` below supplies this provider through spectrum
nonnegativity of transported squares.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveSignSemidef
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hsemidef :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        Q.PosSemidef ∨ (-Q).PosSemidef) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  have hPpos :
      ∃ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∃ _hQ : Invertible Q,
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) ∧ (star Q).PosDef :=
    matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
      (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
      P hτ
      (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_involutive n e i)
      hsemidef
  exact cornerCStarMatrixStarAlgEquiv_of_exists_transportConjPosDef
    n e i hPpos

/--
Two-vector rank-one trace nonnegativity for every self-adjoint implementer is
enough to normalize the transported coordinate corner to the standard
`CStarMatrix` block.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveRankOneCrossTrace
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (htrace :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∀ u v : Fin (n i) → ℂ,
          0 ≤ Matrix.trace
            (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
              (Matrix.vecMulVec u (star v)) *
              Matrix.vecMulVec u (star v))) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveSignSemidef
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      exact matrixBlock_selfAdjoint_signSemidef_of_rankOne_cross_trace_nonneg
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
        Q hQself hτQ (htrace Q hQself hτQ))

/--
All-direction trace nonnegativity for every self-adjoint implementer is enough
to normalize the transported coordinate corner to the standard `CStarMatrix`
block.  This is the corner-level hook for a C*-positive-cone argument that
directly supplies `trace (τ R * R) ≥ 0` for all matrix directions.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveTraceSquare
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (htrace :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∀ R : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          0 ≤ Matrix.trace
            (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R * R)) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveSignSemidef
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      exact matrixBlock_selfAdjoint_signSemidef_of_trace_square_nonneg
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
        Q hQself hτQ (htrace Q hQself hτQ))

/--
For a coordinate corner transported from an ambient C*-algebra, every transported
square has nonnegative ordinary complex spectrum.  Indeed, after pulling the
matrix element back to the corner, the transported product is the coordinate of
the ambient positive element `star x * x`.
-/
theorem
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_square_spectrum_nonneg
    {B : Type u} [CStarAlgebra B]
    {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    ∀ R : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∀ z : ℂ,
      z ∈ spectrum ℂ
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R * R) →
      0 ≤ z := by
  classical
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  intro R z hz
  letI : Algebra ℂ
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    algebraCornerOfIsIdempotentElem
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  letI : StarRing
    (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    instStarRingCornerOfIsStarProjection
      (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
  let φ := algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv n e i
  let x := φ.symm R
  have hprod :
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R * R =
        e (star x.1 * x.1) i := by
    change φ (star (φ.symm R)) * R = e (star x.1 * x.1) i
    have hR : R = φ x := by
      simp [x, φ]
    rw [hR]
    have hxround : φ.symm (φ x) = x := by
      simp [φ]
    rw [hxround]
    change φ (star x) * φ x = e (star x.1 * x.1) i
    rw [← map_mul]
    rfl
  have hzcoord :
      z ∈ spectrum ℂ (e (star x.1 * x.1) i) := by
    simpa [hprod] using hz
  have hzprod :
      z ∈ spectrum ℂ (e (star x.1 * x.1)) := by
    rw [Pi.spectrum_eq]
    exact Set.mem_iUnion.mpr ⟨i, hzcoord⟩
  have hzB : z ∈ spectrum ℂ (star x.1 * x.1) := by
    simpa using (AlgEquiv.spectrum_eq e (star x.1 * x.1)).symm ▸ hzprod
  exact spectrum_nonneg_of_nonneg (star_mul_self_nonneg x.1) hzB

/--
Spectrum nonnegativity of every transported square is enough to normalize the
transported coordinate corner to the standard `CStarMatrix` block.  This is the
corner-level hook for the C*-positive-cone route that first proves nonnegative
ordinary matrix spectrum and then extracts trace nonnegativity.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveTraceSpectrum
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hspec :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∀ R : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∀ z : ℂ,
          z ∈ spectrum ℂ
            (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R *
              R) →
            0 ≤ z) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveTraceSquare
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ R
      exact matrixBlock_trace_nonneg_of_spectrum_nonneg
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R * R)
        (hspec Q hQself hτQ R))

/-! ### Unconditional corner normalization and provider variants -/
/--
Unconditional normalization of one coordinate corner.  The algebraic inner
implementer comes from the Skolem-Noether step, and the required spectrum
nonnegativity of transported squares comes from the ambient C*-positive element
`x^* x`.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))] :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  let hPex :=
    cornerMatrixTransportedStar_exists_inner_implementer
      n e i
  let P := Classical.choose hPex
  let hPtail := Classical.choose_spec hPex
  let hP := Classical.choose hPtail
  let hτ := Classical.choose_spec hPtail
  letI : Invertible P := hP
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveTraceSpectrum
    n e i P hτ
    (by
      intro Q _hQinv _hQself _hτQ R z hz
      exact
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_square_spectrum_nonneg
        n e i R z hz)

/--
Quadratic-form sign control for the self-adjoint implementers is enough to
normalize the transported coordinate corner to the standard `CStarMatrix`
block.  Thus the C*-positive-cone input can be stated at the level of quadratic
forms; the unconditional normalization `cornerCStarMatrixStarAlgEquiv` above
supplies it through spectrum nonnegativity of transported squares instead.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveQuadraticSign
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hquad :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        (∀ v : Fin (n i) → ℂ, 0 ≤ star v ⬝ᵥ (Q *ᵥ v)) ∨
          (∀ v : Fin (n i) → ℂ, star v ⬝ᵥ (Q *ᵥ v) ≤ 0)) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveSignSemidef
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      exact matrixBlock_selfAdjoint_signSemidef_of_quadratic_sign
        Q hQself (hquad Q hQself hτQ))

/--
Scalar-product control from the transported positive cone is enough to
normalize the transported coordinate corner to the standard `CStarMatrix`
block.  This is the rank-one-positive-cone theorem-facing hook.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveScalarProduct
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hprod :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : Fin (n i) → ℂ, 0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveQuadraticSign
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      rcases hprod Q hQself hτQ with ⟨c, hc, hprodQ⟩
      exact matrixBlock_quadratic_sign_of_scalar_product_nonneg Q hc hprodQ)

/--
Normalized rank-one quadratic control from the transported positive cone is
enough to normalize the transported coordinate corner.  This is the theorem-
facing hook for the projective rank-one route, whose C*-specific input is the
normalized inequality with denominator `v^*v`.  The unconditional normalization
`cornerCStarMatrixStarAlgEquiv` above uses spectrum nonnegativity of transported
squares instead.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveNormalizedQuadratic
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hnorm :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : Fin (n i) → ℂ, v ≠ 0 →
            0 ≤ ((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveScalarProduct
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      rcases hnorm Q hQself hτQ with ⟨c, hc, hnormQ⟩
      exact matrixBlock_scalarProductProvider_of_normalized_quadratic Q hc hnormQ)

/--
Rank-one positive-functional control from the transported positive cone is
enough to normalize the transported coordinate corner.  On this route the proof
obligation is the construction of the functional and its rank-one evaluation
formula; the unconditional normalization `cornerCStarMatrixStarAlgEquiv` above
uses spectrum nonnegativity of transported squares instead.
-/
noncomputable def cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveRankOneFunctional
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) [Nonempty (Fin (n i))]
    (P : Matrix (Fin (n i)) (Fin (n i)) ℂ) [Invertible P]
    (hτ : ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
        star (P * M * ⅟P))
    (hrank :
      ∀ Q : Matrix (Fin (n i)) (Fin (n i)) ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
          algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
            star (Q * M * ⅟Q)) →
        ∃ c : ℂ, ∃ Λ : Matrix (Fin (n i)) (Fin (n i)) ℂ → ℂ,
          (0 < c ∨ c < 0) ∧
            (∀ R : Matrix (Fin (n i)) (Fin (n i)) ℂ,
              0 ≤ Λ
                (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i R *
                  R)) ∧
              ∀ v : Fin (n i) → ℂ,
                Λ
                  (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
                    (Matrix.vecMulVec v (star v)) *
                    Matrix.vecMulVec v (star v)) =
                  (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    letI : StarRing
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      instStarRingCornerOfIsStarProjection
        (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner
      ≃⋆ₐ[ℂ] CStarMatrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  exact cornerCStarMatrixStarAlgEquiv_of_transportInvolutiveScalarProduct
    n e i P hτ
    (by
      intro Q _hQinv hQself hτQ
      rcases hrank Q hQself hτQ with ⟨c, Λ, hc, hpos, heval⟩
      exact matrixBlock_scalarProductProvider_of_rankOne_positiveFunctional
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
        Q c hc Λ hpos heval)

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
