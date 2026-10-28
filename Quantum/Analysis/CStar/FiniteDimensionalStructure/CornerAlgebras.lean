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
import Quantum.Analysis.CStar.FiniteDimensionalStructure.BlockDecomposition

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 corner algebras

Carlen 2022 Theorem 1.45 (AH1): finite-dimensional C*-algebra
classification infrastructure stage for star-projection corners,
transported matrix-corner involutions, and inner block-star data.
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

/-! ### Star-projection corner algebras and product decomposition -/
/--
The corner cut out by a star projection is stable under the ambient star.
-/
theorem star_mem_corner_of_isStarProjection
    {B : Type u} [CStarAlgebra B] {p x : B}
    (hp : IsStarProjection p) (hx : x ∈ Subsemigroup.corner p) :
    star x ∈ Subsemigroup.corner p := by
  rw [Subsemigroup.mem_corner_iff hp.isIdempotentElem] at hx ⊢
  rcases hx with ⟨hleft, hright⟩
  constructor
  · calc
      p * star x = star p * star x := by rw [hp.isSelfAdjoint]
      _ = star (x * p) := (star_mul x p).symm
      _ = star x := by rw [hright]
  · calc
      star x * p = star x * star p := by rw [hp.isSelfAdjoint]
      _ = star (p * x) := (star_mul p x).symm
      _ = star x := by rw [hleft]

/--
The star operation on the ambient C*-algebra restricts to the corner cut out by
a star projection.
-/
noncomputable instance instStarRingCornerOfIsStarProjection
    {B : Type u} [CStarAlgebra B] {p : B} (hp : IsStarProjection p) :
    StarRing hp.isIdempotentElem.Corner where
  star x := ⟨star x.1, star_mem_corner_of_isStarProjection hp x.2⟩
  star_involutive x := by
    apply Subtype.ext
    change star (star x.1) = x.1
    exact star_star x.1
  star_mul x y := by
    apply Subtype.ext
    change star (x.1 * y.1) = star y.1 * star x.1
    exact StarMul.star_mul x.1 y.1
  star_add x y := by
    apply Subtype.ext
    change star (x.1 + y.1) = star x.1 + star y.1
    exact StarRing.star_add x.1 y.1

/--
The same star-projection corner, viewed as a non-unital star subalgebra of the
ambient C*-algebra.  The unit of the corner is the projection `p`, not the
ambient unit, so this is intentionally non-unital as a subalgebra of `B`.
-/
noncomputable def starProjectionCorner_nonUnitalStarSubalgebra
    {B : Type u} [CStarAlgebra B] {p : B} (hp : IsStarProjection p) :
    NonUnitalStarSubalgebra ℂ B where
  carrier := Subsemigroup.corner p
  zero_mem' := by
    exact ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp [mul_add, add_mul]⟩
  mul_mem' := by
    intro x y hx hy
    exact (Subsemigroup.corner p).mul_mem hx hy
  smul_mem' := by
    rintro c x ⟨a, rfl⟩
    refine ⟨c • a, ?_⟩
    calc
      p * (c • a) * p = (c • (p * a)) * p := by rw [Algebra.mul_smul_comm]
      _ = c • (p * a * p) := by rw [Algebra.smul_mul_assoc]
  star_mem' := by
    intro x hx
    exact star_mem_corner_of_isStarProjection hp hx

/-- The corner subalgebra has exactly the carrier of the idempotent corner. -/
@[simp]
theorem mem_starProjectionCorner_nonUnitalStarSubalgebra
    {B : Type u} [CStarAlgebra B] {p x : B} (hp : IsStarProjection p) :
    x ∈ starProjectionCorner_nonUnitalStarSubalgebra hp ↔
      x ∈ Subsemigroup.corner p :=
  Iff.rfl

/--
The corner cut out by an idempotent in a complex C*-algebra inherits the
ambient complex algebra structure.  This named definition is used to keep
dependent product instance synthesis stable.
-/
@[reducible]
noncomputable def algebraCornerOfIsIdempotentElem
    {B : Type u} [CStarAlgebra B] {p : B} (hp : IsIdempotentElem p) :
    Algebra ℂ hp.Corner where
  smul c x :=
    ⟨c • x.1, by
      have hx := x.2
      rw [Subsemigroup.mem_corner_iff hp] at hx ⊢
      constructor
      · calc
          p * (c • x.1) = c • (p * x.1) := by
            rw [Algebra.mul_smul_comm]
          _ = c • x.1 := by
            rw [hx.1]
      · calc
          (c • x.1) * p = c • (x.1 * p) := by
            rw [Algebra.smul_mul_assoc]
          _ = c • x.1 := by
            rw [hx.2]⟩
  algebraMap :=
    { toFun := fun c =>
        ⟨c • p, by
          rw [Subsemigroup.mem_corner_iff hp]
          constructor
          · calc
              p * (c • p) = c • (p * p) := by
                rw [Algebra.mul_smul_comm]
              _ = c • p := by
                rw [hp.eq]
          · calc
              (c • p) * p = c • (p * p) := by
                rw [Algebra.smul_mul_assoc]
              _ = c • p := by
                rw [hp.eq]⟩
      map_one' := by
        apply Subtype.ext
        change (1 : ℂ) • p = p
        simp
      map_mul' := by
        intro c d
        apply Subtype.ext
        change (c * d) • p = (c • p) * (d • p)
        calc
          (c * d) • p = c • (d • p) := by
            rw [smul_smul]
          _ = c • (p * (d • p)) := by
            rw [Algebra.mul_smul_comm, hp.eq]
          _ = (c • p) * (d • p) := by
            rw [Algebra.smul_mul_assoc]
      map_zero' := by
        apply Subtype.ext
        change (0 : ℂ) • p = 0
        simp
      map_add' := by
        intro c d
        apply Subtype.ext
        change (c + d) • p = c • p + d • p
        rw [add_smul] }
  commutes' c x := by
    apply Subtype.ext
    have hx := x.2
    rw [Subsemigroup.mem_corner_iff hp] at hx
    change (c • p) * x.1 = x.1 * (c • p)
    calc
      (c • p) * x.1 = c • (p * x.1) := by
        rw [Algebra.smul_mul_assoc]
      _ = c • x.1 := by
        rw [hx.1]
      _ = c • (x.1 * p) := by
        rw [hx.2]
      _ = x.1 * (c • p) := by
        rw [Algebra.mul_smul_comm]
  smul_def' c x := by
    apply Subtype.ext
    have hx := x.2
    rw [Subsemigroup.mem_corner_iff hp] at hx
    change c • x.1 = (c • p) * x.1
    calc
      c • x.1 = c • (p * x.1) := by
        rw [hx.1]
      _ = (c • p) * x.1 := by
        rw [Algebra.smul_mul_assoc]

/--
The standard corner product decomposition associated to the coordinate central
idempotents is compatible with the ambient star operation, componentwise.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv_apply_star_coe
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) (x : B) :
    (((algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) (star x)) i).1 =
      star ((((algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) x) i).1) := by
  let p := algEquivPiMatrixCoordinateCentralIdempotent n e i
  have hp : IsStarProjection p := algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i
  change p * star x * p = star (p * x * p)
  calc
    p * star x * p = star p * star x * star p := by
      rw [hp.isSelfAdjoint]
    _ = star p * (star x * star p) := by
      rw [mul_assoc]
    _ = star p * star (p * x) := by
      rw [← StarMul.star_mul p x]
    _ = star ((p * x) * p) := by
      rw [← StarMul.star_mul (p * x) p]

/--
Equivalently, after equipping every coordinate corner with the restricted star
operation, the standard corner product decomposition maps `star x` to the
coordinatewise star of the image of `x`.
-/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv_map_star
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (x : B) :
    letI : ∀ i : ι,
        StarRing
          (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      fun i =>
        instStarRingCornerOfIsStarProjection
          (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i)
    (algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) (star x) =
      star ((algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) x) := by
  classical
  ext i
  apply Subtype.ext
  exact algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv_apply_star_coe n e i x

/--
The standard corner product decomposition is an algebra equivalence over `ℂ`.
The scalar `c` acts on the `i`-th corner through the corner unit `p_i`, namely
as `c • p_i`.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_cornerAlgEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
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
    B ≃ₐ[ℂ] ∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner :=
  by
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
    exact
      AlgEquiv.ofRingEquiv
        (f := algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e)
        (by
          intro c
          ext i
          apply Subtype.ext
          let p := algEquivPiMatrixCoordinateCentralIdempotent n e i
          have hp : p * p = p :=
            (algEquivPiMatrixCoordinateCentralIdempotent_isIdempotent n e i).eq
          change p * algebraMap ℂ B c * p = c • p
          calc
            p * algebraMap ℂ B c * p = p * (c • (1 : B)) * p := by
              rw [Algebra.algebraMap_eq_smul_one]
            _ = c • p := by
              simp [hp])

/--
With the restricted star on each coordinate corner, the standard corner product
decomposition is a star algebra equivalence.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_cornerStarAlgEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
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
    B ≃⋆ₐ[ℂ] ∀ i : ι,
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner :=
  by
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
      StarAlgEquiv.ofAlgEquiv
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerAlgEquiv n e)
        (by
          intro x
          change (algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) (star x) =
            star ((algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv n e) x)
          exact algEquivPiMatrixCoordinateCentralIdempotent_cornerRingEquiv_map_star n e x)

/--
Each coordinate corner is algebraically the corresponding matrix block from
the original Wedderburn-Artin product decomposition.  This is intentionally
not a star statement.  The restricted involution on this algebraic matrix block
is normalized to the standard adjoint by `cornerCStarMatrixStarAlgEquiv` in
`CornerNormalization.lean`.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixAlgEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    letI : Algebra ℂ
        (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
      algebraCornerOfIsIdempotentElem
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
    ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner ≃ₐ[ℂ]
      Matrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  let p := algEquivPiMatrixCoordinateCentralIdempotent n e i
  have hp : IsIdempotentElem p :=
    algEquivPiMatrixCoordinateCentralIdempotent_isIdempotent n e i
  letI : Algebra ℂ
      (((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) :=
    algebraCornerOfIsIdempotentElem
      ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i)
  refine
    { toFun := fun x => e x.1 i
      invFun := fun M =>
        ⟨e.symm (Pi.single i M), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · change e.symm (Pi.single i M) ∈ Subsemigroup.corner p
    rw [Subsemigroup.mem_corner_iff hp]
    constructor
    · apply e.injective
      ext j a b
      by_cases hji : j = i
      · subst j
        simp [p, algEquivPiMatrixCoordinateCentralIdempotent]
      · simp [p, algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hji]
    · apply e.injective
      ext j a b
      by_cases hji : j = i
      · subst j
        simp [p, algEquivPiMatrixCoordinateCentralIdempotent]
      · simp [p, algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hji]
  · intro x
    apply Subtype.ext
    apply e.injective
    ext j a b
    by_cases hji : j = i
    · subst j
      simp
    · have hxleft : p * x.1 = x.1 := by
        have hxmem : x.1 ∈ Subsemigroup.corner p := by
          exact x.2
        exact ((Subsemigroup.mem_corner_iff hp).mp hxmem).1
      have hcoord : e x.1 j = 0 := by
        have h := congrFun (congrArg (fun y => e y) hxleft) j
        simpa [p, algEquivPiMatrixCoordinateCentralIdempotent, Pi.single_eq_of_ne hji] using h.symm
      simp [Pi.single_eq_of_ne hji, hcoord]
  · intro M
    simp
  · intro x y
    ext a b
    change e (x.1 * y.1) i a b = (e x.1 i * e y.1 i) a b
    simp
  · intro x y
    ext a b
    change e (x.1 + y.1) i a b = e x.1 i a b + e y.1 i a b
    simp
  · intro c
    ext a b
    change e (c • p) i a b =
      (algebraMap ℂ (Matrix (Fin (n i)) (Fin (n i)) ℂ) c) a b
    simp [p, algEquivPiMatrixCoordinateCentralIdempotent, Algebra.algebraMap_eq_smul_one]

/-! ### Transported star on matrix corners -/
/--
Transport the restricted corner involution across the algebraic identification
with the corresponding matrix block.  This is not the standard matrix adjoint
in general; the comparison of this transported involution with the standard
`CStarMatrix` involution is carried out by `cornerCStarMatrixStarAlgEquiv` in
`CornerNormalization.lean`.
-/
noncomputable def algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) (M : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    Matrix (Fin (n i)) (Fin (n i)) ℂ := by
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
  exact φ (star (φ.symm M))

/-- The transported matrix-block involution fixes zero. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_zero
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
        (0 : Matrix (Fin (n i)) (Fin (n i)) ℂ) =
      0 := by
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
  change φ (star (φ.symm 0)) = 0
  calc
    φ (star (φ.symm 0)) = φ (star 0) := by rw [map_zero]
    _ = φ 0 := by rw [star_zero]
    _ = 0 := by rw [map_zero]

/-- The transported matrix-block involution fixes the unit. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_one
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
        (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) =
      1 := by
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
  have hone :
      star (1 :
        ((algEquivPiMatrixCoordinateCentralIdempotent_completeOrthogonal n e).idem i).Corner) =
        1 := by
    apply Subtype.ext
    change star (algEquivPiMatrixCoordinateCentralIdempotent n e i) =
      algEquivPiMatrixCoordinateCentralIdempotent n e i
    exact (algEquivPiMatrixCoordinateCentralIdempotent_isStarProjection n e i).isSelfAdjoint
  change φ (star (φ.symm 1)) = 1
  calc
    φ (star (φ.symm 1)) = φ (star 1) := by rw [map_one]
    _ = φ 1 := by rw [hone]
    _ = 1 := by rw [map_one]

/-- The transported matrix-block involution is involutive. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_involutive
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) (M : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M) =
      M := by
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
  change φ (star (φ.symm (φ (star (φ.symm M))))) = M
  calc
    φ (star (φ.symm (φ (star (φ.symm M))))) =
        φ (star (star (φ.symm M))) := by simp
    _ = φ (φ.symm M) := by rw [star_star]
    _ = M := by simp

/-- The transported matrix-block involution reverses multiplication. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_mul
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (M N : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i (M * N) =
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i N *
        algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M := by
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
  change φ (star (φ.symm (M * N))) =
    φ (star (φ.symm N)) * φ (star (φ.symm M))
  calc
    φ (star (φ.symm (M * N))) =
        φ (star (φ.symm M * φ.symm N)) := by rw [map_mul]
    _ = φ (star (φ.symm N) * star (φ.symm M)) := by
        exact congrArg φ (StarMul.star_mul (φ.symm M) (φ.symm N))
    _ = φ (star (φ.symm N)) * φ (star (φ.symm M)) := by rw [map_mul]

/-- The transported matrix-block involution is additive. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_add
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (M N : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i (M + N) =
      algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M +
        algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i N := by
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
  change φ (star (φ.symm (M + N))) =
    φ (star (φ.symm M)) + φ (star (φ.symm N))
  calc
    φ (star (φ.symm (M + N))) =
        φ (star (φ.symm M + φ.symm N)) := by rw [map_add]
    _ = φ (star (φ.symm M) + star (φ.symm N)) := by
        exact congrArg φ (StarRing.star_add (φ.symm M) (φ.symm N))
    _ = φ (star (φ.symm M)) + φ (star (φ.symm N)) := by rw [map_add]

/-- The transported matrix-block involution is conjugate-linear over `ℂ`. -/
theorem algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_smul
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι)
    (c : ℂ) (M : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i (c • M) =
      star c •
        algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M := by
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
  change φ (star (φ.symm (c • M))) = star c • φ (star (φ.symm M))
  have hcorner : star (c • φ.symm M) = star c • star (φ.symm M) := by
    apply Subtype.ext
    change star (c • (φ.symm M).1) = star c • star (φ.symm M).1
    exact star_smul c (φ.symm M).1
  calc
    φ (star (φ.symm (c • M))) =
        φ (star (c • φ.symm M)) := by rw [map_smul]
    _ = φ (star c • star (φ.symm M)) := by rw [hcorner]
    _ = star c • φ (star (φ.symm M)) := by rw [map_smul]

/--
Composing the transported matrix-block involution with the standard matrix
adjoint gives a complex algebra automorphism of the same matrix block.  Thus
normalizing the transported involution to the standard adjoint can be treated
as a normalization problem for this ordinary algebra automorphism.
-/
noncomputable def
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    Matrix (Fin (n i)) (Fin (n i)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (n i)) (Fin (n i)) ℂ := by
  classical
  let τ :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i
  have hτ_involutive :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_involutive n e i
  have hτ_mul :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_mul n e i
  have hτ_add :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_add n e i
  have hτ_smul :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_smul n e i
  have hτ_one :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar_one n e i
  refine
    { toFun := fun M => star (τ M)
      invFun := fun M => τ (star M)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · intro M
    change τ (star (star (τ M))) = M
    calc
      τ (star (star (τ M))) = τ (τ M) := by rw [star_star]
      _ = M := by simpa [τ] using hτ_involutive M
  · intro M
    change star (τ (τ (star M))) = M
    calc
      star (τ (τ (star M))) = star (star M) := by
        have h := hτ_involutive (star M)
        simpa [τ] using congrArg star h
      _ = M := by rw [star_star]
  · intro M N
    change star (τ (M * N)) = star (τ M) * star (τ N)
    calc
      star (τ (M * N)) = star (τ N * τ M) := by
        have h := hτ_mul M N
        simpa [τ] using congrArg star h
      _ = star (τ M) * star (τ N) := by
        exact StarMul.star_mul (τ N) (τ M)
  · intro M N
    change star (τ (M + N)) = star (τ M) + star (τ N)
    calc
      star (τ (M + N)) = star (τ M + τ N) := by
        have h := hτ_add M N
        simpa [τ] using congrArg star h
      _ = star (τ M) + star (τ N) := by rw [star_add]
  · intro c
    rw [Algebra.algebraMap_eq_smul_one]
    calc
      star (τ (c • 1)) = star (star c • τ 1) := by
        have h := hτ_smul c (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ)
        simpa [τ] using congrArg star h
      _ = c • star (τ 1) := by rw [star_smul, star_star]
      _ = c • 1 := by
        have h : τ (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) = 1 := by
          simpa [τ] using hτ_one
        simp [h]

/--
After identifying the matrix block with the endomorphism algebra of the
standard finite-dimensional complex vector space, the algebra automorphism
`M ↦ (M^{\sharp_i})^*` is inner.  This is the purely algebraic Skolem-Noether
step before the C*-normalization that turns an implementing linear
equivalence into a star normalizer (`cornerCStarMatrixStarAlgEquiv` in
`CornerNormalization.lean`).
-/
theorem
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv_inner
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    ∃ T : (Fin (n i) → ℂ) ≃ₗ[ℂ] (Fin (n i) → ℂ),
      ((algEquivMatrix' (R := ℂ) (n := Fin (n i))).trans
        (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv
          n e i)).trans
        (algEquivMatrix' (R := ℂ) (n := Fin (n i))).symm =
          T.conjAlgEquiv ℂ := by
  exact AlgEquiv.eq_linearEquivConjAlgEquiv _

/--
Pointwise form of the previous innerness hook.  It rewrites
`(M^{\sharp_i})^*` as the matrix representative of conjugation by the
implementing linear equivalence on `End_ℂ(ℂ^{n_i})`.
-/
theorem cornerMatrixStandardStarAfterTransportAlgEquiv_inner_apply
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    ∃ T : (Fin (n i) → ℂ) ≃ₗ[ℂ] (Fin (n i) → ℂ),
      ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
        star
          (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M) =
          algEquivMatrix' (R := ℂ) (n := Fin (n i))
            ((T.conjAlgEquiv ℂ)
              ((algEquivMatrix' (R := ℂ) (n := Fin (n i))).symm M)) := by
  rcases
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv_inner
      n e i with
    ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro M
  let ε := algEquivMatrix' (R := ℂ) (n := Fin (n i))
  let α :=
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv
      n e i
  have hpoint :
      (((ε.trans α).trans ε.symm) (ε.symm M)) =
        (T.conjAlgEquiv ℂ) (ε.symm M) := by
    simpa [ε, α] using congrFun (congrArg DFunLike.coe hT) (ε.symm M)
  have hmatrix := congrArg ε hpoint
  simpa [ε, α,
    algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixStandardStarAfterTransportAlgEquiv]
    using hmatrix

/-! ### Innerness of transported matrix-block star -/
/-- Conjugation by an invertible matrix as a complex algebra automorphism. -/
noncomputable def matrixBlockConjAlgEquivOfInvertible {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) [Invertible Q] :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ where
  toFun M := Q * M * ⅟Q
  invFun M := ⅟Q * M * Q
  left_inv := by
    intro M
    calc
      ⅟Q * (Q * M * ⅟Q) * Q = (⅟Q * Q) * M * (⅟Q * Q) := by noncomm_ring
      _ = M := by simp
  right_inv := by
    intro M
    calc
      Q * (⅟Q * M * Q) * ⅟Q = (Q * ⅟Q) * M * (Q * ⅟Q) := by noncomm_ring
      _ = M := by simp
  map_mul' := by
    intro M N
    calc
      Q * (M * N) * ⅟Q = Q * M * (⅟Q * Q) * N * ⅟Q := by simp [mul_assoc]
      _ = (Q * M * ⅟Q) * (Q * N * ⅟Q) := by noncomm_ring
  map_add' := by
    intro M N
    simp [mul_add, add_mul]
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one]
    calc
      Q * (c • 1) * ⅟Q = c • (Q * 1 * ⅟Q) := by simp
      _ = c • 1 := by simp

/--
Under the standard identification between endomorphisms of `n → ℂ` and
matrices, the conjugation algebra automorphism induced by the linear
equivalence attached to an invertible matrix `P` is ordinary matrix
conjugation by `P`.
-/
theorem algEquivMatrix_conjAlgEquiv_toLinearEquiv'_eq_matrixBlockConj
    {n : Type*} [Fintype n] [DecidableEq n]
    (P M : Matrix n n ℂ) [Invertible P] :
    (algEquivMatrix' (R := ℂ) (n := n))
        (((P.toLinearEquiv' inferInstance).conjAlgEquiv ℂ)
          ((algEquivMatrix' (R := ℂ) (n := n)).symm M)) =
      matrixBlockConjAlgEquivOfInvertible P M := by
  rw [LinearEquiv.conjAlgEquiv_apply]
  change
    LinearMap.toMatrixAlgEquiv'
        ((P.toLinearEquiv' inferInstance).toLinearMap.comp
          ((Matrix.toLinAlgEquiv' M).comp
            (P.toLinearEquiv' inferInstance).symm.toLinearMap)) =
      matrixBlockConjAlgEquivOfInvertible P M
  rw [LinearMap.toMatrixAlgEquiv'_comp, LinearMap.toMatrixAlgEquiv'_comp]
  rw [Matrix.toLinearEquiv'_apply, Matrix.toLinearEquiv'_symm_apply]
  change
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' P) *
        (LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) *
          LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' (⅟P))) =
      matrixBlockConjAlgEquivOfInvertible P M
  rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv',
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv',
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
  dsimp [matrixBlockConjAlgEquivOfInvertible]
  rw [mul_assoc]

/--
Every linear equivalence of the standard finite free complex module is induced
by an invertible matrix in the standard basis.
-/
theorem matrixBlockLinearEquiv_exists_invertible_toLinearEquiv'
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) :
    ∃ P : Matrix n n ℂ, ∃ hP : Invertible P,
      P.toLinearEquiv' hP = T := by
  let P : Matrix n n ℂ :=
    LinearMap.toMatrixAlgEquiv' (T : Module.End ℂ (n → ℂ))
  have hUnitEnd : IsUnit (T : Module.End ℂ (n → ℂ)) :=
    ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv T, rfl⟩
  have hUnitP : IsUnit P := by
    simpa [P] using
      (isUnit_map_iff LinearMap.toMatrixAlgEquiv'
        (T : Module.End ℂ (n → ℂ))).mpr hUnitEnd
  let hP : Invertible P :=
    Classical.choice ((nonempty_invertible_iff_isUnit P).mpr hUnitP)
  refine ⟨P, hP, ?_⟩
  apply LinearEquiv.ext
  intro v
  have hlin :
      (P.toLinearEquiv' hP : Module.End ℂ (n → ℂ)) =
        (T : Module.End ℂ (n → ℂ)) := by
    rw [Matrix.toLinearEquiv'_apply]
    change Matrix.toLin' (LinearMap.toMatrix' (T : Module.End ℂ (n → ℂ))) =
      (T : Module.End ℂ (n → ℂ))
    exact Matrix.toLin'_toMatrix' (T : Module.End ℂ (n → ℂ))
  exact LinearMap.congr_fun hlin v

/--
Turning an innerness formula for the standard adjoint of a transported
involution into the form expected by the normalizer calculation.
-/
theorem matrixBlockTransportedStar_eq_star_conj_of_star_eq_conj
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτstar : ∀ M : Matrix n n ℂ, star (τ M) = P * M * ⅟P)
    (M : Matrix n n ℂ) :
    τ M = star (P * M * ⅟P) := by
  calc
    τ M = star (star (τ M)) := by simp
    _ = star (P * M * ⅟P) := by rw [hτstar]

/--
The transported coordinate-corner involution is inner after composing with the
standard matrix adjoint.  This packages the Skolem-Noether innerness hook and
the passage from linear-equivalence conjugation to ordinary matrix conjugation
in the exact form needed by the C*-normalization providers.
-/
theorem
    cornerMatrixTransportedStar_exists_inner_implementer
    {B : Type u} [CStarAlgebra B] {ι : Type v} [DecidableEq ι] [Fintype ι]
    (n : ι → ℕ)
    (e : B ≃ₐ[ℂ] ∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (i : ι) :
    ∃ P : Matrix (Fin (n i)) (Fin (n i)) ℂ, ∃ _hP : Invertible P,
      ∀ M : Matrix (Fin (n i)) (Fin (n i)) ℂ,
        algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i M =
          star (P * M * ⅟P) := by
  classical
  rcases
    cornerMatrixStandardStarAfterTransportAlgEquiv_inner_apply
      n e i with
    ⟨T, hT⟩
  rcases matrixBlockLinearEquiv_exists_invertible_toLinearEquiv' T with
    ⟨P, hP, hPT⟩
  refine ⟨P, hP, ?_⟩
  letI : Invertible P := hP
  intro M
  refine matrixBlockTransportedStar_eq_star_conj_of_star_eq_conj
    (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i)
    P ?_ M
  intro N
  calc
    star (algEquivPiMatrixCoordinateCentralIdempotent_cornerMatrixTransportedStar n e i N) =
        algEquivMatrix' (R := ℂ) (n := Fin (n i))
          ((T.conjAlgEquiv ℂ)
            ((algEquivMatrix' (R := ℂ) (n := Fin (n i))).symm N)) := hT N
    _ = algEquivMatrix' (R := ℂ) (n := Fin (n i))
          (((P.toLinearEquiv' hP).conjAlgEquiv ℂ)
            ((algEquivMatrix' (R := ℂ) (n := Fin (n i))).symm N)) := by
          rw [hPT]
    _ = matrixBlockConjAlgEquivOfInvertible P N := by
          exact algEquivMatrix_conjAlgEquiv_toLinearEquiv'_eq_matrixBlockConj P N
    _ = P * N * ⅟P := rfl


end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
