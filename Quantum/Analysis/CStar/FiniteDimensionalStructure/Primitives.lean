import Quantum.Analysis.Matrix.UnitIntervalOrder
import Quantum.Analysis.Real.PositiveCayley
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
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinz.Defs

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 primitives

Carlen 2022 Theorem 1.45 (AH1): positive-ray matrix primitives, abstract
convexity/twist bridges, and the closed-positive CFC realization bridge.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

/-! ### Positive-ray matrix and quadratic-form primitives -/

/-- Matrix convex combination with real coefficient, written in complex matrix algebra. -/
def positiveRayMatrixConvexCombo {n : ℕ} (θ : ℝ)
    (X Y : HansenPedersen.Mₙ n) : HansenPedersen.Mₙ n :=
  (θ : ℂ) • X + ((1 - θ : ℝ) : ℂ) • Y

/-- The `1 × 1` positive-ray matrix with real entry `x`. -/
def positiveRayScalarMatrix (x : ℝ) : HansenPedersen.Mₙ 1 :=
  diagonal fun _ : Fin 1 => (x : ℂ)

/-- Vector convex combination with real coefficient, written in complex coordinates. -/
def positiveRayVectorConvexCombo {n : ℕ} (θ : ℝ)
    (v w : Fin n → ℂ) : Fin n → ℂ :=
  (θ : ℂ) • v + ((1 - θ : ℝ) : ℂ) • w

/-- The constant vector in one complex dimension with real coordinate `x`. -/
def positiveRayScalarVector (x : ℝ) : Fin 1 → ℂ :=
  fun _ => (x : ℂ)

/-- Real quadratic form associated to a complex matrix. -/
noncomputable def positiveRayQForm {n : ℕ}
    (A : HansenPedersen.Mₙ n) (v : Fin n → ℂ) : ℝ :=
  Complex.re (dotProduct (star v) (A.mulVec v))

/-- A vector convex combination with identical endpoints is the original vector. -/
lemma positiveRayVectorConvexCombo_self {n : ℕ} (θ : ℝ) (v : Fin n → ℂ) :
    positiveRayVectorConvexCombo θ v v = v := by
  ext i
  change (θ : ℂ) * v i + ((1 - θ : ℝ) : ℂ) * v i = v i
  calc
    (θ : ℂ) * v i + ((1 - θ : ℝ) : ℂ) * v i =
        ((θ : ℂ) + ((1 - θ : ℝ) : ℂ)) * v i := by ring
    _ = v i := by simp

/-- A positive real scalar gives a positive-definite `1 x 1` scalar matrix. -/
lemma positiveRayScalarMatrix_posDef {x : ℝ} (hx : 0 < x) :
    (positiveRayScalarMatrix x).PosDef := by
  unfold positiveRayScalarMatrix
  exact Matrix.PosDef.diagonal fun _ => by
    exact_mod_cast hx

/-- A convex combination of positive-definite positive-ray matrices is positive-definite. -/
lemma positiveRayMatrixConvexCombo_posDef {n : ℕ} {θ : ℝ}
    {X Y : HansenPedersen.Mₙ n}
    (hX : X.PosDef) (hY : Y.PosDef) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (positiveRayMatrixConvexCombo θ X Y).PosDef := by
  by_cases hθzero : θ = 0
  · subst θ
    simpa [positiveRayMatrixConvexCombo] using hY
  by_cases hθone : θ = 1
  · subst θ
    simpa [positiveRayMatrixConvexCombo] using hX
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθzero)
  have h1θpos : 0 < 1 - θ := sub_pos.mpr (lt_of_le_of_ne hθ1 hθone)
  have hθX : (((θ : ℂ) • X) : HansenPedersen.Mₙ n).PosDef := by
    have hr : (((θ : ℂ) • X) : HansenPedersen.Mₙ n) = (θ • X : HansenPedersen.Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact hX.smul hθpos
  have h1Y : ((((1 - θ : ℝ) : ℂ) • Y) : HansenPedersen.Mₙ n).PosDef := by
    have hr : ((((1 - θ : ℝ) : ℂ) • Y) : HansenPedersen.Mₙ n) =
        ((1 - θ : ℝ) • Y : HansenPedersen.Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact hY.smul h1θpos
  simpa [positiveRayMatrixConvexCombo] using hθX.add h1Y

/-- A convex combination of positive-semidefinite positive-ray matrices is semidefinite. -/
lemma positiveRayMatrixConvexCombo_posSemidef {n : ℕ} {θ : ℝ}
    {X Y : HansenPedersen.Mₙ n}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (positiveRayMatrixConvexCombo θ X Y).PosSemidef := by
  have hθX : (((θ : ℂ) • X) : HansenPedersen.Mₙ n).PosSemidef := by
    have hr : (((θ : ℂ) • X) : HansenPedersen.Mₙ n) = (θ • X : HansenPedersen.Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact Matrix.PosSemidef.smul hX hθ0
  have h1Y : ((((1 - θ : ℝ) : ℂ) • Y) : HansenPedersen.Mₙ n).PosSemidef := by
    have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hr : ((((1 - θ : ℝ) : ℂ) • Y) : HansenPedersen.Mₙ n) =
        ((1 - θ : ℝ) • Y : HansenPedersen.Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact Matrix.PosSemidef.smul hY h1θ
  unfold positiveRayMatrixConvexCombo
  exact Matrix.PosSemidef.add hθX h1Y

/-- Adding a positive scalar multiple of the identity makes a semidefinite matrix definite. -/
lemma positiveRayMat_add_pos_scalar_one_posDef {n : ℕ}
    {X : HansenPedersen.Mₙ n} (hX : X.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (X + ε • (1 : HansenPedersen.Mₙ n)).PosDef := by
  have hone : (ε • (1 : HansenPedersen.Mₙ n)).PosDef :=
    Matrix.PosDef.smul (Matrix.PosDef.one : (1 : HansenPedersen.Mₙ n).PosDef) hε
  exact Matrix.PosDef.posSemidef_add hX hone

/-- Adding the same scalar identity perturbation commutes with convex combination. -/
lemma positiveRayMatrixConvexCombo_add_scalar_one {n : ℕ}
    (θ ε : ℝ) (X Y : HansenPedersen.Mₙ n) :
    positiveRayMatrixConvexCombo θ (X + ε • (1 : HansenPedersen.Mₙ n))
        (Y + ε • (1 : HansenPedersen.Mₙ n)) =
      positiveRayMatrixConvexCombo θ X Y + ε • (1 : HansenPedersen.Mₙ n) := by
  ext i j
  simp only [positiveRayMatrixConvexCombo, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Complex.real_smul]
  by_cases hij : i = j
  · subst j
    simp
    ring_nf
  · simp [hij]

/-- Convex combinations of scalar matrices are scalar matrices. -/
lemma positiveRayScalarMatrix_convexCombo (θ x y : ℝ) :
    positiveRayMatrixConvexCombo θ (positiveRayScalarMatrix x) (positiveRayScalarMatrix y) =
      positiveRayScalarMatrix (θ * x + (1 - θ) * y) := by
  unfold positiveRayMatrixConvexCombo positiveRayScalarMatrix
  ext i j
  fin_cases i
  fin_cases j
  change (θ : ℂ) * (x : ℂ) + ((1 - θ : ℝ) : ℂ) * (y : ℂ) =
    ((θ * x + (1 - θ) * y : ℝ) : ℂ)
  norm_num

/-- The scalar vector from `1` to `0` evaluates to the scalar vector `theta`. -/
lemma positiveRayVectorConvexCombo_scalar_zero (θ : ℝ) :
    positiveRayVectorConvexCombo θ (positiveRayScalarVector 1) (positiveRayScalarVector 0) =
      positiveRayScalarVector θ := by
  ext i
  fin_cases i
  change (θ : ℂ) * 1 + ((1 - θ : ℝ) : ℂ) * 0 = (θ : ℂ)
  ring

/-- Scaling the one-dimensional scalar vector scales the quadratic form by `r^2`. -/
lemma positiveRayQForm_scalarVector (A : HansenPedersen.Mₙ 1) (r : ℝ) :
    positiveRayQForm A (positiveRayScalarVector r) =
      r^2 * positiveRayQForm A (positiveRayScalarVector 1) := by
  unfold positiveRayQForm positiveRayScalarVector
  simp [dotProduct, Matrix.mulVec, pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- The quadratic form of the zero scalar vector is zero. -/
lemma positiveRayQForm_scalarVector_zero (A : HansenPedersen.Mₙ 1) :
    positiveRayQForm A (positiveRayScalarVector 0) = 0 := by
  simpa using positiveRayQForm_scalarVector A 0

/-- The quadratic form of a matrix difference is the difference of quadratic forms. -/
lemma positiveRayQForm_sub {n : ℕ}
    (A B : HansenPedersen.Mₙ n) (v : Fin n → ℂ) :
    positiveRayQForm (B - A) v =
      positiveRayQForm B v - positiveRayQForm A v := by
  unfold positiveRayQForm
  simp [Matrix.sub_mulVec]

/-- Quadratic forms distribute over positive-ray matrix convex combinations. -/
lemma positiveRayQForm_convexCombo {n : ℕ} (θ : ℝ)
    (A B : HansenPedersen.Mₙ n) (v : Fin n → ℂ) :
    positiveRayQForm (positiveRayMatrixConvexCombo θ A B) v =
      θ * positiveRayQForm A v + (1 - θ) * positiveRayQForm B v := by
  unfold positiveRayQForm positiveRayMatrixConvexCombo
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    Complex.add_re]
  simp [smul_eq_mul, Complex.mul_re]

/-- Real scalar multiplication preserves Hermitian complex matrices. -/
lemma positiveRay_isHermitian_smul_real {n : ℕ} (r : ℝ)
    {A : HansenPedersen.Mₙ n} (hA : A.IsHermitian) :
    ((r : ℂ) • A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint] at hA ⊢
  exact IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff]) hA

/-- Convex combinations of Hermitian positive-ray matrices are Hermitian. -/
lemma positiveRay_isHermitian_convexCombo {n : ℕ} (θ : ℝ)
    {A B : HansenPedersen.Mₙ n} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (positiveRayMatrixConvexCombo θ A B).IsHermitian := by
  unfold positiveRayMatrixConvexCombo
  exact (positiveRay_isHermitian_smul_real θ hA).add
    (positiveRay_isHermitian_smul_real (1 - θ) hB)

/-! ### Abstract matrix assignment convexity and twist bridges -/
/--
Joint convexity of the vector quadratic forms of a finite-dimensional matrix
assignment `G`.

For the intended AH1 application, `G n X` is the matrix functional calculus
value `g(X)`.  This predicate keeps that realization outside the order bridge.
-/
def PositiveRayMatrixQFormJointConvex
    (G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) : Prop :=
  ∀ {n : ℕ} {X Y : HansenPedersen.Mₙ n} {v w : Fin n → ℂ} {θ : ℝ},
    X.PosDef → Y.PosDef → 0 ≤ θ → θ ≤ 1 →
    positiveRayQForm (G n (positiveRayMatrixConvexCombo θ X Y))
        (positiveRayVectorConvexCombo θ v w) ≤
      θ * positiveRayQForm (G n X) v +
        (1 - θ) * positiveRayQForm (G n Y) w

/--
Finite-dimensional matrix operator convexity on positive definite inputs for
a matrix assignment `G`.
-/
def PositiveRayMatrixOperatorConvex
    (G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) : Prop :=
  ∀ {n : ℕ} {X Y : HansenPedersen.Mₙ n} {θ : ℝ},
    X.PosDef → Y.PosDef → 0 ≤ θ → θ ≤ 1 →
    G n (positiveRayMatrixConvexCombo θ X Y) ≤
      positiveRayMatrixConvexCombo θ (G n X) (G n Y)

/-- Scalar convexity on the open positive ray. -/
def PositiveRayScalarConvex (h : ℝ → ℝ) : Prop :=
  ∀ {x y θ : ℝ}, 0 < x → 0 < y → 0 ≤ θ → θ ≤ 1 →
    h (θ * x + (1 - θ) * y) ≤ θ * h x + (1 - θ) * h y

/--
Finite-dimensional matrix operator convexity on positive semidefinite inputs.

The inputs are required to be Hermitian explicitly, since semidefinite order is
only meaningful on Hermitian matrices in the later closed-positive bridge.
-/
def PositiveRayClosedMatrixOperatorConvex
    (G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) : Prop :=
  ∀ {n : ℕ} {X Y : HansenPedersen.Mₙ n} {θ : ℝ},
    X.IsHermitian → Y.IsHermitian → X.PosSemidef → Y.PosSemidef →
    0 ≤ θ → θ ≤ 1 →
    G n (positiveRayMatrixConvexCombo θ X Y) ≤
      positiveRayMatrixConvexCombo θ (G n X) (G n Y)

/--
If every output of `G` is Hermitian, then joint convexity of the vector
quadratic forms of `G` implies finite-dimensional matrix operator convexity.
-/
theorem positiveRayMatrixOperatorConvex_of_qformJointConvex
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n}
    (hHerm : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), (G n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G) :
    PositiveRayMatrixOperatorConvex G := by
  intro n X Y θ hX hY hθ0 hθ1
  rw [Matrix.le_iff]
  let D : HansenPedersen.Mₙ n :=
    positiveRayMatrixConvexCombo θ (G n X) (G n Y) -
      G n (positiveRayMatrixConvexCombo θ X Y)
  change D.PosSemidef
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (positiveRay_isHermitian_convexCombo θ (hHerm X) (hHerm Y)).sub
      (hHerm (positiveRayMatrixConvexCombo θ X Y))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDherm ?_
  intro v
  have hq := hjoint (n := n) (X := X) (Y := Y) (v := v) (w := v)
    (θ := θ) hX hY hθ0 hθ1
  rw [positiveRayVectorConvexCombo_self] at hq
  have hDq :
      positiveRayQForm D v =
        (θ * positiveRayQForm (G n X) v +
            (1 - θ) * positiveRayQForm (G n Y) v) -
          positiveRayQForm
            (G n (positiveRayMatrixConvexCombo θ X Y)) v := by
    dsimp [D]
    rw [positiveRayQForm_sub, positiveRayQForm_convexCombo]
  have hre : 0 ≤ Complex.re (star v ⬝ᵥ D *ᵥ v) := by
    change 0 ≤ positiveRayQForm D v
    rw [hDq]
    exact sub_nonneg.mpr hq
  have him : 0 = Complex.im (star v ⬝ᵥ D *ᵥ v) := by
    simpa using (Matrix.IsHermitian.im_star_dotProduct_mulVec_self hDherm v).symm
  exact Complex.nonneg_iff.mpr ⟨hre, him⟩

/-- A Hermitian pointwise limit of eventually semidefinite matrices is semidefinite. -/
lemma positiveRayMat_posSemidef_of_tendsto {n : ℕ} {D : HansenPedersen.Mₙ n}
    {F : ℝ → HansenPedersen.Mₙ n}
    (hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 D))
    (hD : D.IsHermitian)
    (hpsd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (F ε).PosSemidef) :
    D.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD ?_
  intro v
  have hq :
      Tendsto (fun ε : ℝ => Complex.re (star v ⬝ᵥ (F ε) *ᵥ v))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.re (star v ⬝ᵥ D *ᵥ v))) := by
    have hcont : Continuous fun M : HansenPedersen.Mₙ n =>
        Complex.re (star v ⬝ᵥ M *ᵥ v) := by
      fun_prop
    exact (hcont.tendsto D).comp hF
  have hnonneg :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ Complex.re (star v ⬝ᵥ (F ε) *ᵥ v) := by
    filter_upwards [hpsd] with ε hε
    exact (Complex.nonneg_iff.mp (hε.dotProduct_mulVec_nonneg v)).1
  have hlim := ge_of_tendsto hq hnonneg
  have him : 0 = Complex.im (star v ⬝ᵥ D *ᵥ v) := by
    simpa using (Matrix.IsHermitian.im_star_dotProduct_mulVec_self hD v).symm
  exact Complex.nonneg_iff.mpr ⟨hlim, him⟩

/-- Matrix-vector multiplication distributes over positive-ray convex combinations. -/
lemma positiveRayMatrixConvexCombo_mulVec {n : ℕ} (θ : ℝ)
    (X Y : HansenPedersen.Mₙ n) (v : Fin n → ℂ) :
    (positiveRayMatrixConvexCombo θ X Y).mulVec v =
      positiveRayVectorConvexCombo θ (X.mulVec v) (Y.mulVec v) := by
  unfold positiveRayMatrixConvexCombo positiveRayVectorConvexCombo
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]

/--
Compatibility saying that the quadratic form of `H n X` is obtained from the
quadratic form of `G n X` after replacing `v` by `X v`.

For the intended AH1 application, this is the abstract form of
`H n X = X * g(X) * X = X^2 g(X)`.
-/
def PositiveRayMatrixQFormTwist
    (G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) : Prop :=
  ∀ {n : ℕ} (X : HansenPedersen.Mₙ n) (v : Fin n → ℂ),
    positiveRayQForm (H n X) v = positiveRayQForm (G n X) (X.mulVec v)

/--
The same twist compatibility, but only on positive definite inputs.  This is
the natural AH1 interface because the operator-convexity conclusions in this
file only evaluate matrix assignments on positive definite matrices.
-/
def PositiveRayMatrixQFormTwistOnPositive
    (G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) : Prop :=
  ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.PosDef → ∀ v : Fin n → ℂ,
    positiveRayQForm (H n X) v = positiveRayQForm (G n X) (X.mulVec v)

/--
If the vector quadratic forms of `G` are jointly convex and `H` is the
quadratic-form twist of `G` by the input matrix, then `H` is matrix operator
convex on positive definite inputs.
-/
theorem positiveRayMatrixOperatorConvex_of_qformJointConvex_twist
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n}
    (hHerm : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwist G H) :
    PositiveRayMatrixOperatorConvex H := by
  intro n X Y θ hX hY hθ0 hθ1
  rw [Matrix.le_iff]
  let D : HansenPedersen.Mₙ n :=
    positiveRayMatrixConvexCombo θ (H n X) (H n Y) -
      H n (positiveRayMatrixConvexCombo θ X Y)
  change D.PosSemidef
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (positiveRay_isHermitian_convexCombo θ (hHerm X) (hHerm Y)).sub
      (hHerm (positiveRayMatrixConvexCombo θ X Y))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDherm ?_
  intro v
  have hq := hjoint (n := n) (X := X) (Y := Y)
    (v := X.mulVec v) (w := Y.mulVec v) (θ := θ) hX hY hθ0 hθ1
  rw [← positiveRayMatrixConvexCombo_mulVec] at hq
  have hq' :
      positiveRayQForm (H n (positiveRayMatrixConvexCombo θ X Y)) v ≤
        θ * positiveRayQForm (H n X) v +
          (1 - θ) * positiveRayQForm (H n Y) v := by
    rw [htwist (positiveRayMatrixConvexCombo θ X Y) v]
    rw [htwist X v, htwist Y v]
    exact hq
  have hDq :
      positiveRayQForm D v =
        (θ * positiveRayQForm (H n X) v +
            (1 - θ) * positiveRayQForm (H n Y) v) -
          positiveRayQForm
            (H n (positiveRayMatrixConvexCombo θ X Y)) v := by
    dsimp [D]
    rw [positiveRayQForm_sub, positiveRayQForm_convexCombo]
  have hre : 0 ≤ Complex.re (star v ⬝ᵥ D *ᵥ v) := by
    change 0 ≤ positiveRayQForm D v
    rw [hDq]
    exact sub_nonneg.mpr hq'
  have him : 0 = Complex.im (star v ⬝ᵥ D *ᵥ v) := by
    simpa using (Matrix.IsHermitian.im_star_dotProduct_mulVec_self hDherm v).symm
  exact Complex.nonneg_iff.mpr ⟨hre, him⟩

/--
Positive-input version of the twist bridge.  It assumes self-adjointness and
the twist equation only for positive definite matrix inputs.
-/
theorem positiveRayMatrixOperatorConvex_of_qformJointConvex_twistOnPositive
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n}
    (hHerm : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.PosDef → (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwistOnPositive G H) :
    PositiveRayMatrixOperatorConvex H := by
  intro n X Y θ hX hY hθ0 hθ1
  have hcombo : (positiveRayMatrixConvexCombo θ X Y).PosDef :=
    positiveRayMatrixConvexCombo_posDef hX hY hθ0 hθ1
  rw [Matrix.le_iff]
  let D : HansenPedersen.Mₙ n :=
    positiveRayMatrixConvexCombo θ (H n X) (H n Y) -
      H n (positiveRayMatrixConvexCombo θ X Y)
  change D.PosSemidef
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (positiveRay_isHermitian_convexCombo θ (hHerm X hX) (hHerm Y hY)).sub
      (hHerm (positiveRayMatrixConvexCombo θ X Y) hcombo)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDherm ?_
  intro v
  have hq := hjoint (n := n) (X := X) (Y := Y)
    (v := X.mulVec v) (w := Y.mulVec v) (θ := θ) hX hY hθ0 hθ1
  rw [← positiveRayMatrixConvexCombo_mulVec] at hq
  have hq' :
      positiveRayQForm (H n (positiveRayMatrixConvexCombo θ X Y)) v ≤
        θ * positiveRayQForm (H n X) v +
          (1 - θ) * positiveRayQForm (H n Y) v := by
    rw [htwist (positiveRayMatrixConvexCombo θ X Y) hcombo v]
    rw [htwist X hX v, htwist Y hY v]
    exact hq
  have hDq :
      positiveRayQForm D v =
        (θ * positiveRayQForm (H n X) v +
            (1 - θ) * positiveRayQForm (H n Y) v) -
          positiveRayQForm
            (H n (positiveRayMatrixConvexCombo θ X Y)) v := by
    dsimp [D]
    rw [positiveRayQForm_sub, positiveRayQForm_convexCombo]
  have hre : 0 ≤ Complex.re (star v ⬝ᵥ D *ᵥ v) := by
    change 0 ≤ positiveRayQForm D v
    rw [hDq]
    exact sub_nonneg.mpr hq'
  have him : 0 = Complex.im (star v ⬝ᵥ D *ᵥ v) := by
    simpa using (Matrix.IsHermitian.im_star_dotProduct_mulVec_self hDherm v).symm
  exact Complex.nonneg_iff.mpr ⟨hre, him⟩

/-! ### Concrete CFC realization and closed-positive bridge -/
/-- Concrete finite-dimensional CFC matrix assignment `X ↦ g(X)`. -/
noncomputable def positiveRayMatrixCfc (g : ℝ → ℝ) (n : ℕ)
    (X : HansenPedersen.Mₙ n) : HansenPedersen.Mₙ n :=
  if hX : X.IsHermitian then hX.cfc g else 0

/-- The positive-input CFC value `g(X)` is Hermitian. -/
lemma positiveRayMatrixCfc_isHermitian_of_posDef {g : ℝ → ℝ} {n : ℕ}
    (X : HansenPedersen.Mₙ n) (hX : X.PosDef) :
    (positiveRayMatrixCfc g n X).IsHermitian := by
  dsimp [positiveRayMatrixCfc]
  rw [dif_pos hX.isHermitian]
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  rw [← Matrix.IsHermitian.cfc_eq hX.isHermitian g]
  exact IsSelfAdjoint.cfc

/-- The concrete CFC value is Hermitian at any Hermitian input. -/
lemma positiveRayMatrixCfc_isHermitian_of_isHermitian {g : ℝ → ℝ} {n : ℕ}
    (X : HansenPedersen.Mₙ n) (hX : X.IsHermitian) :
    (positiveRayMatrixCfc g n X).IsHermitian := by
  dsimp [positiveRayMatrixCfc]
  rw [dif_pos hX]
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  rw [← Matrix.IsHermitian.cfc_eq hX g]
  exact IsSelfAdjoint.cfc

/-- On Hermitian inputs, the concrete matrix CFC agrees with `LownerHeinzCore.cfcR`. -/
lemma positiveRayMatrixCfc_eq_cfcR_of_isHermitian {g : ℝ → ℝ} {n : ℕ}
    (X : HansenPedersen.Mₙ n) (hX : X.IsHermitian) :
    positiveRayMatrixCfc g n X = LownerHeinzCore.cfcR g X := by
  dsimp [positiveRayMatrixCfc, LownerHeinzCore.cfcR]
  rw [dif_pos hX]
  exact (Matrix.IsHermitian.cfc_eq hX g).symm

private lemma positiveRayMatrix_posSemidef_of_spectrum_nonneg {n : ℕ}
    {X : HansenPedersen.Mₙ n} (hX : X.IsHermitian)
    (hXs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) :
    X.PosSemidef := by
  rw [hX.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hmem : hX.eigenvalues i ∈ spectrum ℝ X := by
    exact Set.ext_iff.mp
      (Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues (𝕜 := ℂ) hX)
      (hX.eigenvalues i) |>.mpr ⟨i, rfl⟩
  exact hXs hmem

private lemma positiveRayMatrixConvexCombo_one_sub_eq_real_smul {n : ℕ}
    (t : ℝ) (X Y : HansenPedersen.Mₙ n) :
    positiveRayMatrixConvexCombo (1 - t) X Y = (1 - t) • X + t • Y := by
  ext i j
  simp only [positiveRayMatrixConvexCombo, Matrix.add_apply, Matrix.smul_apply,
    sub_sub_cancel]
  rw [smul_eq_mul, smul_eq_mul]
  rw [Algebra.smul_def, Algebra.smul_def]
  simp

/--
Right-continuity of finite-dimensional CFC under the positive scalar
perturbation `X ↦ X + ε I` at every closed-positive Hermitian input.
-/
def PositiveRayMatrixEndpointPerturbationContinuous (h : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.IsHermitian → X.PosSemidef →
    Tendsto
      (fun ε : ℝ => positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (positiveRayMatrixCfc h n X))

/-- Closed matrix CFC convexity gives matrix operator convexity on `[0, infinity)`. -/
theorem operatorConvexOnClosedPositive_matrix_of_closedMatrixCfcConvex
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (n : ℕ) :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := HansenPedersen.Mₙ n) (Set.Ici (0 : ℝ)) h := by
  intro A B t hA hB ht0 ht1 hAs hBs
  have hAherm : A.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact hA
  have hBherm : B.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact hB
  have hApsd : A.PosSemidef :=
    positiveRayMatrix_posSemidef_of_spectrum_nonneg hAherm hAs
  have hBpsd : B.PosSemidef :=
    positiveRayMatrix_posSemidef_of_spectrum_nonneg hBherm hBs
  have hmat := hclosed (n := n) (X := A) (Y := B) (θ := 1 - t)
    hAherm hBherm hApsd hBpsd (sub_nonneg.mpr ht1) (by linarith)
  rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian (g := h) A hAherm] at hmat
  rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian (g := h) B hBherm] at hmat
  have hCherm : (positiveRayMatrixConvexCombo (1 - t) A B).IsHermitian :=
    positiveRay_isHermitian_convexCombo (1 - t) hAherm hBherm
  rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian
    (g := h) (positiveRayMatrixConvexCombo (1 - t) A B) hCherm] at hmat
  rw [positiveRayMatrixConvexCombo_one_sub_eq_real_smul t A B] at hmat
  rw [positiveRayMatrixConvexCombo_one_sub_eq_real_smul
    t (LownerHeinzCore.cfcR h A) (LownerHeinzCore.cfcR h B)] at hmat
  exact hmat

private lemma positiveRayCStarMatrix_le_of_matrix {n : ℕ}
    {A B : HansenPedersen.Mₙ n} (hAB : A ≤ B) :
    (CStarMatrix.ofMatrix A : CStarMatrix (Fin n) (Fin n) ℂ) ≤
      CStarMatrix.ofMatrix B := by
  rw [← sub_nonneg]
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnon :
      0 ≤ (CStarMatrix.ofMatrix (B - A) :
        CStarMatrix (Fin n) (Fin n) ℂ) :=
    cStarMatrix_nonneg_of_posSemidef hpsd
  simpa [sub_eq_add_neg] using hnon

private lemma positiveRayMatrix_spectrum_symm_subset_of_cstarMatrix {n : ℕ}
    {A : CStarMatrix (Fin n) (Fin n) ℂ} {s : Set ℝ}
    (hA : spectrum ℝ A ⊆ s) :
    spectrum ℝ (CStarMatrix.ofMatrix.symm A : HansenPedersen.Mₙ n) ⊆ s := by
  intro x hx
  have hspec := AlgEquiv.spectrum_eq
    ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin n)).toAlgEquiv)
    (CStarMatrix.ofMatrix.symm A : HansenPedersen.Mₙ n)
  have hx' : x ∈ spectrum ℝ
      (((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin n)).toAlgEquiv)
        (CStarMatrix.ofMatrix.symm A : HansenPedersen.Mₙ n)) := by
    simpa [hspec] using hx
  exact hA hx'

/-- Matrix operator convexity transports to concrete `CStarMatrix` blocks. -/
theorem operatorConvexOnClosedPositive_cstarMatrix_of_matrix
    {h : ℝ → ℝ}
    (hmatrix : ∀ n : ℕ,
      LownerHeinzCore.OperatorConvexOn
        (𝓐 := HansenPedersen.Mₙ n) (Set.Ici (0 : ℝ)) h)
    (n : ℕ) :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) (Set.Ici (0 : ℝ)) h := by
  intro A B t hA hB ht0 ht1 hAs hBs
  have hA' : IsSelfAdjoint (CStarMatrix.ofMatrix.symm A : HansenPedersen.Mₙ n) := by
    rw [isSelfAdjoint_iff] at hA ⊢
    exact congrArg CStarMatrix.ofMatrix.symm hA
  have hB' : IsSelfAdjoint (CStarMatrix.ofMatrix.symm B : HansenPedersen.Mₙ n) := by
    rw [isSelfAdjoint_iff] at hB ⊢
    exact congrArg CStarMatrix.ofMatrix.symm hB
  have hAs' :
      spectrum ℝ (CStarMatrix.ofMatrix.symm A : HansenPedersen.Mₙ n) ⊆
        Set.Ici (0 : ℝ) :=
    positiveRayMatrix_spectrum_symm_subset_of_cstarMatrix hAs
  have hBs' :
      spectrum ℝ (CStarMatrix.ofMatrix.symm B : HansenPedersen.Mₙ n) ⊆
        Set.Ici (0 : ℝ) :=
    positiveRayMatrix_spectrum_symm_subset_of_cstarMatrix hBs
  have hmat := hmatrix n hA' hB' ht0 ht1 hAs' hBs'
  have hcstar := positiveRayCStarMatrix_le_of_matrix hmat
  simpa using hcstar

/-- Closed matrix CFC convexity gives `CStarMatrix` operator convexity. -/
theorem operatorConvexOnClosedPositive_cstarMatrix_of_closedMatrixCfcConvex
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (n : ℕ) :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) (Set.Ici (0 : ℝ)) h :=
  operatorConvexOnClosedPositive_cstarMatrix_of_matrix
    (fun n => operatorConvexOnClosedPositive_matrix_of_closedMatrixCfcConvex hclosed n) n

end Quantum.TraceInequality.Loewner
