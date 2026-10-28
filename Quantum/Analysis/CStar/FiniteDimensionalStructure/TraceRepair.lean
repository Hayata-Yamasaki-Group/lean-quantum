/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.Analysis.CStar.FiniteDimensionalStructure.Implementers

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 trace repair

Carlen 2022 Theorem 1.45 (AH1): trace-product obstructions, cross-trace
repairs, positive-normalized implementer wrappers, and provider variants for
rank-one and trace tests.
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

/-! ### Trace-product obstruction and cross-trace repair -/
/--
For the natural trace functional, a rank-one transported square has the
expected two-quadratic-form value.  Thus the direct trace calculation produces
`(v^* Q v) (v^* Q⁻¹ v)`, not a fixed scalar multiple of `v^* Q v`.
A C*-positive-cone step therefore has to either turn this product condition
into a sign-semidefinite alternative or construct a different functional with a
fixed signed scalar.  The normalization `cornerCStarMatrixStarAlgEquiv`
(`CornerNormalization.lean`) instead uses trace nonnegativity of all transported
squares (`matrixBlock_selfAdjoint_signSemidef_of_trace_square_nonneg` below).
-/
theorem matrixBlock_trace_transport_rankOne_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q]
    (hQself : IsSelfAdjoint Q)
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q))
    (v : n → ℂ) :
    Matrix.trace (τ (Matrix.vecMulVec v (star v)) * Matrix.vecMulVec v (star v)) =
      (star v ⬝ᵥ (Q *ᵥ v)) * (star v ⬝ᵥ (⅟Q *ᵥ v)) := by
  rw [hτ]
  rw [StarMul.star_mul, StarMul.star_mul]
  have hQinvself : star (⅟Q) = ⅟Q :=
    (IsSelfAdjoint.invOf_iff Q).mpr hQself |>.star_eq
  rw [hQinvself, hQself.star_eq]
  have hRstar : star (Matrix.vecMulVec v (star v)) = Matrix.vecMulVec v (star v) := by
    ext i j
    simp [Matrix.vecMulVec]
    ring
  rw [hRstar]
  let R := Matrix.vecMulVec v (star v)
  change Matrix.trace (⅟Q * (R * Q) * R) =
      (star v ⬝ᵥ (Q *ᵥ v)) * (star v ⬝ᵥ (⅟Q *ᵥ v))
  calc
    Matrix.trace (⅟Q * (R * Q) * R) =
        Matrix.trace ((⅟Q * R) * Q * R) := by
          rw [← mul_assoc]
    _ = Matrix.trace
        ((Matrix.vecMulVec (⅟Q *ᵥ v) (star v)) * Q * Matrix.vecMulVec v (star v)) := by
          simp [R, Matrix.mul_vecMulVec]
    _ = Matrix.trace
        (Matrix.vecMulVec (⅟Q *ᵥ v) ((star v) ᵥ* Q) * Matrix.vecMulVec v (star v)) := by
          rw [Matrix.vecMulVec_mul]
    _ = Matrix.trace
        (Matrix.vecMulVec (⅟Q *ᵥ v) ((((star v) ᵥ* Q) ⬝ᵥ v) • star v)) := by
          rw [Matrix.vecMulVec_mul_vecMulVec]
    _ = Matrix.trace
        ((((star v) ᵥ* Q) ⬝ᵥ v) • Matrix.vecMulVec (⅟Q *ᵥ v) (star v)) := by
          congr
          ext i j
          simp [Matrix.vecMulVec]
          ring
    _ = (((star v) ᵥ* Q) ⬝ᵥ v) * Matrix.trace (Matrix.vecMulVec (⅟Q *ᵥ v) (star v)) := by
          simp [smul_eq_mul]
    _ = (((star v) ᵥ* Q) ⬝ᵥ v) * ((⅟Q *ᵥ v) ⬝ᵥ star v) := by
          rw [Matrix.trace_vecMulVec]
    _ = (star v ⬝ᵥ (Q *ᵥ v)) * (star v ⬝ᵥ (⅟Q *ᵥ v)) := by
          rw [Matrix.dotProduct_mulVec]
          congr 1
          rw [dotProduct_comm]

/--
The same trace computation with a two-vector rank-one matrix `u v^*`.
This is the trace identity needed for the strengthened route where the
positive-cone calculation is evaluated on all rank-one directions, rather than
only on projections `v v^*`.
-/
theorem matrixBlock_trace_transport_rankOne_twoVector_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q]
    (hQself : IsSelfAdjoint Q)
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q))
    (u v : n → ℂ) :
    Matrix.trace (τ (Matrix.vecMulVec u (star v)) * Matrix.vecMulVec u (star v)) =
      (star u ⬝ᵥ (Q *ᵥ u)) * (star v ⬝ᵥ (⅟Q *ᵥ v)) := by
  rw [hτ]
  rw [StarMul.star_mul, StarMul.star_mul]
  have hQinvself : star (⅟Q) = ⅟Q :=
    (IsSelfAdjoint.invOf_iff Q).mpr hQself |>.star_eq
  rw [hQinvself, hQself.star_eq]
  have hRstar :
      star (Matrix.vecMulVec u (star v)) = Matrix.vecMulVec v (star u) := by
    ext i j
    simp [Matrix.vecMulVec]
    ring
  rw [hRstar]
  let R := Matrix.vecMulVec u (star v)
  let S := Matrix.vecMulVec v (star u)
  change Matrix.trace (⅟Q * (S * Q) * R) =
      (star u ⬝ᵥ (Q *ᵥ u)) * (star v ⬝ᵥ (⅟Q *ᵥ v))
  calc
    Matrix.trace (⅟Q * (S * Q) * R) =
        Matrix.trace ((⅟Q * S) * Q * R) := by
          rw [← mul_assoc]
    _ = Matrix.trace
        ((Matrix.vecMulVec (⅟Q *ᵥ v) (star u)) * Q * Matrix.vecMulVec u (star v)) := by
          simp [S, R, Matrix.mul_vecMulVec]
    _ = Matrix.trace
        (Matrix.vecMulVec (⅟Q *ᵥ v) ((star u) ᵥ* Q) * Matrix.vecMulVec u (star v)) := by
          rw [Matrix.vecMulVec_mul]
    _ = Matrix.trace
        (Matrix.vecMulVec (⅟Q *ᵥ v) ((((star u) ᵥ* Q) ⬝ᵥ u) • star v)) := by
          rw [Matrix.vecMulVec_mul_vecMulVec]
    _ = Matrix.trace
        ((((star u) ᵥ* Q) ⬝ᵥ u) • Matrix.vecMulVec (⅟Q *ᵥ v) (star v)) := by
          congr
          ext i j
          simp [Matrix.vecMulVec]
          ring
    _ = (((star u) ᵥ* Q) ⬝ᵥ u) * Matrix.trace (Matrix.vecMulVec (⅟Q *ᵥ v) (star v)) := by
          simp [smul_eq_mul]
    _ = (((star u) ᵥ* Q) ⬝ᵥ u) * ((⅟Q *ᵥ v) ⬝ᵥ star v) := by
          rw [Matrix.trace_vecMulVec]
    _ = (star u ⬝ᵥ (Q *ᵥ u)) * (star v ⬝ᵥ (⅟Q *ᵥ v)) := by
          rw [Matrix.dotProduct_mulVec]
          congr 1
          rw [dotProduct_comm]

/--
If every complex spectral value of a finite matrix is nonnegative in the
complex order, then its trace is nonnegative.  This is the algebraic trace
extraction hook for the C*-positive-cone route used in
`cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`): after C*-positivity
shows that the transported square has nonnegative spectrum, the ordinary matrix
trace is nonnegative because it is the sum of the characteristic roots.
-/
theorem matrixBlock_trace_nonneg_of_spectrum_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ)
    (hspec : ∀ z : ℂ, z ∈ spectrum ℂ A → 0 ≤ z) :
    0 ≤ Matrix.trace A := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  exact Multiset.sum_nonneg fun z hz =>
    hspec z (Matrix.mem_spectrum_of_isRoot_charpoly (B := A)
      (Polynomial.isRoot_of_mem_roots hz))

/--
The trace-product condition alone does not force sign-semidefiniteness.  The
matrix `diag(1,-1)` is self-adjoint and involutive, so the trace rank-one
product condition becomes a square and is nonnegative for every vector, but the
matrix is neither positive semidefinite nor negative semidefinite.

This rules out the route that tries to use the standard trace calculation alone
to close the C*-positive-cone normalization step.
-/
noncomputable def matrixBlockTraceProductCounterexampleQ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, (-1 : ℂ)]

/-- The counterexample matrix is involutive. -/
theorem matrixBlockTraceProductCounterexampleQ_sq :
    matrixBlockTraceProductCounterexampleQ * matrixBlockTraceProductCounterexampleQ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBlockTraceProductCounterexampleQ]

/-- The counterexample matrix is invertible using itself as a left inverse. -/
@[reducible] noncomputable def matrixBlockTraceProductCounterexampleQ_invertible :
    Invertible matrixBlockTraceProductCounterexampleQ :=
  invertibleOfLeftInverse matrixBlockTraceProductCounterexampleQ
    matrixBlockTraceProductCounterexampleQ matrixBlockTraceProductCounterexampleQ_sq

/-- The `invOf` of the counterexample matrix is the matrix itself. -/
theorem matrixBlockTraceProductCounterexampleQ_invOf :
    letI : Invertible matrixBlockTraceProductCounterexampleQ :=
      matrixBlockTraceProductCounterexampleQ_invertible
    ⅟matrixBlockTraceProductCounterexampleQ = matrixBlockTraceProductCounterexampleQ := by
  letI : Invertible matrixBlockTraceProductCounterexampleQ :=
    matrixBlockTraceProductCounterexampleQ_invertible
  exact invOf_eq_right_inv matrixBlockTraceProductCounterexampleQ_sq

/-- The counterexample matrix is self-adjoint. -/
theorem matrixBlockTraceProductCounterexampleQ_selfAdjoint :
    IsSelfAdjoint matrixBlockTraceProductCounterexampleQ := by
  rw [isSelfAdjoint_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixBlockTraceProductCounterexampleQ]

/-- The counterexample quadratic form is the difference of two coordinate norms. -/
theorem matrixBlockTraceProductCounterexampleQ_quadratic
    (v : Fin 2 → ℂ) :
    star v ⬝ᵥ (matrixBlockTraceProductCounterexampleQ *ᵥ v) =
      star (v 0) * v 0 - star (v 1) * v 1 := by
  rw [Matrix.vec2_dotProduct]
  simp [matrixBlockTraceProductCounterexampleQ, Matrix.mulVec, dotProduct]
  ring

/-- The counterexample quadratic form has zero imaginary part. -/
theorem matrixBlockTraceProductCounterexampleQ_quadratic_im
    (v : Fin 2 → ℂ) :
    (star v ⬝ᵥ (matrixBlockTraceProductCounterexampleQ *ᵥ v)).im = 0 := by
  rw [matrixBlockTraceProductCounterexampleQ_quadratic]
  simp
  ring

/-- The square of the counterexample quadratic form is nonnegative. -/
theorem matrixBlockTraceProductCounterexampleQ_trace_product_nonneg
    (v : Fin 2 → ℂ) :
    0 ≤
      (star v ⬝ᵥ (matrixBlockTraceProductCounterexampleQ *ᵥ v)) *
        (star v ⬝ᵥ (matrixBlockTraceProductCounterexampleQ *ᵥ v)) := by
  rw [← pow_two]
  exact Complex.sq_nonneg_iff.mpr
    (matrixBlockTraceProductCounterexampleQ_quadratic_im v)

/-- The counterexample matrix is not positive semidefinite. -/
theorem matrixBlockTraceProductCounterexampleQ_not_posSemidef :
    ¬ matrixBlockTraceProductCounterexampleQ.PosSemidef := by
  intro h
  have hdiag : (Matrix.diagonal ![(1 : ℂ), (-1 : ℂ)]).PosSemidef := by
    simpa [matrixBlockTraceProductCounterexampleQ, Matrix.diagonal_vec2] using h
  have hentry := (Matrix.posSemidef_diagonal_iff.mp hdiag) (1 : Fin 2)
  norm_num at hentry

/-- The negative counterexample matrix is not positive semidefinite. -/
theorem matrixBlockTraceProductCounterexampleQ_not_neg_posSemidef :
    ¬ (-matrixBlockTraceProductCounterexampleQ).PosSemidef := by
  intro h
  have hdiag : (Matrix.diagonal ![(-1 : ℂ), (1 : ℂ)]).PosSemidef := by
    simpa [matrixBlockTraceProductCounterexampleQ, Matrix.diagonal_vec2] using h
  have hentry := (Matrix.posSemidef_diagonal_iff.mp hdiag) (0 : Fin 2)
  norm_num at hentry

/-- A trace-product condition does not force a sign-semidefinite implementer. -/
theorem matrixBlock_trace_product_condition_not_signSemidef :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, ∃ hQ : Invertible Q,
      IsSelfAdjoint Q ∧
        letI : Invertible Q := hQ
        (∀ v : Fin 2 → ℂ,
          0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * (star v ⬝ᵥ (⅟Q *ᵥ v))) ∧
          ¬ (Q.PosSemidef ∨ (-Q).PosSemidef) := by
  refine ⟨matrixBlockTraceProductCounterexampleQ,
    matrixBlockTraceProductCounterexampleQ_invertible,
    matrixBlockTraceProductCounterexampleQ_selfAdjoint, ?_, ?_⟩
  · intro v
    letI : Invertible matrixBlockTraceProductCounterexampleQ :=
      matrixBlockTraceProductCounterexampleQ_invertible
    rw [matrixBlockTraceProductCounterexampleQ_invOf]
    exact matrixBlockTraceProductCounterexampleQ_trace_product_nonneg v
  · intro h
    rcases h with h | h
    · exact matrixBlockTraceProductCounterexampleQ_not_posSemidef h
    · exact matrixBlockTraceProductCounterexampleQ_not_neg_posSemidef h

private theorem complex_pos_or_neg_of_ne_of_im_zero {z : ℂ}
    (hz : z ≠ 0) (him : z.im = 0) : 0 < z ∨ z < 0 := by
  have hre : z.re ≠ 0 := by
    intro hzre
    apply hz
    exact Complex.ext hzre him
  rcases lt_or_gt_of_ne hre.symm with hrepos | hreneg
  · left
    rw [Complex.pos_iff]
    exact ⟨hrepos, him.symm⟩
  · right
    rw [Complex.neg_iff]
    exact ⟨hreneg, him⟩

private theorem matrixBlock_exists_quadratic_ne_zero_of_invertible_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) [Invertible A] (hself : IsSelfAdjoint A) :
    ∃ v : n → ℂ, star v ⬝ᵥ (A *ᵥ v) ≠ 0 := by
  by_contra h
  push_neg at h
  have hHerm : A.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact hself
  have hpos : A.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun v => by
      rw [h v])
  have hnegHerm : (-A).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    change star (-A) = -A
    rw [star_neg, hself.star_eq]
  have hnegpos : (-A).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hnegHerm (fun v => by
      rw [Matrix.neg_mulVec, dotProduct_neg, h v]
      simp)
  have hA_le_zero : A ≤ 0 := by
    rw [Matrix.le_iff]
    simpa using hnegpos
  have hzero_le_A : 0 ≤ A := hpos.nonneg
  have hA0 : A = 0 := le_antisymm hA_le_zero hzero_le_A
  have hunit : ⅟A * A = 1 := invOf_mul_self A
  have hunit0 : ⅟A * 0 = 1 := by
    calc
      ⅟A * 0 = ⅟A * A := by
        exact congrArg (fun X : Matrix n n ℂ => ⅟A * X) hA0.symm
      _ = 1 := hunit
  rw [Matrix.mul_zero] at hunit0
  let i : n := Classical.choice inferInstance
  have hentry : (0 : Matrix n n ℂ) i i = (1 : Matrix n n ℂ) i i := by
    simpa using congrArg (fun M : Matrix n n ℂ => M i i) hunit0
  norm_num at hentry

/--
The trace obstruction disappears if the positive-cone computation is made on
two independent rank-one directions.  If every rank-one operator
`u v^*` yields the ordered product
`(u^* Q u) * (v^* Q⁻¹ v) ≥ 0`, then the second factor can be frozen at a
nonzero ordered value and the existing fixed-scalar provider gives a consistent
sign for all quadratic forms of `Q`.
-/
theorem matrixBlock_quadratic_sign_of_cross_trace_product_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℂ) [Invertible Q] (hself : IsSelfAdjoint Q)
    (hcross :
      ∀ u v : n → ℂ,
        0 ≤ (star u ⬝ᵥ (Q *ᵥ u)) * (star v ⬝ᵥ (⅟Q *ᵥ v))) :
    (∀ u : n → ℂ, 0 ≤ star u ⬝ᵥ (Q *ᵥ u)) ∨
      (∀ u : n → ℂ, star u ⬝ᵥ (Q *ᵥ u) ≤ 0) := by
  have hInvSelf : IsSelfAdjoint (⅟Q) :=
    (IsSelfAdjoint.invOf_iff Q).mpr hself
  rcases matrixBlock_exists_quadratic_ne_zero_of_invertible_selfAdjoint
      (⅟Q) hInvSelf with ⟨w, hwne⟩
  have hInvHerm : (⅟Q).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact hInvSelf
  have hwim : (star w ⬝ᵥ (⅟Q *ᵥ w)).im = 0 := by
    simpa using Matrix.IsHermitian.im_star_dotProduct_mulVec_self hInvHerm w
  have hc : 0 < star w ⬝ᵥ (⅟Q *ᵥ w) ∨
      star w ⬝ᵥ (⅟Q *ᵥ w) < 0 :=
    complex_pos_or_neg_of_ne_of_im_zero hwne hwim
  exact matrixBlock_quadratic_sign_of_scalar_product_nonneg Q hc (fun u => hcross u w)

/-- Cross trace-product nonnegativity forces a self-adjoint implementer to have a sign. -/
theorem matrixBlock_selfAdjoint_signSemidef_of_cross_trace_product_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℂ) [Invertible Q] (hself : IsSelfAdjoint Q)
    (hcross :
      ∀ u v : n → ℂ,
        0 ≤ (star u ⬝ᵥ (Q *ᵥ u)) * (star v ⬝ᵥ (⅟Q *ᵥ v))) :
    Q.PosSemidef ∨ (-Q).PosSemidef :=
  matrixBlock_selfAdjoint_signSemidef_of_quadratic_sign Q hself
    (matrixBlock_quadratic_sign_of_cross_trace_product_nonneg Q hself hcross)

/--
If the transported C*-positive-cone argument supplies ordinary trace
nonnegativity for every two-vector rank-one matrix `u v^*`, then the
two-variable trace formula gives the strengthened cross-product condition, and
the implementer is semidefinite up to sign.
-/
theorem matrixBlock_selfAdjoint_signSemidef_of_rankOne_cross_trace_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q] (hself : IsSelfAdjoint Q)
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q))
    (htrace :
      ∀ u v : n → ℂ,
        0 ≤ Matrix.trace (τ (Matrix.vecMulVec u (star v)) * Matrix.vecMulVec u (star v))) :
    Q.PosSemidef ∨ (-Q).PosSemidef := by
  apply matrixBlock_selfAdjoint_signSemidef_of_cross_trace_product_nonneg Q hself
  intro u v
  rw [← matrixBlock_trace_transport_rankOne_twoVector_selfAdjoint τ Q hself hτ u v]
  exact htrace u v

/--
The previous rank-one criterion also applies if the transported positive-cone
calculation supplies trace nonnegativity for all matrix directions.  This keeps
the C*-specific residue as the single task of producing ordinary trace
nonnegativity for transported squares.
-/
theorem matrixBlock_selfAdjoint_signSemidef_of_trace_square_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q] (hself : IsSelfAdjoint Q)
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q))
    (htrace : ∀ R : Matrix n n ℂ, 0 ≤ Matrix.trace (τ R * R)) :
    Q.PosSemidef ∨ (-Q).PosSemidef :=
  matrixBlock_selfAdjoint_signSemidef_of_rankOne_cross_trace_nonneg
    τ Q hself hτ (fun u v => htrace (Matrix.vecMulVec u (star v)))

/--
It is enough to know that every transported square has nonnegative ordinary
matrix spectrum.  The previous trace-square criterion then follows from
`matrixBlock_trace_nonneg_of_spectrum_nonneg`.
-/
theorem matrixBlock_selfAdjoint_signSemidef_of_trace_square_spectrum_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q] (hself : IsSelfAdjoint Q)
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q))
    (hspec :
      ∀ R : Matrix n n ℂ, ∀ z : ℂ,
        z ∈ spectrum ℂ (τ R * R) → 0 ≤ z) :
    Q.PosSemidef ∨ (-Q).PosSemidef :=
  matrixBlock_selfAdjoint_signSemidef_of_trace_square_nonneg
    τ Q hself hτ (fun R =>
      matrixBlock_trace_nonneg_of_spectrum_nonneg (τ R * R) (hspec R))

/--
An unnormalised rank-one fixed-scalar formula cannot come from a genuinely
linear functional.  The left hand side is quartic under the scaling
`v ↦ 2 v`, whereas `(v^* Q v) * c` is quadratic.  Hence any such formula forces
the fixed scalar `c` to be zero as soon as one quadratic form of `Q` is nonzero.

This shows that a C*-positive-cone route must either normalize the
rank-one matrices or extract stronger sign information by another argument; the
unnormalised fixed-scalar linear-functional route is not a valid final target.
-/
theorem matrixBlock_rankOne_fixedScalar_linearFunctional_forces_zero
    {n : Type*} [Fintype n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ)
    (Λ : Matrix n n ℂ → ℂ) {c : ℂ}
    (hΛ_smul : ∀ z : ℂ, ∀ R : Matrix n n ℂ, Λ (z • R) = z * Λ R)
    (hτ_four :
      ∀ R : Matrix n n ℂ, τ ((4 : ℂ) • R) = (4 : ℂ) • τ R)
    (hrank :
      ∀ v : n → ℂ,
        Λ (τ (Matrix.vecMulVec v (star v)) * Matrix.vecMulVec v (star v)) =
          (star v ⬝ᵥ (Q *ᵥ v)) * c)
    {v : n → ℂ}
    (hv : star v ⬝ᵥ (Q *ᵥ v) ≠ 0) :
    c = 0 := by
  let Rv : Matrix n n ℂ := Matrix.vecMulVec v (star v)
  let w : n → ℂ := fun i => (2 : ℂ) * v i
  have hRw : Matrix.vecMulVec w (star w) = (4 : ℂ) • Rv := by
    ext i j
    simp [Rv, w, Matrix.vecMulVec]
    ring
  have hquadw :
      star w ⬝ᵥ (Q *ᵥ w) = (4 : ℂ) * (star v ⬝ᵥ (Q *ᵥ v)) := by
    simp [w, Matrix.mulVec, dotProduct, Finset.mul_sum]
    ring_nf
  have hprodw :
      τ (Matrix.vecMulVec w (star w)) * Matrix.vecMulVec w (star w) =
        (16 : ℂ) • (τ Rv * Rv) := by
    rw [hRw, hτ_four Rv]
    ext i j
    simp only [Matrix.mul_smul, smul_mul, smul_apply, smul_eq_mul]
    ring
  have hrw := hrank w
  have hrv := hrank v
  have hscale :
      (16 : ℂ) * ((star v ⬝ᵥ (Q *ᵥ v)) * c) =
        (4 : ℂ) * ((star v ⬝ᵥ (Q *ᵥ v)) * c) := by
    calc
      (16 : ℂ) * ((star v ⬝ᵥ (Q *ᵥ v)) * c)
          = (16 : ℂ) * Λ (τ Rv * Rv) := by rw [hrv]
      _ = Λ ((16 : ℂ) • (τ Rv * Rv)) := by
          rw [hΛ_smul]
      _ = Λ (τ (Matrix.vecMulVec w (star w)) * Matrix.vecMulVec w (star w)) := by
          rw [hprodw]
      _ = (star w ⬝ᵥ (Q *ᵥ w)) * c := hrw
      _ = (4 : ℂ) * ((star v ⬝ᵥ (Q *ᵥ v)) * c) := by
          rw [hquadw]
          ring
  have hzero : ((star v ⬝ᵥ (Q *ᵥ v)) * c) = 0 := by
    have hsub :
        ((16 : ℂ) - 4) * ((star v ⬝ᵥ (Q *ᵥ v)) * c) = 0 := by
      linear_combination hscale
    have hcoef : ((16 : ℂ) - 4) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hsub).resolve_left hcoef
  exact (mul_eq_zero.mp hzero).resolve_left hv

/-! ### Positive-normalized implementer wrappers -/
/--
A self-adjoint implementer which is semidefinite up to sign can be replaced by
an implementer whose adjoint is positive definite.  The conversion from
sign-semidefinite to positive definite is pure finite-dimensional matrix algebra;
the sign-semidefiniteness itself is obtained from the transported C*-positive cone
in `cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`).
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_selfAdjoint_signSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hself : IsSelfAdjoint P)
    (hsemidef : P.PosSemidef ∨ (-P).PosSemidef) :
    ∃ P' : Matrix n n ℂ, ∃ _hP' : Invertible P',
      (∀ M : Matrix n n ℂ, τ M = star (P' * M * ⅟P')) ∧
        (star P').PosDef := by
  classical
  rcases hsemidef with hPsd | hnegPsd
  · have hPpos : P.PosDef := by
      exact hPsd.posDef_iff_isUnit.mpr (isUnit_of_invertible P)
    refine ⟨P, inferInstance, hτ, ?_⟩
    simpa [hself.star_eq] using hPpos
  · let c : ℂˣ := -1
    rcases matrixBlockTransportedStar_eq_star_conj_of_unit_smul τ P hτ c with
      ⟨hPc, hτc⟩
    refine ⟨(c : ℂ) • P, hPc, hτc, ?_⟩
    have hunit_negP : IsUnit (-P) := by
      simpa [c] using ((isUnit_smul_iff c P).mpr (isUnit_of_invertible P))
    have hnegPpos : (-P).PosDef := by
      exact hnegPsd.posDef_iff_isUnit.mpr hunit_negP
    have hstar : star ((c : ℂ) • P) = -P := by
      calc
        star ((c : ℂ) • P) = star (c : ℂ) • star P := by simp
        _ = (-1 : ℂ) • P := by simp [c, hself.star_eq]
        _ = -P := by ext a b; simp
    simpa [hstar]
      using hnegPpos


/--
If an involutive transported star has any inner implementer and a
C*-positive-cone argument supplies sign-semidefiniteness for every self-adjoint
implementer of the same transported star, then a positive-normalized implementer
exists.  For the transported corner involutions of a C*-algebra, this provider is
supplied in `cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`).
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hsemidef :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        Q.PosSemidef ∨ (-Q).PosSemidef) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  rcases matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_involutive
      τ P hτ hinv with ⟨Q, hQinv, hQself, hτQ⟩
  letI : Invertible Q := hQinv
  exact matrixBlockTransportedStar_exists_posDef_implementer_of_selfAdjoint_signSemidef
    τ Q hτQ hQself (hsemidef Q hQself hτQ)

/--
If a C*-normalization has shown that `star P` is positive definite,
then the square-root implementer exists and hence the transported involution is
conjugate to the standard matrix adjoint.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hPpos : (star P).PosDef) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_square
    τ P hτ (matrixBlock_exists_invertible_star_mul_self_of_posDef (star P) hPpos)

/--
Existence form of the positive-normalized implementer.  This is the shape used
after the C*-normalization step: it need not reuse the first
algebraic implementer, only an implementer of the same transported involution
whose adjoint is positive definite.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (hP : ∃ P : Matrix n n ℂ, ∃ _hP : Invertible P,
      (∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P)) ∧ (star P).PosDef) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  rcases hP with ⟨P, hPinv, hτ, hPpos⟩
  letI : Invertible P := hPinv
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_posDef
    τ P hτ hPpos


/--
Self-adjoint implementers which are semidefinite up to sign already give the
matrix-block normalizer.  Thus, after the phase-adjustment step has produced a
self-adjoint implementer, the only further C*-specific input is to extract the
sign-semidefinite alternative from the transported positive cone; this is done in
`cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`).
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_selfAdjoint_signSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hself : IsSelfAdjoint P)
    (hsemidef : P.PosSemidef ∨ (-P).PosSemidef) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  rcases matrixBlockTransportedStar_exists_posDef_implementer_of_selfAdjoint_signSemidef
      τ P hτ hself hsemidef with ⟨Pnew, hPnewInv, hTauNew, hPnewPos⟩
  letI : Invertible Pnew := hPnewInv
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_posDef
    τ Pnew hTauNew hPnewPos


/--
Involutivity plus a sign-semidefinite provider already gives the matrix-block
normalizer.  The provider itself is not proved here; for the transported corner
involutions of a C*-algebra it is supplied in `cornerCStarMatrixStarAlgEquiv`
(`CornerNormalization.lean`).
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_signSemidefProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hsemidef :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        Q.PosSemidef ∨ (-Q).PosSemidef) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
      τ P hτ hinv hsemidef)

/-! ### Trace and rank-one provider variants -/
/--
Two-vector rank-one trace nonnegativity is enough for the positive-normalized
implementer.  This is the theorem-facing version of the strengthened standard
trace route: after the transported positive cone gives
`trace (τ (u v^*) * (u v^*)) ≥ 0` for every `u,v`, the pure matrix part
produces the sign-semidefinite implementer.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_rankOneCrossTraceProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (htrace :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ u v : n → ℂ,
          0 ≤ Matrix.trace
            (τ (Matrix.vecMulVec u (star v)) * Matrix.vecMulVec u (star v))) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  exact matrixBlock_selfAdjoint_signSemidef_of_rankOne_cross_trace_nonneg
    τ Q hQself hτQ (htrace Q hQself hτQ)

/--
The same two-vector rank-one trace provider yields the matrix-block normalizer.
-/
theorem
    matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_rankOneCrossTraceProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (htrace :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ u v : n → ℂ,
          0 ≤ Matrix.trace
            (τ (Matrix.vecMulVec u (star v)) * Matrix.vecMulVec u (star v))) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_rankOneCrossTraceProvider
      τ P hτ hinv htrace)

/--
All-direction trace nonnegativity is enough for the positive-normalized
implementer.  This is stronger than the rank-one provider and is often the
shape a C*-positive-cone argument naturally supplies.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_traceSquareProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (htrace :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ R : Matrix n n ℂ, 0 ≤ Matrix.trace (τ R * R)) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  exact matrixBlock_selfAdjoint_signSemidef_of_trace_square_nonneg
    τ Q hQself hτQ (htrace Q hQself hτQ)

/--
The same all-direction trace provider yields the matrix-block normalizer.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_traceSquareProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (htrace :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ R : Matrix n n ℂ, 0 ≤ Matrix.trace (τ R * R)) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_traceSquareProvider
      τ P hτ hinv htrace)

/--
Spectrum nonnegativity of every transported square is enough for the
positive-normalized implementer.  This is the provider shape expected after a
C*-positive-cone argument has supplied nonnegative spectrum, before the ordinary
trace is extracted.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_traceSpectrumProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hspec :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ R : Matrix n n ℂ, ∀ z : ℂ,
          z ∈ spectrum ℂ (τ R * R) → 0 ≤ z) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_traceSquareProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ R
  exact matrixBlock_trace_nonneg_of_spectrum_nonneg
    (τ R * R) (hspec Q hQself hτQ R)

/--
The same spectrum provider yields the matrix-block normalizer.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_traceSpectrumProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hspec :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∀ R : Matrix n n ℂ, ∀ z : ℂ,
          z ∈ spectrum ℂ (τ R * R) → 0 ≤ z) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_traceSpectrumProvider
      τ P hτ hinv hspec)

/--
It is enough for a C*-positive-cone argument to give a consistent
sign for all standard quadratic forms of every self-adjoint implementer.
The conversion from that quadratic-form sign condition to the semidefinite
alternative is pure matrix order.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_quadraticSignProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hquad :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        (∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (Q *ᵥ v)) ∨
          (∀ v : n → ℂ, star v ⬝ᵥ (Q *ᵥ v) ≤ 0)) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_signSemidefProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  exact matrixBlock_selfAdjoint_signSemidef_of_quadratic_sign
    Q hQself (hquad Q hQself hτQ)

/--
The same quadratic-form provider is also enough to construct the matrix-block
normalizer.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_quadraticSignProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hquad :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        (∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (Q *ᵥ v)) ∨
          (∀ v : n → ℂ, star v ⬝ᵥ (Q *ᵥ v) ≤ 0)) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_quadraticSignProvider
      τ P hτ hinv hquad)

/--
Rank-one scalar-product control is enough for the sign-semidefinite provider.  This is
the form expected after the transported C*-positive cone has been evaluated on
rank-one matrices: for each self-adjoint implementer, it supplies a nonzero
ordered scalar `c` such that every standard quadratic form multiplied by `c` is
nonnegative.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_scalarProductProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hprod :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_quadraticSignProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  rcases hprod Q hQself hτQ with ⟨c, hc, hprodQ⟩
  exact matrixBlock_quadratic_sign_of_scalar_product_nonneg Q hc hprodQ

/--
The same scalar-product provider yields the matrix-block normalizer.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_scalarProductProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hprod :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_scalarProductProvider
      τ P hτ hinv hprod)

/--
Normalized rank-one quadratic control is enough for the positive-normalized
implementer.  This is the provider shape after the scaling obstruction for
unnormalized rank-one linear functionals: work with the quotient by `v^*v`,
then clear that positive denominator using
`matrixBlock_scalarProductProvider_of_normalized_quadratic`.
-/
theorem
    matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_normalizedQuadraticProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hnorm :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : n → ℂ, v ≠ 0 →
            0 ≤ ((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_scalarProductProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  rcases hnorm Q hQself hτQ with ⟨c, hc, hnormQ⟩
  exact matrixBlock_scalarProductProvider_of_normalized_quadratic Q hc hnormQ

/--
The same normalized rank-one quadratic provider yields the matrix-block
normalizer.
-/
theorem
    matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_normalizedQuadraticProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hnorm :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, (0 < c ∨ c < 0) ∧
          ∀ v : n → ℂ, v ≠ 0 →
            0 ≤ ((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_normalizedQuadraticProvider
      τ P hτ hinv hnorm)

/--
Rank-one positive-functional control is enough for the positive-normalized
implementer.  This packages the positive-cone computation one step
before the scalar-product provider: find a signed scalar and a positive
functional whose rank-one values are the standard quadratic forms times that
scalar.
-/
theorem matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_rankOneFunctionalProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hrank :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, ∃ Λ : Matrix n n ℂ → ℂ,
          (0 < c ∨ c < 0) ∧
            (∀ R : Matrix n n ℂ, 0 ≤ Λ (τ R * R)) ∧
              ∀ v : n → ℂ,
                Λ (τ (Matrix.vecMulVec v (star v)) *
                    Matrix.vecMulVec v (star v)) =
                  (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q,
      (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) ∧
        (star Q).PosDef := by
  refine matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_scalarProductProvider
    τ P hτ hinv ?_
  intro Q _hQinv hQself hτQ
  rcases hrank Q hQself hτQ with ⟨c, Λ, hc, hpos, heval⟩
  exact matrixBlock_scalarProductProvider_of_rankOne_positiveFunctional
    τ Q c hc Λ hpos heval

/--
The same rank-one positive-functional provider yields the matrix-block
normalizer.
-/
theorem
    matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_involutive_rankOneFunctionalProvider
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (hrank :
      ∀ Q : Matrix n n ℂ, [Invertible Q] →
        IsSelfAdjoint Q →
        (∀ M : Matrix n n ℂ, τ M = star (Q * M * ⅟Q)) →
        ∃ c : ℂ, ∃ Λ : Matrix n n ℂ → ℂ,
          (0 < c ∨ c < 0) ∧
            (∀ R : Matrix n n ℂ, 0 ≤ Λ (τ R * R)) ∧
              ∀ v : n → ℂ,
                Λ (τ (Matrix.vecMulVec v (star v)) *
                    Matrix.vecMulVec v (star v)) =
                  (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  exact matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_exists_posDef
    τ
    (matrixBlockTransportedStar_exists_posDef_implementer_of_involutive_rankOneFunctionalProvider
      τ P hτ hinv hrank)

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
