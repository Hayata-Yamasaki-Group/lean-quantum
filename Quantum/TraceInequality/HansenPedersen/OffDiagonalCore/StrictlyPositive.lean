/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore.RectangularOperators

/-!
# Strict-output off-diagonal contractions

Specialized off-diagonal contraction operators and their conjugation identities
for the strict-output setting.

## Main results

* `StrictlyPositive.offDiagContraction` and
  `StrictlyPositive.offDiagContractionCodomainFirst`: off-diagonal block
  operators built from the strict-output contraction and its adjoint.
* `StrictlyPositive.offDiagContractionCodomainFirst_contractive`: contractivity
  of the codomain-first off-diagonal operator.
* The `...star_mul...` lemmas: conjugation identities reducing off-diagonal
  products to rectangular diagonal maps.

## References

* Internal off-diagonal contraction layer for the finite-dimensional
  Hiai-Petz strict data-processing construction.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra

/-- Off-diagonal block operator built from the strict-output contraction
associated to a positive map, a positive-definite input `B`, and positive
definiteness of `Φ 1`. -/
noncomputable def StrictlyPositive.offDiagContraction
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    HansenPedersen.L (hsBlockSpaceRect k l) := by
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  exact offDiagCLMRectHs V (hsAdjoint V)

/-- The square `O⋆ O` of the off-diagonal contraction is a rectangular diagonal
map whose entries are the two products `V ∘ V⋆` and `V⋆ ∘ V`. -/
theorem StrictlyPositive.offDiagContraction_star_mul
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (_hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    star (StrictlyPositive.offDiagContraction Φ hPos hB hΦ1) *
        StrictlyPositive.offDiagContraction Φ hPos hB hΦ1 =
      diagMapCLMRectHs
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          (StrictlyPositive.contraction Φ hPos hB hΦ1)) := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let O := offDiagCLMRectHs V (hsAdjoint V)
  let D0 := diagMapCLMRectHs (k := k) (l := l) (V.comp (hsAdjoint V)) ((hsAdjoint V).comp V)
  have hstar :
      star O = O := by
    simpa [O, hsAdjoint, ContinuousLinearMap.adjoint_adjoint] using
      (offDiagCLMRectHs_star (k := k) (l := l) (a := V) (b := hsAdjoint V))
  have hmul :
      O * O = D0 := by
    simpa [O, D0] using
      (offDiagCLMRectHs_mul_offDiagCLMRectHs (k := k) (l := l)
        (a := V) (b := hsAdjoint V) (c := V) (d := hsAdjoint V))
  calc
    star (StrictlyPositive.offDiagContraction Φ hPos hB hΦ1) *
        StrictlyPositive.offDiagContraction Φ hPos hB hΦ1
      = star O * O := by
          simp [StrictlyPositive.offDiagContraction, O, V]
    _ = O * O := by
          rw [hstar]
    _ = D0 := hmul

/-- Conjugating a rectangular diagonal map of `jOperator` values by the
off-diagonal contraction swaps the two blocks and inserts the contraction and
its Hilbert-Schmidt adjoint. -/
theorem StrictlyPositive.offDiagContraction_star_mul_diagMapCLM
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    star (StrictlyPositive.offDiagContraction Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := k) (l := l)
          (jOperator f A B) (jOperator f (Φ A) (Φ B)) *
        StrictlyPositive.offDiagContraction Φ hPos hB hΦ1 =
      diagMapCLMRectHs
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          ((jOperator f (Φ A) (Φ B)).comp
            (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1))))
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          ((jOperator f A B).comp
            (StrictlyPositive.contraction Φ hPos hB hΦ1))) := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  calc
    star (StrictlyPositive.offDiagContraction Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := k) (l := l)
          (jOperator f A B) (jOperator f (Φ A) (Φ B)) *
        StrictlyPositive.offDiagContraction Φ hPos hB hΦ1
      = offDiagCLMRectHs (k := k) (l := l) V (hsAdjoint V) *
          diagMapCLMRectHs (k := k) (l := l)
            (jOperator f A B) (jOperator f (Φ A) (Φ B)) *
          offDiagCLMRectHs (k := k) (l := l) V (hsAdjoint V) := by
            simp [StrictlyPositive.offDiagContraction, V, offDiagCLMRectHs_star, hsAdjoint,
              ContinuousLinearMap.adjoint_adjoint]
    _ = offDiagCLMRectHs (k := k) (l := l)
          (V.comp (jOperator f (Φ A) (Φ B)))
          ((hsAdjoint V).comp (jOperator f A B)) *
          offDiagCLMRectHs (k := k) (l := l) V (hsAdjoint V) := by
            rw [offDiagCLMRectHs_mul_diagMapCLMRectHs]
            rfl
    _ = diagMapCLMRectHs (k := k) (l := l)
          ((V.comp (jOperator f (Φ A) (Φ B))).comp (hsAdjoint V))
          (((hsAdjoint V).comp (jOperator f A B)).comp V) := by
            simpa using
              (offDiagCLMRectHs_mul_offDiagCLMRectHs
                (k := k) (l := l)
                (a := V.comp (jOperator f (Φ A) (Φ B)))
                (b := (hsAdjoint V).comp (jOperator f A B))
                (c := V) (d := hsAdjoint V))
    _ = diagMapCLMRectHs (k := k) (l := l)
          (V.comp ((jOperator f (Φ A) (Φ B)).comp (hsAdjoint V)))
          ((hsAdjoint V).comp ((jOperator f A B).comp V)) := by
            rfl

/-- Codomain-first off-diagonal block operator built from the adjoint of the
strict-output contraction in the first off-diagonal slot. -/
noncomputable def StrictlyPositive.offDiagContractionCodomainFirst
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    HansenPedersen.L (hsBlockSpaceRect l k) := by
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  exact offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V

/-- The codomain-first off-diagonal contraction is norm-contracting when the
positive map satisfies the Hilbert-Schmidt adjoint Schwarz condition. -/
theorem StrictlyPositive.offDiagContractionCodomainFirst_contractive
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (x : hsBlockSpaceRect l k) :
    ‖StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 x‖ ≤ ‖x‖ := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hout :
      ‖StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 x‖ =
        √(‖hsAdjoint V x.snd‖ ^ 2 + ‖V x.fst‖ ^ 2) :=
    by
      simpa [StrictlyPositive.offDiagContractionCodomainFirst, offDiagCLMRectHs_apply, V] using
        (WithLp.prod_norm_eq_of_L2
          (x := StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 x))
  rw [hout]
  have hfst :
      ‖V x.fst‖ ≤ ‖x.fst‖ := by
    simpa [V] using StrictlyPositive.contraction_contractive Φ hPos hSch hB hΦ1 x.fst
  have hsnd :
      ‖hsAdjoint V x.snd‖ ≤ ‖x.snd‖ := by
    let y : Mₙ (Nat.succ l) := hsAdjoint V x.snd
    have hVy : ‖V y‖ ≤ ‖y‖ := by
      simpa [V, y] using StrictlyPositive.contraction_contractive Φ hPos hSch hB hΦ1 y
    have hinner0 :
        inner ℂ (hsAdjoint V x.snd) y = inner ℂ x.snd (V y) := by
      exact
        @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := Nat.succ l))
          (instMatrixNormedAddCommGroup (n := Nat.succ k))
          (instMatrixInnerProductSpace (n := Nat.succ l))
          (instMatrixInnerProductSpace (n := Nat.succ k))
          (instMatrixCompleteSpace (n := Nat.succ l))
          (instMatrixCompleteSpace (n := Nat.succ k))
          V y x.snd
    have hinner : inner ℂ y y = inner ℂ x.snd (V y) := by
      simpa [y, hsAdjoint] using hinner0
    have hsq : ‖y‖ ^ 2 ≤ ‖x.snd‖ * ‖y‖ := by
      calc
        ‖y‖ ^ 2 = Complex.re (inner ℂ y y) := by
          simpa using (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (x := y))
        _ = Complex.re (inner ℂ x.snd (V y)) := by rw [hinner]
        _ ≤ ‖x.snd‖ * ‖V y‖ := re_inner_le_norm (𝕜 := ℂ) _ _
        _ ≤ ‖x.snd‖ * ‖y‖ := by gcongr
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    have hx_nonneg : 0 ≤ ‖x.snd‖ := norm_nonneg x.snd
    have hy_le : ‖y‖ ≤ ‖x.snd‖ := by
      nlinarith
    simpa [y] using hy_le
  have hsq :
      ‖hsAdjoint V x.snd‖ ^ 2 + ‖V x.fst‖ ^ 2 ≤ ‖x.snd‖ ^ 2 + ‖x.fst‖ ^ 2 := by
    nlinarith [hfst, hsnd, norm_nonneg (V x.fst), norm_nonneg (x.fst),
      norm_nonneg (hsAdjoint V x.snd), norm_nonneg (x.snd)]
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hxnorm : ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := WithLp.prod_norm_eq_of_L2 x
  rw [hxnorm]
  simpa [add_comm, add_left_comm, add_assoc, V] using hsqrt

/-- Conjugating a codomain-first diagonal map of `jOperator` values by the
codomain-first off-diagonal contraction produces the corresponding diagonal
map with `V` and `V⋆` inserted on the two components. -/
theorem StrictlyPositive.offDiagContractionCodomainFirst_star_mul_diagMapCLM
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k)
          (jOperator f (Φ A) (Φ B)) (jOperator f A B) *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 =
      diagMapCLMRectHs
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          ((jOperator f A B).comp
            (StrictlyPositive.contraction Φ hPos hB hΦ1)))
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          ((jOperator f (Φ A) (Φ B)).comp
            (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))) := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  calc
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k)
          (jOperator f (Φ A) (Φ B)) (jOperator f A B) *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1
      = offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V *
          diagMapCLMRectHs (k := l) (l := k)
            (jOperator f (Φ A) (Φ B)) (jOperator f A B) *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            simp [StrictlyPositive.offDiagContractionCodomainFirst, V, offDiagCLMRectHs_star,
              hsAdjoint, ContinuousLinearMap.adjoint_adjoint]
    _ = offDiagCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp (jOperator f A B))
          (V.comp (jOperator f (Φ A) (Φ B))) *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            rw [offDiagCLMRectHs_mul_diagMapCLMRectHs]
            rfl
    _ = diagMapCLMRectHs (k := l) (l := k)
          (((hsAdjoint V).comp (jOperator f A B)).comp V)
          ((V.comp (jOperator f (Φ A) (Φ B))).comp (hsAdjoint V)) := by
            simpa using
              (offDiagCLMRectHs_mul_offDiagCLMRectHs
                (k := l) (l := k)
                (a := (hsAdjoint V).comp (jOperator f A B))
                (b := V.comp (jOperator f (Φ A) (Φ B)))
                (c := hsAdjoint V) (d := V))
    _ = diagMapCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp ((jOperator f A B).comp V))
          (V.comp ((jOperator f (Φ A) (Φ B)).comp (hsAdjoint V))) := by
            rfl

/-- The previous codomain-first conjugation identity specialized to the raw
`jArg` operators instead of `jOperator f`. -/
theorem StrictlyPositive.offDiagContractionCodomainFirst_star_mul_jArg_diagMapCLM
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (_hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k)
          (jArg (Φ A) (Φ B)) (jArg A B) *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 =
      diagMapCLMRectHs
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          ((jArg A B).comp
            (StrictlyPositive.contraction Φ hPos hB hΦ1)))
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          ((jArg (Φ A) (Φ B)).comp
            (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))) := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  calc
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k)
          (jArg (Φ A) (Φ B)) (jArg A B) *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1
      = offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V *
          diagMapCLMRectHs (k := l) (l := k)
            (jArg (Φ A) (Φ B)) (jArg A B) *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            simp [StrictlyPositive.offDiagContractionCodomainFirst, V, offDiagCLMRectHs_star,
              hsAdjoint, ContinuousLinearMap.adjoint_adjoint]
    _ = offDiagCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp (jArg A B))
          (V.comp (jArg (Φ A) (Φ B))) *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            rw [offDiagCLMRectHs_mul_diagMapCLMRectHs]
            rfl
    _ = diagMapCLMRectHs (k := l) (l := k)
          (((hsAdjoint V).comp (jArg A B)).comp V)
          ((V.comp (jArg (Φ A) (Φ B))).comp (hsAdjoint V)) := by
            simpa using
              (offDiagCLMRectHs_mul_offDiagCLMRectHs
                (k := l) (l := k)
                (a := (hsAdjoint V).comp (jArg A B))
                (b := V.comp (jArg (Φ A) (Φ B)))
                (c := hsAdjoint V) (d := V))
    _ = diagMapCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp ((jArg A B).comp V))
          (V.comp ((jArg (Φ A) (Φ B)).comp (hsAdjoint V))) := by
            rfl

/-- Generic codomain-first conjugation identity for an arbitrary pair of
Hilbert-Schmidt operators in the two diagonal slots. -/
theorem StrictlyPositive.offDiagContractionCodomainFirst_star_mul_diagMapCLM_generic
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (TΦ : HSOp (Nat.succ l))
    (TA : HSOp (Nat.succ k)) :
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k) TΦ TA *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1 =
      diagMapCLMRectHs
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          (TA.comp (StrictlyPositive.contraction Φ hPos hB hΦ1)))
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          (TΦ.comp (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))) := by
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  letI := instMatrixCompleteSpace (n := Nat.succ l)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixCompleteSpace (n := Nat.succ k)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  calc
    star (StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1) *
        diagMapCLMRectHs (k := l) (l := k) TΦ TA *
        StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1
      = offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V *
          diagMapCLMRectHs (k := l) (l := k) TΦ TA *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            simp [StrictlyPositive.offDiagContractionCodomainFirst, V, offDiagCLMRectHs_star,
              hsAdjoint, ContinuousLinearMap.adjoint_adjoint]
    _ = offDiagCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp TA)
          (V.comp TΦ) *
          offDiagCLMRectHs (k := l) (l := k) (hsAdjoint V) V := by
            rw [offDiagCLMRectHs_mul_diagMapCLMRectHs]
            rfl
    _ = diagMapCLMRectHs (k := l) (l := k)
          (((hsAdjoint V).comp TA).comp V)
          ((V.comp TΦ).comp (hsAdjoint V)) := by
            simpa using
              (offDiagCLMRectHs_mul_offDiagCLMRectHs
                (k := l) (l := k)
                (a := (hsAdjoint V).comp TA)
                (b := V.comp TΦ)
                (c := hsAdjoint V) (d := V))
    _ = diagMapCLMRectHs (k := l) (l := k)
          ((hsAdjoint V).comp (TA.comp V))
          (V.comp (TΦ.comp (hsAdjoint V))) := by
            rfl



end HiaiPetz
