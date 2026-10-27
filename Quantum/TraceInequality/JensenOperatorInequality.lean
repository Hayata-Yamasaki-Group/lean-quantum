/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.JensenOperatorInequalityIImpIV

/-!
# Jensen's operator inequality

This module proves the contraction form of Jensen's inequality for operator-convex
functions and develops its consequences for operator monotonicity. Block operators
and continuous functional calculus supply the proof on complex Hilbert spaces.
-/

-- Keep long block-operator and CFC expressions on one line.
set_option linter.style.longLine false

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

noncomputable local instance : Algebra ℝ (HSum ℋ →L[ℂ] HSum ℋ) := by infer_instance
noncomputable local instance : NormedSpace ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : Module ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance

-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
noncomputable local instance : NonnegSpectrumClass ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/--
Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe.
This is the theorem-level uniform counterpart to the operator-level `...All` predicates.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.
-/
def JensenContractionConditionAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    JensenContractionCondition (ℋ := K) f

omit [Nontrivial ℋ] in
/--
Compression identity for the block column `V = [[X, 0], [Y, 0]]`: conjugating the block
diagonal `diag(A, B)` by `V` compresses it to `diag(X* A X + Y* B Y, 0)`.

This is the single elaboration-heavy block-matrix computation shared by the `(iv) → (v)`
wrappers; proving it once for atomic `A B X Y` keeps the main theorems within the default
heartbeat budget.
-/
private lemma star_blockCol_mul_blockDiagonal_mul_blockCol_wrap (A B X Y : (ℋ →L[ℂ] ℋ)) :
    star (blockOp (ℋ := ℋ) X 0 Y 0) * blockDiagonal (ℋ := ℋ) A B *
        blockOp (ℋ := ℋ) X 0 Y 0 =
      blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
  rw [show star (blockOp (ℋ := ℋ) X 0 Y 0) = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 by
    simp]
  rw [blockDiagonal_eq_blockOp (ℋ := ℋ) A B]
  rw [blockOp_mul, blockOp_mul, blockDiagonal_eq_blockOp]
  congr 1 <;> simp [mul_assoc]

omit [Nontrivial ℋ] in
/-- `V* V = diag(X* X + Y* Y, 0)` for the block column `V = [[X, 0], [Y, 0]]`. -/
private lemma star_blockCol_mul_blockCol_wrap (X Y : (ℋ →L[ℂ] ℋ)) :
    star (blockOp (ℋ := ℋ) X 0 Y 0) * blockOp (ℋ := ℋ) X 0 Y 0 =
      blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
  simpa using star_blockCol_mul_blockDiagonal_mul_blockCol_wrap (ℋ := ℋ) 1 1 X Y

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- `1 - diag(S, 0) = diag(1 - S, 1)` on the two-fold Hilbert sum. -/
private lemma one_sub_blockDiagonal_zero_wrap (S : (ℋ →L[ℂ] ℋ)) :
    (1 : (HSum ℋ →L[ℂ] HSum ℋ)) - blockDiagonal (ℋ := ℋ) S 0 =
      blockDiagonal (ℋ := ℋ) (1 - S) 1 := by
  refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;> simp [sub_eq_add_neg]

omit [Nontrivial ℋ] in
/--
The block column `V = [[X, 0], [Y, 0]]` is a contraction as soon as
`X* X + Y* Y ≤ 1`.
-/
private lemma norm_blockCol_le_one_wrap {X Y : (ℋ →L[ℂ] ℋ)}
    (hXY : star X * X + star Y * Y ≤ (1 : (ℋ →L[ℂ] ℋ))) :
    ‖blockOp (ℋ := ℋ) X 0 Y 0‖ ≤ 1 := by
  have hle : star (blockOp (ℋ := ℋ) X 0 Y 0) * blockOp (ℋ := ℋ) X 0 Y 0 ≤ 1 := by
    rw [star_blockCol_mul_blockCol_wrap (ℋ := ℋ) X Y]
    refine sub_nonneg.mp ?_
    rw [one_sub_blockDiagonal_zero_wrap]
    exact blockDiagonal_nonneg (ℋ := ℋ) (sub_nonneg.mpr hXY) (by simp)
  have hnonneg :
      (0 : (HSum ℋ →L[ℂ] HSum ℋ)) ≤ star (blockOp (ℋ := ℋ) X 0 Y 0) * blockOp (ℋ := ℋ) X 0 Y 0 :=
    star_mul_self_nonneg _
  have hnormSq : ‖star (blockOp (ℋ := ℋ) X 0 Y 0) * blockOp (ℋ := ℋ) X 0 Y 0‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).2 hle
  have hnormSq' : ‖blockOp (ℋ := ℋ) X 0 Y 0‖ * ‖blockOp (ℋ := ℋ) X 0 Y 0‖ ≤ 1 := by
    rwa [CStarRing.norm_star_mul_self (x := blockOp (ℋ := ℋ) X 0 Y 0)] at hnormSq
  have hsq : ‖blockOp (ℋ := ℋ) X 0 Y 0‖ ^ 2 ≤ 1 := by
    simpa [pow_two] using hnormSq'
  nlinarith [norm_nonneg (blockOp (ℋ := ℋ) X 0 Y 0)]



/-- Localized version of Theorem 2.5.2, `(i) ⇒ (v)`, on the nonnegative half-line.

For a continuous, uniformly operator-convex function on `[0, ∞)` with `f(0) ≤ 0`,
this is the binary contractive-column Jensen inequality.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.
-/
theorem jensenColumn_of_opConvexIciAll {f : ℝ → ℝ}
    (hf : OperatorConvexIciAllContNonposAtZero.{u} f) :
    JensenContractiveColumnCondition (ℋ := ℋ) f := by
  intro A B X Y hA hB hAs hBs hXY
  have hA0 : (0 : (ℋ →L[ℂ] ℋ)) ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2
      fun x hx => hAs hx
  have hB0 : (0 : (ℋ →L[ℂ] ℋ)) ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2
      fun x hx => hBs hx
  letI : Nontrivial (HSum ℋ →L[ℂ] HSum ℋ) := nontrivial_hsumL (ℋ := ℋ)
  have hsum_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ star X * A * X + star Y * B * Y := by
    exact add_nonneg (by simpa [mul_assoc] using star_left_conjugate_nonneg hA0 X)
      (by simpa [mul_assoc] using star_left_conjugate_nonneg hB0 Y)
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) :=
    IsSelfAdjoint.of_nonneg hsum_nonneg
  have hsum_spec : spectrum ℝ (star X * A * X + star Y * B * Y) ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg (ℋ := ℋ) hsum_nonneg
  have hcore :=
    (jensenContraction_of_opConvexIciAll (ℋ := HSum ℋ) (f := f) hf)
      (A := blockDiagonal (ℋ := ℋ) A B) (X := blockOp (ℋ := ℋ) X 0 Y 0)
      (blockDiagonal_selfAdjoint (ℋ := ℋ) hA hB)
      (spectrum_Ici_of_nonneg (ℋ := HSum ℋ) (blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0))
      (norm_blockCol_le_one_wrap (ℋ := ℋ) hXY)
  rw [star_blockCol_mul_blockDiagonal_mul_blockCol_wrap,
    cfcR_blockDiagonal (ℋ := ℋ) (f := f) (star X * A * X + star Y * B * Y) 0 hsum_sa
      (by simp)
      (continuousOn_union_of_subset_Ici (f := f) hf.2.1 hsum_spec
        spectrum_zero_subset_Ici),
    cfcR_blockDiagonal (ℋ := ℋ) (f := f) A B hA hB
      (continuousOn_union_of_subset_Ici (f := f) hf.2.1 hAs hBs),
    star_blockCol_mul_blockDiagonal_mul_blockCol_wrap] at hcore
  exact blockDiagonal_le_left (ℋ := ℋ) hcore

end Theorem252

end JensenOperatorInequality
