/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.Internal.ShiftedCompressionInstances
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.ResidualOperators
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.InnerProduct
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
Quadratic-form and final residual comparison layer for shifted strict-output compression.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
open scoped HiaiPetz.RectangularOperatorInstances
open ProofNetInternal.ShiftedCompressionInstances

noncomputable section MatrixScopedInstances

private noncomputable abbrev diagCoreABINormedAddCommGroup {k l : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ l × Mₙ k)) :=
  WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ l) (β := Mₙ k)

private noncomputable abbrev diagCoreABICompleteSpace {k l : ℕ} :
    CompleteSpace (WithLp 2 (Mₙ l × Mₙ k)) :=
  inferInstance

private noncomputable abbrev diagCoreABIRealCFC {k l : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (diagCoreABINormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

namespace StrictlyPositive

-- This localized alias still elaborates a large cross-space `cfcR ≤ diagMapCLM` statement.
/-- Family form of the shifted ambient diagonal-core inequality: for every positive-definite `A`
and every `p > 0`, the real CFC of `shiftedNegFn f p` at the ambient `J`-argument operator is
dominated by the rectangular diagonal map built from the negated first and second RHS cores. -/
def ShiftedAmbientDiagCoreFamily
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (_hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ (_hA : Matrix.PosDef A) ⦃p : ℝ⦄, 0 < p →
    @HansenPedersen.cfcR (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (diagCoreABINormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
        (strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l))
        (diagCoreABICompleteSpace (k := Nat.succ k) (l := Nat.succ l))
        (diagCoreABIRealCFC (k := Nat.succ k) (l := Nat.succ l))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) ≤
      diagMapCLMRectHs (k := l) (l := k)
        (-StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p)
        (-StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p)

end StrictlyPositive

-- The family builder expands the same cross-space ambient inequality at the theorem header.
/-- The shifted negative inverse inequality for `f`, together with the positivity, Schwarz and
positive-definiteness hypotheses, yields the family form `ShiftedAmbientDiagCoreFamily`. -/
theorem StrictlyPositive.shiftedAmbientDiagCoreFamily_of_shiftedInverseInequality
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hshiftII : ShiftedInverseInequalityNeg f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.ShiftedAmbientDiagCoreFamily f Φ A B hPos hSch hB hΦ1 := by
  intro hA p hp
  exact StrictlyPositive.shiftedAmbient_inverseInequality_diag_core
    (f := f) hf (Φ := Φ) (A := A) (B := B) hshiftII hPos hSch hA hB hΦ1 hp

-- Keep the compression cut at the fixed-`hA` ambient diag-core stage; the first-corner bridge is
-- proved later inside the last-mile proof search rather than as a separate top-level theorem.
namespace StrictlyPositive

/-- Fixed-`A` form of the shifted ambient diagonal-core inequality: with the positive-definite `A`
supplied as a hypothesis, for every `p > 0` the real CFC of `shiftedNegFn f p` at the ambient
`J`-argument operator is dominated by the rectangular diagonal map of the negated first and second
RHS cores. -/
def ShiftedAmbientDiagCoreAt
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (_hSch : HSAdjointSchwarz Φ)
    (_hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ ⦃p : ℝ⦄, 0 < p →
    @HansenPedersen.cfcR (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (diagCoreABINormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
        (strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l))
        (diagCoreABICompleteSpace (k := Nat.succ k) (l := Nat.succ l))
        (diagCoreABIRealCFC (k := Nat.succ k) (l := Nat.succ l))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) ≤
      diagMapCLMRectHs (k := l) (l := k)
        (-StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p)
        (-StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p)

end StrictlyPositive

/-- The shifted negative inverse inequality for `f`, with the positivity/Schwarz/positive-definite
hypotheses, yields the fixed-`A` form `ShiftedAmbientDiagCoreAt`. -/
theorem StrictlyPositive.shiftedAmbientDiagCoreAt_of_shiftedInverseInequality
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hshiftII : ShiftedInverseInequalityNeg f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1 := by
  intro p hp
  exact StrictlyPositive.shiftedAmbient_inverseInequality_diag_core
    (f := f) hf (Φ := Φ) (A := A) (B := B) hshiftII hPos hSch hA hB hΦ1 hp

/-- The matrix-monotone condition on `f` (with `f` continuous and positive on `(0, ∞)`) yields the
fixed-`A` diagonal-core inequality `ShiftedAmbientDiagCoreAt`, routing through operator convexity
and the shifted negative inverse inequality. -/
theorem shiftedAmbientDiagCoreAt_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1 := by
  have hconvNeg : ShiftedAllHOperatorConvexNeg f := by
    exact shiftedAllHOperatorConvexNeg_of_matrixMonotoneCondition f hf hpos hI
  have hshiftII : ShiftedInverseInequalityNeg f := by
    exact shiftedInverseInequalityNeg_of_shiftedAllHOperatorConvexNeg
      (f := f) (hf := hf) (hpos := hpos) hconvNeg
  exact StrictlyPositive.shiftedAmbientDiagCoreAt_of_shiftedInverseInequality
    (f := f) hf (Φ := Φ) (A := A) (B := B) hshiftII hPos hSch hA hB hΦ1

/-- First-corner consequence of the diagonal-core inequality: for every `X`, the inner product of
`X` with `-(shiftedAmbientFirstRhsCore) X - (shiftedAmbientFirstLhs) X` is nonnegative. -/
theorem StrictlyPositive.shiftedAmbientFirst_inner_nonneg_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    0 ≤
      inner ℂ
        (-(StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X -
          (StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X)
        X := by
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CStarAlgebra (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) :=
    strictEquivShiftedPairCStarAlgebra (k := Nat.succ k) (l := Nat.succ l)
  letI : ContinuousFunctionalCalculus ℝ
      (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
    strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
  have hdiag := hdiagCore hp
  have hx :
      0 ≤
        inner ℂ
            ((-StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p -
                StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p)
              (WithLp.toLp 2 (X, 0)).fst)
            X +
          inner ℂ
            ((-StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p -
                StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p)
              (WithLp.toLp 2 (X, 0)).snd)
            0 := by
    simpa only [StrictlyPositive.ambientJArgCFC_eq_diagMapCLM
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 hp,
      HansenPedersen.Internal.diagMapCLM_sub, HansenPedersen.Internal.diagMapCLM_apply,
      WithLp.prod_inner_apply] using
      hdiag.inner_nonneg_left (WithLp.toLp 2 (X, 0))
  simpa [StrictlyPositive.shiftedAmbientFirstLhs] using hx

/-- Monotonicity of the Hilbert–Schmidt quadratic form from inner-product nonnegativity: if
`0 ≤ Re (inner ℂ ((T - S) X) X)` for all `X`, then
`Re (tr (Xᴴ * S X)) ≤ Re (tr (Xᴴ * T X))`. -/
theorem hsQForm_le_of_inner_nonneg {n : ℕ}
    {S T : HSOp n}
    (hST : ∀ X : Mₙ n, 0 ≤ Complex.re (inner ℂ ((T - S) X) X)) (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (S X))) ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hnonneg : 0 ≤ Complex.re (inner ℂ ((T - S) X) X) := by
    exact hST X
  have hinner :
      Complex.re (inner ℂ (S X) X) ≤ Complex.re (inner ℂ (T X) X) := by
    have hrew :
        Complex.re (inner ℂ ((T - S) X) X) =
          Complex.re (inner ℂ (T X) X) - Complex.re (inner ℂ (S X) X) := by
      simp [ContinuousLinearMap.sub_apply, Complex.sub_re]
    rw [hrew] at hnonneg
    linarith
  simpa [HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun] using hinner

/-- Quadratic-form form of the first-corner bound from the diagonal-core inequality:
`Re (tr (Xᴴ * shiftedAmbientFirstLhs X)) ≤ -Re (tr (Xᴴ * shiftedAmbientFirstRhsCore X))`. -/
theorem StrictlyPositive.shiftedAmbientFirst_qform_le_neg_rhsCore_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) ≤
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X))) := by
  have hinner :=
    StrictlyPositive.shiftedAmbientFirst_inner_nonneg_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hSch hA hB hΦ1 hdiagCore hp X
  have hinner_re :
      Complex.re
          (inner ℂ ((StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X)
            X) ≤
        -Complex.re
          (inner ℂ ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X) X) := by
    have hinner_re0 :
        0 ≤
          Complex.re
            (inner ℂ
              (-(StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X -
                (StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X)
              X) :=
      (Complex.le_def.mp hinner).1
    have hrew :
        Complex.re
            (inner ℂ
              (-(StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X -
                (StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X)
              X) =
          -Complex.re
              (inner ℂ ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X) X) +
            -Complex.re
              (inner ℂ
                ((StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X) X) := by
      simp [sub_eq_add_neg, add_comm]
    rw [hrew] at hinner_re0
    linarith
  have hrew :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X))) ≤
        -Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) := by
    simpa [HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun] using hinner_re
  linarith

/-- First-corner quadratic-form bound rewritten through the contraction: the first LHS quadratic
form at `X` is dominated by minus the shifted-domain CFC quadratic form at `contraction … X`. -/
theorem StrictlyPositive.shiftedAmbientFirst_qform_le_neg_shiftedDomain_qform_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) ≤
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
              (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
  have hfirst :=
    StrictlyPositive.shiftedAmbientFirst_qform_le_neg_rhsCore_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hSch hA hB hΦ1 hdiagCore hp X
  simpa [StrictlyPositive.shiftedAmbientFirstRhsCore_qform_eq_shiftedDomain_qform
    (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 (X := X)] using hfirst

/-- Second-corner consequence of the diagonal-core inequality: for every `X`, the inner product of
`X` with `-(shiftedAmbientSecondRhsCore) X - (shiftedAmbientSecondLhs) X` is nonnegative. -/
theorem StrictlyPositive.shiftedAmbientSecond_inner_nonneg_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ k)) :
    0 ≤
      inner ℂ
        (-(StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X -
          (StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X)
        X := by
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CStarAlgebra (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) :=
    strictEquivShiftedPairCStarAlgebra (k := Nat.succ k) (l := Nat.succ l)
  letI : ContinuousFunctionalCalculus ℝ
      (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
    strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
  have hdiag := hdiagCore hp
  have hx :
      0 ≤
        inner ℂ
            ((-StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p -
                StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p)
              (WithLp.toLp 2 (0, X)).fst)
            0 +
          inner ℂ
            ((-StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p -
                StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p)
              (WithLp.toLp 2 (0, X)).snd)
            X := by
    simpa only [StrictlyPositive.ambientJArgCFC_eq_diagMapCLM
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 hp,
      HansenPedersen.Internal.diagMapCLM_sub, HansenPedersen.Internal.diagMapCLM_apply,
      WithLp.prod_inner_apply] using
      hdiag.inner_nonneg_left (WithLp.toLp 2 (0, X))
  simpa [StrictlyPositive.shiftedAmbientSecondLhs] using hx

/-- Quadratic-form form of the second-corner bound from the diagonal-core inequality:
`Re (tr (Xᴴ * shiftedAmbientSecondLhs X)) ≤ -Re (tr (Xᴴ * shiftedAmbientSecondRhsCore X))`. -/
theorem StrictlyPositive.shiftedAmbientSecond_qform_le_neg_rhsCore_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X))) ≤
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X))) := by
  have hinner :=
    StrictlyPositive.shiftedAmbientSecond_inner_nonneg_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hSch hA hB hΦ1 hdiagCore hp X
  have hinner_re :
      Complex.re
          (inner ℂ ((StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X)
            X) ≤
        -Complex.re
          (inner ℂ ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X) X) := by
    have hinner_re0 :
        0 ≤
          Complex.re
            (inner ℂ
              (-(StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X -
                (StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X)
              X) :=
      (Complex.le_def.mp hinner).1
    have hrew :
        Complex.re
            (inner ℂ
              (-(StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X -
                (StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X)
              X) =
          -Complex.re
              (inner ℂ ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X) X) +
            -Complex.re
              (inner ℂ
                ((StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X) X) := by
      simp [sub_eq_add_neg, add_comm]
    rw [hrew] at hinner_re0
    linarith
  have hrew :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X))) ≤
        -Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X))) := by
    simpa [HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun] using hinner_re
  linarith

/-- Second-corner quadratic-form bound rewritten through the contraction's adjoint: the second LHS
quadratic form at `X` is dominated by minus the shifted-codomain CFC quadratic form at
`hsAdjoint (contraction …) X`. -/
theorem StrictlyPositive.shiftedAmbientSecond_qform_le_neg_shiftedCodomain_qform_of_diagCoreAt
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X))) ≤
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X) *
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p)
              ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X)))) := by
  have hsecond :=
    StrictlyPositive.shiftedAmbientSecond_qform_le_neg_rhsCore_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hSch hA hB hΦ1 hdiagCore hp X
  simpa [StrictlyPositive.shiftedAmbientSecondRhsCore_qform_eq_shiftedCodomain_qform
    (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 (X := X)] using hsecond

/-- The first LHS quadratic form is the negation of the first positive-part CFC quadratic form:
`Re (tr (Xᴴ * shiftedAmbientFirstLhs X)) = -Re (tr (Xᴴ * ambientShiftedFirstPosCFC X))`,
since `shiftedNegFn` negates `f (· + p)` under the continuous functional calculus. -/
theorem StrictlyPositive.shiftedAmbientFirstLhs_qform_eq_neg_shiftedAmbientFirst_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ}
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) =
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) := by
  have hneg :
      StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p =
        -StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p := by
    change cfc (fun x : ℝ ↦ -((fun t : ℝ ↦ f (t + p)) x))
        (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) =
      -cfc (fun t : ℝ ↦ f (t + p))
        (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)
    simpa [StrictlyPositive.shiftedNegFn] using
      (cfc_neg (f := fun t : ℝ ↦ f (t + p))
        (a := StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1))
  have hq :=
    congrArg
      (fun T : HSOp (Nat.succ l) =>
        Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))))
      hneg
  simpa [StrictlyPositive.shiftedAmbientFirstLhs] using hq

/-- The second LHS quadratic form is the negation of the second positive-part CFC quadratic form:
`Re (tr (Xᴴ * shiftedAmbientSecondLhs X)) = -Re (tr (Xᴴ * ambientShiftedSecondPosCFC X))`,
since `shiftedNegFn` negates `f (· + p)` under the continuous functional calculus. -/
theorem StrictlyPositive.shiftedAmbientSecondLhs_qform_eq_neg_shiftedAmbientSecond_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ}
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientSecondLhs f Φ A B hPos hB hΦ1 p) X))) =
      -Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientShiftedSecondPosCFC f Φ A B hPos hB hΦ1 p) X))) := by
  have hneg :
      StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p =
        -StrictlyPositive.ambientShiftedSecondPosCFC f Φ A B hPos hB hΦ1 p := by
    change cfc (fun x : ℝ ↦ -((fun t : ℝ ↦ f (t + p)) x))
        (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) =
      -cfc (fun t : ℝ ↦ f (t + p))
        (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1)
    simpa [StrictlyPositive.shiftedNegFn] using
      (cfc_neg (f := fun t : ℝ ↦ f (t + p))
        (a := StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1))
  have hq :=
    congrArg
      (fun T : HSOp (Nat.succ k) =>
        Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))))
      hneg
  simpa [StrictlyPositive.shiftedAmbientSecondLhs] using hq

end MatrixScopedInstances

end HiaiPetz
