/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StrictlyPositive.PositiveCFC
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Standard rectangular reduction bridge

Shared notation for rectangular Hilbert--Schmidt operators.  The direct and
inverse rectangular assertions are stated directly in Mathlib's order on
continuous linear maps.

## Main results

* `DirectRectLE` and `InverseRectLE`: the direct and inverse rectangular
  assertions in Mathlib operator order.
* `hsAdjoint_directRectOp` and `hsAdjoint_inverseRectOp`: self-adjointness
  identities for the rectangular composite operators.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Section 6.1.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Rectangular Hilbert--Schmidt maps from `Nat.succ l` matrices to
`Nat.succ k` matrices, used to avoid zero-dimensional boundary cases. -/
abbrev RectReductionMap (k l : ℕ) := HSMap (Nat.succ l) (Nat.succ k)

/-- Hilbert--Schmidt endomorphisms on the positive-dimensional matrix space
indexed by `Nat.succ n`. -/
abbrev RectReductionOp (n : ℕ) := HSOp (Nat.succ n)

/-- The direct rectangular composite `V* TA V`, acting on the output-side
Hilbert--Schmidt space. -/
noncomputable def directRectOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) : RectReductionOp l :=
  (hsAdjoint V).comp (TA.comp V)

/-- The inverse rectangular composite `V TΦ⁻¹ V*`, acting on the input-side
Hilbert--Schmidt space. -/
noncomputable def inverseRectOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TΦ : RectReductionOp l) : RectReductionOp k :=
  V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))

/-- The direct rectangular inequality
`V* TA V ≤ TΦ`. -/
abbrev DirectRectLE
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  directRectOp V TA ≤ TΦ

/-- The inverse rectangular inequality
`V TΦ⁻¹ V* ≤ TA⁻¹`. -/
abbrev InverseRectLE
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  inverseRectOp V TΦ ≤ Ring.inverse TA

-- Leaving the self-adjoint assembly in the theorem body exhausts the heartbeats, so
-- it is pushed to a declaration boundary as a file-local helper.
/-- If `TA` is self-adjoint, then the direct rectangular composite
`V* TA V` is fixed by the Hilbert--Schmidt adjoint. -/
theorem hsAdjoint_directRectOp
    {k l : ℕ}
    {V : RectReductionMap k l}
    {TA : RectReductionOp k}
    (hTA_sa : IsSelfAdjoint TA) :
    hsAdjoint (directRectOp V TA) = directRectOp V TA := by
  have hTA : hsAdjoint TA = TA := by
    simpa [hsAdjoint] using hTA_sa
  have hV : hsAdjoint (hsAdjoint V) = V := by
    simp [hsAdjoint]
  calc
    hsAdjoint (directRectOp V TA)
        = (hsAdjoint (TA.comp V)).comp (hsAdjoint (hsAdjoint V)) := by
            dsimp [directRectOp, hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
                (Mₙ (Nat.succ l))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (hsAdjoint V) (TA.comp V))
    _ = ((hsAdjoint V).comp (hsAdjoint TA)).comp (hsAdjoint (hsAdjoint V)) := by
          rw [show hsAdjoint (TA.comp V) = (hsAdjoint V).comp (hsAdjoint TA) by
            dsimp [hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
                (Mₙ (Nat.succ k))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ k))
                TA V)]
    _ = directRectOp V TA := by
          rw [hV, hTA, ContinuousLinearMap.comp_assoc]
          rfl

-- The inverse side is isolated at a declaration boundary in the same way.
/-- If `TΦ⁻¹` is self-adjoint, then the inverse rectangular composite
`V TΦ⁻¹ V*` is fixed by the Hilbert--Schmidt adjoint. -/
theorem hsAdjoint_inverseRectOp
    {k l : ℕ}
    {V : RectReductionMap k l}
    {TΦ : RectReductionOp l}
    (hTΦinv_sa : IsSelfAdjoint (Ring.inverse TΦ)) :
    hsAdjoint (inverseRectOp V TΦ) = inverseRectOp V TΦ := by
  have hTΦinv : hsAdjoint (Ring.inverse TΦ) = Ring.inverse TΦ := by
    simpa [hsAdjoint] using hTΦinv_sa
  have hV : hsAdjoint (hsAdjoint V) = V := by
    simp [hsAdjoint]
  calc
    hsAdjoint (inverseRectOp V TΦ)
        = (hsAdjoint ((Ring.inverse TΦ).comp (hsAdjoint V))).comp (hsAdjoint V) := by
            dsimp [inverseRectOp, hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
                (Mₙ (Nat.succ k))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ l))
                V ((Ring.inverse TΦ).comp (hsAdjoint V)))
    _ = ((hsAdjoint (hsAdjoint V)).comp (hsAdjoint (Ring.inverse TΦ))).comp (hsAdjoint V) := by
          rw [show hsAdjoint ((Ring.inverse TΦ).comp (hsAdjoint V)) =
              (hsAdjoint (hsAdjoint V)).comp (hsAdjoint (Ring.inverse TΦ)) by
            dsimp [hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
                (Mₙ (Nat.succ l))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (Ring.inverse TΦ) (hsAdjoint V))]
    _ = inverseRectOp V TΦ := by
          rw [hV, hTΦinv, ContinuousLinearMap.comp_assoc]
          rfl

end MatrixScopedInstances

end HiaiPetz
