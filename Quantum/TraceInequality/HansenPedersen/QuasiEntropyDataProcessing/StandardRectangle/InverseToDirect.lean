/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.HilbertSchmidt.Contractive
import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StrictlyPositive.PositiveCFC
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Transport
-- Shared rectangular map and endomorphism types.
import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Definitions
import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm

/-!
# Inverse-to-direct rectangular core

Core operator-order argument converting the inverse rectangular inequality into
the direct rectangular inequality for strictly positive Hilbert--Schmidt
operators.  The proof introduces the normalized rectangular map `U`, derives
`UU* ≤ 1`, transfers contractivity to `U*U ≤ 1`, and conjugates by square roots
to recover the direct inequality.

## Main results

* `directCoreRectUUstar_le_one_of_inverseRectLE`: inverse order implies `UU* ≤ 1`.
* `directCoreRectUstarU_le_one_of_uUstar_le_one`: contractivity transfer
  from `UU*` to `U*U`.
* `directRectLE_of_directCoreRectUstarU_le_one`: `U*U ≤ 1` implies the direct
  rectangular inequality.

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

/-- Normalized rectangular transport map `U` used in the inverse-to-direct
core argument.  It is the `rectU` construction specialized to positive
dimensions. -/
noncomputable def directCoreRectUDef
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionMap k l :=
  rectU V TA TΦ

/-- The output-side contraction operator `U*U` associated with
`directCoreRectUDef`. -/
noncomputable def directCoreRectUstarUOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionOp l :=
  let U : RectReductionMap k l := directCoreRectUDef V TA TΦ
  (hsAdjoint U).comp U

/-- The input-side contraction operator `UU*` associated with
`directCoreRectUDef`. -/
noncomputable def directCoreRectUUstarOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionOp k :=
  let U : RectReductionMap k l := directCoreRectUDef V TA TΦ
  U.comp (hsAdjoint U)

/-- Direct rectangular composite `V* TA V` used by the core proof before it is
translated to the bridge API. -/
noncomputable def directCoreDirectRectOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) : RectReductionOp l :=
  (hsAdjoint V).comp (TA.comp V)

/-- Inverse rectangular composite `V TΦ⁻¹ V*` used by the core proof before it
is translated to the bridge API. -/
noncomputable def directCoreInverseRectOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TΦ : RectReductionOp l) : RectReductionOp k :=
  V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))

private abbrev DirectCoreRectUUstarLeOne
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  directCoreRectUUstarOp V TA TΦ ≤ 1

private abbrev DirectCoreRectUstarULeOne
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  directCoreRectUstarUOp V TA TΦ ≤ 1

private abbrev DirectCoreDirectRectLe
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  directCoreDirectRectOp V TA ≤ TΦ

private abbrev DirectCoreInverseRectLe
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  directCoreInverseRectOp V TΦ ≤ Ring.inverse TA

/-- From the inverse rectangular operator inequality, conjugating by `TA^(1/2)`
identifies the normalized input-side operator and yields `UU* ≤ 1`. -/
theorem directCoreRectUUstar_le_one_of_inverseRectLE
    {k l : ℕ}
    {TA : RectReductionOp k} {TΦ : RectReductionOp l}
    (V : RectReductionMap k l)
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ))
    (hrect_le : DirectCoreInverseRectLe V TA TΦ) :
    DirectCoreRectUUstarLeOne V TA TΦ := by
  let sqrtTA : RectReductionOp k := hsSqrtPos TA
  let invSqrtTΦ : RectReductionOp l := hsInvSqrtPos TΦ
  let U : RectReductionMap k l := directCoreRectUDef V TA TΦ
  have hsqrtTA_sa : IsSelfAdjoint sqrtTA := by
    simpa [sqrtTA] using hsSqrtPos_isSelfAdjoint hTA_sa
  have hconj :
      sqrtTA * directCoreInverseRectOp V TΦ * sqrtTA ≤
        sqrtTA * Ring.inverse TA * sqrtTA := by
    simpa [hsqrtTA_sa.star_eq] using star_left_conjugate_le_conjugate hrect_le sqrtTA
  have hleft :
      sqrtTA * directCoreInverseRectOp V TΦ * sqrtTA =
        directCoreRectUUstarOp V TA TΦ := by
    simpa [sqrtTA, invSqrtTΦ, directCoreInverseRectOp, directCoreRectUUstarOp,
      directCoreRectUDef, U, hsAdjoint, ContinuousLinearMap.comp_assoc] using
      rectU_comp_hsAdjoint_rectU
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      sqrtTA * Ring.inverse TA * sqrtTA = (1 : RectReductionOp k) := by
    ext X
    simp [sqrtTA,
      hsSqrtPos_mul_ringInverse_mul_sqrtPos_eq_one hTA_sa hσTA]
  rw [hleft, hright] at hconj
  exact hconj

/-- If the normalized map satisfies `UU* ≤ 1`, then its adjoint side also
satisfies `U*U ≤ 1`; the proof passes through the contractivity of `U*`. -/
theorem directCoreRectUstarU_le_one_of_uUstar_le_one
    {k l : ℕ}
    {TA : RectReductionOp k} {TΦ : RectReductionOp l}
    (V : RectReductionMap k l)
    (hUUstar : DirectCoreRectUUstarLeOne V TA TΦ) :
    DirectCoreRectUstarULeOne V TA TΦ := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  let U : RectReductionMap k l := directCoreRectUDef V TA TΦ
  let F : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l) := hsAdjoint U
  let Fraw : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l) := F
  let Fadj : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k) := hsAdjoint F
  let FstarF : RectReductionOp k := Fadj.comp Fraw
  let FFstar : RectReductionOp l := Fraw.comp Fadj
  have hFstarF : FstarF ≤ 1 := by
    simpa [FstarF, Fadj, Fraw, F, directCoreRectUUstarOp, U, directCoreRectUDef, hsAdjoint]
      using hUUstar
  have hF_contract : ∀ x : Mₙ (Nat.succ k), ‖F x‖ ≤ ‖x‖ := by
    intro x
    have hx_op :
        Complex.re (Matrix.trace (Matrix.conjTranspose x * (FstarF x))) ≤
          Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ k)) x))) := by
      exact hsQForm_le_of_le hFstarF x
    have hFx_sq :
        ‖F x‖ ^ 2 =
          Complex.re (Matrix.trace (Matrix.conjTranspose x * (FstarF x))) := by
      simpa [FstarF, Fadj, Fraw, F, hsAdjoint] using
        (HiaiPetz.AmbientSubmodule.hsQForm_hsAdjoint_comp_eq_norm_sq F x).symm
    have hx_sq :
        Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ k)) x))) =
          ‖x‖ ^ 2 := by
      calc
        Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ k)) x)))
            = Complex.re (inner ℂ ((1 : HSOp (Nat.succ k)) x) x) := by
                rw [hsQForm_real_eq_inner_real]
        _ = (↑(‖x‖ ^ 2) : ℂ).re := by
              simp [inner_self_eq_norm_sq_to_K]
        _ = ‖x‖ ^ 2 := by
              rw [Complex.ofReal_re]
    have hx : ‖F x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have hx' := hx_op
      rw [← hFx_sq, hx_sq] at hx'
      exact hx'
    nlinarith [norm_nonneg (F x), norm_nonneg x, hx]
  have hFFstar : FFstar ≤ 1 := by
    refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      FFstar (1 : HSOp (Nat.succ l)) ?_ ?_
    · have hFFstar_nonneg : 0 ≤ (FFstar : HSOp (Nat.succ l)) := by
        exact ((@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ (Nat.succ l))
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := Nat.succ l))
          (instMatrixInnerProductSpace (n := Nat.succ l))
          (FFstar : HSOp (Nat.succ l))).2 (by
            simpa [FFstar, Fadj, Fraw, F, hsAdjoint] using
              HiaiPetz.Core.self_comp_hsAdjoint_isPositive F))
      exact IsSelfAdjoint.sub (IsSelfAdjoint.one _) (IsSelfAdjoint.of_nonneg hFFstar_nonneg)
    · intro y
      have hsq :
          ‖Fadj y‖ ^ 2 =
            Complex.re (Matrix.trace (Matrix.conjTranspose y * (FFstar y))) := by
        simpa [FFstar, Fadj, Fraw, F, hsAdjoint] using
          (HiaiPetz.AmbientSubmodule.hsQForm_comp_hsAdjoint_eq_norm_sq F y).symm
      have hFy : ‖Fadj y‖ ≤ ‖y‖ := by
        simpa [Fadj] using hsAdjoint_contract_of_contract F hF_contract y
      have hy_sq : ‖Fadj y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
        nlinarith [norm_nonneg (Fadj y), norm_nonneg y, hFy]
      have hone : RCLike.re (inner ℂ ((1 : HSOp (Nat.succ l)) y) y) = ‖y‖ ^ 2 := by
        calc
          RCLike.re (inner ℂ ((1 : HSOp (Nat.succ l)) y) y)
              = (↑(‖y‖ ^ 2) : ℂ).re := by
                  simp [inner_self_eq_norm_sq_to_K]
          _ = ‖y‖ ^ 2 := by
                rw [Complex.ofReal_re]
      have hy_eval :
          RCLike.re (inner ℂ (((1 : HSOp (Nat.succ l)) - FFstar) y) y) =
            ‖y‖ ^ 2 - ‖Fadj y‖ ^ 2 := by
        have hsq_inner : RCLike.re (inner ℂ (FFstar y) y) = ‖Fadj y‖ ^ 2 := by
          have hsq' := hsq
          rw [hsQForm_real_eq_inner_real (T := FFstar) y] at hsq'
          simpa using hsq'.symm
        calc
          RCLike.re (inner ℂ (((1 : HSOp (Nat.succ l)) - FFstar) y) y)
              = RCLike.re (inner ℂ ((1 : HSOp (Nat.succ l)) y) y) -
                RCLike.re (inner ℂ (FFstar y) y) := by
                  simp [ContinuousLinearMap.sub_apply, Complex.sub_re]
          _ = ‖y‖ ^ 2 - ‖Fadj y‖ ^ 2 := by
                rw [hone, hsq_inner]
      rw [hy_eval]
      linarith
  simpa [DirectCoreRectUstarULeOne, directCoreRectUstarUOp, U, FFstar, Fadj, Fraw, F,
    directCoreRectUDef, hsAdjoint] using hFFstar

/-- Conjugating `U*U ≤ 1` by `TΦ^(1/2)` reconstructs the direct rectangular
operator inequality `V* TA V ≤ TΦ`. -/
theorem directRectLE_of_directCoreRectUstarU_le_one
    {k l : ℕ}
    {TA : RectReductionOp k} {TΦ : RectReductionOp l}
    (V : RectReductionMap k l)
    (hTA_sa : IsSelfAdjoint TA)
    (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ))
    (hUstarU : DirectCoreRectUstarULeOne V TA TΦ) :
    DirectCoreDirectRectLe V TA TΦ := by
  let sqrtTA : RectReductionOp k := hsSqrtPos TA
  let sqrtTΦ : RectReductionOp l := hsSqrtPos TΦ
  let invSqrtTΦ : RectReductionOp l := hsInvSqrtPos TΦ
  let U : RectReductionMap k l := directCoreRectUDef V TA TΦ
  have hsqrtTΦ_sa : IsSelfAdjoint sqrtTΦ := by
    simpa [sqrtTΦ] using hsSqrtPos_isSelfAdjoint hTΦ_sa
  have hUstarU' : directCoreRectUstarUOp V TA TΦ ≤ 1 := by
    simpa [directCoreRectUstarUOp, U, directCoreRectUDef, hsAdjoint] using hUstarU
  have hconj :
      sqrtTΦ * directCoreRectUstarUOp V TA TΦ * sqrtTΦ ≤
        sqrtTΦ * (1 : RectReductionOp l) * sqrtTΦ := by
    simpa [hsqrtTΦ_sa.star_eq] using star_left_conjugate_le_conjugate hUstarU' sqrtTΦ
  have hleft :
      sqrtTΦ * directCoreRectUstarUOp V TA TΦ * sqrtTΦ =
        directCoreDirectRectOp V TA := by
    simpa [sqrtTΦ, directCoreRectUstarUOp, directCoreDirectRectOp,
      directCoreRectUDef, U, hsAdjoint, ContinuousLinearMap.comp_assoc] using
      hsSqrtPos_comp_hsAdjoint_rectU_comp_rectU_comp_hsSqrtPos
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      sqrtTΦ * (1 : RectReductionOp l) * sqrtTΦ = TΦ := by
    ext X
    simp [sqrtTΦ,
      hsSqrtPos_sq hTΦ_sa hσTΦ]
  rw [hleft, hright] at hconj
  exact hconj

end MatrixScopedInstances

end HiaiPetz
