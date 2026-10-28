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
import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Definitions
import Quantum.TraceInequality.HansenPedersen.StrictlyPositive.PositiveCFC
import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm

/-!
# Direct-to-inverse rectangular core

Core operator-order argument converting the direct rectangular inequality into
the inverse rectangular inequality for strictly positive Hilbert--Schmidt
operators.  The proof uses the normalized rectangular map `U`, obtains
`U*U ≤ 1`, transfers contractivity to `UU* ≤ 1`, and then conjugates by inverse
square roots to recover the inverse inequality.

## Main results

* `invUstarURectUstarU_le_one_of_directRectLE`: direct order implies `U*U ≤ 1`.
* `invAdjointRectUUstar_le_one_of_uStarU_le_one`: contractivity transfer
  from `U*U` to `UU*`.
* `inverseRectLE_of_invUUStarCoreRectUUstar_le_one`: `UU* ≤ 1` implies the inverse
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

private noncomputable def invUstarURectU
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionMap k l :=
  rectU V TA TΦ

private noncomputable def invUstarURectUstarUOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionOp l :=
  let U : RectReductionMap k l := invUstarURectU V TA TΦ
  (hsAdjoint U).comp U

private noncomputable def invUstarUDirectRectOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (_TΦ : RectReductionOp l) :
    RectReductionOp l :=
  (hsAdjoint V).comp (TA.comp V)

private noncomputable def InvUstarURectUstarULeOne
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  invUstarURectUstarUOp V TA TΦ ≤ 1

private noncomputable def InvUstarUDirectRectLe
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  invUstarUDirectRectOp V TA TΦ ≤ TΦ

/-- From the direct rectangular operator inequality, conjugating by `TΦ^(-1/2)`
identifies the normalized output-side operator and yields `U*U ≤ 1`. -/
theorem invUstarURectUstarU_le_one_of_directRectLE
    {k l : ℕ}
    {TA : RectReductionOp k} {TΦ : RectReductionOp l}
    (V : RectReductionMap k l)
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ))
    (hrect_le : InvUstarUDirectRectLe V TA TΦ) :
    InvUstarURectUstarULeOne V TA TΦ := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  let sqrtTA : RectReductionOp k := hsSqrtPos TA
  let invSqrtTΦ : RectReductionOp l := hsInvSqrtPos TΦ
  let U : RectReductionMap k l := invUstarURectU V TA TΦ
  have hinvSqrtTΦ_sa : IsSelfAdjoint invSqrtTΦ := by
    simpa [invSqrtTΦ] using hsInvSqrtPos_isSelfAdjoint hTΦ_sa
  have hSqrtSq : sqrtTA.comp sqrtTA = TA := by
    simpa [sqrtTA] using hsSqrtPos_sq hTA_sa hσTA
  have hSqrtSq_apply :
      ∀ Z, sqrtTA (sqrtTA Z) = TA Z := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hSqrtSq
  have hconj :
      invSqrtTΦ * invUstarUDirectRectOp V TA TΦ * invSqrtTΦ ≤
        invSqrtTΦ * TΦ * invSqrtTΦ := by
    simpa [InvUstarUDirectRectLe, invUstarUDirectRectOp,
      hinvSqrtTΦ_sa.star_eq] using
      star_left_conjugate_le_conjugate hrect_le invSqrtTΦ
  have hleft :
      invSqrtTΦ * invUstarUDirectRectOp V TA TΦ * invSqrtTΦ =
        invUstarURectUstarUOp V TA TΦ := by
    simpa [U, invUstarUDirectRectOp, invUstarURectUstarUOp,
      invUstarURectU,
      invSqrtTΦ, ContinuousLinearMap.comp_assoc]
      using hsAdjoint_rectU_comp_rectU
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      invSqrtTΦ * TΦ * invSqrtTΦ = (1 : HSOp (Nat.succ l)) := by
    simpa [invSqrtTΦ, hsAdjoint, hinvSqrtTΦ_sa.star_eq, ContinuousLinearMap.comp_assoc] using
      hsInvSqrtPos_mul_self_mul_invSqrtPos_eq_one hTΦ_sa hσTΦ
  rw [hleft, hright] at hconj
  exact hconj

private noncomputable def invAdjointRectU
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionMap k l :=
  rectU V TA TΦ

private noncomputable def invAdjointRectUstarUOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionOp l :=
  let U : RectReductionMap k l := invAdjointRectU V TA TΦ
  (hsAdjoint U).comp U

private noncomputable def invAdjointRectUUstarOp
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) :
    RectReductionOp k :=
  let U : RectReductionMap k l := invAdjointRectU V TA TΦ
  U.comp (hsAdjoint U)

private abbrev InvAdjointRectUstarULeOne
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  invAdjointRectUstarUOp V TA TΦ ≤ 1

private abbrev InvAdjointRectUUstarLeOne
    {k l : ℕ}
    (V : RectReductionMap k l)
    (TA : RectReductionOp k) (TΦ : RectReductionOp l) : Prop :=
  invAdjointRectUUstarOp V TA TΦ ≤ 1

/-- If the normalized map satisfies `U*U ≤ 1`, then its input-side product
also satisfies `UU* ≤ 1`; the proof uses contractivity of `U` and of its
Hilbert--Schmidt adjoint. -/
theorem invAdjointRectUUstar_le_one_of_uStarU_le_one
    {k l : ℕ}
    {TA : RectReductionOp k} {TΦ : RectReductionOp l}
    (V : RectReductionMap k l)
    (hUstarU : InvAdjointRectUstarULeOne V TA TΦ) :
    InvAdjointRectUUstarLeOne V TA TΦ := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  let U : RectReductionMap k l := invAdjointRectU V TA TΦ
  let Uraw : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k) := U
  let Uadj : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l) := hsAdjoint U
  let UstarU : RectReductionOp l := Uadj.comp Uraw
  let UUstar : RectReductionOp k := Uraw.comp Uadj
  have hUstarU' : UstarU ≤ 1 := by
    simpa [UstarU, Uadj, Uraw, invAdjointRectUstarUOp, U,
      invAdjointRectU, hsAdjoint] using hUstarU
  have hU_contract : ∀ x : Mₙ (Nat.succ l), ‖U x‖ ≤ ‖x‖ := by
    intro x
    have hx_op :
        Complex.re (Matrix.trace (Matrix.conjTranspose x * (UstarU x))) ≤
          Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ l)) x))) := by
      exact hsQForm_le_of_le hUstarU' x
    have hUx_sq :
        ‖U x‖ ^ 2 =
          Complex.re (Matrix.trace (Matrix.conjTranspose x * (UstarU x))) := by
      simpa [UstarU, Uadj, Uraw, hsAdjoint] using
        (HiaiPetz.AmbientSubmodule.hsQForm_hsAdjoint_comp_eq_norm_sq U x).symm
    have hx_sq :
        Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ l)) x))) =
          ‖x‖ ^ 2 := by
      calc
        Complex.re (Matrix.trace (Matrix.conjTranspose x * ((1 : HSOp (Nat.succ l)) x)))
            = Complex.re (inner ℂ ((1 : HSOp (Nat.succ l)) x) x) := by
                rw [hsQForm_real_eq_inner_real]
        _ = (↑(‖x‖ ^ 2) : ℂ).re := by
              simp [inner_self_eq_norm_sq_to_K]
        _ = ‖x‖ ^ 2 := by
              rw [Complex.ofReal_re]
    have hx :
        ‖U x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have hx' := hx_op
      rw [← hUx_sq, hx_sq] at hx'
      exact hx'
    nlinarith [norm_nonneg (U x), norm_nonneg x, hx]
  have hUUstar : UUstar ≤ 1 := by
    refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ k))
      UUstar (1 : HSOp (Nat.succ k)) ?_ ?_
    · have hUself :
          IsSelfAdjoint (UUstar : HSOp (Nat.succ k)) := by
        have hUUstar_nonneg : 0 ≤ (UUstar : HSOp (Nat.succ k)) := by
          exact ((@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ (Nat.succ k))
            (inferInstance : RCLike ℂ)
            (instMatrixNormedAddCommGroup (n := Nat.succ k))
            (instMatrixInnerProductSpace (n := Nat.succ k))
            (UUstar : HSOp (Nat.succ k))).2 (by
              simpa [UUstar, Uadj, Uraw, hsAdjoint] using
                HiaiPetz.Core.self_comp_hsAdjoint_isPositive U))
        exact IsSelfAdjoint.of_nonneg hUUstar_nonneg
      exact IsSelfAdjoint.sub
        (IsSelfAdjoint.one _)
        hUself
    · intro y
      have hsq :
          ‖Uadj y‖ ^ 2 =
            Complex.re (Matrix.trace (Matrix.conjTranspose y * (UUstar y))) := by
        simpa [UUstar, Uadj, Uraw, hsAdjoint] using
          (HiaiPetz.AmbientSubmodule.hsQForm_comp_hsAdjoint_eq_norm_sq U y).symm
      have hUy : ‖Uadj y‖ ≤ ‖y‖ := by
        simpa [Uadj] using hsAdjoint_contract_of_contract U hU_contract y
      have hy_sq : ‖Uadj y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
        nlinarith [norm_nonneg (Uadj y), norm_nonneg y, hUy]
      have hone : RCLike.re (inner ℂ ((1 : HSOp (Nat.succ k)) y) y) = ‖y‖ ^ 2 := by
        calc
          RCLike.re (inner ℂ ((1 : HSOp (Nat.succ k)) y) y)
              = (↑(‖y‖ ^ 2) : ℂ).re := by
                  simp [inner_self_eq_norm_sq_to_K]
          _ = ‖y‖ ^ 2 := by
                rw [Complex.ofReal_re]
      have hy_eval :
          RCLike.re (inner ℂ (((1 : HSOp (Nat.succ k)) - UUstar) y) y) =
            ‖y‖ ^ 2 - ‖Uadj y‖ ^ 2 := by
        have hsq_inner : RCLike.re (inner ℂ (UUstar y) y) = ‖Uadj y‖ ^ 2 := by
          have hsq' := hsq
          rw [hsQForm_real_eq_inner_real (T := UUstar) y] at hsq'
          simpa using hsq'.symm
        calc
          RCLike.re (inner ℂ (((1 : HSOp (Nat.succ k)) - UUstar) y) y)
              = RCLike.re (inner ℂ ((1 : HSOp (Nat.succ k)) y) y) -
                RCLike.re (inner ℂ (UUstar y) y) := by
                  simp [ContinuousLinearMap.sub_apply, Complex.sub_re]
          _ = ‖y‖ ^ 2 - ‖Uadj y‖ ^ 2 := by
                rw [hone, hsq_inner]
      rw [hy_eval]
      linarith
  simpa [InvAdjointRectUUstarLeOne, invAdjointRectUUstarOp, U, UUstar] using
    hUUstar

/-- The input-side normalized operator `UU*` built from `rectU`; this is the
quantity bounded by one before inverse-square-root conjugation. -/
noncomputable def invUUStarCoreRectUUstarOp
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (TA : HSOp (Nat.succ k)) (TΦ : HSOp (Nat.succ l)) :
    HSOp (Nat.succ k) :=
  (rectU V TA TΦ).comp (hsAdjoint (rectU V TA TΦ))

/-- Core proposition asserting the normalized input-side operator satisfies
`UU* ≤ 1`. -/
abbrev invUUStarCoreRectUUstarExpr
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (TA : HSOp (Nat.succ k)) (TΦ : HSOp (Nat.succ l)) : Prop :=
  invUUStarCoreRectUUstarOp V TA TΦ ≤ 1

/-- Bridge-facing alias for the normalized `UU* ≤ 1` proposition. -/
abbrev invUUStarRectUUstarExpr
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (TA : HSOp (Nat.succ k)) (TΦ : HSOp (Nat.succ l)) : Prop :=
  invUUStarCoreRectUUstarExpr V TA TΦ

/-- Direct rectangular operator order implies the normalized `UU* ≤ 1`
condition used by the inverse reconstruction step. -/
theorem invUUStarRectUUstar_le_one_of_directRectLE
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ))
    (hrect_le : DirectRectLE V TA TΦ) :
    invUUStarCoreRectUUstarExpr V TA TΦ := by
  have hUstarU :=
    invUstarURectUstarU_le_one_of_directRectLE
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ (by
        simpa [DirectRectLE, directRectOp] using hrect_le)
  have hUUstar :=
    invAdjointRectUUstar_le_one_of_uStarU_le_one (V := V) hUstarU
  simpa [invUUStarCoreRectUUstarExpr, invUUStarCoreRectUUstarOp] using hUUstar

/-- The direct rectangular assertion in Mathlib operator order, together with
positivity and invertibility hypotheses, implies the normalized `UU* ≤ 1`
condition. -/
theorem invUUStarRectUUstar_le_one_of_directRectLE_of_nonneg
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA0 : 0 ≤ TA) (hTΦ0 : 0 ≤ TΦ)
    (hTAu : IsUnit TA) (hTΦu : IsUnit TΦ) :
    DirectRectLE V TA TΦ →
      invUUStarRectUUstarExpr V TA TΦ := by
  intro hrect
  have hTA_sa : IsSelfAdjoint TA := IsSelfAdjoint.of_nonneg hTA0
  have hTΦ_sa : IsSelfAdjoint TΦ := IsSelfAdjoint.of_nonneg hTΦ0
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTA0 hTAu
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTΦ0 hTΦu
  simpa [invUUStarRectUUstarExpr, invUUStarCoreRectUUstarExpr, invUUStarCoreRectUUstarOp] using
    invUUStarRectUUstar_le_one_of_directRectLE
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ hrect

end MatrixScopedInstances

private noncomputable def invCoreInverseRectOp
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (TΦ : HSOp (Nat.succ l)) : HSOp (Nat.succ k) :=
  V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))

private abbrev InvCoreInverseRectLe
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (TA : HSOp (Nat.succ k)) (TΦ : HSOp (Nat.succ l)) : Prop :=
  invCoreInverseRectOp V TΦ ≤ Ring.inverse TA

/-- Left-hand reconstruction identity: conjugating the normalized `UU*`
operator by `TA^(-1/2)` gives `V TΦ⁻¹ V*`. -/
theorem invUUStarCoreRectUUstarOp_conj_eq
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    hsInvSqrtPos TA *
        invUUStarCoreRectUUstarOp V TA TΦ *
        hsInvSqrtPos TA =
      V.comp ((Ring.inverse TΦ).comp (hsAdjoint V)) := by
  simpa [invUUStarCoreRectUUstarOp] using
    hsInvSqrtPos_comp_rectU_comp_hsAdjoint_rectU_comp_hsInvSqrtPos
      (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ

/-- Conjugating the bound `UU* ≤ 1` by `TA^(-1/2)` preserves operator order
and gives the comparison needed for the inverse inequality. -/
theorem invUUStarCoreRectUUstarOp_conj_le
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA_sa : IsSelfAdjoint TA) (_hTΦ_sa : IsSelfAdjoint TΦ)
    (hUUstar : invUUStarCoreRectUUstarExpr V TA TΦ) :
    hsInvSqrtPos TA *
        invUUStarCoreRectUUstarOp V TA TΦ *
        hsInvSqrtPos TA ≤
      hsInvSqrtPos TA * (1 : HSOp (Nat.succ k)) * hsInvSqrtPos TA := by
  let invSqrtTA : HSOp (Nat.succ k) := hsInvSqrtPos TA
  have hinvSqrtTA_sa : IsSelfAdjoint invSqrtTA := by
    simpa [invSqrtTA] using hsInvSqrtPos_isSelfAdjoint hTA_sa
  have hUUstar' : invUUStarCoreRectUUstarOp V TA TΦ ≤ 1 := by
    simpa [invUUStarCoreRectUUstarExpr] using hUUstar
  change invSqrtTA * invUUStarCoreRectUUstarOp V TA TΦ * invSqrtTA ≤
      invSqrtTA * (1 : HSOp (Nat.succ k)) * invSqrtTA
  simpa [invSqrtTA, hinvSqrtTA_sa.star_eq] using
    star_left_conjugate_le_conjugate hUUstar' invSqrtTA

/-- Final direct-to-inverse core step: the normalized `UU* ≤ 1` condition
reconstructs `V TΦ⁻¹ V* ≤ TA⁻¹`. -/
theorem inverseRectLE_of_invUUStarCoreRectUUstar_le_one
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ))
    (hUUstar : invUUStarCoreRectUUstarExpr V TA TΦ) :
    InvCoreInverseRectLe V TA TΦ := by
  have hconj :
      hsInvSqrtPos TA *
          invUUStarCoreRectUUstarOp V TA TΦ *
          hsInvSqrtPos TA ≤
        hsInvSqrtPos TA * (1 : HSOp (Nat.succ k)) * hsInvSqrtPos TA :=
    invUUStarCoreRectUUstarOp_conj_le
      (V := V) hTA_sa hTΦ_sa hUUstar
  have hleft :
      hsInvSqrtPos TA *
          invUUStarCoreRectUUstarOp V TA TΦ *
          hsInvSqrtPos TA =
        V.comp ((Ring.inverse TΦ).comp (hsAdjoint V)) :=
    invUUStarCoreRectUUstarOp_conj_eq
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      hsInvSqrtPos TA * (1 : HSOp (Nat.succ k)) * hsInvSqrtPos TA =
        Ring.inverse TA :=
    HiaiPetz.PositiveCFC.hsInvSqrtPos_mul_one_mul_self_eq_ringInverse hTA_sa hσTA
  rw [hleft, hright] at hconj
  exact hconj

end HiaiPetz
