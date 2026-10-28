/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Operator

/-!
# Rectangular transport operator identities

Operator equalities for the rectangular transport operator `rectU V TA TΦ`, packaging its `U†U`
and `UU†` composites (and their `sqrt`/`invSqrt` sandwich forms) as single bridge lemmas so that
use sites avoid the heavy pointwise expansion of these compositions.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

-- Expanding the `U†U` form of `rectU` pointwise at use sites is heavy, so
-- confined once to the operator-equality bridge on the Core side.
/-- Operator-equality bridge for the `U†U` form of `rectU`: the sandwiched composite
`invSqrt(TΦ) ∘ V† TA V ∘ invSqrt(TΦ)` equals `(rectU V TA TΦ)† ∘ rectU V TA TΦ`. -/
theorem hsAdjoint_rectU_comp_rectU
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (_hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (hsInvSqrtPos TΦ).comp
        (((hsAdjoint V).comp (TA.comp V)).comp (hsInvSqrtPos TΦ)) =
      (hsAdjoint (rectU V TA TΦ)).comp (rectU V TA TΦ) := by
  have hsqrtTA_hadj :
      hsAdjoint (hsSqrtPos TA) = hsSqrtPos TA := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, hsSqrtPos] using
      (hsSqrtPos_isSelfAdjoint hTA_sa).star_eq
  have hinvSqrtTΦ_hadj :
      hsAdjoint (hsInvSqrtPos TΦ) = hsInvSqrtPos TΦ := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, hsInvSqrtPos] using
      (hsInvSqrtPos_isSelfAdjoint hTΦ_sa).star_eq
  have hSqrtSq : (hsSqrtPos TA).comp (hsSqrtPos TA) = TA := by
    simpa [hsSqrtPos] using hsSqrtPos_sq hTA_sa hσTA
  have hSqrtSq_apply :
      ∀ Z, hsSqrtPos TA (hsSqrtPos TA Z) = TA Z := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hSqrtSq
  have hadjU :
      hsAdjoint (rectU V TA TΦ) =
        ((hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V)).comp
          (hsAdjoint (hsSqrtPos TA)) := by
    calc
      hsAdjoint (rectU V TA TΦ)
          = hsAdjoint ((hsSqrtPos TA).comp (V.comp (hsInvSqrtPos TΦ))) := by
              rfl
      _ = (hsAdjoint (V.comp (hsInvSqrtPos TΦ))).comp
            (hsAdjoint (hsSqrtPos TA)) := by
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
                  (hsSqrtPos TA) (V.comp (hsInvSqrtPos TΦ)))
      _ = ((hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V)).comp
            (hsAdjoint (hsSqrtPos TA)) := by
              rw [show hsAdjoint (V.comp (hsInvSqrtPos TΦ)) =
                  (hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V) by
                    dsimp [hsAdjoint]
                    exact
                      (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ l))
                        (Mₙ (Nat.succ k))
                        (inferInstance : RCLike ℂ)
                        (instMatrixNormedAddCommGroup (n := Nat.succ l))
                        (instMatrixNormedAddCommGroup (n := Nat.succ l))
                        (instMatrixNormedAddCommGroup (n := Nat.succ k))
                        (instMatrixInnerProductSpace (n := Nat.succ l))
                        (instMatrixInnerProductSpace (n := Nat.succ l))
                        (instMatrixInnerProductSpace (n := Nat.succ k))
                        (instMatrixCompleteSpace (n := Nat.succ l))
                        (instMatrixCompleteSpace (n := Nat.succ k))
                        (instMatrixCompleteSpace (n := Nat.succ l))
                        V (hsInvSqrtPos TΦ))]
  rw [hadjU, hsqrtTA_hadj, hinvSqrtTΦ_hadj]
  ext X i j
  change
    (hsInvSqrtPos TΦ) ((hsAdjoint V) (TA (V ((hsInvSqrtPos TΦ) X)))) i j =
      (hsInvSqrtPos TΦ)
        ((hsAdjoint V)
          ((hsSqrtPos TA)
            ((hsSqrtPos TA) (V ((hsInvSqrtPos TΦ) X))))) i j
  rw [show TA (V ((hsInvSqrtPos TΦ) X)) =
      (hsSqrtPos TA)
        ((hsSqrtPos TA) (V ((hsInvSqrtPos TΦ) X))) by
        symm
        exact hSqrtSq_apply _]

-- Expanding the `UU†` form of `rectU` pointwise at use sites is also heavy, so
-- confined once to the operator-equality bridge on the Core side.
/-- Operator-equality bridge for the `UU†` form of `rectU`: the sandwiched composite
`sqrt(TA) ∘ V TΦ⁻¹ V† ∘ sqrt(TA)` equals `rectU V TA TΦ ∘ (rectU V TA TΦ)†`. -/
theorem rectU_comp_hsAdjoint_rectU
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (_hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (hsSqrtPos TA).comp
        ((V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))).comp (hsSqrtPos TA)) =
      (rectU V TA TΦ).comp (hsAdjoint (rectU V TA TΦ)) := by
  have hsqrtTA_hadj :
      hsAdjoint (hsSqrtPos TA) = hsSqrtPos TA := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, hsSqrtPos] using
      (hsSqrtPos_isSelfAdjoint hTA_sa).star_eq
  have hinvSqrtTΦ_hadj :
      hsAdjoint (hsInvSqrtPos TΦ) = hsInvSqrtPos TΦ := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, hsInvSqrtPos] using
      (hsInvSqrtPos_isSelfAdjoint hTΦ_sa).star_eq
  have hInvSq :
      (hsInvSqrtPos TΦ).comp (hsInvSqrtPos TΦ) = Ring.inverse TΦ := by
    simpa [hsInvSqrtPos] using
      hsInvSqrtPos_mul_self_eq_ringInverse hTΦ_sa hσTΦ
  have hInvSq_apply :
      ∀ Z, Ring.inverse TΦ Z =
        hsInvSqrtPos TΦ (hsInvSqrtPos TΦ Z) := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using (congrArg (fun S => S Z) hInvSq).symm
  have hadjU :
      hsAdjoint (rectU V TA TΦ) =
        ((hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V)).comp
          (hsAdjoint (hsSqrtPos TA)) := by
    calc
      hsAdjoint (rectU V TA TΦ)
          = hsAdjoint ((hsSqrtPos TA).comp (V.comp (hsInvSqrtPos TΦ))) := by
              rfl
      _ = (hsAdjoint (V.comp (hsInvSqrtPos TΦ))).comp
            (hsAdjoint (hsSqrtPos TA)) := by
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
                  (hsSqrtPos TA) (V.comp (hsInvSqrtPos TΦ)))
      _ = ((hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V)).comp
            (hsAdjoint (hsSqrtPos TA)) := by
              rw [show hsAdjoint (V.comp (hsInvSqrtPos TΦ)) =
                  (hsAdjoint (hsInvSqrtPos TΦ)).comp (hsAdjoint V) by
                    dsimp [hsAdjoint]
                    exact
                      (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ l))
                        (Mₙ (Nat.succ k))
                        (inferInstance : RCLike ℂ)
                        (instMatrixNormedAddCommGroup (n := Nat.succ l))
                        (instMatrixNormedAddCommGroup (n := Nat.succ l))
                        (instMatrixNormedAddCommGroup (n := Nat.succ k))
                        (instMatrixInnerProductSpace (n := Nat.succ l))
                        (instMatrixInnerProductSpace (n := Nat.succ l))
                        (instMatrixInnerProductSpace (n := Nat.succ k))
                        (instMatrixCompleteSpace (n := Nat.succ l))
                        (instMatrixCompleteSpace (n := Nat.succ k))
                        (instMatrixCompleteSpace (n := Nat.succ l))
                        V (hsInvSqrtPos TΦ))]
  rw [hadjU, hsqrtTA_hadj, hinvSqrtTΦ_hadj]
  ext X i j
  change
    (hsSqrtPos TA)
      (V ((Ring.inverse TΦ) ((hsAdjoint V) ((hsSqrtPos TA) X)))) i j =
      (hsSqrtPos TA)
        (V
          ((hsInvSqrtPos TΦ)
            ((hsInvSqrtPos TΦ) ((hsAdjoint V) ((hsSqrtPos TA) X))))) i j
  rw [show Ring.inverse TΦ ((hsAdjoint V) ((hsSqrtPos TA) X)) =
      (hsInvSqrtPos TΦ)
        ((hsInvSqrtPos TΦ) ((hsAdjoint V) ((hsSqrtPos TA) X))) by
        exact hInvSq_apply _]

-- To avoid leaving pointwise expansions at use sites on the inverse side as well,
-- a bridge returning `invSqrt(TA) * (UU†) * invSqrt(TA)` directly is placed on the Core side.
/-- Strip the `sqrt(TA)` sandwich from the `UU†` bridge:
`invSqrt(TA) ∘ (rectU ∘ rectU†) ∘ invSqrt(TA)` equals `V ∘ TΦ⁻¹ ∘ V†`. -/
theorem hsInvSqrtPos_comp_rectU_comp_hsAdjoint_rectU_comp_hsInvSqrtPos
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (hsInvSqrtPos TA).comp
        (((rectU V TA TΦ).comp (hsAdjoint (rectU V TA TΦ))).comp
          (hsInvSqrtPos TA)) =
      V.comp ((Ring.inverse TΦ).comp (hsAdjoint V)) := by
  have hcore :=
    rectU_comp_hsAdjoint_rectU
      (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hInvMulSqrt :
      (hsInvSqrtPos TA).comp (hsSqrtPos TA) = (1 : HSOp (Nat.succ k)) := by
    simpa [hsSqrtPos, hsInvSqrtPos] using
      hsInvSqrtPos_mul_sqrtPos hTA_sa hσTA
  have hSqrtMulInv :
      (hsSqrtPos TA).comp (hsInvSqrtPos TA) = (1 : HSOp (Nat.succ k)) := by
    simpa [hsSqrtPos, hsInvSqrtPos] using
      hsSqrtPos_mul_invSqrtPos hTA_sa hσTA
  have hInvMulSqrt_apply :
      ∀ Z, hsInvSqrtPos TA (hsSqrtPos TA Z) = Z := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hInvMulSqrt
  have hSqrtMulInv_apply :
      ∀ Z, hsSqrtPos TA (hsInvSqrtPos TA Z) = Z := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hSqrtMulInv
  rw [← hcore]
  ext X i j
  change
    (hsInvSqrtPos TA
      (hsSqrtPos TA
        ((V.comp ((Ring.inverse TΦ).comp (hsAdjoint V)))
          (hsSqrtPos TA (hsInvSqrtPos TA X))))) i j =
      ((V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))) X) i j
  rw [hSqrtMulInv_apply]
  rw [hInvMulSqrt_apply]

-- Assembling `sqrt(TΦ) * (U†U) * sqrt(TΦ)` at use sites is also heavy, so
-- it is confined to the Core side as a direct-side operator equality.
/-- Recover `V† TA V` by sandwiching the `U†U` bridge with `sqrt(TΦ)`:
`sqrt(TΦ) ∘ (rectU† ∘ rectU) ∘ sqrt(TΦ)` equals `V† ∘ TA ∘ V`. -/
theorem hsSqrtPos_comp_hsAdjoint_rectU_comp_rectU_comp_hsSqrtPos
    {k l : ℕ}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (hsSqrtPos TΦ).comp
        (((hsAdjoint (rectU V TA TΦ)).comp (rectU V TA TΦ)).comp
          (hsSqrtPos TΦ)) =
      (hsAdjoint V).comp (TA.comp V) := by
  have hcore :=
    hsAdjoint_rectU_comp_rectU
      (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hSqrtMulInv :
      (hsSqrtPos TΦ).comp (hsInvSqrtPos TΦ) = (1 : HSOp (Nat.succ l)) := by
    simpa [hsSqrtPos, hsInvSqrtPos] using
      hsSqrtPos_mul_invSqrtPos hTΦ_sa hσTΦ
  have hInvMulSqrt :
      (hsInvSqrtPos TΦ).comp (hsSqrtPos TΦ) = (1 : HSOp (Nat.succ l)) := by
    simpa [hsSqrtPos, hsInvSqrtPos] using
      hsInvSqrtPos_mul_sqrtPos hTΦ_sa hσTΦ
  rw [← hcore]
  ext X i j
  let Y := (hsAdjoint V) ((TA.comp V) X)
  have hInner :
      hsInvSqrtPos TΦ (hsSqrtPos TΦ X) = X := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S X) hInvMulSqrt
  have hOuter :
      hsSqrtPos TΦ (hsInvSqrtPos TΦ Y) = Y := by
    simpa [Y, ContinuousLinearMap.comp_apply] using congrArg (fun S => S Y) hSqrtMulInv
  change
    (hsSqrtPos TΦ
      (hsInvSqrtPos TΦ
        (((hsAdjoint V).comp (TA.comp V))
          (hsInvSqrtPos TΦ (hsSqrtPos TΦ X))))) i j =
      (((hsAdjoint V).comp (TA.comp V)) X) i j
  rw [hInner]
  simpa [Y, ContinuousLinearMap.comp_apply] using congrArg (fun Z => Z i j) hOuter

end MatrixScopedInstances
end HiaiPetz
