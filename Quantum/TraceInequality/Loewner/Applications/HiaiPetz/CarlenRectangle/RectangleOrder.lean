/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.ConditionIToLoewner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.PositiveInverse
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.Infrastructure

-- positive-part decomposition for positive maps

/-!
# Carlen rectangle order conversion

This module contains the rectangle-order conversion stage of the Carlen 2022
Theorem 1.46 argument: inverse/direct rectangle order equivalence and the
Carlen condition (2)/(3) equivalence for the G-operator.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instCarlenRectangleHSOpCStarAlgebra
  instCarlenRectangleHSOpPartialOrder
  instCarlenRectangleHSOpStarRing
  instCarlenRectangleHSOpStarOrderedRing
  instCarlenRectangleComplexCFC
  instCarlenRectangleRealCFC
  instCarlenRectangleHSOpNonnegSpectrumClass
  instCarlenRectangleHSOpSMulZeroClass
  instCarlenRectangleHSOpIsBoundedSMul
  instCarlenRectangleHSOpContinuousSMul
  instCarlenRectangleHSOpRealAlgebra
  instCarlenRectangleHSOpRealRealTower

noncomputable section

/-! ### Inverse-form rectangle order implies direct rectangle order -/
-- Pointwise Hilbert--Schmidt adjoint expansion for the normalized rectangle.
/--
The adjoint-square of Carlen's normalized rectangle `U` expands to the inverse
rectangle conjugated by `TΦ^{-1/2}`. This is the square-root rectangle algebra
used in Carlen's operator-monotonicity route [carlen2022].
-/
theorem hsAdjoint_carlenRectU_comp_carlenRectU {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (_hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (carlenRectInvSqrt TΦ).comp
        (((hsAdjoint V).comp (TA.comp V)).comp (carlenRectInvSqrt TΦ)) =
      (hsAdjoint (carlenRectU V TA TΦ)).comp (carlenRectU V TA TΦ) := by
  have hsqrtTA_hadj :
      hsAdjoint (carlenRectSqrt TA) = carlenRectSqrt TA := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, carlenRectSqrt] using
      (carlenRectSqrt_isSelfAdjoint hTA_sa).star_eq
  have hinvSqrtTΦ_hadj :
      hsAdjoint (carlenRectInvSqrt TΦ) = carlenRectInvSqrt TΦ := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, carlenRectInvSqrt] using
      (carlenRectInvSqrt_isSelfAdjoint hTΦ_sa).star_eq
  have hSqrtSq : (carlenRectSqrt TA).comp (carlenRectSqrt TA) = TA := by
    simpa [carlenRectSqrt] using carlenRectSqrt_sq hTA_sa hσTA
  have hSqrtSq_apply :
      ∀ Z, carlenRectSqrt TA (carlenRectSqrt TA Z) = TA Z := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hSqrtSq
  have hadjU :
      hsAdjoint (carlenRectU V TA TΦ) =
        ((hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V)).comp
          (hsAdjoint (carlenRectSqrt TA)) := by
    calc
      hsAdjoint (carlenRectU V TA TΦ)
          = hsAdjoint ((carlenRectSqrt TA).comp (V.comp (carlenRectInvSqrt TΦ))) := by
              rfl
      _ = (hsAdjoint (V.comp (carlenRectInvSqrt TΦ))).comp
            (hsAdjoint (carlenRectSqrt TA)) := by
              dsimp [hsAdjoint]
              exact
                (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ m) (Mₙ m)
                  (inferInstance : RCLike ℂ)
                  (instMatrixNormedAddCommGroup (n := n))
                  (instMatrixNormedAddCommGroup (n := m))
                  (instMatrixNormedAddCommGroup (n := m))
                  (instMatrixInnerProductSpace (n := n))
                  (instMatrixInnerProductSpace (n := m))
                  (instMatrixInnerProductSpace (n := m))
                  (instMatrixCompleteSpace (n := n))
                  (instMatrixCompleteSpace (n := m))
                  (instMatrixCompleteSpace (n := m))
                  (carlenRectSqrt TA) (V.comp (carlenRectInvSqrt TΦ)))
      _ = ((hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V)).comp
            (hsAdjoint (carlenRectSqrt TA)) := by
              rw [show hsAdjoint (V.comp (carlenRectInvSqrt TΦ)) =
                  (hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V) by
                    dsimp [hsAdjoint]
                    exact
                      (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ n) (Mₙ m)
                        (inferInstance : RCLike ℂ)
                        (instMatrixNormedAddCommGroup (n := n))
                        (instMatrixNormedAddCommGroup (n := n))
                        (instMatrixNormedAddCommGroup (n := m))
                        (instMatrixInnerProductSpace (n := n))
                        (instMatrixInnerProductSpace (n := n))
                        (instMatrixInnerProductSpace (n := m))
                        (instMatrixCompleteSpace (n := n))
                        (instMatrixCompleteSpace (n := m))
                        (instMatrixCompleteSpace (n := n))
                        V (carlenRectInvSqrt TΦ))]
  rw [hadjU, hsqrtTA_hadj, hinvSqrtTΦ_hadj]
  ext X i j
  change
    (carlenRectInvSqrt TΦ) ((hsAdjoint V) (TA (V ((carlenRectInvSqrt TΦ) X)))) i j =
      (carlenRectInvSqrt TΦ)
        ((hsAdjoint V)
          ((carlenRectSqrt TA) ((carlenRectSqrt TA) (V ((carlenRectInvSqrt TΦ) X))))) i j
  rw [show TA (V ((carlenRectInvSqrt TΦ) X)) =
      (carlenRectSqrt TA)
        ((carlenRectSqrt TA) (V ((carlenRectInvSqrt TΦ) X))) by
        symm
        exact hSqrtSq_apply _]

/--
The product `U U†` of Carlen's normalized rectangle expands to the inverse
rectangle between two copies of `TA^{1/2}`. This is the companion square-root
identity for the rectangle argument [carlen2022].
-/
theorem carlenRectU_comp_hsAdjoint_carlenRectU {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (_hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (carlenRectSqrt TA).comp
        ((carlenRectInverseOp V TΦ).comp (carlenRectSqrt TA)) =
      (carlenRectU V TA TΦ).comp (hsAdjoint (carlenRectU V TA TΦ)) := by
  have hsqrtTA_hadj :
      hsAdjoint (carlenRectSqrt TA) = carlenRectSqrt TA := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, carlenRectSqrt] using
      (carlenRectSqrt_isSelfAdjoint hTA_sa).star_eq
  have hinvSqrtTΦ_hadj :
      hsAdjoint (carlenRectInvSqrt TΦ) = carlenRectInvSqrt TΦ := by
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint, carlenRectInvSqrt] using
      (carlenRectInvSqrt_isSelfAdjoint hTΦ_sa).star_eq
  have hInvSq :
      (carlenRectInvSqrt TΦ).comp (carlenRectInvSqrt TΦ) = Ring.inverse TΦ := by
    simpa [carlenRectInvSqrt] using
      carlenRectInvSqrt_mul_self_eq_ringInverse hTΦ_sa hσTΦ
  have hInvSq_apply :
      ∀ Z, Ring.inverse TΦ Z =
        carlenRectInvSqrt TΦ (carlenRectInvSqrt TΦ Z) := by
    intro Z
    simpa [ContinuousLinearMap.comp_apply] using (congrArg (fun S => S Z) hInvSq).symm
  have hadjU :
      hsAdjoint (carlenRectU V TA TΦ) =
        ((hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V)).comp
          (hsAdjoint (carlenRectSqrt TA)) := by
    calc
      hsAdjoint (carlenRectU V TA TΦ)
          = hsAdjoint ((carlenRectSqrt TA).comp (V.comp (carlenRectInvSqrt TΦ))) := by
              rfl
      _ = (hsAdjoint (V.comp (carlenRectInvSqrt TΦ))).comp
            (hsAdjoint (carlenRectSqrt TA)) := by
              dsimp [hsAdjoint]
              exact
                (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ m) (Mₙ m)
                  (inferInstance : RCLike ℂ)
                  (instMatrixNormedAddCommGroup (n := n))
                  (instMatrixNormedAddCommGroup (n := m))
                  (instMatrixNormedAddCommGroup (n := m))
                  (instMatrixInnerProductSpace (n := n))
                  (instMatrixInnerProductSpace (n := m))
                  (instMatrixInnerProductSpace (n := m))
                  (instMatrixCompleteSpace (n := n))
                  (instMatrixCompleteSpace (n := m))
                  (instMatrixCompleteSpace (n := m))
                  (carlenRectSqrt TA) (V.comp (carlenRectInvSqrt TΦ)))
      _ = ((hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V)).comp
            (hsAdjoint (carlenRectSqrt TA)) := by
              rw [show hsAdjoint (V.comp (carlenRectInvSqrt TΦ)) =
                  (hsAdjoint (carlenRectInvSqrt TΦ)).comp (hsAdjoint V) by
                    dsimp [hsAdjoint]
                    exact
                      (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ n) (Mₙ m)
                        (inferInstance : RCLike ℂ)
                        (instMatrixNormedAddCommGroup (n := n))
                        (instMatrixNormedAddCommGroup (n := n))
                        (instMatrixNormedAddCommGroup (n := m))
                        (instMatrixInnerProductSpace (n := n))
                        (instMatrixInnerProductSpace (n := n))
                        (instMatrixInnerProductSpace (n := m))
                        (instMatrixCompleteSpace (n := n))
                        (instMatrixCompleteSpace (n := m))
                        (instMatrixCompleteSpace (n := n))
                        V (carlenRectInvSqrt TΦ))]
  rw [hadjU, hsqrtTA_hadj, hinvSqrtTΦ_hadj]
  ext X i j
  change
    (carlenRectSqrt TA)
      (V ((Ring.inverse TΦ) ((hsAdjoint V) ((carlenRectSqrt TA) X)))) i j =
      (carlenRectSqrt TA)
        (V
          ((carlenRectInvSqrt TΦ)
            ((carlenRectInvSqrt TΦ) ((hsAdjoint V) ((carlenRectSqrt TA) X))))) i j
  rw [show Ring.inverse TΦ ((hsAdjoint V) ((carlenRectSqrt TA) X)) =
      (carlenRectInvSqrt TΦ)
        ((carlenRectInvSqrt TΦ) ((hsAdjoint V) ((carlenRectSqrt TA) X))) by
        exact hInvSq_apply _]

/--
Conjugating `U† U` by `TΦ^{1/2}` recovers the direct rectangle operator
`V† TA V`. This is the algebraic normalization step in the Carlen rectangle
proof [carlen2022].
-/
theorem carlenRectSqrt_comp_hsAdjoint_U_comp_U_comp_sqrt {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    (carlenRectSqrt TΦ).comp
        (((hsAdjoint (carlenRectU V TA TΦ)).comp (carlenRectU V TA TΦ)).comp
          (carlenRectSqrt TΦ)) =
      (hsAdjoint V).comp (TA.comp V) := by
  have hcore :=
    hsAdjoint_carlenRectU_comp_carlenRectU
      (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hSqrtMulInv :
      (carlenRectSqrt TΦ).comp (carlenRectInvSqrt TΦ) = (1 : HSOp n) := by
    simpa [carlenRectSqrt, carlenRectInvSqrt] using
      carlenRectSqrt_mul_invSqrt hTΦ_sa hσTΦ
  have hInvMulSqrt :
      (carlenRectInvSqrt TΦ).comp (carlenRectSqrt TΦ) = (1 : HSOp n) := by
    simpa [carlenRectSqrt, carlenRectInvSqrt] using
      carlenRectInvSqrt_mul_sqrt hTΦ_sa hσTΦ
  rw [← hcore]
  ext X i j
  let Y := (hsAdjoint V) ((TA.comp V) X)
  have hInner :
      carlenRectInvSqrt TΦ (carlenRectSqrt TΦ X) = X := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun S => S X) hInvMulSqrt
  have hOuter :
      carlenRectSqrt TΦ (carlenRectInvSqrt TΦ Y) = Y := by
    simpa [Y, ContinuousLinearMap.comp_apply] using congrArg (fun S => S Y) hSqrtMulInv
  change
    (carlenRectSqrt TΦ
      (carlenRectInvSqrt TΦ
        (((hsAdjoint V).comp (TA.comp V))
          (carlenRectInvSqrt TΦ (carlenRectSqrt TΦ X))))) i j =
      (((hsAdjoint V).comp (TA.comp V)) X) i j
  rw [hInner]
  simpa [Y, ContinuousLinearMap.comp_apply] using congrArg (fun Z => Z i j) hOuter

/--
An inverse-form rectangle inequality implies the corresponding direct-form
rectangle inequality. This is Carlen's square-root rectangle flip
[carlen2022].
-/
theorem carlenRectangle_inverse_to_direct_of_le {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectInverseOp V TΦ ≤ Ring.inverse TA →
      carlenRectDirectOp V TA ≤ TΦ := by
  intro hrect_le
  let sqrtTA : HSOp m := carlenRectSqrt TA
  let sqrtTΦ : HSOp n := carlenRectSqrt TΦ
  let U : HSMap n m := carlenRectU V TA TΦ
  have hsqrtTA_sa : IsSelfAdjoint sqrtTA := by
    simpa [sqrtTA] using carlenRectSqrt_isSelfAdjoint hTA_sa
  have hconj :
      sqrtTA * carlenRectInverseOp V TΦ * sqrtTA ≤
        sqrtTA * Ring.inverse TA * sqrtTA := by
    simpa [hsqrtTA_sa.star_eq] using
      (@star_left_conjugate_le_conjugate (HSOp m)
        (inferInstance : NonUnitalSemiring (HSOp m))
        (instCarlenRectangleHSOpPartialOrder (n := m))
        (instCarlenRectangleHSOpStarRing (n := m))
        (instCarlenRectangleHSOpStarOrderedRing (n := m))
        (a := carlenRectInverseOp V TΦ) (b := Ring.inverse TA)
        hrect_le sqrtTA)
  have hleft :
      sqrtTA * carlenRectInverseOp V TΦ * sqrtTA = U.comp (hsAdjoint U) := by
    simpa [sqrtTA, U, carlenRectU, ContinuousLinearMap.comp_assoc] using
      carlenRectU_comp_hsAdjoint_carlenRectU
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      sqrtTA * Ring.inverse TA * sqrtTA = (1 : HSOp m) := by
    ext X
    simp [sqrtTA, carlenRectSqrt_mul_ringInverse_mul_sqrt_eq_one hTA_sa hσTA]
  have hUUstar : U.comp (hsAdjoint U) ≤ 1 := by
    rw [hleft, hright] at hconj
    exact hconj
  have hUstarU : (hsAdjoint U).comp U ≤ 1 := by
    have hraw :=
      @clm_self_comp_adjoint_le_one_of_adjoint_comp_self_le_one
        (Mₙ m) (Mₙ n)
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := m))
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (hsAdjoint U)
        (by
          have hdouble : hsAdjoint (hsAdjoint U) = U := by
            simp [hsAdjoint]
          simpa [hsAdjoint, hdouble] using hUUstar)
    simpa [hsAdjoint] using hraw
  have hsqrtTΦ_sa : IsSelfAdjoint sqrtTΦ := by
    simpa [sqrtTΦ] using carlenRectSqrt_isSelfAdjoint hTΦ_sa
  have hconj_final :
      sqrtTΦ * ((hsAdjoint U).comp U) * sqrtTΦ ≤
        sqrtTΦ * (1 : HSOp n) * sqrtTΦ := by
    simpa [hsqrtTΦ_sa.star_eq] using
      (@star_left_conjugate_le_conjugate (HSOp n)
        (inferInstance : NonUnitalSemiring (HSOp n))
        (instCarlenRectangleHSOpPartialOrder (n := n))
        (instCarlenRectangleHSOpStarRing (n := n))
        (instCarlenRectangleHSOpStarOrderedRing (n := n))
        (a := (hsAdjoint U).comp U) (b := (1 : HSOp n))
        hUstarU sqrtTΦ)
  have hleft_final :
      sqrtTΦ * ((hsAdjoint U).comp U) * sqrtTΦ = carlenRectDirectOp V TA := by
    simpa [sqrtTΦ, U, carlenRectDirectOp, ContinuousLinearMap.comp_assoc] using
      carlenRectSqrt_comp_hsAdjoint_U_comp_U_comp_sqrt
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright_final :
      sqrtTΦ * (1 : HSOp n) * sqrtTΦ = TΦ := by
    ext X
    simp [sqrtTΦ, carlenRectSqrt_sq hTΦ_sa hσTΦ]
  rw [hleft_final, hright_final] at hconj_final
  exact hconj_final

/--
The standard square-root rectangle step: inverse-form Hilbert--Schmidt order
implies direct Hilbert--Schmidt order for positive invertible endpoint
operators.
-/
theorem carlenRectangle_inverse_to_direct {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    HSLE (carlenRectInverseOp V TΦ) (Ring.inverse TA) →
      HSLE (carlenRectDirectOp V TA) TΦ := by
  intro hrect
  exact HSLE_of_le
    (carlenRectangle_inverse_to_direct_of_le V hTA_sa hTΦ_sa hσTA hσTΦ
      (carlenRectangle_inverse_HSLE_to_le hTA_sa hTΦ_sa hσTA hσTΦ hrect))

/-! ### Direct rectangle order implies inverse-form rectangle order -/
/-- The inverse square root conjugates `T` to the identity on positive spectrum. -/
theorem carlenRectInvSqrt_mul_self_mul_invSqrt_eq_one {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectInvSqrt T * T * carlenRectInvSqrt T = (1 : HSOp n) := by
  have hsq : carlenRectSqrt T * carlenRectSqrt T = T :=
    carlenRectSqrt_sq hT hσT
  calc
    carlenRectInvSqrt T * T * carlenRectInvSqrt T
        = carlenRectInvSqrt T * (carlenRectSqrt T * carlenRectSqrt T) *
            carlenRectInvSqrt T := by rw [hsq]
    _ = (carlenRectInvSqrt T * carlenRectSqrt T) *
        (carlenRectSqrt T * carlenRectInvSqrt T) := by
              rw [← mul_assoc, mul_assoc (carlenRectInvSqrt T * carlenRectSqrt T)
                (carlenRectSqrt T) (carlenRectInvSqrt T)]
    _ = 1 := by
          rw [carlenRectInvSqrt_mul_sqrt hT hσT, carlenRectSqrt_mul_invSqrt hT hσT,
            one_mul]

/--
For self-adjoint rectangle data, Hilbert-Schmidt quadratic order implies the
ambient Loewner order for the direct rectangle.
-/
theorem carlenRectangle_direct_HSLE_to_le {n m : ℕ}
    {V : HSMap n m} {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ) :
    HSLE (carlenRectDirectOp V TA) TΦ → carlenRectDirectOp V TA ≤ TΦ := by
  intro hrect
  have hdirect_sa : IsSelfAdjoint (carlenRectDirectOp V TA) := by
    have hAdj : hsAdjoint (carlenRectDirectOp V TA) = carlenRectDirectOp V TA := by
      calc
        hsAdjoint (carlenRectDirectOp V TA)
            = (hsAdjoint (TA.comp V)).comp (hsAdjoint (hsAdjoint V)) := by
                dsimp [carlenRectDirectOp, hsAdjoint]
                exact
                  (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ m) (Mₙ n)
                    (inferInstance : RCLike ℂ)
                    (instMatrixNormedAddCommGroup (n := n))
                    (instMatrixNormedAddCommGroup (n := m))
                    (instMatrixNormedAddCommGroup (n := n))
                    (instMatrixInnerProductSpace (n := n))
                    (instMatrixInnerProductSpace (n := m))
                    (instMatrixInnerProductSpace (n := n))
                    (instMatrixCompleteSpace (n := n))
                    (instMatrixCompleteSpace (n := n))
                    (instMatrixCompleteSpace (n := m))
                    (hsAdjoint V) (TA.comp V))
        _ = ((hsAdjoint V).comp (hsAdjoint TA)).comp V := by
              rw [show hsAdjoint (TA.comp V) = (hsAdjoint V).comp (hsAdjoint TA) by
                dsimp [hsAdjoint]
                exact
                  (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ n) (Mₙ m) (Mₙ m)
                    (inferInstance : RCLike ℂ)
                    (instMatrixNormedAddCommGroup (n := n))
                    (instMatrixNormedAddCommGroup (n := m))
                    (instMatrixNormedAddCommGroup (n := m))
                    (instMatrixInnerProductSpace (n := n))
                    (instMatrixInnerProductSpace (n := m))
                    (instMatrixInnerProductSpace (n := m))
                    (instMatrixCompleteSpace (n := n))
                    (instMatrixCompleteSpace (n := m))
                    (instMatrixCompleteSpace (n := m))
                    TA V)]
              rw [show hsAdjoint (hsAdjoint V) = V by
                simp [hsAdjoint]]
        _ = carlenRectDirectOp V TA := by
              have hTA_adj : hsAdjoint TA = TA := by
                simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint] using hTA_sa.star_eq
              rw [hTA_adj]
              rfl
    simpa [hsAdjoint, ContinuousLinearMap.star_eq_adjoint] using hAdj
  exact le_of_HSLE_of_isSelfAdjoint hrect (IsSelfAdjoint.sub hTΦ_sa hdirect_sa)

/--
A direct-form rectangle inequality implies the inverse-form rectangle
inequality. This is the reverse square-root rectangle flip [carlen2022].
-/
theorem carlenRectangle_direct_to_inverse_of_le {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectDirectOp V TA ≤ TΦ →
      carlenRectInverseOp V TΦ ≤ Ring.inverse TA := by
  intro hrect_le
  let invSqrtTA : HSOp m := carlenRectInvSqrt TA
  let invSqrtTΦ : HSOp n := carlenRectInvSqrt TΦ
  let U : HSMap n m := carlenRectU V TA TΦ
  have hinvSqrtTΦ_sa : IsSelfAdjoint invSqrtTΦ := by
    simpa [invSqrtTΦ] using carlenRectInvSqrt_isSelfAdjoint hTΦ_sa
  have hconj :
      invSqrtTΦ * carlenRectDirectOp V TA * invSqrtTΦ ≤
        invSqrtTΦ * TΦ * invSqrtTΦ := by
    simpa [hinvSqrtTΦ_sa.star_eq] using
      (@star_left_conjugate_le_conjugate (HSOp n)
        (inferInstance : NonUnitalSemiring (HSOp n))
        (instCarlenRectangleHSOpPartialOrder (n := n))
        (instCarlenRectangleHSOpStarRing (n := n))
        (instCarlenRectangleHSOpStarOrderedRing (n := n))
        (a := carlenRectDirectOp V TA) (b := TΦ)
        hrect_le invSqrtTΦ)
  have hleft :
      invSqrtTΦ * carlenRectDirectOp V TA * invSqrtTΦ =
        (hsAdjoint U).comp U := by
    simpa [invSqrtTΦ, U, carlenRectDirectOp, ContinuousLinearMap.comp_assoc] using
      hsAdjoint_carlenRectU_comp_carlenRectU
        (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
  have hright :
      invSqrtTΦ * TΦ * invSqrtTΦ = (1 : HSOp n) := by
    ext X
    simp [invSqrtTΦ, carlenRectInvSqrt_mul_self_mul_invSqrt_eq_one hTΦ_sa hσTΦ]
  have hUstarU : (hsAdjoint U).comp U ≤ 1 := by
    rw [hleft, hright] at hconj
    exact hconj
  have hUUstar : U.comp (hsAdjoint U) ≤ 1 := by
    have hraw :=
      @clm_self_comp_adjoint_le_one_of_adjoint_comp_self_le_one
        (Mₙ n) (Mₙ m)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := m))
        U
        (by simpa [hsAdjoint] using hUstarU)
    simpa [hsAdjoint] using hraw
  have hinvSqrtTA_sa : IsSelfAdjoint invSqrtTA := by
    simpa [invSqrtTA] using carlenRectInvSqrt_isSelfAdjoint hTA_sa
  have hconj_final :
      invSqrtTA * (U.comp (hsAdjoint U)) * invSqrtTA ≤
        invSqrtTA * (1 : HSOp m) * invSqrtTA := by
    simpa [hinvSqrtTA_sa.star_eq] using
      (@star_left_conjugate_le_conjugate (HSOp m)
        (inferInstance : NonUnitalSemiring (HSOp m))
        (instCarlenRectangleHSOpPartialOrder (n := m))
        (instCarlenRectangleHSOpStarRing (n := m))
        (instCarlenRectangleHSOpStarOrderedRing (n := m))
        (a := U.comp (hsAdjoint U)) (b := (1 : HSOp m))
        hUUstar invSqrtTA)
  have hleft_final :
      invSqrtTA * (U.comp (hsAdjoint U)) * invSqrtTA =
        carlenRectInverseOp V TΦ := by
    have hcore :
        (carlenRectSqrt TA).comp ((carlenRectInverseOp V TΦ).comp (carlenRectSqrt TA)) =
          U.comp (hsAdjoint U) := by
      simpa [U] using
        carlenRectU_comp_hsAdjoint_carlenRectU
          (V := V) (TA := TA) (TΦ := TΦ) hTA_sa hTΦ_sa hσTA hσTΦ
    rw [← hcore]
    ext X i j
    have hInvMulSqrt :
        ∀ Z, invSqrtTA (carlenRectSqrt TA Z) = Z := by
      intro Z
      have hmul :
          (carlenRectInvSqrt TA).comp (carlenRectSqrt TA) = (1 : HSOp m) := by
        simpa [carlenRectInvSqrt, carlenRectSqrt] using
          carlenRectInvSqrt_mul_sqrt hTA_sa hσTA
      simpa [invSqrtTA, ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hmul
    have hSqrtMulInv :
        ∀ Z, carlenRectSqrt TA (invSqrtTA Z) = Z := by
      intro Z
      have hmul :
          (carlenRectSqrt TA).comp (carlenRectInvSqrt TA) = (1 : HSOp m) := by
        simpa [carlenRectInvSqrt, carlenRectSqrt] using
          carlenRectSqrt_mul_invSqrt hTA_sa hσTA
      simpa [invSqrtTA, ContinuousLinearMap.comp_apply] using congrArg (fun S => S Z) hmul
    change
      invSqrtTA
        (carlenRectSqrt TA
          (carlenRectInverseOp V TΦ (carlenRectSqrt TA (invSqrtTA X)))) i j =
        (carlenRectInverseOp V TΦ X) i j
    rw [hSqrtMulInv X, hInvMulSqrt (carlenRectInverseOp V TΦ X)]
  have hright_final :
      invSqrtTA * (1 : HSOp m) * invSqrtTA = Ring.inverse TA := by
    ext X
    simp [invSqrtTA, carlenRectInvSqrt_mul_self_eq_ringInverse hTA_sa hσTA]
  rw [hleft_final, hright_final] at hconj_final
  exact hconj_final

/--
The reverse square-root rectangle step: direct Hilbert--Schmidt order implies
inverse-form Hilbert--Schmidt order for positive invertible endpoint
operators.
-/
theorem carlenRectangle_direct_to_inverse {n m : ℕ}
    (V : HSMap n m) {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    HSLE (carlenRectDirectOp V TA) TΦ →
      HSLE (carlenRectInverseOp V TΦ) (Ring.inverse TA) := by
  intro hrect
  exact HSLE_of_le
    (carlenRectangle_direct_to_inverse_of_le V hTA_sa hTΦ_sa hσTA hσTΦ
      (carlenRectangle_direct_HSLE_to_le hTA_sa hTΦ_sa hrect))

/-! ### G-operator positivity and Carlen condition (2)/(3) equivalence -/
/-- `G_f(X,Y)` is self-adjoint under Carlen's positivity and continuity hypotheses. -/
theorem gOperator_isSelfAdjoint_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsSelfAdjoint (gOperator f X Y) :=
  @IsStrictlyPositive.isSelfAdjoint (HSOp n)
    inferInstance
    (instCarlenRectangleHSOpPartialOrder (n := n))
    (instCarlenRectangleHSOpStarRing (n := n))
    (instCarlenRectangleHSOpStarOrderedRing (n := n))
    (gOperator f X Y)
    (gOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY)

/-- `G_f(X,Y)` has positive real spectrum under Carlen's function hypotheses. -/
theorem gOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    spectrum ℝ (gOperator f X Y) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (gOperator f X Y)
      (gOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY) x hx

/--
The theorem-facing inverse `G_f⁻¹(X,Y)` is the ring inverse of `G_f(X,Y)`
under Carlen's positivity and continuity hypotheses.
-/
theorem gOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gOperatorInv f X Y = Ring.inverse (gOperator f X Y) := by
  have hleft :
      gOperatorInv f X Y * gOperator f X Y = 1 :=
    gOperatorInv_mul_gOperator_eq_one_of_carlenFunctionHypothesis hf hX hY
  have hright :
      gOperator f X Y * Ring.inverse (gOperator f X Y) = 1 :=
    Ring.mul_inverse_cancel (gOperator f X Y)
      (gOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hX hY).isUnit
  exact left_inv_eq_right_inv hleft hright

/--
Pointwise equivalence between Carlen's inverse-form and direct-form
data-processing inequalities for `G_f`.
-/
theorem gOperator_inverse_dpi_iff_direct_dpi_of_carlenFunctionHypothesis
    {n m : ℕ} (Φ : HSMap n m) {f : ℝ → ℝ} {X Y : Mₙ m}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hΦX : MatrixPosDef (hsAdjoint Φ X))
    (hΦY : MatrixPosDef (hsAdjoint Φ Y)) :
    HSLE
      (Φ.comp
        ((gOperatorInv f (hsAdjoint Φ X) (hsAdjoint Φ Y)).comp (hsAdjoint Φ)))
      (gOperatorInv f X Y)
      ↔
    HSLE
      ((hsAdjoint Φ).comp ((gOperator f X Y).comp Φ))
      (gOperator f (hsAdjoint Φ X) (hsAdjoint Φ Y)) := by
  let TA : HSOp m := gOperator f X Y
  let TΦ : HSOp n := gOperator f (hsAdjoint Φ X) (hsAdjoint Φ Y)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using gOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hX hY
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using gOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦX hΦY
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using gOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hX hY
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using
      gOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦX hΦY
  have hInvTA : Ring.inverse TA = gOperatorInv f X Y := by
    simpa [TA] using
      (gOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hX hY).symm
  have hInvTΦ :
      Ring.inverse TΦ = gOperatorInv f (hsAdjoint Φ X) (hsAdjoint Φ Y) := by
    simpa [TΦ] using
      (gOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦX hΦY).symm
  constructor
  · intro hinv
    have hrect : HSLE (carlenRectInverseOp Φ TΦ) (Ring.inverse TA) := by
      simpa [carlenRectInverseOp, TA, TΦ, hInvTA, hInvTΦ] using hinv
    have hdirect : HSLE (carlenRectDirectOp Φ TA) TΦ :=
      carlenRectangle_inverse_to_direct Φ hTA_sa hTΦ_sa hσTA hσTΦ hrect
    simpa [carlenRectDirectOp, TA, TΦ] using hdirect
  · intro hdirect
    have hrect : HSLE (carlenRectDirectOp Φ TA) TΦ := by
      simpa [carlenRectDirectOp, TA, TΦ] using hdirect
    have hinv : HSLE (carlenRectInverseOp Φ TΦ) (Ring.inverse TA) :=
      carlenRectangle_direct_to_inverse Φ hTA_sa hTΦ_sa hσTA hσTΦ hrect
    simpa [carlenRectInverseOp, TA, TΦ, hInvTA, hInvTΦ] using hinv

end

end Quantum.TraceInequality.Loewner.HiaiPetz
