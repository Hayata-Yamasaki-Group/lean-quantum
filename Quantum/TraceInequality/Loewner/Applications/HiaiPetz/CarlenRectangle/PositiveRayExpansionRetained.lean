/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ScalarKubo
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.InverseTermReductionRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.PositiveRayExpansion
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai

/-!
# Carlen rectangle positive-ray expansions

This module contains the positive-ray CFC expansions before endpoint
multiplication, the three-term operator expansions, and direct G Kubo DPI.
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

/--
Explicit `G`-operator expansion gate with the endpoint and slope
Hilbert--Schmidt terms supplied by Kadison--Choi Schwarz for a unital
two-positive map.
-/
theorem gOperator_dpi_of_explicit_kubo_terms_and_isUnitalTwoPositiveMap
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {X Y : Mₙ m}
    {c b : ℝ} {KXY : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KXY.comp Ψ)) KΦ)
    (hGXY :
      gOperator f₀ X Y =
        (c : ℂ) • leftMul Y + (b : ℂ) • rightMul X + KXY)
    (hGΦ :
      gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y) =
        (c : ℂ) • leftMul (hsAdjoint Ψ Y) +
          (b : ℂ) • rightMul (hsAdjoint Ψ X) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f₀ X Y).comp Ψ))
      (gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) := by
  rcases gOperator_linear_terms_dpi_of_isUnitalTwoPositiveMap Ψ hΨ hX hY with
    ⟨hleft, hright⟩
  exact
    gOperator_dpi_of_explicit_kubo_terms Ψ hc hb
      hleft hright hkernel hGXY hGΦ

/--
Kubo--Ando representation gate for the direct `G`-DPI, once the
operator-level Kubo expansion and the integrated fixed-kernel inequality have
been supplied explicitly.
-/
theorem gOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {X Y : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    {KXY : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (h0 : 0 ≤ f₀ 0)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KXY.comp Ψ)) KΦ)
    (hGXY :
      gOperator f₀ X Y =
        (f₀ 0 : ℂ) • leftMul Y + ((rep.b : ℝ) : ℂ) • rightMul X + KXY)
    (hGΦ :
      gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y) =
        (f₀ 0 : ℂ) • leftMul (hsAdjoint Ψ Y) +
          ((rep.b : ℝ) : ℂ) • rightMul (hsAdjoint Ψ X) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f₀ X Y).comp Ψ))
      (gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
  gOperator_dpi_of_explicit_kubo_terms_and_isUnitalTwoPositiveMap
    Ψ hΨ hX hY h0 (by exact_mod_cast rep.b.property)
    hkernel hGXY hGΦ

/--
Kubo--Ando representation gate for the direct `G`-DPI when positivity on the
open positive half-line supplies the missing endpoint coefficient
nonnegativity.
-/
theorem gOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {X Y : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    {KXY : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KXY.comp Ψ)) KΦ)
    (hGXY :
      gOperator f₀ X Y =
        (f₀ 0 : ℂ) • leftMul Y + ((rep.b : ℝ) : ℂ) • rightMul X + KXY)
    (hGΦ :
      gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y) =
        (f₀ 0 : ℂ) • leftMul (hsAdjoint Ψ Y) +
          ((rep.b : ℝ) : ℂ) • rightMul (hsAdjoint Ψ X) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f₀ X Y).comp Ψ))
      (gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
  gOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms
    Ψ rep hΨ hX hY
    (positiveRayKuboAndoRep_endpoint_nonneg_of_pos rep hpos)
    hkernel hGXY hGΦ

end

end Quantum.TraceInequality.Loewner.HiaiPetz
