/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.BochnerDPI
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions

/-!
# Carlen rectangle condition I stage

This module contains the theorem-facing Carlen rectangle declarations moved
from the aggregate rectangle file.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

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

/-! ### Condition I to direct DPI on G and J surfaces -/
/-- Real CFC on `gArg` only depends on the function over the positive ray. -/
theorem hsCfcR_gArg_congr_on_positive {n : ℕ} {f g : ℝ → ℝ} {X Y : Mₙ n}
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = g x)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    hsCfcR f (gArg X Y) = hsCfcR g (gArg X Y) := by
  apply cfc_congr
  intro x hx
  exact hfg (gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY hx)

/-- `G_f(X,Y)` only depends on `f` over the positive spectrum of `gArg X Y`. -/
theorem gOperator_congr_on_positive {n : ℕ} {f g : ℝ → ℝ} {X Y : Mₙ n}
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = g x)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gOperator f X Y = gOperator g X Y := by
  unfold gOperator
  rw [hsCfcR_gArg_congr_on_positive hfg hX hY]

/-- Real CFC on `jArg` only depends on the function over the positive ray. -/
theorem hsCfcR_jArg_congr_on_positive {n : ℕ} {f g : ℝ → ℝ} {A B : Mₙ n}
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = g x)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsCfcR f (jArg A B) = hsCfcR g (jArg A B) := by
  apply cfc_congr
  intro x hx
  exact hfg (jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB hx)

/-- `J_f(A,B)` only depends on `f` over the positive spectrum of `jArg A B`. -/
theorem jOperator_congr_on_positive {n : ℕ} {f g : ℝ → ℝ} {A B : Mₙ n}
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = g x)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    jOperator f A B = jOperator g A B := by
  change hsCfcR f (jArg A B) * rightMul B = hsCfcR g (jArg A B) * rightMul B
  rw [hsCfcR_jArg_congr_on_positive hfg hA hB]

/--
Loewner-native condition I gives the strict direct `J_f` DPI when the endpoint
terms are supplied by Schwarz and the fixed-kernel route is supplied by an
explicit pointwise inverse-form kernel DPI.

This theorem takes the inverse-form kernel input as a hypothesis instead of
deriving it from the Schwarz inequality, and shows that this input is the only
further operator inequality needed to reach the direct `J_f` DPI.  In the
strict-output setting of `StrictOutput.lean` the corresponding input is supplied
by `pointwiseInvKernelInput_of_hsAdjointSchwarz_outputs`.
-/
theorem jOperator_dpi_of_loewnerConditionI_pointwiseInvKernel_schwarzMap
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hf : LoewnerConditionI f)
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hstar : ∀ X : Mₙ n, Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X))
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x)
    (hkernelInv :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          (Ψ.comp
            ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
              (hsAdjoint Ψ)))
          (jKuboKernelInvForm t A B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
      (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  rcases loewnerConditionI_to_positiveRayKuboAndoRep hf with
    ⟨f₀, hagree, ⟨rep⟩⟩
  have hpos₀ : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x := by
    intro x hx
    rw [hagree hx]
    exact hpos hx
  have hkernel :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
          (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
    intro t ht
    exact jKuboKernel_dpi_of_invForm_HSLE_and_matrixPosDef
      Ψ ht hA hB hΨA hΨB (hkernelInv ht)
  have hbase :
      HSLE
        ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
        (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jOperator_dpi_of_positiveRayKuboAndoRep_pointwiseKernel_schwarzMap
      Ψ rep hSch hstar hA hB hΨA hΨB hpos₀ hkernel
      (by
        intro k X Y hX hY
        exact weighted_jKuboKernel_integrable_of_positiveRayKuboAndoRep rep hX hY)
      (by
        intro k X Y hX hY
        exact positiveRayKuboAndoRep_hsCfcR_preright_expansion rep hX hY)
  have hAB : jOperator f₀ A B = jOperator f A B :=
    jOperator_congr_on_positive hagree hA hB
  have hΨAB :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B) :=
    jOperator_congr_on_positive hagree hΨA hΨB
  simpa [hAB, hΨAB] using hbase

/-! ### Named J inverse and strict unital-adjoint DPI package -/
/-- The Hiai--Petz CFC argument commutes with the endpoint right multiplication `R_B`. -/
theorem jArg_commute_rightMul_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hB : MatrixPosDef B) :
    Commute (jArg A B) (rightMul B : HSOp n) := by
  rw [commute_iff_eq]
  calc
    jArg A B * (rightMul B : HSOp n) = leftMul A :=
      jArg_mul_rightMul_of_matrixPosDef hB
    _ = (rightMul B : HSOp n) * jArg A B := by
      rw [jArg_eq_rightMul_mul_leftMul]
      calc
        leftMul A
            = ((rightMul B : HSOp n) * rightMul (posInv B)) * leftMul A := by
                rw [rightMul_mul_rightMul_posInv_of_matrixPosDef hB, one_mul]
        _ = (rightMul B : HSOp n) * (rightMul (posInv B) * leftMul A) := by
              rw [mul_assoc]

/-- The Hiai--Petz CFC argument commutes with `R_{B⁻¹}`. -/
theorem jArg_commute_rightMul_posInv {n : ℕ} (A B : Mₙ n) :
    Commute (jArg A B) (rightMul (posInv B) : HSOp n) := by
  rw [commute_iff_eq]
  ext X i j
  simp [jArg, ContinuousLinearMap.mul_apply, posInv, Matrix.mul_assoc]

/--
Applying a positive continuous function to the positive Hiai--Petz CFC argument
is strictly positive.
-/
theorem hsCfcR_jArg_isStrictlyPositive_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsStrictlyPositive (hsCfcR f (jArg A B)) := by
  have hσ : spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hcont : ContinuousOn f (spectrum ℝ (jArg A B)) :=
    hf.1.mono hσ
  have hstrict : IsStrictlyPositive (jArg A B) :=
    jArg_isStrictlyPositive_of_matrixPosDef hA hB
  have hsa : IsSelfAdjoint (jArg A B) :=
    @IsStrictlyPositive.isSelfAdjoint (HSOp n)
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarRing (n := n))
      (instCarlenRectangleHSOpStarOrderedRing (n := n))
      (jArg A B) hstrict
  rw [hsCfcR]
  exact
    (@cfc_isStrictlyPositive_iff ℝ (HSOp n) IsSelfAdjoint
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpStarRing (n := n))
      (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      f (jArg A B) hcont hsa).mpr
      (fun x hx => hf.2 (hσ hx))

/-- The real CFC inverse formula for `f(jArg A B)` under Carlen's function hypothesis. -/
theorem hsCfcR_inv_jArg_eq_inverse_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg A B) =
      Ring.inverse (hsCfcR f (jArg A B)) := by
  have hσ : spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hcont : ContinuousOn f (spectrum ℝ (jArg A B)) :=
    hf.1.mono hσ
  have hnonzero : ∀ x ∈ spectrum ℝ (jArg A B), f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hf.2 (hσ hx))
  have hstrict : IsStrictlyPositive (jArg A B) :=
    jArg_isStrictlyPositive_of_matrixPosDef hA hB
  have hsa : IsSelfAdjoint (jArg A B) :=
    @IsStrictlyPositive.isSelfAdjoint (HSOp n)
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarRing (n := n))
      (instCarlenRectangleHSOpStarOrderedRing (n := n))
      (jArg A B) hstrict
  simpa [hsCfcR] using
    (cfc_inv (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (f := f) (a := jArg A B) hnonzero (hf := hcont) (ha := hsa))

/-- The theorem-facing Hiai--Petz perspective operator `J_f(A,B)` is strictly positive. -/
theorem jOperator_isStrictlyPositive_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsStrictlyPositive (jOperator f A B) := by
  have hF : IsStrictlyPositive (hsCfcR f (jArg A B)) :=
    hsCfcR_jArg_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB
  have hR : IsStrictlyPositive (rightMul B : HSOp n) :=
    rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hB)
  have hcomm : Commute (hsCfcR f (jArg A B)) (rightMul B : HSOp n) := by
    simpa [hsCfcR] using
      (jArg_commute_rightMul_of_matrixPosDef (A := A) hB).cfc_real f
  have hprod : IsStrictlyPositive (hsCfcR f (jArg A B) * rightMul B : HSOp n) :=
    (@IsStrictlyPositive.commute_iff (HSOp n)
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarRing (n := n))
      (instCarlenRectangleHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (hsCfcR f (jArg A B)) (rightMul B : HSOp n) hF hR).mp hcomm
  simpa [jOperator] using hprod

/-- `J_f(A,B)` is self-adjoint under Carlen's positivity and continuity hypotheses. -/
theorem jOperator_isSelfAdjoint_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsSelfAdjoint (jOperator f A B) :=
  @IsStrictlyPositive.isSelfAdjoint (HSOp n)
    inferInstance
    (instCarlenRectangleHSOpPartialOrder (n := n))
    (instCarlenRectangleHSOpStarRing (n := n))
    (instCarlenRectangleHSOpStarOrderedRing (n := n))
    (jOperator f A B)
    (jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB)

/-- `J_f(A,B)` has positive real spectrum under Carlen's positivity and continuity hypotheses. -/
theorem jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    spectrum ℝ (jOperator f A B) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (jOperator f A B)
      (jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB) x hx

/-- `J_f(A,B)` is a unit under Carlen's positivity and continuity hypotheses. -/
theorem jOperator_isUnit_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsUnit (jOperator f A B) :=
  (jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB).isUnit

/-- The theorem-facing inverse is a left inverse of `J_f(A,B)`. -/
theorem jOperatorInv_mul_jOperator_eq_one_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    jOperatorInv f A B * jOperator f A B = 1 := by
  let F : HSOp n := hsCfcR f (jArg A B)
  let Finv : HSOp n := hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg A B)
  let R : HSOp n := rightMul B
  let Rinv : HSOp n := rightMul (posInv B)
  have hFinv : Finv = Ring.inverse F := by
    simpa [F, Finv] using
      hsCfcR_inv_jArg_eq_inverse_of_carlenFunctionHypothesis hf hA hB
  have hFunit : IsUnit F :=
    (hsCfcR_jArg_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB).isUnit
  have hRinvR : Rinv * R = 1 := by
    simpa [R, Rinv] using rightMul_posInv_mul_rightMul_of_matrixPosDef hB
  have hFinvF : Finv * F = 1 := by
    rw [hFinv]
    exact Ring.inverse_mul_cancel F hFunit
  have hcomm : Commute F Rinv := by
    simpa [F, Rinv, hsCfcR] using
      (jArg_commute_rightMul_posInv A B).cfc_real f
  calc
    jOperatorInv f A B * jOperator f A B
        = (Finv * Rinv) * (F * R) := by
            rfl
    _ = (Finv * F) * (Rinv * R) := by
          calc
            (Finv * Rinv) * (F * R)
                = Finv * (Rinv * F) * R := by
                    rw [mul_assoc, ← mul_assoc Rinv F R, mul_assoc Finv (Rinv * F) R]
            _ = Finv * (F * Rinv) * R := by
                    rw [← hcomm.eq]
            _ = (Finv * F) * (Rinv * R) := by
                    rw [← mul_assoc Finv F Rinv, mul_assoc (Finv * F) Rinv R]
    _ = 1 := by
          rw [hFinvF, hRinvR, one_mul]

/--
The theorem-facing inverse `J_f⁻¹(A,B)` is the ring inverse of `J_f(A,B)`
under Carlen's positivity and continuity hypotheses.
-/
theorem jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis {n : ℕ}
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    jOperatorInv f A B = Ring.inverse (jOperator f A B) := by
  have hleft :
      jOperatorInv f A B * jOperator f A B = 1 :=
    jOperatorInv_mul_jOperator_eq_one_of_carlenFunctionHypothesis hf hA hB
  have hright :
      jOperator f A B * Ring.inverse (jOperator f A B) = 1 :=
    Ring.mul_inverse_cancel (jOperator f A B)
      (jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hf hA hB).isUnit
  exact left_inv_eq_right_inv hleft hright

end

end Quantum.TraceInequality.Loewner.HiaiPetz
