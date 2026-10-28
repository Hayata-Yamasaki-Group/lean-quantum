/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.FixedKernelGate

/-!
# Carlen rectangle G-kernel stage

This module contains the G-kernel definitions, star bridge, positivity facts,
and the direct fixed-kernel DPI stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
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

/-! ### G-kernel definitions, star bridge, and positivity facts -/
/--
Inverse-form of the fixed kernel for Carlen's direct perspective:
`t • R_{X^{-1}} + L_{Y^{-1}}`.
-/
noncomputable def gKuboKernelInvForm {n : ℕ} (t : ℝ) (X Y : Mₙ n) : HSOp n :=
  (t : ℂ) • rightMul (posInv X) + leftMul (posInv Y)

/-- Fixed kernel for the direct Carlen perspective `G_f`. -/
noncomputable def gKuboKernel {n : ℕ} (t : ℝ) (X Y : Mₙ n) : HSOp n :=
  Ring.inverse (gKuboKernelInvForm t X Y)

/--
The Bochner-integrated fixed-kernel term in the direct Carlen perspective
decomposition.
-/
noncomputable def gKuboKernelIntegral {n : ℕ} {f₀ : ℝ → ℝ}
    (rep : PositiveRayKuboAndoRep f₀) (X Y : Mₙ n) : HSOp n :=
  ∫ t : ℝ, (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y)
    ∂(rep.ν : MeasureTheory.Measure ℝ)

/-- The Carlen CFC argument is self-adjoint for positive-definite inputs. -/
theorem gArg_isSelfAdjoint_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsSelfAdjoint (gArg X Y) :=
  @IsStrictlyPositive.isSelfAdjoint (HSOp n)
    inferInstance
    (instCarlenRectangleHSOpPartialOrder (n := n))
    (instCarlenRectangleHSOpStarRing (n := n))
    (instCarlenRectangleHSOpStarOrderedRing (n := n))
    (gArg X Y) (gArg_isStrictlyPositive_of_matrixPosDef hX hY)

/--
For positive-definite endpoints, real CFC of `gArg A B` is transported to
real CFC of `jArg A B` by conjugate transpose.
-/
theorem hsCfcR_gArg_conjTranspose_eq_jArg_conjTranspose {n : ℕ}
    {f : ℝ → ℝ} {A B W : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn f (spectrum ℝ (gArg A B))) :
    Matrix.conjTranspose ((hsCfcR f (gArg A B)) W) =
      (hsCfcR f (jArg A B)) (Matrix.conjTranspose W) := by
  have hT : IsSelfAdjoint (gArg A B) :=
    gArg_isSelfAdjoint_of_matrixPosDef hA hB
  have hnat :
      conjTransposeConjHSOp (hsCfcR f (gArg A B)) =
        hsCfcR f (conjTransposeConjHSOp (gArg A B)) :=
    hsCfcR_conjTransposeConjHSOp (f := f) (T := gArg A B) hf hT
  have hbridge :
      conjTransposeConjHSOp (hsCfcR f (gArg A B)) =
        hsCfcR f (jArg A B) := by
    simpa [conjTransposeConjHSOp_gArg_eq_jArg hA hB] using hnat
  have happ := congrArg (fun T : HSOp n => T (Matrix.conjTranspose W)) hbridge
  simpa [conjTransposeConjHSOp_apply] using happ

/--
The same conjugate-transpose transport for the inverse scalar CFC
`x ↦ (f x)⁻¹`.
-/
theorem hsCfcR_inv_gArg_conjTranspose_eq_jArg_conjTranspose {n : ℕ}
    {f : ℝ → ℝ} {A B W : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn (fun x : ℝ => (f x)⁻¹) (spectrum ℝ (gArg A B))) :
    Matrix.conjTranspose
        ((hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg A B)) W) =
      (hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg A B)) (Matrix.conjTranspose W) :=
  hsCfcR_gArg_conjTranspose_eq_jArg_conjTranspose
    (f := fun x : ℝ => (f x)⁻¹) hA hB hf

/-- The direct `G_f` and `J_f` quadratic forms agree under star. -/
theorem gOperator_qform_eq_jOperator_qform_star {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn f (spectrum ℝ (gArg A B))) :
    hsQF (gOperator f A B) Z = hsQF (jOperator f A B) (Matrix.conjTranspose Z) :=
  gOperator_qform_eq_jOperator_qform_star_of_hsCfcR_intertwines
    (f := f) (A := A) (B := B) (Z := Z) hB
    (fun W => hsCfcR_gArg_conjTranspose_eq_jArg_conjTranspose
      (f := f) (A := A) (B := B) (W := W) hA hB hf)

/-- The inverse `G_f` and `J_f` quadratic forms agree under star. -/
theorem gOperatorInv_qform_eq_jOperatorInv_qform_star {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn (fun x : ℝ => (f x)⁻¹) (spectrum ℝ (gArg A B))) :
    hsQF (gOperatorInv f A B) Z =
      hsQF (jOperatorInv f A B) (Matrix.conjTranspose Z) :=
  gOperatorInv_qform_eq_jOperatorInv_qform_star_of_hsCfcR_intertwines
    (f := f) (A := A) (B := B) (Z := Z) hB
    (fun W => hsCfcR_inv_gArg_conjTranspose_eq_jArg_conjTranspose
      (f := f) (A := A) (B := B) (W := W) hA hB hf)

/-- The inverse-form direct fixed kernel is strictly positive under positivity. -/
theorem gKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (ht : 0 ≤ t)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsStrictlyPositive (gKuboKernelInvForm t X Y) := by
  have hright : 0 ≤ ((t : ℂ) • (rightMul (posInv X) : HSOp n)) :=
    rightMul_smul_nonneg_of_matrix_posSemidef ht
      (matrixPosDef_posInv_posDef hX).posSemidef
  have hleft : IsStrictlyPositive (leftMul (posInv Y) : HSOp n) :=
    leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posInv_posDef hY)
  simpa [gKuboKernelInvForm] using
    @IsStrictlyPositive.nonneg_add (HSOp n)
      (instCarlenRectangleHSOpCStarAlgebra (n := n))
      (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarOrderedRing (n := n))
      ((t : ℂ) • (rightMul (posInv X) : HSOp n))
      (leftMul (posInv Y) : HSOp n) hright hleft

/-- The inverse-form direct fixed kernel has positive real spectrum. -/
theorem gKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (ht : 0 ≤ t)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    spectrum ℝ (gKuboKernelInvForm t X Y) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (gKuboKernelInvForm t X Y)
      (gKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef ht hX hY) x hx

/-- The inverse-form direct fixed kernel is a unit under positivity. -/
theorem gKuboKernelInvForm_isUnit_of_matrixPosDef {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (ht : 0 ≤ t)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsUnit (gKuboKernelInvForm t X Y) :=
  (gKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef ht hX hY).isUnit

/-- The inverse-form direct fixed kernel is self-adjoint under positivity. -/
theorem gKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef {n : ℕ}
    {t : ℝ} {X Y : Mₙ n} (ht : 0 ≤ t)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsSelfAdjoint (gKuboKernelInvForm t X Y) :=
  @IsStrictlyPositive.isSelfAdjoint (HSOp n)
    inferInstance
    (instCarlenRectangleHSOpPartialOrder (n := n))
    (instCarlenRectangleHSOpStarRing (n := n))
    (instCarlenRectangleHSOpStarOrderedRing (n := n))
    (gKuboKernelInvForm t X Y)
    (gKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef ht hX hY)

/-- Self-adjointness of the direct Carlen fixed kernel from its inverse form. -/
theorem gKuboKernel_isSelfAdjoint_of_invForm_facts {n : ℕ}
    {t : ℝ} {X Y : Mₙ n}
    (hInv_sa : IsSelfAdjoint (gKuboKernelInvForm t X Y))
    (hσInv : spectrum ℝ (gKuboKernelInvForm t X Y) ⊆ Set.Ioi (0 : ℝ)) :
    IsSelfAdjoint (gKuboKernel t X Y) := by
  simpa [gKuboKernel] using
    carlenRingInverse_isSelfAdjoint hInv_sa hσInv

/-- Positive real spectrum of the direct Carlen fixed kernel from its inverse form. -/
theorem gKuboKernel_spectrum_subset_Ioi_of_invForm_facts {n : ℕ}
    {t : ℝ} {X Y : Mₙ n}
    (hInv_sa : IsSelfAdjoint (gKuboKernelInvForm t X Y))
    (hσInv : spectrum ℝ (gKuboKernelInvForm t X Y) ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ (gKuboKernel t X Y) ⊆ Set.Ioi (0 : ℝ) := by
  rw [gKuboKernel, ← carlenCfcR_inv_eq_ringInverse hInv_sa hσInv]
  dsimp [hsCfcR]
  have hmap := cfc_map_spectrum (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
    (f := fun x : ℝ => x⁻¹) (a := gKuboKernelInvForm t X Y)
    (ha := hInv_sa)
    (hf := by
      intro x hx
      exact
        (continuousAt_inv₀
          (ne_of_gt (by simpa [Set.mem_Ioi] using hσInv hx))).continuousWithinAt)
  refine hmap.symm ▸ ?_
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact inv_pos.mpr (by simpa [Set.mem_Ioi] using hσInv hy)

/-- The fixed-kernel inverse formula for the direct Carlen kernel. -/
theorem gKuboKernel_inverse_eq_invForm_of_isUnit {n : ℕ} (t : ℝ) (X Y : Mₙ n)
    (hu : IsUnit (gKuboKernelInvForm t X Y)) :
    Ring.inverse (gKuboKernel t X Y) = gKuboKernelInvForm t X Y := by
  rcases hu with ⟨u, hu_eq⟩
  rw [gKuboKernel, ← hu_eq, Ring.inverse_unit]
  simp

/-! ### Direct G fixed-kernel DPI via inverse-form Lieb--Ruskai -/
/--
Conjugating the inverse-form direct fixed kernel by a Hilbert--Schmidt map
expands into the conjugated right and left inverse terms.
-/
theorem gKuboKernelInvForm_adjoint_comp_expand {n m : ℕ} (Ψ : HSMap n m)
    (t : ℝ) (X Y : Mₙ n) :
    Ψ.comp ((gKuboKernelInvForm t X Y).comp (hsAdjoint Ψ)) =
      (t : ℂ) • (Ψ.comp ((rightMul (posInv X)).comp (hsAdjoint Ψ))) +
        Ψ.comp ((leftMul (posInv Y)).comp (hsAdjoint Ψ)) := by
  apply ContinuousLinearMap.ext
  intro Z
  simp only [gKuboKernelInvForm, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Complex.coe_smul, ContinuousLinearMap.add_apply]
  rw [map_add]
  congr 1
  change Ψ (((t : ℂ) • rightMul (posInv X)) ((hsAdjoint Ψ) Z)) =
    (((t : ℂ) • (Ψ.comp ((rightMul (posInv X)).comp (hsAdjoint Ψ)))) Z)
  rw [ContinuousLinearMap.smul_apply]
  rw [map_smul]
  rw [ContinuousLinearMap.smul_apply]
  simp [ContinuousLinearMap.comp_apply]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
