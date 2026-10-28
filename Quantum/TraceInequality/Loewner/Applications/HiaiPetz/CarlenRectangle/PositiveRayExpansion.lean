/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ScalarKubo

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

/-! ### Positive-ray CFC expansions before endpoint multiplication -/
/--
The positive-ray Kubo--Ando scalar representation expands the real CFC at
`jArg A B` before the final right endpoint factor in `jOperator`.
-/
theorem positiveRayKuboAndoRep_hsCfcR_preright_expansion
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsCfcR f₀ (jArg A B) =
      (f₀ 0 : ℂ) • (1 : HSOp n) +
        ((rep.b : ℝ) : ℂ) • jArg A B +
          jKuboKernelIntegral rep A B * rightMul (posInv B) := by
  let T : HSOp n := jArg A B
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let I : ℝ → ℝ := fun x : ℝ =>
    ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂μ
  have hT : IsSelfAdjoint T := by
    simpa [T] using jArg_isSelfAdjoint_of_matrixPosDef hA hB
  have hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ) := by
    simpa [T] using jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hI_cont : ContinuousOn I (spectrum ℝ T) := by
    simpa [I, μ] using
      (positiveRayKuboAndoRep_integral_kernel_continuousOn_spectrum
        (n := n) (T := T) rep hσT)
  have hformula :
      hsCfcR f₀ T =
        hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T := by
    dsimp [hsCfcR, _root_.HiaiPetz.hsCfcR]
    apply cfc_congr
    intro x hx
    have hx0 : x ∈ Set.Ici (0 : ℝ) := by
      have hxpos : 0 < x := by simpa [Set.mem_Ioi] using hσT hx
      exact le_of_lt hxpos
    simpa [I, μ] using rep.formula hx0
  have hsplit :
      hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T =
        (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            hsCfcR I T := by
    have haff_cont :
        ContinuousOn (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) (spectrum ℝ T) := by
      fun_prop
    have haff :
        cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) T =
          (f₀ 0 : ℂ) • (1 : HSOp n) + ((rep.b : ℝ) : ℂ) • T := by
      have hswap :
          cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) T =
            cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (fun x : ℝ => (rep.b : ℝ) * x + f₀ 0) T := by
        apply cfc_congr
        intro x hx
        ring
      rw [hswap]
      rw [cfc_add_const (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
        (r := f₀ 0) (f := fun x : ℝ => (rep.b : ℝ) * x)
        (a := T) (ha := hT)]
      rw [cfc_const_mul_id (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
        (r := (rep.b : ℝ)) (a := T) (ha := hT)]
      simp only [Complex.coe_smul]
      exact add_comm _ _
    dsimp [hsCfcR, _root_.HiaiPetz.hsCfcR]
    rw [cfc_add (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (a := T)
      (f := fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x)
      (g := I) haff_cont hI_cont]
    rw [haff]
    rfl
  have hI_cfc :
      hsCfcR I T =
        ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ := by
    simpa [I, μ] using
      (hsCfcR_positiveRayKuboAndoRep_integral_kernel
        (n := n) (T := T) rep hT hσT)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hkernel_integral :
      ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ =
        jKuboKernelIntegral rep A B * rightMul (posInv B) := by
    let L : HSOp n →L[ℂ] HSOp n :=
      (ContinuousLinearMap.mul ℂ (HSOp n)).flip (rightMul (posInv B))
    have hweighted :
        MeasureTheory.Integrable
          (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B)) μ := by
      simpa [μ] using
        weighted_jKuboKernel_integrable_of_positiveRayKuboAndoRep rep hA hB
    have hcongr :
        (fun t : ℝ =>
            hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T) =ᵐ[μ]
          fun t : ℝ =>
            (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) *
              rightMul (posInv B) := by
      filter_upwards [hsupport] with t ht
      have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
      simpa [T] using
        hsCfcR_positiveRayKuboAndoKernel_jArg_eq_weighted_jKuboKernel_rightMul
          (t := t) htpos hA hB
    calc
      ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ
          = ∫ t : ℝ,
              (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) *
                rightMul (posInv B) ∂μ := by
              exact integral_congr_ae hcongr
      _ = (∫ t : ℝ, (((1 + t : ℝ) : ℂ) • jKuboKernel t A B) ∂μ) *
            rightMul (posInv B) := by
          simpa [L] using (L.integral_comp_comm hweighted)
      _ = jKuboKernelIntegral rep A B * rightMul (posInv B) := by
          simp [jKuboKernelIntegral, μ]
  calc
    hsCfcR f₀ (jArg A B) = hsCfcR f₀ T := by rfl
    _ = hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T := hformula
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            hsCfcR I T := hsplit
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            jKuboKernelIntegral rep A B * rightMul (posInv B) := by
          rw [hI_cfc, hkernel_integral]
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • jArg A B +
            jKuboKernelIntegral rep A B * rightMul (posInv B) := by
          rfl

/--
The positive-ray Kubo--Ando scalar representation expands the real CFC at
`gArg X Y` before the final left endpoint factor in `gOperator`.
-/
theorem positiveRayKuboAndoRep_hsCfcR_preleft_expansion
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ n} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    hsCfcR f₀ (gArg X Y) =
      (f₀ 0 : ℂ) • (1 : HSOp n) +
        ((rep.b : ℝ) : ℂ) • gArg X Y +
          gKuboKernelIntegral rep X Y * leftMul (posInv Y) := by
  let T : HSOp n := gArg X Y
  let μ : MeasureTheory.Measure ℝ := (rep.ν : MeasureTheory.Measure ℝ)
  let I : ℝ → ℝ := fun x : ℝ =>
    ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂μ
  have hT : IsSelfAdjoint T := by
    simpa [T] using gArg_isSelfAdjoint_of_matrixPosDef hX hY
  have hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ) := by
    simpa [T] using gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hI_cont : ContinuousOn I (spectrum ℝ T) := by
    simpa [I, μ] using
      (positiveRayKuboAndoRep_integral_kernel_continuousOn_spectrum
        (n := n) (T := T) rep hσT)
  have hformula :
      hsCfcR f₀ T =
        hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T := by
    dsimp [hsCfcR, _root_.HiaiPetz.hsCfcR]
    apply cfc_congr
    intro x hx
    have hx0 : x ∈ Set.Ici (0 : ℝ) := by
      have hxpos : 0 < x := by simpa [Set.mem_Ioi] using hσT hx
      exact le_of_lt hxpos
    simpa [I, μ] using rep.formula hx0
  have hsplit :
      hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T =
        (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            hsCfcR I T := by
    have haff_cont :
        ContinuousOn (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) (spectrum ℝ T) := by
      fun_prop
    have haff :
        cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) T =
          (f₀ 0 : ℂ) • (1 : HSOp n) + ((rep.b : ℝ) : ℂ) • T := by
      have hswap :
          cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x) T =
            cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (fun x : ℝ => (rep.b : ℝ) * x + f₀ 0) T := by
        apply cfc_congr
        intro x hx
        ring
      rw [hswap]
      rw [cfc_add_const (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
        (r := f₀ 0) (f := fun x : ℝ => (rep.b : ℝ) * x)
        (a := T) (ha := hT)]
      rw [cfc_const_mul_id (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
        (r := (rep.b : ℝ)) (a := T) (ha := hT)]
      simp only [Complex.coe_smul]
      exact add_comm _ _
    dsimp [hsCfcR, _root_.HiaiPetz.hsCfcR]
    rw [cfc_add (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (a := T)
      (f := fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x)
      (g := I) haff_cont hI_cont]
    rw [haff]
    rfl
  have hI_cfc :
      hsCfcR I T =
        ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ := by
    simpa [I, μ] using
      (hsCfcR_positiveRayKuboAndoRep_integral_kernel
        (n := n) (T := T) rep hT hσT)
  have hsupport : ∀ᵐ t ∂μ, t ∈ Set.Ioi (0 : ℝ) := by
    simpa [μ] using (MeasureTheory.mem_ae_iff).mpr rep.support
  have hkernel_integral :
      ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ =
        gKuboKernelIntegral rep X Y * leftMul (posInv Y) := by
    let L : HSOp n →L[ℂ] HSOp n :=
      (ContinuousLinearMap.mul ℂ (HSOp n)).flip (leftMul (posInv Y))
    have hweighted :
        MeasureTheory.Integrable
          (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y)) μ := by
      simpa [μ] using
        weighted_gKuboKernel_integrable_of_positiveRayKuboAndoRep rep hX hY
    have hcongr :
        (fun t : ℝ =>
            hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T) =ᵐ[μ]
          fun t : ℝ =>
            (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) *
              leftMul (posInv Y) := by
      filter_upwards [hsupport] with t ht
      have htpos : 0 < t := by simpa [Set.mem_Ioi] using ht
      simpa [T] using
        hsCfcR_positiveRayKuboAndoKernel_gArg_eq_weighted_gKuboKernel_leftMul
          (t := t) htpos hX hY
    calc
      ∫ t : ℝ,
          hsCfcR (fun x : ℝ => positiveRayKuboAndoKernel x t) T ∂μ
          = ∫ t : ℝ,
              (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) *
                leftMul (posInv Y) ∂μ := by
              exact integral_congr_ae hcongr
      _ = (∫ t : ℝ, (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y) ∂μ) *
            leftMul (posInv Y) := by
          simpa [L] using (L.integral_comp_comm hweighted)
      _ = gKuboKernelIntegral rep X Y * leftMul (posInv Y) := by
          simp [gKuboKernelIntegral, μ]
  calc
    hsCfcR f₀ (gArg X Y) = hsCfcR f₀ T := by rfl
    _ = hsCfcR (fun x : ℝ => f₀ 0 + (rep.b : ℝ) * x + I x) T := hformula
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            hsCfcR I T := hsplit
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • T +
            gKuboKernelIntegral rep X Y * leftMul (posInv Y) := by
          rw [hI_cfc, hkernel_integral]
    _ = (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • gArg X Y +
            gKuboKernelIntegral rep X Y * leftMul (posInv Y) := by
          rfl

/--
If the real CFC part of `J_f(A,B)` is expanded before the final right endpoint
factor, the definition of `jOperator` gives the endpoint, slope, and fixed-kernel
integral expansion after multiplying by `R_B`.
-/
theorem jOperator_expansion_of_hsCfcR_preright_expansion
    {n : ℕ} {f₀ : ℝ → ℝ} {A B : Mₙ n}
    (rep : PositiveRayKuboAndoRep f₀)
    (hB : MatrixPosDef B)
    (hCfc :
      hsCfcR f₀ (jArg A B) =
        (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • jArg A B +
            jKuboKernelIntegral rep A B * rightMul (posInv B)) :
    jOperator f₀ A B =
      (f₀ 0 : ℂ) • rightMul B + ((rep.b : ℝ) : ℂ) • leftMul A +
        jKuboKernelIntegral rep A B := by
  have harg : (jArg A B) * rightMul B = leftMul A :=
    jArg_mul_rightMul_of_matrixPosDef hB
  have hright : (rightMul (posInv B) : HSOp n) * rightMul B = 1 :=
    rightMul_posInv_mul_rightMul_of_matrixPosDef hB
  change hsCfcR f₀ (jArg A B) * rightMul B = _
  rw [hCfc]
  ext X i j
  have hargX : (jArg A B) (rightMul B X) = leftMul A X := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T X) harg
  have hrightX : (rightMul (posInv B) : HSOp n) (rightMul B X) = X := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T X) hright
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [hargX, hrightX]

/--
If the real CFC part of `G_f(X,Y)` is expanded before the final left endpoint
factor, the definition of `gOperator` gives the endpoint, slope, and fixed-kernel
integral expansion after multiplying by `L_Y`.
-/
theorem gOperator_expansion_of_hsCfcR_preleft_expansion
    {n : ℕ} {f₀ : ℝ → ℝ} {X Y : Mₙ n}
    (rep : PositiveRayKuboAndoRep f₀)
    (hY : MatrixPosDef Y)
    (hCfc :
      hsCfcR f₀ (gArg X Y) =
        (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • gArg X Y +
            gKuboKernelIntegral rep X Y * leftMul (posInv Y)) :
    gOperator f₀ X Y =
      (f₀ 0 : ℂ) • leftMul Y + ((rep.b : ℝ) : ℂ) • rightMul X +
        gKuboKernelIntegral rep X Y := by
  have harg : (gArg X Y) * leftMul Y = rightMul X :=
    gArg_mul_leftMul_of_matrixPosDef hY
  have hleft : (leftMul (posInv Y) : HSOp n) * leftMul Y = 1 :=
    leftMul_posInv_mul_leftMul_of_matrixPosDef hY
  rw [gOperator, hCfc]
  ext Z i j
  have hargZ : (gArg X Y) (leftMul Y Z) = rightMul X Z := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T Z) harg
  have hleftZ : (leftMul (posInv Y) : HSOp n) (leftMul Y Z) = Z := by
    simpa [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : HSOp n => T Z) hleft
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [hargZ, hleftZ]

/--
The positive-ray Kubo--Ando representation of `f₀` gives Carlen's direct
perspective decomposition into the endpoint term, the slope term, and the
Bochner integral of the fixed kernels.
-/
theorem gOperator_expansion_of_positiveRayKuboAndoRep
    {n : ℕ} {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ n} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    gOperator f₀ X Y =
      (f₀ 0 : ℂ) • leftMul Y + ((rep.b : ℝ) : ℂ) • rightMul X +
        gKuboKernelIntegral rep X Y := by
  exact
    gOperator_expansion_of_hsCfcR_preleft_expansion
      rep hY (positiveRayKuboAndoRep_hsCfcR_preleft_expansion rep hX hY)

/-! ### Three-term operator expansions and direct G Kubo DPI -/
/--
Algebraic Kubo--Ando expansion gate for Carlen's direct perspective `G_f`.

Once the two `G`-operators have been expanded into endpoint, slope, and fixed
kernel parts, the direct DPI follows by adding the corresponding
Hilbert--Schmidt quadratic-form inequalities.
-/
theorem gOperator_dpi_of_explicit_kubo_terms
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {X Y : Mₙ m}
    {c b : ℝ} {KXY : HSOp m} {KΦ : HSOp n}
    (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hleft :
      HSLE ((hsAdjoint Ψ).comp ((leftMul Y).comp Ψ))
        (leftMul (hsAdjoint Ψ Y)))
    (hright :
      HSLE ((hsAdjoint Ψ).comp ((rightMul X).comp Ψ))
        (rightMul (hsAdjoint Ψ X)))
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
  have hleft_scaled :
      HSLE
        ((c : ℂ) • ((hsAdjoint Ψ).comp ((leftMul Y).comp Ψ)))
        ((c : ℂ) • leftMul (hsAdjoint Ψ Y)) :=
    HSLE_smul_of_nonneg hc hleft
  have hright_scaled :
      HSLE
        ((b : ℂ) • ((hsAdjoint Ψ).comp ((rightMul X).comp Ψ)))
        ((b : ℂ) • rightMul (hsAdjoint Ψ X)) :=
    HSLE_smul_of_nonneg hb hright
  have hsum :=
    HSLE_add (HSLE_add hleft_scaled hright_scaled) hkernel
  convert hsum using 1
  ext Z i j
  simp only [hGXY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [map_add, map_add, map_smul, map_smul]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
