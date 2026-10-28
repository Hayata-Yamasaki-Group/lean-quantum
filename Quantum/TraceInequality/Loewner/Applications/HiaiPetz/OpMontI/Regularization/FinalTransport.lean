/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Regularization.ConditionTransport

/-!
# Regularization final transport

This module contains the Hiai--Petz continuity, support limits,
ambient-regularized conditions, raw-support equivalences, and final transport
used in the regularization stage of Carlen 2022, Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder Matrix.Norms.Frobenius Topology
open Filter

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  regularizationHSOpCStarAlgebra
  regularizationHSOpComplexAlgebra
  regularizationHSOpNormedAlgebra
  regularizationHSOpRealCFC
  regularizationHSOpSMulZeroClass
  regularizationHSOpIsBoundedSMul
  regularizationHSOpContinuousSMul
  regularizationHSOpContinuousMul


/-! ### Hiai-Petz J continuity and support limits -/
/-- The Hiai--Petz strict `J_f` operator is continuous under positive identity regularization. -/
theorem jOperator_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ => jOperator f (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (jOperator f A B)) := by
  have hcfc :
      Tendsto
        (fun ε : ℝ => hsCfcR f
          (jArg (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n))))
        (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR f (jArg A B))) :=
    hsCfcR_jArg_tendsto_add_pos_smul_one_nhdsGT hA hB hf
  have hright :
      Tendsto (fun ε : ℝ => (rightMul (B + ε • (1 : Mₙ n)) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (rightMul B)) :=
    rightMul_tendsto_add_pos_smul_one_nhdsGT B
  exact hcfc.mul hright

/-- The Hiai--Petz theorem-facing inverse `J_f^{-1}` operator is continuous under positive
identity regularization. -/
theorem jOperatorInv_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    Tendsto
      (fun ε : ℝ => jOperatorInv f (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (jOperatorInv f A B)) := by
  have hfinv : ContinuousOn (fun x : ℝ => (f x)⁻¹) (Set.Ioi (0 : ℝ)) :=
    hf.1.inv₀ (fun x hx => ne_of_gt (hf.2 hx))
  have hcfc :
      Tendsto
        (fun ε : ℝ => hsCfcR (fun x : ℝ => (f x)⁻¹)
          (jArg (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n))))
        (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR (fun x : ℝ => (f x)⁻¹) (jArg A B))) :=
    hsCfcR_jArg_tendsto_add_pos_smul_one_nhdsGT hA hB hfinv
  have hright :
      Tendsto (fun ε : ℝ => (rightMul (posInv (B + ε • (1 : Mₙ n))) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (rightMul (posInv B))) :=
    rightMul_posInv_tendsto_add_pos_smul_one_nhdsGT hB
  simpa [jOperatorInv] using hcfc.mul hright

/-- Embedding a reduced output-support coordinate matrix returns the original ambient image. -/
theorem outputSupportCornerEmbed_outputSupportReducedHSMap
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    (outputSupportMatrixCornerModel Φ).cornerEmbed
        (outputSupportReducedHSMap Φ hPos X) =
      Φ X := by
  change
    ((outputSupportMatrixCornerModel Φ).toMat.symm
      ((outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, phi_image_mem_outputCorner Φ hPos X⟩)).1 =
      Φ X
  exact congrArg Subtype.val
    ((outputSupportMatrixCornerModel Φ).toMat.symm_apply_apply
      ⟨Φ X, phi_image_mem_outputCorner Φ hPos X⟩)

/-- The raw support-corner `J_f` coordinate model is the reduced-coordinate limit of positive
identity regularization. -/
theorem rawSupportCornerJOperatorModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ =>
        jOperator f
          (outputSupportReducedHSMap Φ hPos A
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim))
          (outputSupportReducedHSMap Φ hPos B
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (rawSupportCornerJOperatorModelConj f Φ hPos A B)) := by
  have hredA : MatrixPosDef (outputSupportReducedHSMap Φ hPos A) :=
    outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA
  have hredB : MatrixPosDef (outputSupportReducedHSMap Φ hPos B) :=
    outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hB
  have ht :
      Tendsto
        (fun ε : ℝ =>
          jOperator f
            (outputSupportReducedHSMap Φ hPos A
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim))
            (outputSupportReducedHSMap Φ hPos B
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (jOperator f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B))) :=
    jOperator_tendsto_add_pos_smul_one_nhdsGT hredA hredB hf
  have htarget :
      rawSupportCornerJOperatorModelConj f Φ hPos A B =
        jOperator f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B) :=
    rawSupportCornerJOperator_conj_eq_reducedMap_jOperator f Φ hPos A B
  simpa [htarget] using ht

/-- The raw support-corner theorem-facing inverse `J_f^{-1}` coordinate model is the
reduced-coordinate limit of positive identity regularization. -/
theorem rawSupportCornerJOperatorInvModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    Tendsto
      (fun ε : ℝ =>
        jOperatorInv f
          (outputSupportReducedHSMap Φ hPos A
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim))
          (outputSupportReducedHSMap Φ hPos B
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (rawSupportCornerJOperatorInvModelConj f Φ hPos A B)) := by
  have hredA : MatrixPosDef (outputSupportReducedHSMap Φ hPos A) :=
    outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA
  have hredB : MatrixPosDef (outputSupportReducedHSMap Φ hPos B) :=
    outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hB
  have ht :
      Tendsto
        (fun ε : ℝ =>
          jOperatorInv f
            (outputSupportReducedHSMap Φ hPos A
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim))
            (outputSupportReducedHSMap Φ hPos B
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel Φ).dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B))) :=
    jOperatorInv_tendsto_add_pos_smul_one_nhdsGT hf hredA hredB
  have htarget :
      rawSupportCornerJOperatorInvModelConj f Φ hPos A B =
        jOperatorInv f (outputSupportReducedHSMap Φ hPos A)
          (outputSupportReducedHSMap Φ hPos B) :=
    rawSupportCornerJOperatorInv_conj_eq_reducedMap_jOperatorInv f Φ hPos A B
  simpa [htarget] using ht

/-! ### Hiai-Petz compressed J regularization -/
/-- F2a direct half: compressing the ambient positive-identity regularized `J_f` to the
output support corner converges to the raw support-corner `J_f` coordinate model. -/
theorem rawSupportCornerJOperator_tendsto_regularized_cornerCompress
    {n m : ℕ} {f : ℝ → ℝ}
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ =>
        (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj Φ)
          (jOperator f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (rawSupportCornerJOperatorModelConj f Φ hPos A B)) := by
  let model : MatrixCornerModel (outputSupportProj Φ) :=
    outputSupportMatrixCornerModel Φ
  let Ared : Mₙ model.dim := outputSupportReducedHSMap Φ hPos A
  let Bred : Mₙ model.dim := outputSupportReducedHSMap Φ hPos B
  have hredA : MatrixPosDef Ared := by
    simpa [Ared, model] using
      outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA
  have hredB : MatrixPosDef Bred := by
    simpa [Bred, model] using
      outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hB
  have hcoord :
      Tendsto
        (fun ε : ℝ =>
          jOperator f
            (Ared + ε • (1 : Mₙ model.dim))
            (Bred + ε • (1 : Mₙ model.dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (rawSupportCornerJOperatorModelConj f Φ hPos A B)) := by
    simpa [Ared, Bred, model] using
      rawSupportCornerJOperatorModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
        Φ hPos hA hB hf
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj Φ)
          (jOperator f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))) =
        jOperator f
          (Ared + ε • (1 : Mₙ model.dim))
          (Bred + ε • (1 : Mₙ model.dim)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAembed : model.cornerEmbed Ared = Φ A := by
      simp [model, Ared]
    have hBembed : model.cornerEmbed Bred = Φ B := by
      simp [model, Bred]
    exact model.cornerCompressHSOp_jOperator_add_real_smul_one_of_cornerEmbed_eq
      (OutputSupportProj.isProj Φ) (f := f) hAembed hBembed hredA hredB hε
  exact hcoord.congr' (heq.mono fun _ h => h.symm)

/-- F2a inverse half: compressing the ambient positive-identity regularized `J_f^{-1}` to the
output support corner converges to the raw support-corner inverse `J_f` coordinate model. -/
theorem rawSupportCornerJOperatorInv_tendsto_regularized_cornerCompress
    {n m : ℕ} {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    Tendsto
      (fun ε : ℝ =>
        (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj Φ)
          (jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (rawSupportCornerJOperatorInvModelConj f Φ hPos A B)) := by
  let model : MatrixCornerModel (outputSupportProj Φ) :=
    outputSupportMatrixCornerModel Φ
  let Ared : Mₙ model.dim := outputSupportReducedHSMap Φ hPos A
  let Bred : Mₙ model.dim := outputSupportReducedHSMap Φ hPos B
  have hredA : MatrixPosDef Ared := by
    simpa [Ared, model] using
      outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hA
  have hredB : MatrixPosDef Bred := by
    simpa [Bred, model] using
      outputSupportReducedHSMap_image_posDef_of_matrixPosDef Φ hPos hB
  have hcoord :
      Tendsto
        (fun ε : ℝ =>
          jOperatorInv f
            (Ared + ε • (1 : Mₙ model.dim))
            (Bred + ε • (1 : Mₙ model.dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (rawSupportCornerJOperatorInvModelConj f Φ hPos A B)) := by
    simpa [Ared, Bred, model] using
      rawSupportCornerJOperatorInvModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
        hf Φ hPos hA hB
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj Φ)
          (jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))) =
        jOperatorInv f
          (Ared + ε • (1 : Mₙ model.dim))
          (Bred + ε • (1 : Mₙ model.dim)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAembed : model.cornerEmbed Ared = Φ A := by
      simp [model, Ared]
    have hBembed : model.cornerEmbed Bred = Φ B := by
      simp [model, Bred]
    exact model.cornerCompressHSOp_jOperatorInv_add_real_smul_one_of_cornerEmbed_eq
      (OutputSupportProj.isProj Φ) (f := f) hAembed hBembed hredA hredB hε
  exact hcoord.congr' (heq.mono fun _ h => h.symm)

/-! ### Hiai-Petz ambient-regularized conditions -/
/-- Hiai--Petz condition `(ii)`, read in ambient paper notation through positive identity
regularized quadratic-form limits of the composed inverse expression. -/
def ConditionII_ambientRegularized (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      ∀ K : Mₙ n,
        ∃ L : ℝ,
          Tendsto
            (fun ε : ℝ =>
              hsQF
                ((hsAdjoint Φ).comp
                  ((jOperatorInv f
                    (Φ A + ε • (1 : Mₙ m))
                    (Φ B + ε • (1 : Mₙ m))).comp
                    Φ))
                K)
            (𝓝[>] (0 : ℝ))
            (𝓝 L) ∧
          L ≤ hsQF (jOperatorInv f A B) K

/-- Hiai--Petz condition `(iii)`, read in ambient paper notation through support-compressed
positive identity regularized quadratic-form limits. -/
def ConditionIII_ambientRegularized (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      let model : MatrixCornerModel (outputSupportProj Φ) :=
        outputSupportMatrixCornerModel Φ
      ∀ Z : Mₙ model.dim,
        ∃ L : ℝ,
          Tendsto
            (fun ε : ℝ =>
              hsQF
                (model.cornerCompressHSOp
                  (OutputSupportProj.isProj Φ)
                  (jOperator f
                    (Φ A + ε • (1 : Mₙ m))
                    (Φ B + ε • (1 : Mₙ m))))
                Z)
            (𝓝[>] (0 : ℝ))
            (𝓝 L) ∧
          hsQF (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ))) Z ≤ L

/-! ### Hiai-Petz raw-support equivalences and final transport -/
/-- The ambient-regularized inverse quadratic-form expression converges to the raw
paper-support inverse left-hand side. -/
theorem conditionII_ambientRegularized_lhs_tendsto_rawPaperSupport_lhs
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (K : Mₙ n) :
    let Ψ := outputSupportReducedHSMap Φ hPos
    Tendsto
      (fun ε : ℝ =>
        hsQF
          ((hsAdjoint Φ).comp
            ((jOperatorInv f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))).comp
              Φ))
          K)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (hsQF
          ((hsAdjoint Ψ).comp
            ((rawSupportCornerJOperatorInvModelConj f Φ hPos A B).comp Ψ))
          K)) := by
  let Ψ := outputSupportReducedHSMap Φ hPos
  let model : MatrixCornerModel (outputSupportProj Φ) :=
    outputSupportMatrixCornerModel Φ
  let Z : Mₙ model.dim := Ψ K
  let supportOp : HSOp model.dim := rawSupportCornerJOperatorInvModelConj f Φ hPos A B
  have hcompressed :
      Tendsto
        (fun ε : ℝ =>
          (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj Φ)
            (jOperatorInv f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))))
        (𝓝[>] (0 : ℝ))
        (𝓝 supportOp) := by
    simpa [supportOp] using
      rawSupportCornerJOperatorInv_tendsto_regularized_cornerCompress hf Φ hPos hA hB
  have hqcompressed :
      Tendsto
        (fun ε : ℝ =>
          hsQF
            ((outputSupportMatrixCornerModel Φ).cornerCompressHSOp
              (OutputSupportProj.isProj Φ)
              (jOperatorInv f
                (Φ A + ε • (1 : Mₙ m))
                (Φ B + ε • (1 : Mₙ m))))
            Z)
        (𝓝[>] (0 : ℝ))
        (𝓝 (hsQF supportOp Z)) :=
    hsQF_tendsto_of_tendsto hcompressed Z
  have hsource : ∀ ε : ℝ,
      hsQF
        ((hsAdjoint Φ).comp
          ((jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))).comp
            Φ))
        K =
      hsQF
        ((outputSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj Φ)
          (jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m))))
        Z := by
    intro ε
    have hZembed : model.cornerEmbed Z = Φ K := by
      exact outputSupportCornerEmbed_outputSupportReducedHSMap Φ hPos K
    let Tε : HSOp m :=
      jOperatorInv f
        (Φ A + ε • (1 : Mₙ m))
        (Φ B + ε • (1 : Mₙ m))
    calc
      hsQF
          ((hsAdjoint Φ).comp
            ((jOperatorInv f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))).comp
              Φ))
          K =
        hsQF
          (jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m)))
          (Φ K) := by
          simpa only [Tε, hsAdjoint_hsAdjoint] using
            hsQF_comp_adjoint (hsAdjoint Φ) Tε K
      _ =
        hsQF
          (jOperatorInv f
            (Φ A + ε • (1 : Mₙ m))
            (Φ B + ε • (1 : Mₙ m)))
          (model.cornerEmbed Z) := by
          exact congrArg
            (fun W : Mₙ m =>
              hsQF
                (jOperatorInv f
                  (Φ A + ε • (1 : Mₙ m))
                  (Φ B + ε • (1 : Mₙ m)))
                W)
            hZembed.symm
      _ =
        hsQF
          ((outputSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj Φ)
            (jOperatorInv f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))))
          Z := by
          exact
            (MatrixCornerModel.cornerCompressHSOp_hsQF_eq
              (outputSupportMatrixCornerModel Φ) (OutputSupportProj.isProj Φ)
              (jOperatorInv f
                (Φ A + ε • (1 : Mₙ m))
                (Φ B + ε • (1 : Mₙ m)))
              Z).symm
  have htarget :
      hsQF
        ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
        K =
      hsQF supportOp Z := by
    simpa only [Z, hsAdjoint_hsAdjoint] using
      hsQF_comp_adjoint (hsAdjoint Ψ) supportOp K
  have hambient :=
    hqcompressed.congr' (Eventually.of_forall fun ε => (hsource ε).symm)
  change
    Tendsto
      (fun ε : ℝ =>
        hsQF
          ((hsAdjoint Φ).comp
            ((jOperatorInv f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))).comp
              Φ))
          K)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (hsQF
          ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
          K))
  simpa only [htarget] using hambient

/-- The ambient-regularized direct support-compressed quadratic-form expression converges to
the raw paper-support direct right-hand side. -/
theorem conditionIII_ambientRegularized_rhs_tendsto_rawPaperSupport_rhs
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {n m : ℕ} (Φ : HSMap n m) (hPos : IsPositiveMap Φ)
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (Z : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    Tendsto
      (fun ε : ℝ =>
        hsQF
          ((outputSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj Φ)
            (jOperator f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))))
          Z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (hsQF (rawSupportCornerJOperatorModelConj f Φ hPos A B) Z)) := by
  have hcompressed :
      Tendsto
        (fun ε : ℝ =>
          (outputSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj Φ)
            (jOperator f
              (Φ A + ε • (1 : Mₙ m))
              (Φ B + ε • (1 : Mₙ m))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (rawSupportCornerJOperatorModelConj f Φ hPos A B)) :=
    rawSupportCornerJOperator_tendsto_regularized_cornerCompress Φ hPos hA hB hf
  exact hsQF_tendsto_of_tendsto hcompressed Z

/-- Hiai--Petz ambient-regularized condition `(ii)` is equivalent to the raw
paper-support inverse condition. -/
theorem ConditionII_ambientRegularized_iff_rawPaperSupport
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    ConditionII_ambientRegularized f ↔
      ConditionII_rawPaperSupport f := by
  constructor
  · intro hreg n m Φ A B hPos hTrace hSch hA hB
    let Ψ := outputSupportReducedHSMap Φ hPos
    let supportOp : HSOp (outputSupportMatrixCornerModel Φ).dim :=
      rawSupportCornerJOperatorInvModelConj f Φ hPos A B
    apply HSLE_of_hsQF_le
    intro K
    rcases hreg (n := n) (m := m) Φ (A := A) (B := B)
        hPos hTrace hSch hA hB K with
      ⟨L, hlimL, hLle⟩
    have hlimSupport :
        Tendsto
          (fun ε : ℝ =>
            hsQF
              ((hsAdjoint Φ).comp
                ((jOperatorInv f
                  (Φ A + ε • (1 : Mₙ m))
                  (Φ B + ε • (1 : Mₙ m))).comp
                  Φ))
              K)
          (𝓝[>] (0 : ℝ))
          (𝓝
            (hsQF
              ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
              K)) := by
      simpa [Ψ, supportOp] using
        conditionII_ambientRegularized_lhs_tendsto_rawPaperSupport_lhs
          hf Φ hPos hA hB K
    have hL :
        L =
          hsQF
            ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
            K :=
      tendsto_nhds_unique hlimL hlimSupport
    simpa [ConditionII_rawPaperSupport, Ψ, supportOp, hL.symm] using hLle
  · intro hsupp n m Φ A B hPos hTrace hSch hA hB K
    let Ψ := outputSupportReducedHSMap Φ hPos
    let supportOp : HSOp (outputSupportMatrixCornerModel Φ).dim :=
      rawSupportCornerJOperatorInvModelConj f Φ hPos A B
    refine
      ⟨hsQF
        ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
        K, ?_, ?_⟩
    · simpa [Ψ, supportOp] using
        conditionII_ambientRegularized_lhs_tendsto_rawPaperSupport_lhs
          hf Φ hPos hA hB K
    · have hsupp' :
          HSLE
            ((hsAdjoint Ψ).comp (supportOp.comp Ψ))
            (jOperatorInv f A B) := by
        simpa [ConditionII_rawPaperSupport, Ψ, supportOp] using
          hsupp (n := n) (m := m) Φ (A := A) (B := B)
            hPos hTrace hSch hA hB
      exact hsQF_le_of_HSLE hsupp' K

/-- Hiai--Petz ambient-regularized condition `(iii)` is equivalent to the raw
paper-support direct condition. -/
theorem ConditionIII_ambientRegularized_iff_rawPaperSupport
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    ConditionIII_ambientRegularized f ↔
      ConditionIII_rawPaperSupport f := by
  constructor
  · intro hreg n m Φ A B hPos hTrace hSch hA hB
    let Ψ := outputSupportReducedHSMap Φ hPos
    let model : MatrixCornerModel (outputSupportProj Φ) :=
      outputSupportMatrixCornerModel Φ
    let supportOp : HSOp model.dim := rawSupportCornerJOperatorModelConj f Φ hPos A B
    apply HSLE_of_hsQF_le
    intro Z
    rcases hreg (n := n) (m := m) Φ (A := A) (B := B)
        hPos hTrace hSch hA hB Z with
      ⟨L, hlimL, hleL⟩
    have hlimSupport :
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (model.cornerCompressHSOp
                (OutputSupportProj.isProj Φ)
                (jOperator f
                  (Φ A + ε • (1 : Mₙ m))
                  (Φ B + ε • (1 : Mₙ m))))
              Z)
          (𝓝[>] (0 : ℝ))
          (𝓝 (hsQF supportOp Z)) := by
      simpa [model, supportOp] using
        conditionIII_ambientRegularized_rhs_tendsto_rawPaperSupport_rhs
          hf Φ hPos hA hB Z
    have hL : L = hsQF supportOp Z :=
      tendsto_nhds_unique hlimL hlimSupport
    simpa [ConditionIII_rawPaperSupport, Ψ, model, supportOp, hL] using hleL
  · intro hsupp n m Φ A B hPos hTrace hSch hA hB
    let Ψ := outputSupportReducedHSMap Φ hPos
    let model : MatrixCornerModel (outputSupportProj Φ) :=
      outputSupportMatrixCornerModel Φ
    change ∀ Z : Mₙ model.dim,
      ∃ L : ℝ,
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (model.cornerCompressHSOp
                (OutputSupportProj.isProj Φ)
                (jOperator f
                  (Φ A + ε • (1 : Mₙ m))
                  (Φ B + ε • (1 : Mₙ m))))
              Z)
          (𝓝[>] (0 : ℝ))
          (𝓝 L) ∧
        hsQF (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ))) Z ≤ L
    intro Z
    let supportOp : HSOp model.dim := rawSupportCornerJOperatorModelConj f Φ hPos A B
    refine ⟨hsQF supportOp Z, ?_, ?_⟩
    · simpa [model, supportOp] using
        conditionIII_ambientRegularized_rhs_tendsto_rawPaperSupport_rhs
          hf Φ hPos hA hB Z
    · have hsupp' :
          HSLE
            (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)))
            supportOp := by
        simpa [ConditionIII_rawPaperSupport, Ψ, model, supportOp] using
          hsupp (n := n) (m := m) Φ (A := A) (B := B)
            hPos hTrace hSch hA hB
      exact hsQF_le_of_HSLE hsupp' Z

/-- Ambient-regularized Hiai--Petz aggregate statement, with paper conditions `(ii)` and
`(iii)` read through positive identity regularization. -/
def ambientRegularizedQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (ConditionI f → ConditionIII_ambientRegularized f) ∧
    (ConditionII_ambientRegularized f ↔ ConditionIII_ambientRegularized f) ∧
    (ConditionIII_ambientRegularized f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f)

/-- Ambient-regularized Hiai--Petz theorem via the Loewner route.  The raw paper-support
theorem is transported through the F2c regularized/raw condition equivalences.
Theorem 6.2 of [hiai2025]. -/
theorem ambient_regularized_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    ambientRegularizedQuasiEntropyDpiPackageStmt f := by
  intro hf hposf
  let hfCarlen : CarlenOpMontIFunctionHypothesis f := ⟨hf, hposf⟩
  rcases raw_paper_support_quasiEntropy_dpi_package_via_loewner (f := f) hf hposf with
    ⟨hI_to_IIIraw, hIIraw_iff_IIIraw, hIIIraw_to_IV, hIV_to_I_matrix,
      hI_matrix_to_I⟩
  have hII :
      ConditionII_ambientRegularized f ↔
        ConditionII_rawPaperSupport f :=
    ConditionII_ambientRegularized_iff_rawPaperSupport (f := f) hfCarlen
  have hIII :
      ConditionIII_ambientRegularized f ↔
        ConditionIII_rawPaperSupport f :=
    ConditionIII_ambientRegularized_iff_rawPaperSupport (f := f) hf
  refine ⟨?_, ?_, ?_, hIV_to_I_matrix, hI_matrix_to_I⟩
  · intro hI
    exact hIII.2 (hI_to_IIIraw hI)
  · constructor
    · intro hIIamb
      exact hIII.2 (hIIraw_iff_IIIraw.1 (hII.1 hIIamb))
    · intro hIIIamb
      exact hII.2 (hIIraw_iff_IIIraw.2 (hIII.1 hIIIamb))
  · intro hIIIamb
    exact hIIIraw_to_IV (hIII.1 hIIIamb)

/-- Alias emphasizing that the ambient-regularized Hiai--Petz wrapper uses the
Carlen--Loewner operator-monotonicity route upstream.
Theorem 6.2 of [hiai2025]. -/
theorem ambient_regularized_quasiEntropy_dpi_package_via_carlen_opmontI {f : ℝ → ℝ} :
    ambientRegularizedQuasiEntropyDpiPackageStmt f :=
  ambient_regularized_quasiEntropy_dpi_package_via_loewner
end

end Quantum.TraceInequality.Loewner.HiaiPetz
