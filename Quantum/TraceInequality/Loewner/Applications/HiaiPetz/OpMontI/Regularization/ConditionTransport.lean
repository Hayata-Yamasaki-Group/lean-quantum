/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Regularization.OperatorCompression
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai

/-!
# Regularization condition transport

This module contains the functional-calculus continuity, support-corner
limits, condition transport, and ambient Carlen `opmontI` wrapper used in
the regularization stage of Carlen 2022, Theorem 1.46.
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
  regularizationHSOpContinuousStar
  regularizationHSOpComplexAlgebra
  regularizationHSOpNormedAlgebra
  regularizationHSOpRealCFC
  regularizationHSOpSMulZeroClass
  regularizationHSOpIsBoundedSMul
  regularizationHSOpContinuousSMul
  regularizationHSOpContinuousMul


/-! ### Functional-calculus continuity for G and J arguments -/
/-- Real CFC is continuous along Hilbert--Schmidt operators whose spectra eventually stay in
a common compact set and whose elements stay self-adjoint. -/
theorem hsCfcR_tendsto_of_tendsto_selfadjoint_spectrum_subset {n : ℕ}
    {α : Type*} {l : Filter α} {k : ℝ → ℝ} {T : α → HSOp n} {T₀ : HSOp n}
    {s : Set ℝ} (hs : IsCompact s)
    (hT : Tendsto T l (𝓝 T₀))
    (hσ : ∀ᶠ a in l, spectrum ℝ (T a) ⊆ s)
    (hsa : ∀ᶠ a in l, IsSelfAdjoint (T a))
    (hσ₀ : spectrum ℝ T₀ ⊆ s) (hsa₀ : IsSelfAdjoint T₀)
    (hk : ContinuousOn k s) :
    Tendsto (fun a => hsCfcR k (T a)) l (𝓝 (hsCfcR k T₀)) := by
  simpa [hsCfcR] using
    (hT.cfc (A := HSOp n) (p := IsSelfAdjoint) hs k hσ hsa hσ₀ hsa₀ hk)

/-- Real CFC is continuous along Hilbert--Schmidt operators when the scalar function is continuous
on a neighborhood of the limiting spectrum and the operators are eventually self-adjoint. -/
theorem hsCfcR_tendsto_of_tendsto_selfadjoint_spectrum_mem_nhdsSet {n : ℕ}
    {α : Type*} {l : Filter α} {k : ℝ → ℝ} {T : α → HSOp n} {T₀ : HSOp n}
    {s : Set ℝ} (hs : s ∈ 𝓝ˢ (spectrum ℝ T₀))
    (hT : Tendsto T l (𝓝 T₀))
    (hsa : ∀ᶠ a in l, IsSelfAdjoint (T a))
    (hsa₀ : IsSelfAdjoint T₀)
    (hk : ContinuousOn k s) :
    Tendsto (fun a => hsCfcR k (T a)) l (𝓝 (hsCfcR k T₀)) := by
  obtain ⟨S, ⟨hS_nhds, hS_compact⟩, hS_subset⟩ :=
    (spectrum.isCompact (𝕜 := ℝ) T₀).nhdsSet_basis_isCompact.mem_iff.mp hs
  have hσ_nhds : ∀ᶠ T' : HSOp n in 𝓝 T₀, spectrum ℝ T' ⊆ S :=
    (upperHemicontinuous_spectrum ℝ (HSOp n)).upperHemicontinuousAt T₀ S hS_nhds |>.mono
      fun _ => subset_of_mem_nhdsSet
  have hσ : ∀ᶠ a in l, spectrum ℝ (T a) ⊆ S :=
    hT.eventually hσ_nhds
  have hσ₀ : spectrum ℝ T₀ ⊆ S :=
    subset_of_mem_nhdsSet hS_nhds
  exact
    hsCfcR_tendsto_of_tendsto_selfadjoint_spectrum_subset hS_compact hT hσ hsa hσ₀ hsa₀
      (hk.mono hS_subset)

/-- The Carlen CFC factor `hsCfcR k (gArg X Y)` is continuous under strict positive identity
regularization whenever `k` is continuous on the positive ray. -/
theorem hsCfcR_gArg_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {k : ℝ → ℝ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hk : ContinuousOn k (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ => hsCfcR k (gArg (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n))))
      (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR k (gArg X Y))) := by
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝ˢ (spectrum ℝ (gArg X Y)) := by
    rw [isOpen_Ioi.mem_nhdsSet]
    exact gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hsa :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        IsSelfAdjoint (gArg (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n))) := by
    filter_upwards [hεpos] with ε hε
    exact gArg_isSelfAdjoint_of_matrixPosDef
      (matrixPosDef_add_pos_smul_one hX hε)
      (matrixPosDef_add_pos_smul_one hY hε)
  exact
    hsCfcR_tendsto_of_tendsto_selfadjoint_spectrum_mem_nhdsSet hs
      (gArg_tendsto_add_pos_smul_one_nhdsGT hY) hsa
      (gArg_isSelfAdjoint_of_matrixPosDef hX hY) hk

/-- The Hiai--Petz CFC factor `hsCfcR k (jArg A B)` is continuous under strict positive identity
regularization whenever `k` is continuous on the positive ray. -/
theorem hsCfcR_jArg_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {k : ℝ → ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hk : ContinuousOn k (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ => hsCfcR k (jArg (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n))))
      (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR k (jArg A B))) := by
  have hs : Set.Ioi (0 : ℝ) ∈ 𝓝ˢ (spectrum ℝ (jArg A B)) := by
    rw [isOpen_Ioi.mem_nhdsSet]
    exact jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hsa :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        IsSelfAdjoint (jArg (A + ε • (1 : Mₙ n)) (B + ε • (1 : Mₙ n))) := by
    filter_upwards [hεpos] with ε hε
    exact jArg_isSelfAdjoint_of_matrixPosDef
      (matrixPosDef_add_pos_smul_one hA hε)
      (matrixPosDef_add_pos_smul_one hB hε)
  exact
    hsCfcR_tendsto_of_tendsto_selfadjoint_spectrum_mem_nhdsSet hs
      (jArg_tendsto_add_pos_smul_one_nhdsGT hB) hsa
      (jArg_isSelfAdjoint_of_matrixPosDef hA hB) hk

/-- Carlen's strict `G_f` operator is continuous under positive identity regularization. -/
theorem gOperator_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {f : ℝ → ℝ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ => gOperator f (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (gOperator f X Y)) := by
  have hcfc :
      Tendsto
        (fun ε : ℝ => hsCfcR f
          (gArg (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n))))
        (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR f (gArg X Y))) :=
    hsCfcR_gArg_tendsto_add_pos_smul_one_nhdsGT hX hY hf
  have hleft :
      Tendsto (fun ε : ℝ => (leftMul (Y + ε • (1 : Mₙ n)) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (leftMul Y)) :=
    leftMul_tendsto_add_pos_smul_one_nhdsGT Y
  simpa [gOperator] using hcfc.mul hleft

/-- Carlen's theorem-facing inverse `G_f^{-1}` operator is continuous under positive identity
regularization. -/
theorem gOperatorInv_tendsto_add_pos_smul_one_nhdsGT {n : ℕ} {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    Tendsto
      (fun ε : ℝ => gOperatorInv f (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n)))
      (𝓝[>] (0 : ℝ)) (𝓝 (gOperatorInv f X Y)) := by
  have hfinv : ContinuousOn (fun x : ℝ => (f x)⁻¹) (Set.Ioi (0 : ℝ)) :=
    hf.1.inv₀ (fun x hx => ne_of_gt (hf.2 hx))
  have hcfc :
      Tendsto
        (fun ε : ℝ => hsCfcR (fun x : ℝ => (f x)⁻¹)
          (gArg (X + ε • (1 : Mₙ n)) (Y + ε • (1 : Mₙ n))))
        (𝓝[>] (0 : ℝ)) (𝓝 (hsCfcR (fun x : ℝ => (f x)⁻¹) (gArg X Y))) :=
    hsCfcR_gArg_tendsto_add_pos_smul_one_nhdsGT hX hY hfinv
  have hleft :
      Tendsto (fun ε : ℝ => (leftMul (posInv (Y + ε • (1 : Mₙ n))) : HSOp n))
        (𝓝[>] (0 : ℝ)) (𝓝 (leftMul (posInv Y))) :=
    leftMul_posInv_tendsto_add_pos_smul_one_nhdsGT hY
  simpa [gOperatorInv] using hcfc.mul hleft

/-! ### Carlen support-corner G limits -/
/-- Carlen's support-corner `G_f` model is the limit of positive identity regularization in the
reduced support coordinates. -/
theorem carlenSupportGOperatorModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    {X Y : Mₙ m} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ =>
        gOperator f
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim))
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (carlenSupportGOperatorModelConj f Φ hAdjPos X Y)) := by
  have hredX : MatrixPosDef (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X) :=
    hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hX
  have hredY : MatrixPosDef (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) :=
    hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hY
  have ht :
      Tendsto
        (fun ε : ℝ =>
          gOperator f
            (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim))
            (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y))) :=
    gOperator_tendsto_add_pos_smul_one_nhdsGT hredX hredY hf
  have htarget :
      carlenSupportGOperatorModelConj f Φ hAdjPos X Y =
        gOperator f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) :=
    carlenSupportGOperator_conj_eq_reducedMap_gOperator f Φ hAdjPos X Y
  simpa [htarget] using ht

/-- Carlen's support-corner theorem-facing inverse `G_f^{-1}` model is the limit of positive
identity regularization in the reduced support coordinates. -/
theorem carlenSupportGOperatorInvModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    {X Y : Mₙ m} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    Tendsto
      (fun ε : ℝ =>
        gOperatorInv f
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim))
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
            + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y)) := by
  have hredX : MatrixPosDef (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X) :=
    hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hX
  have hredY : MatrixPosDef (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) :=
    hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hY
  have ht :
      Tendsto
        (fun ε : ℝ =>
          gOperatorInv f
            (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim))
            (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
              + ε • (1 : Mₙ (outputSupportMatrixCornerModel (hsAdjoint Φ)).dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y))) :=
    gOperatorInv_tendsto_add_pos_smul_one_nhdsGT hf hredX hredY
  have htarget :
      carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y =
        gOperatorInv f (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X)
          (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y) :=
    carlenSupportGOperatorInv_conj_eq_reducedMap_gOperatorInv f Φ hAdjPos X Y
  simpa [htarget] using ht

/-- Embedding a reduced adjoint-support coordinate matrix returns the original ambient
adjoint image. -/
theorem carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap
    {n m : ℕ} (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (X : Mₙ m) :
    (carlenAdjointSupportMatrixCornerModel Φ).cornerEmbed
        (outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X) =
      hsAdjoint Φ X := by
  change
    ((outputSupportMatrixCornerModel (hsAdjoint Φ)).toMat.symm
      ((outputSupportMatrixCornerModel (hsAdjoint Φ)).toMat
        ⟨hsAdjoint Φ X, phi_image_mem_outputCorner (hsAdjoint Φ) hAdjPos X⟩)).1 =
      hsAdjoint Φ X
  exact congrArg Subtype.val
    ((outputSupportMatrixCornerModel (hsAdjoint Φ)).toMat.symm_apply_apply
      ⟨hsAdjoint Φ X, phi_image_mem_outputCorner (hsAdjoint Φ) hAdjPos X⟩)

/-- Carlen's support-corner `G_f` model is the limit of ambient positive identity
regularization after A0 corner compression. -/
theorem carlenSupportGOperatorModelConj_tendsto_ambient_compressed_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    {X Y : Mₙ m} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Tendsto
      (fun ε : ℝ =>
        (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj (hsAdjoint Φ))
          (gOperator f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (carlenSupportGOperatorModelConj f Φ hAdjPos X Y)) := by
  let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
    carlenAdjointSupportMatrixCornerModel Φ
  let Xred : Mₙ model.dim := outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
  let Yred : Mₙ model.dim := outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
  have hredX : MatrixPosDef Xred := by
    simpa [Xred, model, carlenAdjointSupportMatrixCornerModel] using
      hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hX
  have hredY : MatrixPosDef Yred := by
    simpa [Yred, model, carlenAdjointSupportMatrixCornerModel] using
      hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hY
  have hcoord :
      Tendsto
        (fun ε : ℝ =>
          gOperator f
            (Xred + ε • (1 : Mₙ model.dim))
            (Yred + ε • (1 : Mₙ model.dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (carlenSupportGOperatorModelConj f Φ hAdjPos X Y)) := by
    simpa [Xred, Yred, model, carlenAdjointSupportMatrixCornerModel] using
      carlenSupportGOperatorModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
        Φ hAdjPos hX hY hf
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj (hsAdjoint Φ))
          (gOperator f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))) =
        gOperator f
          (Xred + ε • (1 : Mₙ model.dim))
          (Yred + ε • (1 : Mₙ model.dim)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hXembed : model.cornerEmbed Xred = hsAdjoint Φ X := by
      simpa [model, Xred, carlenAdjointSupportMatrixCornerModel] using
        carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap Φ hAdjPos X
    have hYembed : model.cornerEmbed Yred = hsAdjoint Φ Y := by
      simpa [model, Yred, carlenAdjointSupportMatrixCornerModel] using
        carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap Φ hAdjPos Y
    exact model.cornerCompressHSOp_gOperator_add_real_smul_one_of_cornerEmbed_eq
      (OutputSupportProj.isProj (hsAdjoint Φ)) (f := f) hXembed hYembed hredX hredY hε
  exact hcoord.congr' (heq.mono fun _ h => h.symm)

/-- Carlen's support-corner theorem-facing inverse `G_f^{-1}` model is the limit of ambient
positive identity regularization after A0 corner compression. -/
theorem carlenSupportGOperatorInvModelConj_tendsto_ambient_compressed_add_pos_smul_one_nhdsGT
    {n m : ℕ} {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    {X Y : Mₙ m} (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    Tendsto
      (fun ε : ℝ =>
        (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj (hsAdjoint Φ))
          (gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y)) := by
  let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
    carlenAdjointSupportMatrixCornerModel Φ
  let Xred : Mₙ model.dim := outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X
  let Yred : Mₙ model.dim := outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y
  have hredX : MatrixPosDef Xred := by
    simpa [Xred, model, carlenAdjointSupportMatrixCornerModel] using
      hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hX
  have hredY : MatrixPosDef Yred := by
    simpa [Yred, model, carlenAdjointSupportMatrixCornerModel] using
      hsAdjoint_image_posDef_on_adjointSupport Φ hAdjPos hY
  have hcoord :
      Tendsto
        (fun ε : ℝ =>
          gOperatorInv f
            (Xred + ε • (1 : Mₙ model.dim))
            (Yred + ε • (1 : Mₙ model.dim)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y)) := by
    simpa [Xred, Yred, model, carlenAdjointSupportMatrixCornerModel] using
      carlenSupportGOperatorInvModelConj_tendsto_reduced_add_pos_smul_one_nhdsGT
        hf Φ hAdjPos hX hY
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj (hsAdjoint Φ))
          (gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))) =
        gOperatorInv f
          (Xred + ε • (1 : Mₙ model.dim))
          (Yred + ε • (1 : Mₙ model.dim)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hXembed : model.cornerEmbed Xred = hsAdjoint Φ X := by
      simpa [model, Xred, carlenAdjointSupportMatrixCornerModel] using
        carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap Φ hAdjPos X
    have hYembed : model.cornerEmbed Yred = hsAdjoint Φ Y := by
      simpa [model, Yred, carlenAdjointSupportMatrixCornerModel] using
        carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap Φ hAdjPos Y
    exact model.cornerCompressHSOp_gOperatorInv_add_real_smul_one_of_cornerEmbed_eq
      (OutputSupportProj.isProj (hsAdjoint Φ)) (f := f) hXembed hYembed hredX hredY hε
  exact hcoord.congr' (heq.mono fun _ h => h.symm)

/-! ### Carlen condition two composed inverse limit -/
/-- Carlen condition (2), in the original composed ambient expression, is the quadratic-form
limit of the positive identity regularization and lands on the support-corner condition (2)
left-hand side. -/
theorem carlenCondition2_regularized_lhs_tendsto_support_lhs
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    {n m : ℕ} (Φ : HSMap n m) (hΦ : IsUnitalTwoPositiveMap Φ)
    {X Y : Mₙ m} (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (K : Mₙ m) :
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    Tendsto
      (fun ε : ℝ =>
        hsQF
          (Φ.comp
            ((gOperatorInv f
              (hsAdjoint Φ X + ε • (1 : Mₙ n))
              (hsAdjoint Φ Y + ε • (1 : Mₙ n))).comp
              (hsAdjoint Φ)))
          K)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (hsQF
          (Ψ.comp
            ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
              (hsAdjoint Ψ)))
          K)) := by
  let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
  let Ψ := carlenInputSupportReducedMap Φ hAdjPos
  let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
    carlenAdjointSupportMatrixCornerModel Φ
  let Z : Mₙ model.dim := hsAdjoint Ψ K
  let supportOp : HSOp model.dim := carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y
  have hcompressed :
      Tendsto
        (fun ε : ℝ =>
          (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj (hsAdjoint Φ))
            (gOperatorInv f
              (hsAdjoint Φ X + ε • (1 : Mₙ n))
              (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
        (𝓝[>] (0 : ℝ))
        (𝓝 supportOp) := by
    simpa [supportOp, hAdjPos] using
      carlenSupportGOperatorInvModelConj_tendsto_ambient_compressed_add_pos_smul_one_nhdsGT
        hf Φ hAdjPos hX hY
  have hqcompressed :
      Tendsto
        (fun ε : ℝ =>
          hsQF
            ((carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
              (OutputSupportProj.isProj (hsAdjoint Φ))
              (gOperatorInv f
                (hsAdjoint Φ X + ε • (1 : Mₙ n))
                (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
            Z)
        (𝓝[>] (0 : ℝ))
        (𝓝 (hsQF supportOp Z)) :=
    hsQF_tendsto_of_tendsto hcompressed Z
  have hsource : ∀ ε : ℝ,
      hsQF
        (Φ.comp
          ((gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))).comp
            (hsAdjoint Φ)))
        K =
      hsQF
        ((carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
          (OutputSupportProj.isProj (hsAdjoint Φ))
          (gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
        Z := by
    intro ε
    have hZembed : model.cornerEmbed Z = hsAdjoint Φ K := by
      simpa [model, Z, Ψ, hAdjPos, carlenAdjointSupportMatrixCornerModel,
        carlenInputSupportReducedMap_hsAdjoint_apply] using
        carlenAdjointSupportCornerEmbed_outputSupportReducedHSMap Φ hAdjPos K
    calc
      hsQF
          (Φ.comp
            ((gOperatorInv f
              (hsAdjoint Φ X + ε • (1 : Mₙ n))
              (hsAdjoint Φ Y + ε • (1 : Mₙ n))).comp
              (hsAdjoint Φ)))
          K =
        hsQF
          (gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n)))
          (hsAdjoint Φ K) := by
          rw [hsQF_comp_adjoint]
      _ =
        hsQF
          (gOperatorInv f
            (hsAdjoint Φ X + ε • (1 : Mₙ n))
            (hsAdjoint Φ Y + ε • (1 : Mₙ n)))
          (model.cornerEmbed Z) := by
          rw [hZembed]
      _ =
        hsQF
          ((carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
            (OutputSupportProj.isProj (hsAdjoint Φ))
            (gOperatorInv f
              (hsAdjoint Φ X + ε • (1 : Mₙ n))
              (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
          Z := by
          rw [← MatrixCornerModel.cornerCompressHSOp_hsQF_eq]
  have htarget :
      hsQF supportOp Z =
        hsQF
          (Ψ.comp (supportOp.comp (hsAdjoint Ψ)))
          K := by
    symm
    simpa [Z] using hsQF_comp_adjoint Ψ supportOp K
  have hambient :=
    hqcompressed.congr' (Eventually.of_forall fun ε => (hsource ε).symm)
  simpa [hAdjPos, Ψ, model, Z, supportOp, htarget] using hambient

/-! ### Carlen ambient-regularized conditions and opmontI wrapper -/
/-- Carlen condition (2), read in ambient paper notation through positive identity
regularized quadratic-form limits. -/
def CarlenOpMontICondition2_regularized (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    ∀ K : Mₙ m,
      ∃ L : ℝ,
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (Φ.comp
                ((gOperatorInv f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))).comp
                  (hsAdjoint Φ)))
              K)
          (𝓝[>] (0 : ℝ))
          (𝓝 L) ∧
        L ≤ hsQF (gOperatorInv f X Y) K

/-- Carlen condition (3), read in ambient paper notation through positive identity
regularized support-compressed quadratic-form limits. -/
def CarlenOpMontICondition3_regularized (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
      carlenAdjointSupportMatrixCornerModel Φ
    ∀ Z : Mₙ model.dim,
      ∃ L : ℝ,
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (model.cornerCompressHSOp
                (OutputSupportProj.isProj (hsAdjoint Φ))
                (gOperator f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
              Z)
          (𝓝[>] (0 : ℝ))
          (𝓝 L) ∧
        hsQF
          ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
          Z ≤ L

/-- The ambient-regularized Carlen condition (2) is equivalent to the support-corner
condition (2). -/
theorem carlenCondition2_regularized_iff_support
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontICondition2_regularized f ↔
      CarlenOpMontICondition2_support f := by
  constructor
  · intro hreg n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    apply HSLE_of_hsQF_le
    intro K
    rcases hreg (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY K with
      ⟨L, hlimL, hLle⟩
    have hlimSupport :
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (Φ.comp
                ((gOperatorInv f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))).comp
                  (hsAdjoint Φ)))
              K)
          (𝓝[>] (0 : ℝ))
          (𝓝
            (hsQF
              (Ψ.comp
                ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
                  (hsAdjoint Ψ)))
              K)) := by
      simpa [hAdjPos, Ψ] using
        carlenCondition2_regularized_lhs_tendsto_support_lhs hf Φ hΦ hX hY K
    have hL :
        L =
          hsQF
            (Ψ.comp
              ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
                (hsAdjoint Ψ)))
            K :=
      tendsto_nhds_unique hlimL hlimSupport
    simpa [hAdjPos, Ψ, hL.symm] using hLle
  · intro hsupp n m Φ X Y hΦ hX hY K
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    refine
      ⟨hsQF
        (Ψ.comp
          ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
            (hsAdjoint Ψ)))
        K, ?_, ?_⟩
    · simpa [hAdjPos, Ψ] using
        carlenCondition2_regularized_lhs_tendsto_support_lhs hf Φ hΦ hX hY K
    · have hsupp' :
          HSLE
            (Ψ.comp
              ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
                (hsAdjoint Ψ)))
            (gOperatorInv f X Y) := by
        simpa [hAdjPos, Ψ] using
          hsupp (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY
      exact hsQF_le_of_HSLE hsupp' K

/-- The ambient-regularized Carlen condition (3) is equivalent to the support-corner
condition (3). -/
theorem carlenCondition3_regularized_iff_support
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontICondition3_regularized f ↔
      CarlenOpMontICondition3_support f := by
  constructor
  · intro hreg n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
      carlenAdjointSupportMatrixCornerModel Φ
    let supportOp : HSOp model.dim := carlenSupportGOperatorModelConj f Φ hAdjPos X Y
    apply HSLE_of_hsQF_le
    intro Z
    rcases hreg (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY Z with
      ⟨L, hlimL, hleL⟩
    have hcompressed :
        Tendsto
          (fun ε : ℝ =>
            (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
              (OutputSupportProj.isProj (hsAdjoint Φ))
              (gOperator f
                (hsAdjoint Φ X + ε • (1 : Mₙ n))
                (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
          (𝓝[>] (0 : ℝ))
          (𝓝 supportOp) := by
      simpa [supportOp, hAdjPos] using
        carlenSupportGOperatorModelConj_tendsto_ambient_compressed_add_pos_smul_one_nhdsGT
          Φ hAdjPos hX hY hf.1
    have hlimSupport :
        Tendsto
          (fun ε : ℝ =>
            hsQF
              ((carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
                (OutputSupportProj.isProj (hsAdjoint Φ))
                (gOperator f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
              Z)
          (𝓝[>] (0 : ℝ))
          (𝓝 (hsQF supportOp Z)) :=
      hsQF_tendsto_of_tendsto hcompressed Z
    have hL : L = hsQF supportOp Z :=
      tendsto_nhds_unique hlimL hlimSupport
    simpa [hAdjPos, Ψ, model, supportOp, hL] using hleL
  · intro hsupp n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    let model : MatrixCornerModel (carlenAdjointSupportProj Φ) :=
      carlenAdjointSupportMatrixCornerModel Φ
    change ∀ Z : Mₙ model.dim,
      ∃ L : ℝ,
        Tendsto
          (fun ε : ℝ =>
            hsQF
              (model.cornerCompressHSOp
                (OutputSupportProj.isProj (hsAdjoint Φ))
                (gOperator f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
              Z)
          (𝓝[>] (0 : ℝ))
          (𝓝 L) ∧
        hsQF
          ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
          Z ≤ L
    intro Z
    let supportOp : HSOp model.dim := carlenSupportGOperatorModelConj f Φ hAdjPos X Y
    refine ⟨hsQF supportOp Z, ?_, ?_⟩
    · have hcompressed :
          Tendsto
            (fun ε : ℝ =>
              (carlenAdjointSupportMatrixCornerModel Φ).cornerCompressHSOp
                (OutputSupportProj.isProj (hsAdjoint Φ))
                (gOperator f
                  (hsAdjoint Φ X + ε • (1 : Mₙ n))
                  (hsAdjoint Φ Y + ε • (1 : Mₙ n))))
            (𝓝[>] (0 : ℝ))
            (𝓝 supportOp) := by
        simpa [supportOp, hAdjPos] using
          carlenSupportGOperatorModelConj_tendsto_ambient_compressed_add_pos_smul_one_nhdsGT
            Φ hAdjPos hX hY hf.1
      exact hsQF_tendsto_of_tendsto hcompressed Z
    · have hsupp' :
          HSLE
            ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
            supportOp := by
        simpa [hAdjPos, Ψ, model, supportOp] using
          hsupp (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY
      exact hsQF_le_of_HSLE hsupp' Z

/-- Ambient-regularized Carlen `opmontI`: the support-corner paper theorem transported to
the regularized ambient paper conditions. -/
theorem carlenOpMontI_ambientRegularized_paper
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    (CarlenOpMontICondition1 f ↔ CarlenOpMontICondition2_regularized f) ∧
      (CarlenOpMontICondition2_regularized f ↔
        CarlenOpMontICondition3_regularized f) ∧
      (CarlenOpMontICondition3_regularized f ↔
        CarlenOpMontICondition4 f) := by
  rcases carlenOpMontI_support_paper (f := f) hf with ⟨h12support, h23support, h34support⟩
  have h2 : CarlenOpMontICondition2_regularized f ↔
      CarlenOpMontICondition2_support f :=
    carlenCondition2_regularized_iff_support (f := f) hf
  have h3 : CarlenOpMontICondition3_regularized f ↔
      CarlenOpMontICondition3_support f :=
    carlenCondition3_regularized_iff_support (f := f) hf
  exact ⟨h12support.trans h2.symm, (h2.trans h23support).trans h3.symm,
    h3.trans h34support⟩
end

end Quantum.TraceInequality.Loewner.HiaiPetz
