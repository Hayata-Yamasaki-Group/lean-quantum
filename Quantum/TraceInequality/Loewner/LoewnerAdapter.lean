/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Interface
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.StrictOutputDPIViaLoewner

import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.CornerModels
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.ReducedMap
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.StrictOutputLift
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.SupportCorners

/-!
# Loewner provider for the neutral Hiai--Petz 6.2 interface

The Loewner surface uses `MatrixPosDef` and the quadratic-form order `HSLE`.
The compatibility lemmas below hide both choices.  The reverse order conversion
uses the existing self-adjoint Carlen rectangle lemmas.
-/

namespace ProofNet

open Quantum.TraceInequality.Loewner.HiaiPetz
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

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

private theorem strictDirectDPI_iff_loewner {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    StrictDirectDPI f ↔ ConditionIII_strict f := by
  constructor
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    apply HSLE_of_le
    exact h Φ hPos hTrace hSch
      (matrixPosDef_iff_posDef.mp hA) (matrixPosDef_iff_posDef.mp hB)
      (matrixPosDef_iff_posDef.mp hΦ1)
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    have hfCarlen : CarlenOpMontIFunctionHypothesis f :=
      ⟨hf, fun {x} hx ↦ hpos x hx⟩
    have hA' : MatrixPosDef A := matrixPosDef_iff_posDef.mpr hA
    have hB' : MatrixPosDef B := matrixPosDef_iff_posDef.mpr hB
    have hΦ1' : MatrixPosDef (Φ (1 : Mₙ n)) := matrixPosDef_iff_posDef.mpr hΦ1
    have hΦA : MatrixPosDef (Φ A) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1' hA'
    have hΦB : MatrixPosDef (Φ B) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1' hB'
    let TA : HSOp n := jOperator f A B
    let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
    have hTA_sa : IsSelfAdjoint TA := by
      simpa [TA] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hTΦ_sa : IsSelfAdjoint TΦ := by
      simpa [TΦ] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hΦA hΦB
    have hraw : HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ := by
      simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using
        (h Φ hPos hTrace hSch hA' hB' hΦ1')
    simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using
      (carlenRectangle_direct_HSLE_to_le hTA_sa hTΦ_sa hraw)

private theorem strictInverseDPI_iff_loewner {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    StrictInverseDPI f ↔ ConditionII_strict f := by
  constructor
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    apply HSLE_of_le
    exact h Φ hPos hTrace hSch
      (matrixPosDef_iff_posDef.mp hA) (matrixPosDef_iff_posDef.mp hB)
      (matrixPosDef_iff_posDef.mp hΦ1)
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    have hfCarlen : CarlenOpMontIFunctionHypothesis f :=
      ⟨hf, fun {x} hx ↦ hpos x hx⟩
    have hA' : MatrixPosDef A := matrixPosDef_iff_posDef.mpr hA
    have hB' : MatrixPosDef B := matrixPosDef_iff_posDef.mpr hB
    have hΦ1' : MatrixPosDef (Φ (1 : Mₙ n)) := matrixPosDef_iff_posDef.mpr hΦ1
    have hΦA : MatrixPosDef (Φ A) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1' hA'
    have hΦB : MatrixPosDef (Φ B) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1' hB'
    let TA : HSOp n := jOperator f A B
    let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
    have hTA_sa : IsSelfAdjoint TA := by
      simpa [TA] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hTΦ_sa : IsSelfAdjoint TΦ := by
      simpa [TΦ] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hΦA hΦB
    have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
      simpa [TA] using
        jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
      simpa [TΦ] using
        jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfCarlen hΦA hΦB
    have hJΦ :
        jOperatorInv f (Φ A) (Φ B) = Ring.inverse (jOperator f (Φ A) (Φ B)) :=
      jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hfCarlen hΦA hΦB
    have hJAB : jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
      jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hraw : HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) := by
      simpa [carlenRectInverseOp, TA, TΦ, hJΦ, hJAB, hsAdjoint_hsAdjoint] using
        (h Φ hPos hTrace hSch hA' hB' hΦ1')
    change
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ) ≤
        jOperatorInv f A B
    rw [hJΦ, hJAB]
    simpa [carlenRectInverseOp, TA, TΦ, hsAdjoint_hsAdjoint] using
      (carlenRectangle_inverse_HSLE_to_le hTA_sa hTΦ_sa hσTA hσTΦ hraw)

private theorem jointConcavity_iff_loewner {f : ℝ → ℝ} :
    JointConcavity f ↔ QuasiEntropyDPI.quasiEntropyJointConcavityCondition f := by
  constructor
  · intro h n A₁ A₂ B₁ B₂ X t ht0 ht1 hA₁ hA₂ hB₁ hB₂
    exact h ht0 ht1
      (matrixPosDef_iff_posDef.mp hA₁) (matrixPosDef_iff_posDef.mp hA₂)
      (matrixPosDef_iff_posDef.mp hB₁) (matrixPosDef_iff_posDef.mp hB₂)
  · intro h n A₁ A₂ B₁ B₂ X t ht0 ht1 hA₁ hA₂ hB₁ hB₂
    exact h ht0 ht1
      (matrixPosDef_iff_posDef.mpr hA₁) (matrixPosDef_iff_posDef.mpr hA₂)
      (matrixPosDef_iff_posDef.mpr hB₁) (matrixPosDef_iff_posDef.mpr hB₂)

private theorem outputSupportDirectDPI_iff_loewner {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    OutputSupportDirectDPI f ↔ ConditionIII_book f := by
  constructor
  · intro h n m Φ A B hPos hTrace hSch hA hB
    apply HSLE_of_le
    exact h Φ hPos hTrace hSch
      (matrixPosDef_iff_posDef.mp hA) (matrixPosDef_iff_posDef.mp hB)
  · intro h n m Φ A B hPos hTrace hSch hA hB
    dsimp only
    have hfCarlen : CarlenOpMontIFunctionHypothesis f :=
      ⟨hf, fun {x} hx ↦ hpos x hx⟩
    have hA' : MatrixPosDef A := matrixPosDef_iff_posDef.mpr hA
    have hB' : MatrixPosDef B := matrixPosDef_iff_posDef.mpr hB
    let Ψ := outputSupportReducedHSMap Φ hPos
    have hready := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
    have hΨA : MatrixPosDef (Ψ A) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
        Ψ hready.positive hready.outputPosDef hA'
    have hΨB : MatrixPosDef (Ψ B) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
        Ψ hready.positive hready.outputPosDef hB'
    let TA : HSOp n := jOperator f A B
    let TΨ : HSOp (outputSupportMatrixCornerModel Φ).dim := jOperator f (Ψ A) (Ψ B)
    have hTA_sa : IsSelfAdjoint TA := by
      simpa [TA] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hTΨ_sa : IsSelfAdjoint TΨ := by
      simpa [TΨ] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hΨA hΨB
    have hraw : HSLE (carlenRectDirectOp (hsAdjoint Ψ) TA) TΨ := by
      simpa [carlenRectDirectOp, TA, TΨ, Ψ, hsAdjoint_hsAdjoint] using
        (h Φ hPos hTrace hSch hA' hB')
    change Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)) ≤ jOperator f (Ψ A) (Ψ B)
    simpa [carlenRectDirectOp, TA, TΨ, hsAdjoint_hsAdjoint] using
      (carlenRectangle_direct_HSLE_to_le hTA_sa hTΨ_sa hraw)

private theorem outputSupportInverseDPI_iff_loewner {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    OutputSupportInverseDPI f ↔ ConditionII_book f := by
  constructor
  · intro h n m Φ A B hPos hTrace hSch hA hB
    apply HSLE_of_le
    exact h Φ hPos hTrace hSch
      (matrixPosDef_iff_posDef.mp hA) (matrixPosDef_iff_posDef.mp hB)
  · intro h n m Φ A B hPos hTrace hSch hA hB
    dsimp only
    have hfCarlen : CarlenOpMontIFunctionHypothesis f :=
      ⟨hf, fun {x} hx ↦ hpos x hx⟩
    have hA' : MatrixPosDef A := matrixPosDef_iff_posDef.mpr hA
    have hB' : MatrixPosDef B := matrixPosDef_iff_posDef.mpr hB
    let Ψ := outputSupportReducedHSMap Φ hPos
    have hready := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
    have hΨA : MatrixPosDef (Ψ A) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
        Ψ hready.positive hready.outputPosDef hA'
    have hΨB : MatrixPosDef (Ψ B) :=
      isPositiveMap_matrixPosDef_of_map_one_matrixPosDef
        Ψ hready.positive hready.outputPosDef hB'
    let TA : HSOp n := jOperator f A B
    let TΨ : HSOp (outputSupportMatrixCornerModel Φ).dim := jOperator f (Ψ A) (Ψ B)
    have hTA_sa : IsSelfAdjoint TA := by
      simpa [TA] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hTΨ_sa : IsSelfAdjoint TΨ := by
      simpa [TΨ] using
        jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfCarlen hΨA hΨB
    have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
      simpa [TA] using
        jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hσTΨ : spectrum ℝ TΨ ⊆ Set.Ioi (0 : ℝ) := by
      simpa [TΨ] using
        jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfCarlen hΨA hΨB
    have hJΨ :
        jOperatorInv f (Ψ A) (Ψ B) = Ring.inverse (jOperator f (Ψ A) (Ψ B)) :=
      jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hfCarlen hΨA hΨB
    have hJAB : jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
      jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hfCarlen hA' hB'
    have hsource := h Φ hPos hTrace hSch hA' hB'
    change
      HSLE ((hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ))
        (jOperatorInv f A B) at hsource
    rw [hJΨ, hJAB] at hsource
    have hraw : HSLE (carlenRectInverseOp (hsAdjoint Ψ) TΨ) (Ring.inverse TA) := by
      simpa [carlenRectInverseOp, TA, TΨ, hsAdjoint_hsAdjoint] using hsource
    change
      (hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ) ≤
        jOperatorInv f A B
    rw [hJΨ, hJAB]
    simpa [carlenRectInverseOp, TA, TΨ, hsAdjoint_hsAdjoint] using
      (carlenRectangle_inverse_HSLE_to_le hTA_sa hTΨ_sa hσTA hσTΨ hraw)

/-- The Loewner construction supplies the common strict-output package. -/
theorem strictDPIEquivalences_via_loewner {f : ℝ → ℝ} : StrictDPIEquivalences f := by
  intro hf hpos
  rcases strict_output_quasiEntropy_dpi_package_via_loewner (f := f) hf hpos with
    ⟨hIiffII, hIIiffIII, hIIIiffIV, _hIVtoImat, _hImatToI⟩
  have hII := strictInverseDPI_iff_loewner hf hpos
  have hIII := strictDirectDPI_iff_loewner hf hpos
  have hIV := jointConcavity_iff_loewner (f := f)
  have hIiffII' : MatrixMonotone f ↔ ConditionII_strict f := by
    simpa [MatrixMonotone] using hIiffII
  exact {
    matrixMonotone_iff_strictInverseDPI := hIiffII'.trans hII.symm
    strictInverseDPI_iff_strictDirectDPI := (hII.trans hIIiffIII).trans hIII.symm
    strictDirectDPI_iff_jointConcavity :=
      ⟨HiaiPetz.QuasiEntropyDataProcessing.jointConcavity_of_strictDirectDPI f hf,
        ((hIII.trans hIIIiffIV).trans hIV.symm).mpr⟩
    matrixMonotone_of_jointConcavity :=
      HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos }

/-- The Loewner construction supplies the common general-output package. -/
theorem outputSupportDPIEquivalences_via_loewner
    {f : ℝ → ℝ} : OutputSupportDPIEquivalences f := by
  intro hf hpos
  rcases book_output_support_quasiEntropy_dpi_package_via_loewner (f := f) hf hpos with
    ⟨hItoIII, hIIiffIII, hIIItoIV, _hIVtoImat, _hImatToI⟩
  have hII := outputSupportInverseDPI_iff_loewner hf hpos
  have hIII := outputSupportDirectDPI_iff_loewner hf hpos
  have hIV := jointConcavity_iff_loewner (f := f)
  exact {
    outputSupportDirectDPI_of_matrixMonotone := fun hI ↦
      hIII.mpr (hItoIII (show ConditionI f from hI))
    outputSupportInverseDPI_iff_outputSupportDirectDPI :=
      (hII.trans hIIiffIII).trans hIII.symm
    jointConcavity_of_outputSupportDirectDPI := fun hDirect ↦
      hIV.mpr (hIIItoIV (hIII.mp hDirect))
    matrixMonotone_of_jointConcavity :=
      HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos }

/-- Both Loewner-construction packages, bundled as an explicit provider value. -/
def loewnerProvider : Provider where
  route := .loewner
  strictDPIEquivalences := strictDPIEquivalences_via_loewner
  outputSupportDPIEquivalences := outputSupportDPIEquivalences_via_loewner

end ProofNet
