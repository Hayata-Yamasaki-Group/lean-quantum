/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import
Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.InverseToDirect
import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Definitions

/-!
# Standard rectangular inverse-to-direct theorem

Surface assembly for the standard rectangular reduction in positive dimensions.
Rectangle assertions use Mathlib's operator order directly, and this module
combines the shared notation with the inverse-to-direct core argument.

## Main results

* `inverseRingCore_to_directCore_rect`: an inverse rectangular inequality
  implies the direct rectangular inequality under nonnegativity and
  invertibility assumptions.

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

/-- In the positive-dimensional rectangular setting, the inverse inequality
`V TΦ⁻¹ V* ≤ TA⁻¹` implies the direct inequality `V* TA V ≤ TΦ`, with both
assertions interpreted in Mathlib operator order. -/
theorem inverseRingCore_to_directCore_rect
    {k l : ℕ}
    {TA : HSOp (Nat.succ k)} {TΦ : HSOp (Nat.succ l)}
    (V : HSMap (Nat.succ l) (Nat.succ k))
    (hTA0 : 0 ≤ TA) (hTΦ0 : 0 ≤ TΦ)
    (hTAu : IsUnit TA) (hTΦu : IsUnit TΦ) :
    InverseRectLE V TA TΦ →
      DirectRectLE V TA TΦ := by
  intro hrect
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  have hTA_sa : IsSelfAdjoint TA := IsSelfAdjoint.of_nonneg hTA0
  have hTΦ_sa : IsSelfAdjoint TΦ := IsSelfAdjoint.of_nonneg hTΦ0
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTA0 hTAu
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTΦ0 hTΦu
  have hUUstar := by
    exact directCoreRectUUstar_le_one_of_inverseRectLE
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ hrect
  have hUstarU := by
    exact directCoreRectUstarU_le_one_of_uUstar_le_one
      (V := V) hUUstar
  have hfinal :
      DirectRectLE V TA TΦ := by
    exact directRectLE_of_directCoreRectUstarU_le_one
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ hUstarU
  exact hfinal

end MatrixScopedInstances
end HiaiPetz
