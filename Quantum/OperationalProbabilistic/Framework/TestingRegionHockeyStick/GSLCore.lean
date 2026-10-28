/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TestingRegion.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.OperationalProbabilistic.Framework.OperationalStateDistance.GSLCore

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Hockey-stick divergence over testing regions

This file defines the operational hockey-stick quantity from the feasible
binary testing region.  At order one it agrees exactly with
`operationalStateDistance`: that existing distance is one half of the
operational state norm, so no additional factor of two appears in the public
correspondence theorem.

This is only the abstract operational definition and correspondence.  It does
not identify the quantity with a quantum positive-part trace formula.
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- Public hockey-stick orders, restricted to the standard range `gamma ≥ 1`. -/
abbrev HockeyStickOrder := {gamma : ℝ // 1 ≤ gamma}

namespace HockeyStickOrder

/-- The order-one endpoint of the public hockey-stick parameter range. -/
def one : HockeyStickOrder :=
  ⟨1, le_rfl⟩

end HockeyStickOrder

/-- The hockey-stick quantity `E_gamma`, as the clipped signed support of the
binary testing region. -/
noncomputable def hockeyStick (gamma : HockeyStickOrder) {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) : ℝ≥0∞ :=
  regionSupENNReal
    (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 - gamma.1 * z.2))
    (testingRegion (Sys := Sys) rho sigma)

/-- On normalized state pairs and public orders, hockey-stick values are at
most one. -/
theorem hockeyStick_le_one (gamma : HockeyStickOrder) {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    hockeyStick (Sys := Sys) gamma rho sigma ≤ 1 := by
  unfold hockeyStick regionSupENNReal
  apply iSup_le
  rintro ⟨z, hz⟩
  rw [ENNReal.ofReal_le_one]
  change z.1 - gamma.1 * z.2 ≤ 1
  have hzSquare := testingRegion_subset_unitSquare (Sys := Sys) rho sigma hz
  have hgamma_nonneg : 0 ≤ gamma.1 := le_trans zero_le_one gamma.2
  have hx_le : z.1 ≤ 1 := hzSquare.1.2
  have hproduct : 0 ≤ gamma.1 * z.2 :=
    mul_nonneg hgamma_nonneg hzSquare.2.1
  linarith

/-- Hockey-stick values on normalized state pairs are finite. -/
theorem hockeyStick_ne_top (gamma : HockeyStickOrder) {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    hockeyStick (Sys := Sys) gamma rho sigma ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (hockeyStick_le_one (Sys := Sys) gamma rho sigma)

private theorem binaryObservationDiffEval_le_operationalStateNorm {A : Sys}
    (M : BinaryObservationTest (Sys := Sys) A)
    (eta : OperationalStateSpaceReal (Sys := Sys) A) :
    binaryObservationDiffEval (Sys := Sys) M eta ≤
      operationalStateNorm (Sys := Sys) eta := by
  let S : Set ℝ := operationalStateNormEvalRange (Sys := Sys)
    (eta : StateOperationalQuotient (Sys := Sys) A)
  have hzero : IsEffect (Sys := Sys) (M.outcome BinaryObservationIndex.zero) :=
    binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.zero
  have hone : IsEffect (Sys := Sys) (M.outcome BinaryObservationIndex.one) :=
    binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.one
  have hzero_mem :
      stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.zero) hzero eta ∈ S := by
    exact ⟨⟨M.outcome BinaryObservationIndex.zero,
      boundedEffect_of_isEffect (Sys := Sys) hzero⟩, trivial, rfl⟩
  have hone_mem :
      stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.one) hone eta ∈ S := by
    exact ⟨⟨M.outcome BinaryObservationIndex.one,
      boundedEffect_of_isEffect (Sys := Sys) hone⟩, trivial, rfl⟩
  have hone_le :
      stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.one) hone eta ≤ sSup S :=
    le_csSup (operationalStateNorm_evalRange_bddAbove (Sys := Sys) eta) hone_mem
  have hzero_le :
      sInf S ≤ stateOperationalQuotientEval (Sys := Sys)
        (M.outcome BinaryObservationIndex.zero) hzero eta :=
    csInf_le (operationalStateNorm_evalRange_bddBelow (Sys := Sys) eta) hzero_mem
  unfold binaryObservationDiffEval operationalStateNorm
  change
    stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.one) hone eta -
        stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.zero) hzero eta ≤
      sSup S - sInf S
  linarith

private theorem binaryObservationDiffEval_stateDiff_eq_two_mul {A : Sys}
    (M : BinaryObservationTest (Sys := Sys) A)
    (rho sigma : NormalizedState (Sys := Sys) A) :
    binaryObservationDiffEval (Sys := Sys) M
        (operationalStateClass (Sys := Sys) rho.1 rho.2.1 -
          operationalStateClass (Sys := Sys) sigma.1 sigma.2.1) =
      2 * (prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1) := by
  let eta : OperationalStateSpaceReal (Sys := Sys) A :=
    operationalStateClass (Sys := Sys) rho.1 rho.2.1 -
      operationalStateClass (Sys := Sys) sigma.1 sigma.2.1
  have hzero : IsEffect (Sys := Sys) (M.outcome BinaryObservationIndex.zero) :=
    binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.zero
  have hone : IsEffect (Sys := Sys) (M.outcome BinaryObservationIndex.one) :=
    binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.one
  have hsum :
      M.outcome BinaryObservationIndex.zero +
          M.outcome BinaryObservationIndex.one = detEffect (Sys := Sys) A :=
    binaryObservation_total_eq_detEffect (Sys := Sys) M
  have hsumEff : IsEffect (Sys := Sys)
      (M.outcome BinaryObservationIndex.zero +
        M.outcome BinaryObservationIndex.one) := by
    simpa [hsum] using detEffect_isEffect (Sys := Sys) A
  have hdetEval :
      stateOperationalQuotientEval (Sys := Sys) (detEffect (Sys := Sys) A)
          (detEffect_isEffect (Sys := Sys) A) eta = 0 := by
    dsimp [eta]
    simp [map_sub, operationalStateClass, rho.2.2, sigma.2.2]
  have hsumEval :
      stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.zero) hzero eta +
        stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.one) hone eta = 0 := by
    calc
      _ = stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.zero +
            M.outcome BinaryObservationIndex.one) hsumEff eta :=
        (stateOperationalQuotientEval_add_effect (Sys := Sys)
          (M.outcome BinaryObservationIndex.zero)
          (M.outcome BinaryObservationIndex.one) hzero hone hsumEff eta).symm
      _ = stateOperationalQuotientEval (Sys := Sys)
          (detEffect (Sys := Sys) A) (detEffect_isEffect (Sys := Sys) A) eta :=
        stateOperationalQuotientEval_congr_effect (Sys := Sys) hsum hsumEff
          (detEffect_isEffect (Sys := Sys) A) eta
      _ = 0 := hdetEval
  have honeEval :
      stateOperationalQuotientEval (Sys := Sys)
          (M.outcome BinaryObservationIndex.one) hone eta =
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
          prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 := by
    dsimp [eta]
    simp [map_sub, operationalStateClass]
  change binaryObservationDiffEval (Sys := Sys) M eta = _
  unfold binaryObservationDiffEval
  linarith

private theorem testingPoint_score_le_operationalStateDistance {A : Sys}
    (M : BinaryObservationTest (Sys := Sys) A)
    (rho sigma : NormalizedState (Sys := Sys) A) :
    prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 ≤
      operationalStateDistance (Sys := Sys)
        (operationalStateClass (Sys := Sys) rho.1 rho.2.1)
        (operationalStateClass (Sys := Sys) sigma.1 sigma.2.1) := by
  have hdiff := binaryObservationDiffEval_le_operationalStateNorm (Sys := Sys) M
    (operationalStateClass (Sys := Sys) rho.1 rho.2.1 -
      operationalStateClass (Sys := Sys) sigma.1 sigma.2.1)
  rw [binaryObservationDiffEval_stateDiff_eq_two_mul (Sys := Sys) M rho sigma] at hdiff
  unfold operationalStateDistance
  norm_num
  linarith

/-- At order one, hockey-stick divergence is exactly the existing operational
state distance.  The latter is defined as one half of the operational norm;
the complement symmetry of a normalized state difference supplies the factor
two internally, so the displayed equality has coefficient `1`. -/
theorem hockeyStick_one_eq_operationalStateDistance {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    hockeyStick (Sys := Sys) HockeyStickOrder.one rho sigma =
      ENNReal.ofReal
        (operationalStateDistance (Sys := Sys)
          (operationalStateClass (Sys := Sys) rho.1 rho.2.1)
          (operationalStateClass (Sys := Sys) sigma.1 sigma.2.1)) := by
  apply le_antisymm
  · unfold hockeyStick regionSupENNReal
    apply iSup_le
    rintro ⟨z, hz⟩
    rcases hz with ⟨M, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    simpa [testingPoint, HockeyStickOrder.one] using
      testingPoint_score_le_operationalStateDistance (Sys := Sys) M rho sigma
  · let H : ℝ≥0∞ :=
      hockeyStick (Sys := Sys) HockeyStickOrder.one rho sigma
    let eta : OperationalStateSpaceReal (Sys := Sys) A :=
      operationalStateClass (Sys := Sys) rho.1 rho.2.1 -
        operationalStateClass (Sys := Sys) sigma.1 sigma.2.1
    have hHtop : H ≠ ⊤ := by
      dsimp [H]
      exact hockeyStick_ne_top (Sys := Sys) HockeyStickOrder.one rho sigma
    have hnorm : operationalStateNorm (Sys := Sys) eta ≤ 2 * H.toReal := by
      apply operationalStateNorm_le_of_forall_binaryObservationDiff_le
      intro M
      rw [show eta =
          operationalStateClass (Sys := Sys) rho.1 rho.2.1 -
            operationalStateClass (Sys := Sys) sigma.1 sigma.2.1 by rfl]
      rw [binaryObservationDiffEval_stateDiff_eq_two_mul (Sys := Sys) M rho sigma]
      have hscore :
          ENNReal.ofReal
              (prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
                prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1) ≤ H := by
        dsimp [H]
        unfold hockeyStick regionSupENNReal
        exact le_iSup_of_le
          ⟨testingPoint (Sys := Sys) rho sigma M, ⟨M, rfl⟩⟩
          (by simp [testingPoint, HockeyStickOrder.one])
      have hscoreReal :
          prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
              prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 ≤
            H.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hHtop).mp hscore
      linarith
    apply ENNReal.ofReal_le_of_le_toReal
    unfold operationalStateDistance
    change (2 : ℝ)⁻¹ * operationalStateNorm (Sys := Sys) eta ≤ H.toReal
    norm_num
    linarith

end

end OPT
