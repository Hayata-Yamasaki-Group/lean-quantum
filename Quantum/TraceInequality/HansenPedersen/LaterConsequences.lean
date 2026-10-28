/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- The shift-approximation lemmas are public in `Quantum/TraceInequality/ShiftApproximation.lean`.
-- The private declarations of this file belong to three proof steps:
-- (1) the midpoint scalar inequality of Lemma 5.1.10,
-- (2) the CFC limit of the shifted reciprocal in Lemma 5.1.10
--     (one_div_add_t_tendsto_one_div etc.),
-- (3) the condition-conversion route of Corollary 5.1.11 (conditionV/VI bridges, reversal of the reciprocal order).
-- They are specific to this proof route and are kept private.

import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.Surface
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Surface
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Basic
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.VI2Instances
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.ConditionVIToII
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Surface
import Quantum.TraceInequality.HansenPedersen.ShiftApproximation

/-!
# Later consequences of the Hansen--Pedersen route

This file collects the downstream Hiai--Yanagi Chapter 5.1 consequences that
depend on the shared interval operator-monotonicity and operator-convexity
predicates and the monotone--convex equivalence layer.
Source: the Hansen--Pedersen development of these interval predicates.
It contains the reciprocal-function Lemma 5.1.10, the
positive-function equivalences of Corollary 5.1.11, and the proved examples
from Example 5.1.12.  The unproved aggregate examples and Furuta statement are
isolated under `HansenPedersen.Frontier`.

## Main results

* `one_div_operatorConvex_and_neg_one_div_operatorMonotone_Ioi`: Lemma 5.1.10
  on `(0,∞)`.
* `allHOperatorMonotone_equivalences_of_pos`: Corollary 5.1.11 for positive
  functions on `(0,∞)`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Lemma 5.1.10, Corollary 5.1.11, Example 5.1.12, and Theorem 5.1.19.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC510Plus

/- Instance caches: same pattern as
`CompressionInequality/RatioMonotoneToProjection.lean` — the real-scalar action
on `L ℋ` and its order/topology compatibility classes each trigger a deep,
non-cached `synthInstance` derivation re-run at many use sites of the CFC
arguments below. Section-level reducible local instances turn each search into
a head-match. -/

/-- Local reducible cache for the real module structure on `L ℋ`. -/
@[reducible, local instance] noncomputable def instModuleRealLHScoped :
    Module ℝ (L ℋ) := inferInstance

/-- Local reducible cache for monotonicity of real scalar multiplication in the scalar. -/
@[reducible, local instance] noncomputable def instPosSMulMonoRealLHScoped :
    PosSMulMono ℝ (L ℋ) := inferInstance

/-- Local reducible cache for monotonicity of real scalar multiplication in the operator. -/
@[reducible, local instance] noncomputable def instSMulPosMonoRealLHScoped :
    SMulPosMono ℝ (L ℋ) := inferInstance

/-- Local reducible cache for continuity of the real scalar action on `L ℋ`. -/
@[reducible, local instance] noncomputable def instContinuousSMulRealLHScoped :
    ContinuousSMul ℝ (L ℋ) := inferInstance

/-- Local reducible cache for the compatibility of star with real scalar multiplication. -/
@[reducible, local instance] noncomputable def instStarModuleRealLHScoped :
    StarModule ℝ (L ℋ) := inferInstance

/-- Local reducible cache for the real algebra structure on bounded operators. -/
@[reducible, local instance] noncomputable def instAlgebraRealLHScoped :
    Algebra ℝ (L ℋ) := inferInstance

/-- Local reducible cache for the real scalar multiplication structure on `L ℋ`. -/
@[reducible, local instance] noncomputable def instSMulRealLHScoped :
    SMul ℝ (L ℋ) := inferInstance

/-- Local reducible cache for the real multiplicative action on `L ℋ`. -/
@[reducible, local instance] noncomputable def instMulActionRealLHScoped :
    MulAction ℝ (L ℋ) := inferInstance

/-- Local reducible cache for the zero-preserving real scalar action on `L ℋ`. -/
@[reducible, local instance] noncomputable def instSMulZeroClassRealLHScoped :
    SMulZeroClass ℝ (L ℋ) := inferInstance

/-- Local reducible cache for right-addition monotonicity in the operator order. -/
@[reducible, local instance] noncomputable def instAddRightMonoLHScoped :
    AddRightMono (L ℋ) := inferInstance

/-- Local reducible cache for left-addition monotonicity in the operator order. -/
@[reducible, local instance] noncomputable def instAddLeftMonoLHScoped :
    AddLeftMono (L ℋ) := inferInstance

/-- Local reducible cache for reflecting order through right addition on `L ℋ`. -/
@[reducible, local instance] noncomputable def instAddRightReflectLELHScoped :
    AddRightReflectLE (L ℋ) := inferInstance

/-- Local reducible cache for the `star_mul` law on bounded operators. -/
@[reducible, local instance] noncomputable def instStarMulLHScoped :
    StarMul (L ℋ) := inferInstance

/-- Local reducible cache for the monoid structure on bounded operators. -/
@[reducible, local instance] noncomputable def instMonoidLHScoped :
    Monoid (L ℋ) := inferInstance

/-- Convexity half of **Lemma 5.1.10**.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem one_div_operatorConvexOnInterval_Ioi :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa [OperatorConvexOnInterval] using
    (LownerHeinzTheorem.one_div_operatorConvexOn_Ioi (ℋ := ℋ))

private lemma scalar_reciprocal_midpoint_le {t : ℝ} (ht : 0 < t) :
    (((1 + t) / 2)⁻¹ : ℝ) ≤ (1 + t⁻¹) / 2 := by
  field_simp [ht.ne']
  nlinarith [sq_nonneg (t - 1)]

private theorem one_div_operatorMidpointConvexOnInterval_Ioi_book_nontrivial :
    OperatorMidpointConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  intro A B hA hB hAs hBs
  /- Step 1: Conjugate by A^{-1/2} to reduce the midpoint reciprocal inequality to X. -/
  let S := ConvexityCharacterization.sqrtPos A
  let U := ConvexityCharacterization.invSqrtPos A
  let X := U * B * U
  let m : ℝ → ℝ := fun x ↦ (1 / 2 : ℝ) * (x + 1)
  let f : ℝ → ℝ := fun x ↦ (m x)⁻¹
  let g : ℝ → ℝ := fun x ↦ (1 / 2 : ℝ) * (1 + x⁻¹)
  have hA0 : 0 ≤ A := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi (ℋ := ℋ) hA hAs
  have hB0 : 0 ≤ B := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi (ℋ := ℋ) hB hBs
  have hApos : IsStrictlyPositive A :=
    isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi hA hAs
  have hBpos : IsStrictlyPositive B :=
    isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi hB hBs
  have hAs_pos : spectrum ℝ A ⊆ positiveOpenRay (⊤ : WithTop ℝ) := by
    simpa [positiveOpenRay_top] using hAs
  have hS_sa : IsSelfAdjoint S :=
    ConvexityCharacterization.sqrtPos_selfAdjoint (K := ℋ) (A := A)
  have hU_sa : IsSelfAdjoint U :=
    ConvexityCharacterization.invSqrtPos_selfAdjoint (K := ℋ) (A := A)
  have hUS : U * S = (1 : L ℋ) := by
    simpa [U, S] using
      ConvexityCharacterization.invSqrtPos_mul_sqrtPos (K := ℋ) (A := A) hA hAs_pos
  have hSU : S * U = (1 : L ℋ) := by
    simpa [U, S] using
      ConvexityCharacterization.sqrtPos_mul_invSqrtPos (K := ℋ) (A := A) hA hAs_pos
  have hSS : S * S = A := by
    simpa [S] using
      ConvexityCharacterization.sqrtPos_sq (K := ℋ) (A := A) hA hAs_pos
  have hU_unit : IsUnit U := by
    refine ⟨⟨U, S, hUS, hSU⟩, rfl⟩
  have hX0 : 0 ≤ X := by
    simpa [X, hU_sa.star_eq, mul_assoc] using star_left_conjugate_nonneg hB0 U
  have hX_sa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX0
  have hXpos : IsStrictlyPositive X := by
    rw [show X = star U * B * U by simp [X, hU_sa.star_eq]]
    exact (IsUnit.isStrictlyPositive_star_left_conjugate_iff (u := U) (a := B) hU_unit).2 hBpos
  have hXs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hXpos.spectrum_pos hx
  have hm_cont : ContinuousOn m (spectrum ℝ X) := by
    have hone : ContinuousOn (fun _ : ℝ ↦ (1 : ℝ)) (spectrum ℝ X) := continuousOn_const
    change ContinuousOn (fun x : ℝ ↦ (1 / 2 : ℝ) * (x + 1)) (spectrum ℝ X)
    simpa [m, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm] using
      (continuousOn_id.add hone).const_mul (1 / 2 : ℝ)
  have hf_cont : ContinuousOn f (spectrum ℝ X) := by
    refine (hm_cont.inv₀ ?_)
    intro x hx
    have hx0 : 0 < x := by
      simpa [Set.mem_Ioi] using hXs hx
    dsimp [m]
    linarith
  have hg_cont : ContinuousOn g (spectrum ℝ X) := by
    have hcont_inv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ X) :=
      ContinuousOn.inv₀ continuousOn_id (by
        intro x hx
        exact ne_of_gt (by simpa [Set.mem_Ioi] using hXs hx))
    have hone : ContinuousOn (fun _ : ℝ ↦ (1 : ℝ)) (spectrum ℝ X) := continuousOn_const
    change ContinuousOn (fun x : ℝ ↦ (1 / 2 : ℝ) * (1 + x⁻¹)) (spectrum ℝ X)
    simpa [g, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm] using
      (hone.add hcont_inv).const_mul (1 / 2 : ℝ)
  /- Step 2: Lift the scalar reciprocal midpoint bound to CFC on spectrum X. -/
  have hcore_nonneg : (0 : L ℋ) ≤ cfcR (ℋ := ℋ) (fun x : ℝ ↦ g x - f x) X := by
    refine cfc_nonneg ?_
    intro x hx
    dsimp [f, g]
    simpa [m, div_eq_mul_inv, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using sub_nonneg.mpr
      (scalar_reciprocal_midpoint_le (by simpa [Set.mem_Ioi] using hXs hx))
  have hX_midpoint :
      cfcR (ℋ := ℋ) f X ≤ cfcR (ℋ := ℋ) g X := by
    have hsub :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ g x - f x) X =
          cfcR (ℋ := ℋ) g X - cfcR (ℋ := ℋ) f X := by
      simpa [cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR] using
        (cfc_sub (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
          (f := g) (g := f) (a := X) hg_cont hf_cont)
    rw [hsub] at hcore_nonneg
    exact sub_nonneg.mp hcore_nonneg
  /- Step 3: Identify the affine CFC of X with the midpoint operator M needed for inversion. -/
  let M : L ℋ := (1 / 2 : ℝ) • ((1 : L ℋ) + X)
  have hM_eq : cfcR (ℋ := ℋ) m X = M := by
    have hadd :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ x + 1) X = (1 : L ℋ) + X := by
      simpa [cfcR, cfc_id' (R := ℝ) (a := X) (ha := hX_sa), add_comm] using
        (cfc_add_const (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
          (r := (1 : ℝ)) (f := fun x : ℝ ↦ x) (a := X)
          (hf := continuousOn_id) (ha := hX_sa))
    calc
      cfcR (ℋ := ℋ) m X
          = (1 / 2 : ℝ) • cfcR (ℋ := ℋ) (fun x : ℝ ↦ x + 1) X := by
              simpa [m, cfcR] using
                (cfc_const_mul (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
                  (r := (1 / 2 : ℝ)) (f := fun x : ℝ ↦ x + 1) (a := X)
                  (hf := continuousOn_id.add continuousOn_const))
      _ = M := by
            simpa [M] using congrArg (fun T : L ℋ => (1 / 2 : ℝ) • T) hadd
  have hMm : spectrum ℝ M ⊆ Set.Ioi (0 : ℝ) := by
    have hMpos : IsStrictlyPositive M := by
      rw [← hM_eq]
      simpa [m, cfcR] using
        ((cfc_isStrictlyPositive_iff (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
          (f := m) (a := X) hm_cont hX_sa).2 (by
            intro x hx
            have hx0 : 0 < x := by
              simpa [Set.mem_Ioi] using hXs hx
            dsimp [m]
            linarith))
    intro x hx
    exact hMpos.spectrum_pos hx
  have hM_sa : IsSelfAdjoint M := by
    rw [← hM_eq]
    simp [m, cfcR]
  have hf_eq : cfcR (ℋ := ℋ) f X = Ring.inverse M := by
    dsimp [f]
    have h' := cfc_inv (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
      (f := m) (a := X) (fun x hx ↦ by
        have hx0 : 0 < x := by
          simpa [Set.mem_Ioi] using hXs hx
        dsimp [m]
        linarith) (ha := hX_sa)
    simpa [hM_eq] using h'
  have hXinv_eq : cfcR (ℋ := ℋ) (fun x : ℝ ↦ x⁻¹) X = Ring.inverse X :=
    cfcR_inv_eq_inverse (A := X) hX_sa hXs
  have hg_eq :
      cfcR (ℋ := ℋ) g X = (1 / 2 : ℝ) • ((1 : L ℋ) + Ring.inverse X) := by
    have hcont_inv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ X) :=
      ContinuousOn.inv₀ continuousOn_id (by
        intro x hx
        exact ne_of_gt (by simpa [Set.mem_Ioi] using hXs hx))
    have hadd :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 + x⁻¹) X = (1 : L ℋ) + Ring.inverse X := by
      simpa [cfcR, hXinv_eq, add_comm] using
        (cfc_add_const (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
          (r := (1 : ℝ)) (f := fun x : ℝ ↦ x⁻¹) (a := X)
          (hf := hcont_inv) (ha := hX_sa))
    calc
      cfcR (ℋ := ℋ) g X
          = (1 / 2 : ℝ) • cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 + x⁻¹) X := by
              simpa [g, cfcR] using
                (cfc_const_mul (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
                  (r := (1 / 2 : ℝ)) (f := fun x : ℝ ↦ 1 + x⁻¹) (a := X)
                  (hf := continuousOn_const.add hcont_inv))
      _ = (1 / 2 : ℝ) • ((1 : L ℋ) + Ring.inverse X) := by rw [hadd]
  have hX_eq : X = U * B * U := rfl
  have hmid_expr :
      ((1 / 2 : ℝ) • (A + B)) = S * M * S := by
    have hSXS : S * X * S = B := by
      dsimp [X]
      calc
        S * (U * B * U) * S = (S * U) * B * (U * S) := by
          simp [mul_assoc]
        _ = B := by
          simp [hSU, hUS]
    calc
      ((1 / 2 : ℝ) • (A + B))
          = (1 / 2 : ℝ) • (S * S + S * X * S) := by
              rw [hSS, hSXS]
      _ = S * M * S := by
            dsimp [M]
            simp [mul_assoc, add_mul, mul_add]
  have hmid_spec : spectrum ℝ ((1 / 2 : ℝ) • (A + B)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hmid_expr]
    intro x hx
    have hS_unit : IsUnit S := by
      refine ⟨⟨S, U, hSU, hUS⟩, rfl⟩
    have hmid_pos : IsStrictlyPositive (star S * M * S) := by
      exact (IsUnit.isStrictlyPositive_star_left_conjugate_iff (u := S) (a := M) hS_unit).2 <| by
        rw [show M = cfcR (ℋ := ℋ) m X by exact hM_eq.symm]
        simpa [m, cfcR] using
          ((cfc_isStrictlyPositive_iff (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
            (f := m) (a := X) hm_cont hX_sa).2 (by
              intro y hy
              have hy0 : 0 < y := by
                simpa [Set.mem_Ioi] using hXs hy
              dsimp [m]
              linarith))
          
    have hx' : x ∈ spectrum ℝ (star S * M * S) := by
      simpa [hS_sa.star_eq, hmid_expr] using hx
    exact hmid_pos.spectrum_pos hx'
  have hmid_nonneg : (0 : L ℋ) ≤ (1 / 2 : ℝ) • (A + B) := by
    rw [hmid_expr]
    simpa [hS_sa.star_eq] using star_left_conjugate_nonneg
      (show 0 ≤ M by
        exact (isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi hM_sa hMm).nonneg) S
  have hmid_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (A + B)) := IsSelfAdjoint.of_nonneg hmid_nonneg
  /- Step 4: Rewrite the reciprocal of the midpoint as the conjugate of the inverse of M. -/
  have hleft_eq :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) ((1 / 2 : ℝ) • (A + B))
        = U * cfcR (ℋ := ℋ) f X * U := by
    have hleft_inv :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) ((1 / 2 : ℝ) • (A + B))
          = Ring.inverse ((1 / 2 : ℝ) • (A + B)) := by
      have hleft_inv' :
          cfcR (ℋ := ℋ) (fun x : ℝ ↦ x⁻¹) ((1 / 2 : ℝ) • (A + B))
            = Ring.inverse ((1 / 2 : ℝ) • (A + B)) := by
        exact cfcR_inv_eq_inverse (A := ((1 / 2 : ℝ) • (A + B))) hmid_sa hmid_spec
      simpa [one_div] using hleft_inv'
    have hmul :
        (U * Ring.inverse M * U) * ((1 / 2 : ℝ) • (A + B)) = (1 : L ℋ) := by
      rw [hmid_expr]
      calc
        U * Ring.inverse M * U * (S * M * S)
            = U * Ring.inverse M * (U * S) * M * S := by
                simp [mul_assoc]
        _ = U * Ring.inverse M * (1 : L ℋ) * M * S := by
              rw [hUS]
        _ = U * Ring.inverse M * M * S := by
              simp
        _ = U * (Ring.inverse M * M) * S := by
              simp [mul_assoc]
        _ = U * S := by
              rw [Ring.inverse_mul_cancel M
                (isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi hM_sa hMm).isUnit]
              simp
        _ = 1 := hUS
    have hmid_unit : IsUnit ((1 / 2 : ℝ) • (A + B)) :=
      (isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi hmid_sa hmid_spec).isUnit
    have hleft_inv_eq :
        Ring.inverse ((1 / 2 : ℝ) • (A + B)) = U * Ring.inverse M * U := by
      calc
        Ring.inverse ((1 / 2 : ℝ) • (A + B))
            = (1 : L ℋ) * Ring.inverse ((1 / 2 : ℝ) • (A + B)) := by rw [one_mul]
        _ = (U * Ring.inverse M * U) * ((1 / 2 : ℝ) • (A + B)) *
              Ring.inverse ((1 / 2 : ℝ) • (A + B)) := by rw [hmul]
        _ = U * Ring.inverse M * U := by
              exact Ring.mul_inverse_cancel_right ((1 / 2 : ℝ) • (A + B))
                (U * Ring.inverse M * U) hmid_unit
    calc
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) ((1 / 2 : ℝ) • (A + B))
          = Ring.inverse ((1 / 2 : ℝ) • (A + B)) := hleft_inv
      _ = U * Ring.inverse M * U := hleft_inv_eq
      _ = U * cfcR (ℋ := ℋ) f X * U := by rw [hf_eq]
  /- Step 5: Rewrite the endpoint reciprocals in the same conjugated coordinates. -/
  have hAinv_eq :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A = U * (1 : L ℋ) * U := by
    have hAinv : cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A = Ring.inverse A := by
      simpa [one_div] using cfcR_inv_eq_inverse (A := A) hA hAs
    have hmul : (U * (1 : L ℋ) * U) * A = (1 : L ℋ) := by
      have hAsq : A = S * S := hSS.symm
      calc
        U * 1 * U * A = (U * U) * A := by simp [mul_assoc]
        _ = U * (U * (S * S)) := by rw [hAsq]; simp [mul_assoc]
        _ = U * ((U * S) * S) := by simp [mul_assoc]
        _ = U * S := by
              rw [hUS]
              exact hUS
        _ = 1 := hUS
    have hAinv_eq' : Ring.inverse A = U * (1 : L ℋ) * U := by
      calc
        Ring.inverse A = (1 : L ℋ) * Ring.inverse A := by simp
        _ = (U * (1 : L ℋ) * U) * A * Ring.inverse A := by rw [hmul]
        _ = U * (1 : L ℋ) * U := by
              exact Ring.mul_inverse_cancel_right A (U * (1 : L ℋ) * U) hApos.isUnit
    calc
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A = Ring.inverse A := hAinv
      _ = U * (1 : L ℋ) * U := hAinv_eq'
  have hBinv_eq :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B = U * (Ring.inverse X) * U := by
    have hBinv : cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B = Ring.inverse B := by
      simpa [one_div] using cfcR_inv_eq_inverse (A := B) hB hBs
    have hmul : (U * Ring.inverse X * U) * B = (1 : L ℋ) := by
      have hSXS : S * X * S = B := by
        dsimp [X]
        calc
          S * (U * B * U) * S = (S * U) * B * (U * S) := by
            simp [mul_assoc]
          _ = B := by
            simp [hSU, hUS]
      calc
        U * Ring.inverse X * U * B
            = U * Ring.inverse X * U * (S * X * S) := by rw [← hSXS]
        _ = U * Ring.inverse X * (U * S) * X * S := by simp [mul_assoc]
        _ = U * Ring.inverse X * X * S := by
              rw [hUS]
              simp
        _ = U * (Ring.inverse X * X) * S := by simp [mul_assoc]
        _ = U * S := by
              rw [Ring.inverse_mul_cancel X hXpos.isUnit]
              simp
        _ = 1 := hUS
    have hBinv_eq' : Ring.inverse B = U * Ring.inverse X * U := by
      calc
        Ring.inverse B = (1 : L ℋ) * Ring.inverse B := by simp
        _ = (U * Ring.inverse X * U) * B * Ring.inverse B := by rw [hmul]
        _ = U * Ring.inverse X * U := by
              exact Ring.mul_inverse_cancel_right B (U * Ring.inverse X * U) hBpos.isUnit
    calc
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B = Ring.inverse B := hBinv
      _ = U * Ring.inverse X * U := hBinv_eq'
  have hright_eq :
      (1 / 2 : ℝ) • (cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A
        + cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B)
        = U * cfcR (ℋ := ℋ) g X * U := by
    rw [hg_eq, hAinv_eq, hBinv_eq]
    calc
      (1 / 2 : ℝ) • (U * 1 * U + U * Ring.inverse X * U)
          = (1 / 2 : ℝ) • (U * ((1 : L ℋ) + Ring.inverse X) * U) := by
              simp [mul_assoc, mul_add, add_mul]
      _ = U * ((1 / 2 : ℝ) • (((1 : L ℋ) + Ring.inverse X) * U)) := by
            simp [mul_assoc]
      _ = U * (((1 / 2 : ℝ) • ((1 : L ℋ) + Ring.inverse X)) * U) := by
            rw [← smul_mul_assoc]
      _ = U * ((1 / 2 : ℝ) • ((1 : L ℋ) + Ring.inverse X)) * U := by
            simp [mul_assoc]
  /- Step 6: Transfer the CFC inequality through conjugation and undo the coordinate change. -/
  calc
    cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) ((1 / 2 : ℝ) • (A + B))
        = U * cfcR (ℋ := ℋ) f X * U := hleft_eq
    _ ≤ U * cfcR (ℋ := ℋ) g X * U := by
          simpa [hU_sa.star_eq, mul_assoc] using star_left_conjugate_le_conjugate hX_midpoint U
    _ = (1 / 2 : ℝ) • (cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A
          + cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B) := hright_eq.symm

omit [Nontrivial (L ℋ)] in
/-- Book-facing midpoint core for **Lemma 5.1.10**. This theorem follows the book's midpoint
route: scalar reciprocal inequality, CFC lift, and substitution
`X = A^{-1/2} B A^{-1/2}`.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem one_div_operatorMidpointConvexOnInterval_Ioi_book :
    OperatorMidpointConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  by_cases hnt : Nontrivial (L ℋ)
  · letI := hnt
    exact one_div_operatorMidpointConvexOnInterval_Ioi_book_nontrivial (ℋ := ℋ)
  · intro A B hA hB hAs hBs
    haveI : Subsingleton (L ℋ) := not_nontrivial_iff_subsingleton.mp hnt
    exact le_of_eq (Subsingleton.elim _ _)

omit [Nontrivial (L ℋ)] in
/-- Book-statement monotonicity half for Lemma 5.1.10. This follows the low-level
inverse-order-reversal route corresponding to Exercise 2.3(5).
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem neg_one_div_operatorMonotoneOnInterval_Ioi_book :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(1 / x)) := by
  intro A B hA hB hAs hBs hAB
  have hA0 : 0 ≤ A := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi (ℋ := ℋ) hA hAs
  have hB0 : 0 ≤ B := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi (ℋ := ℋ) hB hBs
  let f : ℝ → ℝ := fun x ↦ x
  have hA_ne0 : ∀ x ∈ spectrum ℝ A, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (by simpa [f, Set.mem_Ioi] using hAs hx)
  have hB_ne0 : ∀ x ∈ spectrum ℝ B, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (by simpa [f, Set.mem_Ioi] using hBs hx)
  let uA : (L ℋ)ˣ :=
    cfcUnits (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A hA_ne0 (ha := hA)
  let uB : (L ℋ)ˣ :=
    cfcUnits (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f B hB_ne0 (ha := hB)
  have huA_val : (uA : L ℋ) = A := by
    simp [uA, cfcUnits, f, cfc_id' (R := ℝ) (a := A) (ha := hA)]
  have huB_val : (uB : L ℋ) = B := by
    simp [uB, cfcUnits, f, cfc_id' (R := ℝ) (a := B) (ha := hB)]
  have huB_nonneg : 0 ≤ (uB : L ℋ) := by
    simpa [huB_val] using hB0
  have huA_nonneg : 0 ≤ (uA : L ℋ) := by
    simpa [huA_val] using hA0
  have hua_le_hub : (uA : L ℋ) ≤ (uB : L ℋ) := by
    simpa [huA_val, huB_val] using hAB
  have hanti :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B ≤
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A := by
    have hinv : ((uB⁻¹ : (L ℋ)ˣ) : L ℋ) ≤ ((uA⁻¹ : (L ℋ)ˣ) : L ℋ) := by
      simpa using
        (CStarAlgebra.inv_le_inv (A := L ℋ) (a := uA) (b := uB)
          huA_nonneg hua_le_hub)
    simpa [uA, uB, cfcUnits, cfcR, f, one_div] using hinv
  have hneg :
      -(cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A) ≤
        -(cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B) := by
    exact neg_le_neg hanti
  simpa [cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR, cfc_neg] using hneg

private lemma conditionV_iff_quotient_monotone_Ioi {f : ℝ → ℝ} :
    ConvexityCharacterization.ConditionV.{u} ⊤ f ↔
      AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ f t / t) := by
  simp [ConvexityCharacterization.ConditionV, positiveOpenRay_top]

private lemma neg_inv_neg_div_eq_tdiv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    -(((-y) / x)⁻¹) = x / y := by
  field_simp [hx.ne', hy.ne']

private lemma neg_inv_neg_div_eq_mul_div {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    -(((-a) / (x * b))⁻¹) = x * b / a := by
  field_simp [hx.ne', ha.ne', hb.ne']

section Corollary511

@[fun_prop] private lemma continuousOn_inv_of_pos_Ioi {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) :
    ContinuousOn (fun t : ℝ ↦ 1 / f t) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hfx : f x ≠ 0 := (hpos x hx).ne'
  simpa [one_div] using (hf x hx).inv₀ hfx

@[fun_prop] private lemma continuousOn_tdiv_of_pos_Ioi {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) :
    ContinuousOn (fun t : ℝ ↦ t / f t) (Set.Ioi (0 : ℝ)) := by
  exact continuousOn_id.div hf <| by
    intro x hx
    exact (hpos x hx).ne'

@[fun_prop] private lemma continuousOn_f_div_t_Ioi {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun t : ℝ ↦ f t / t) (Set.Ioi (0 : ℝ)) := by
  exact hf.div continuousOn_id <| by
    intro x hx
    exact (show x ≠ 0 by exact ne_of_gt hx)

private lemma conditionVI_neg_iff_monotone_Ici {f : ℝ → ℝ} :
    ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t) ↔
      AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) f := by
  simp [ConvexityCharacterization.ConditionVI]

private lemma operatorMonotone_negInv_of_negative
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hneg : ∀ t ∈ Set.Ioi (0 : ℝ), h t < 0)
    (hmono : OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) h) :
    OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ -((h t)⁻¹)) := by
  intro A B hA hB hσA hσB hAB
  let k : ℝ → ℝ := fun t : ℝ ↦ -h t
  have hkA_cont : ContinuousOn k (spectrum ℝ A) := by
    refine hcont.neg.mono ?_
    intro x hx
    exact hσA hx
  have hkB_cont : ContinuousOn k (spectrum ℝ B) := by
    refine hcont.neg.mono ?_
    intro x hx
    exact hσB hx
  have hkA_ne0 : ∀ x ∈ spectrum ℝ A, k x ≠ 0 := by
    intro x hx
    exact (ne_of_gt (by simpa [k] using neg_pos.mpr (hneg x (hσA hx))))
  have hkB_ne0 : ∀ x ∈ spectrum ℝ B, k x ≠ 0 := by
    intro x hx
    exact (ne_of_gt (by simpa [k] using neg_pos.mpr (hneg x (hσB hx))))
  let uA : (L K)ˣ :=
    cfcUnits (R := ℝ) (A := L K) (p := IsSelfAdjoint) k A hkA_ne0 hkA_cont (ha := hA)
  let uB : (L K)ˣ :=
    cfcUnits (R := ℝ) (A := L K) (p := IsSelfAdjoint) k B hkB_ne0 hkB_cont (ha := hB)
  have huA_nonneg : 0 ≤ (uA : L K) := by
    dsimp [uA, k]
    refine cfc_nonneg ?_
    intro x hx
    exact le_of_lt (neg_pos.mpr (hneg x (hσA hx)))
  have huB_nonneg : 0 ≤ (uB : L K) := by
    dsimp [uB, k]
    refine cfc_nonneg ?_
    intro x hx
    exact le_of_lt (neg_pos.mpr (hneg x (hσB hx)))
  have hbase : cfcR (ℋ := K) h A ≤ cfcR (ℋ := K) h B := hmono hA hB hσA hσB hAB
  have huB_le_huA : (uB : L K) ≤ (uA : L K) := by
    simpa [uA, uB, cfcUnits, cfcR, k, cfc_neg] using neg_le_neg hbase
  have hinv : ((uA⁻¹ : (L K)ˣ) : L K) ≤ ((uB⁻¹ : (L K)ˣ) : L K) := by
    simpa using (CStarAlgebra.inv_le_inv (A := L K) (a := uB) (b := uA) huB_nonneg huB_le_huA)
  simpa [uA, uB, cfcUnits, cfcR, k, one_div] using hinv

private lemma allHOperatorMonotone_negInv_of_negative {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hneg : ∀ t ∈ Set.Ioi (0 : ℝ), h t < 0)
    (hmono : AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) h) :
    AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ -((h t)⁻¹)) := by
  intro K _ _ _ _ _
  exact operatorMonotone_negInv_of_negative (K := K) hcont hneg (hmono K)

private lemma operatorMonotoneOnInterval_congr_Ioi
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioi (0 : ℝ), f x = g x)
    (hmono : OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) f) :
    OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) g := by
  intro A B hA hB hσA hσB hAB
  have hAeq : cfcR (ℋ := K) g A = cfcR (ℋ := K) f A := by
    apply cfc_congr
    intro x hx
    symm
    exact hfg x (hσA hx)
  have hBeq : cfcR (ℋ := K) g B = cfcR (ℋ := K) f B := by
    apply cfc_congr
    intro x hx
    symm
    exact hfg x (hσB hx)
  rw [hAeq, hBeq]
  exact hmono hA hB hσA hσB hAB

private lemma allHOperatorMonotoneOnInterval_congr_Ioi
    {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioi (0 : ℝ), f x = g x)
    (hmono : AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) f) :
    AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) g := by
  intro K _ _ _ _ _
  exact operatorMonotoneOnInterval_congr_Ioi (K := K) hfg (hmono K)

private lemma cfc_tdiv_shift_tendsto_Ioi
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) :
    Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ x / f (x + p)) A)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (cfcR (ℋ := K) (fun x : ℝ ↦ x / f x) A)) := by
  let h : ℝ → ℝ := fun x : ℝ ↦ 1 / f x
  have hh : ContinuousOn h (Set.Ioi (0 : ℝ)) := continuousOn_inv_of_pos_Ioi hf hpos
  have hshift :
      Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := K) h A)) :=
    shifted_cfc_tendsto_Ioi (K := K) hA hσA hh
  have hrepr :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := K) (fun x : ℝ ↦ x / f (x + p)) A =
          A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hcont_shift : ContinuousOn (fun x : ℝ ↦ h (x + p)) (spectrum ℝ A) := by
      refine hh.comp (continuousOn_id.add continuousOn_const) ?_
      intro x hx
      have hx0 : 0 < x := by simpa [Set.mem_Ioi] using hσA hx
      have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
      exact add_pos hx0 hp0
    calc
      cfcR (ℋ := K) (fun x : ℝ ↦ x / f (x + p)) A
          = cfcR (ℋ := K) (fun x : ℝ ↦ x * h (x + p)) A := by
              apply cfc_congr
              intro x hx
              simp [h, div_eq_mul_inv]
      _ = cfcR (ℋ := K) (fun x : ℝ ↦ x) A *
            cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
            simpa [cfcR] using
              (cfc_mul (R := ℝ) (A := L K) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ h (x + p)) (a := A)
                (hf := continuousOn_id) (hg := hcont_shift))
      _ = A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
            simp [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)]
  have htarget :
      cfcR (ℋ := K) (fun x : ℝ ↦ x / f x) A = A * cfcR (ℋ := K) h A := by
    calc
      cfcR (ℋ := K) (fun x : ℝ ↦ x / f x) A
          = cfcR (ℋ := K) (fun x : ℝ ↦ x * h x) A := by
              apply cfc_congr
              intro x hx
              simp [h, div_eq_mul_inv]
      _ = cfcR (ℋ := K) (fun x : ℝ ↦ x) A * cfcR (ℋ := K) h A := by
            simpa [cfcR] using
              (cfc_mul (R := ℝ) (A := L K) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x) (g := h) (a := A)
                (hf := continuousOn_id)
                (hg := hh.mono (by intro x hx; exact hσA hx)))
      _ = A * cfcR (ℋ := K) h A := by
            simp [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)]
  have hmul :
      Filter.Tendsto (fun p : ℝ ↦ A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (A * cfcR (ℋ := K) h A)) := by
    simpa using (tendsto_const_nhds.mul hshift)
  have hmul' :
      Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ x / f (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (A * cfcR (ℋ := K) h A)) := by
    exact hmul.congr' (Filter.EventuallyEq.symm hrepr)
  simpa [htarget] using hmul'

private lemma cfc_mul_shift_div_t_tendsto_Ioi
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ x * f (x + p) / (x + p)) A)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (cfcR (ℋ := K) f A)) := by
  let h : ℝ → ℝ := fun x : ℝ ↦ f x / x
  have hh : ContinuousOn h (Set.Ioi (0 : ℝ)) := continuousOn_f_div_t_Ioi hf
  have hshift :
      Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := K) h A)) :=
    shifted_cfc_tendsto_Ioi (K := K) hA hσA hh
  have hrepr :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := K) (fun x : ℝ ↦ x * f (x + p) / (x + p)) A =
          A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hcont_shift : ContinuousOn (fun x : ℝ ↦ h (x + p)) (spectrum ℝ A) := by
      refine hh.comp (continuousOn_id.add continuousOn_const) ?_
      intro x hx
      have hx0 : 0 < x := by simpa [Set.mem_Ioi] using hσA hx
      have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
      exact add_pos hx0 hp0
    calc
      cfcR (ℋ := K) (fun x : ℝ ↦ x * f (x + p) / (x + p)) A
          = cfcR (ℋ := K) (fun x : ℝ ↦ x * h (x + p)) A := by
              apply cfc_congr
              intro x hx
              simp [h, div_eq_mul_inv, mul_assoc]
      _ = cfcR (ℋ := K) (fun x : ℝ ↦ x) A *
            cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
            simpa [cfcR] using
              (cfc_mul (R := ℝ) (A := L K) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ h (x + p)) (a := A)
                (hf := continuousOn_id) (hg := hcont_shift))
      _ = A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A := by
            simp [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)]
  have htarget : cfcR (ℋ := K) f A = A * cfcR (ℋ := K) h A := by
    calc
      cfcR (ℋ := K) f A = cfcR (ℋ := K) (fun x : ℝ ↦ x * h x) A := by
        apply cfc_congr
        intro x hx
        have hx0 : x ≠ 0 := (show 0 < x by simpa [Set.mem_Ioi] using hσA hx).ne'
        calc
          f x = x * (f x / x) := by field_simp [hx0]
          _ = x * h x := by simp [h]
      _ = cfcR (ℋ := K) (fun x : ℝ ↦ x) A * cfcR (ℋ := K) h A := by
            simpa [cfcR] using
              (cfc_mul (R := ℝ) (A := L K) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x) (g := h) (a := A)
                (hf := continuousOn_id)
                (hg := hh.mono (by intro x hx; exact hσA hx)))
      _ = A * cfcR (ℋ := K) h A := by
            simp [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)]
  have hmul :
      Filter.Tendsto (fun p : ℝ ↦ A * cfcR (ℋ := K) (fun x : ℝ ↦ h (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (A * cfcR (ℋ := K) h A)) := by
    simpa using (tendsto_const_nhds.mul hshift)
  have hmul' :
      Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ x * f (x + p) / (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (A * cfcR (ℋ := K) h A)) := by
    exact hmul.congr' (Filter.EventuallyEq.symm hrepr)
  simpa [htarget] using hmul'

-- final 5.1.11 equivalence combines several shifted CFC bridge theorems
/-- **Corollary 5.1.11** in Lean.
Source: Hiai–Yanagi, Corollary 5.1.11. -/
theorem allHOperatorMonotone_equivalences_of_pos {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) :
    ((AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) f ↔
        AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ t / f t)) ∧
      (AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ t / f t) ↔
        AllHOperatorConcaveOnInterval.{u} (Set.Ioi (0 : ℝ)) f) ∧
      (AllHOperatorConcaveOnInterval.{u} (Set.Ioi (0 : ℝ)) f →
        AllHOperatorConvexOnInterval.{u} (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ 1 / f t))) := by
  let q : ℝ → ℝ := fun t : ℝ ↦ t / f t
  let g : ℝ → ℝ := fun t : ℝ ↦ 1 / f t
  /- Step 1: Record continuity of the quotient and reciprocal on the positive domain. -/
  have hqcont : ContinuousOn q (Set.Ioi (0 : ℝ)) := by
    simpa [q] using continuousOn_tdiv_of_pos_Ioi hf hpos
  have hgcont : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    simpa [g] using continuousOn_inv_of_pos_Ioi hf hpos
  /- Step 2: Show f monotone implies t / f t monotone via shifted half-lines. -/
  have h12 :
      AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) f ↔
        AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) q := by
    constructor
    · intro hmono K _ _ _ _ _
      refine operatorMonotoneOn_of_tendsto_Ioi (K := K)
        (F := fun p x : ℝ ↦ x / f (x + p)) (f := q) ?_ ?_
      · intro A hA hσA
        simpa [q] using cfc_tdiv_shift_tendsto_Ioi (K := K) hA hσA hf hpos
      · filter_upwards [self_mem_nhdsWithin] with p hp
        have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
        let fp : ℝ → ℝ := fun t : ℝ ↦ f (t + p)
        let hneg : ℝ → ℝ := fun t : ℝ ↦ -fp t
        have hfp_cont_half : ContinuousOn fp (halfOpenRay ⊤) := by
          simpa [fp] using continuousOn_shift_Ici hf hp0
        have hneg_cont_half : ContinuousOn hneg (halfOpenRay ⊤) := by
          simpa [hneg] using hfp_cont_half.neg
        have hneg_nonpos : ∀ t ∈ halfOpenRay ⊤, hneg t ≤ 0 := by
          intro t ht
          have htp : 0 < t + p := add_pos_of_nonneg_of_pos ht.1 hp0
          have hfp_pos : 0 < fp t := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
          simpa [hneg, fp] using neg_nonpos.mpr hfp_pos.le
        have hmono_shift_half : AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) fp := by
          simpa [fp] using allHOperatorMonotone_shift_Ici hf hmono hp0
        have hVI : ConvexityCharacterization.ConditionVI.{u} hneg := by
          exact (conditionVI_neg_iff_monotone_Ici (f := fp)).mpr hmono_shift_half
        have h58 := operatorConvexity_characterizations_top hneg
        have h58 := h58 hneg_cont_half
        have hIffVI :
            ConvexityCharacterization.ConditionI.{u} ⊤ hneg ↔
              ConvexityCharacterization.ConditionVI.{u} hneg :=
          h58.2 hneg_nonpos
        have hI : ConvexityCharacterization.ConditionI.{u} ⊤ hneg := hIffVI.mpr hVI
        have hIffV :
            ConvexityCharacterization.ConditionI.{u} ⊤ hneg ↔
              ConvexityCharacterization.ConditionV.{u} ⊤ hneg :=
          h58.1.2.2.2
        have hV : ConvexityCharacterization.ConditionV.{u} ⊤ hneg := hIffV.mp hI
        have hquot :
            AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ))
              (fun t : ℝ ↦ hneg t / t) := by
          exact (conditionV_iff_quotient_monotone_Ioi (f := hneg)).mp hV
        have hquot_cont : ContinuousOn (fun t : ℝ ↦ hneg t / t) (Set.Ioi (0 : ℝ)) := by
          have hneg_cont_Ioi : ContinuousOn hneg (Set.Ioi (0 : ℝ)) := by
            refine hneg_cont_half.mono ?_
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using hx.le
          exact continuousOn_f_div_t_Ioi hneg_cont_Ioi
        have hquot_neg : ∀ t ∈ Set.Ioi (0 : ℝ), hneg t / t < 0 := by
          intro t ht
          have htp : 0 < t + p := add_pos ht hp0
          have hfp_pos : 0 < fp t := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
          have hneg_neg : hneg t < 0 := by simpa [hneg, fp] using neg_neg_iff_pos.mpr hfp_pos
          exact div_neg_of_neg_of_pos hneg_neg ht
        have hres :
            OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ))
              (fun t : ℝ ↦ -((hneg t / t)⁻¹)) :=
          operatorMonotone_negInv_of_negative (K := K) hquot_cont hquot_neg (hquot K)
        refine operatorMonotoneOnInterval_congr_Ioi (K := K) ?_ hres
        intro t ht
        have htp : 0 < t + p := add_pos ht hp0
        have hfp_pos : 0 < fp t := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
        simpa [hneg, fp, q] using neg_inv_neg_div_eq_tdiv ht hfp_pos
    /- Step 3: Reverse the quotient step by applying the same mechanism to the shifted quotient. -/
    · intro hqmono K _ _ _ _ _
      refine operatorMonotoneOn_of_tendsto_Ioi (K := K)
        (F := fun p x : ℝ ↦ x * f (x + p) / (x + p)) (f := f) ?_ ?_
      · intro A hA hσA
        exact cfc_mul_shift_div_t_tendsto_Ioi (K := K) hA hσA hf
      · filter_upwards [self_mem_nhdsWithin] with p hp
        have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
        let qp : ℝ → ℝ := fun t : ℝ ↦ (t + p) / f (t + p)
        let hneg : ℝ → ℝ := fun t : ℝ ↦ -qp t
        have hqp_shift_half : AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) qp := by
          simpa [qp, q] using allHOperatorMonotone_shift_Ici hqcont hqmono hp0
        have hneg_cont_half : ContinuousOn hneg (halfOpenRay ⊤) := by
          have hqp_cont_half : ContinuousOn qp (halfOpenRay ⊤) := by
            simpa [qp, q] using continuousOn_shift_Ici hqcont hp0
          simpa [hneg] using hqp_cont_half.neg
        have hneg_nonpos : ∀ t ∈ halfOpenRay ⊤, hneg t ≤ 0 := by
          intro t ht
          have htp : 0 < t + p := add_pos_of_nonneg_of_pos ht.1 hp0
          have hfp_pos : 0 < f (t + p) := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
          have hqp_pos : 0 < qp t := by
            exact div_pos htp hfp_pos
          simpa [hneg] using neg_nonpos.mpr hqp_pos.le
        have hVI : ConvexityCharacterization.ConditionVI.{u} hneg := by
          exact (conditionVI_neg_iff_monotone_Ici (f := qp)).mpr hqp_shift_half
        have h58 := operatorConvexity_characterizations_top hneg
        have h58 := h58 hneg_cont_half
        have hIffVI :
            ConvexityCharacterization.ConditionI.{u} ⊤ hneg ↔
              ConvexityCharacterization.ConditionVI.{u} hneg :=
          h58.2 hneg_nonpos
        have hI : ConvexityCharacterization.ConditionI.{u} ⊤ hneg := hIffVI.mpr hVI
        have hIffV :
            ConvexityCharacterization.ConditionI.{u} ⊤ hneg ↔
              ConvexityCharacterization.ConditionV.{u} ⊤ hneg :=
          h58.1.2.2.2
        have hV : ConvexityCharacterization.ConditionV.{u} ⊤ hneg := hIffV.mp hI
        have hquot :
            AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ))
              (fun t : ℝ ↦ hneg t / t) := by
          exact (conditionV_iff_quotient_monotone_Ioi (f := hneg)).mp hV
        have hquot_cont : ContinuousOn (fun t : ℝ ↦ hneg t / t) (Set.Ioi (0 : ℝ)) := by
          have hneg_cont_Ioi : ContinuousOn hneg (Set.Ioi (0 : ℝ)) := by
            refine hneg_cont_half.mono ?_
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using hx.le
          exact continuousOn_f_div_t_Ioi hneg_cont_Ioi
        have hquot_neg : ∀ t ∈ Set.Ioi (0 : ℝ), hneg t / t < 0 := by
          intro t ht
          have htp : 0 < t + p := add_pos ht hp0
          have hfp_pos : 0 < f (t + p) := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
          have hqp_pos : 0 < qp t := div_pos htp hfp_pos
          have hneg_neg : hneg t < 0 := by simpa [hneg] using neg_neg_iff_pos.mpr hqp_pos
          exact div_neg_of_neg_of_pos hneg_neg ht
        have hres :
            OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ))
              (fun t : ℝ ↦ -((hneg t / t)⁻¹)) :=
          operatorMonotone_negInv_of_negative (K := K) hquot_cont hquot_neg (hquot K)
        refine operatorMonotoneOnInterval_congr_Ioi (K := K) ?_ hres
        intro t ht
        have htp : 0 < t + p := add_pos ht hp0
        have hfp_pos : 0 < f (t + p) := hpos (t + p) (by simpa [Set.mem_Ioi] using htp)
        have ht_ne : t ≠ 0 := ht.ne'
        have htp_ne : t + p ≠ 0 := htp.ne'
        have hfp_ne : f (t + p) ≠ 0 := hfp_pos.ne'
        calc
          -((hneg t / t)⁻¹)
              = -(((-(t + p)) / (t * f (t + p)))⁻¹) := by
                  have hdiv : hneg t / t = (-(t + p)) / (t * f (t + p)) := by
                    calc
                      hneg t / t = (-((t + p) / f (t + p))) / t := by simp [hneg, qp]
                      _ = (-(t + p)) / (t * f (t + p)) := by
                            field_simp [ht_ne, hfp_ne]
                  rw [hdiv]
          _ = t * f (t + p) / (t + p) := by
                exact neg_inv_neg_div_eq_mul_div ht htp hfp_pos
  /- Step 4: Convert positive monotonicity to concavity by shifted half-line limits. -/
  have h13 :
      AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) f ↔
        AllHOperatorConcaveOnInterval.{u} (Set.Ioi (0 : ℝ)) f := by
    constructor
    · intro hmono K _ _ _ _ _
      refine operatorConcaveOn_of_tendsto_Ioi (K := K)
        (F := fun p x : ℝ ↦ f (x + p)) (f := f) ?_ ?_
      · intro A hA hσA
        exact shifted_cfc_tendsto_Ioi (K := K) hA hσA hf
      · filter_upwards [self_mem_nhdsWithin] with p hp
        have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
        let fp : ℝ → ℝ := fun t : ℝ ↦ f (t + p)
        have hfp_cont_half : ContinuousOn fp (halfOpenRay ⊤) := by
          simpa [fp] using continuousOn_shift_Ici hf hp0
        have hfp_nonneg : ∀ t ∈ halfOpenRay ⊤, 0 ≤ fp t := by
          intro t ht
          have htp : 0 < t + p := add_pos_of_nonneg_of_pos ht.1 hp0
          exact (hpos (t + p) (by simpa [Set.mem_Ioi] using htp)).le
        have hmono_shift_half : AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) fp := by
          simpa [fp] using allHOperatorMonotone_shift_Ici hf hmono hp0
        have hconc_half : AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) fp := by
          exact (allHOperatorMonotone_iff_concave_of_nonneg
            (f := fp) hfp_cont_half hfp_nonneg).mp hmono_shift_half
        intro A B t hA hB ht0 ht1 hσA hσB
        exact hconc_half K hA hB ht0 ht1
          (by
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using le_of_lt (hσA hx))
          (by
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using le_of_lt (hσB hx))
    · intro hconc K _ _ _ _ _
      refine operatorMonotoneOn_of_tendsto_Ioi (K := K)
        (F := fun p x : ℝ ↦ f (x + p)) (f := f) ?_ ?_
      · intro A hA hσA
        exact shifted_cfc_tendsto_Ioi (K := K) hA hσA hf
      · filter_upwards [self_mem_nhdsWithin] with p hp
        have hp0 : 0 < p := by simpa [Set.mem_Ioi] using hp
        let fp : ℝ → ℝ := fun t : ℝ ↦ f (t + p)
        have hfp_cont_half : ContinuousOn fp (halfOpenRay ⊤) := by
          simpa [fp] using continuousOn_shift_Ici hf hp0
        have hfp_nonneg : ∀ t ∈ halfOpenRay ⊤, 0 ≤ fp t := by
          intro t ht
          have htp : 0 < t + p := add_pos_of_nonneg_of_pos ht.1 hp0
          exact (hpos (t + p) (by simpa [Set.mem_Ioi] using htp)).le
        have hconc_shift_half : AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) fp := by
          simpa [fp] using allHOperatorConcave_shift_Ici (hf := hf) (hconc := hconc) (hp0 := hp0)
        have h9_fp :
            AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) fp ↔
              AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) fp :=
          allHOperatorMonotone_iff_concave_of_nonneg (f := fp) hfp_cont_half hfp_nonneg
        have hmono_shift_half : AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) fp := by
          exact h9_fp.mpr hconc_shift_half
        intro A B hA hB hσA hσB hAB
        exact hmono_shift_half K hA hB
          (by
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using le_of_lt (hσA hx))
          (by
            intro x hx
            simpa [halfOpenRay_top, Set.mem_Ici] using le_of_lt (hσB hx))
          hAB
  /- Step 5: Derive convexity of 1 / f from concavity of f by inverting the positive CFC values. -/
  have h34 :
      AllHOperatorConcaveOnInterval.{u} (Set.Ioi (0 : ℝ)) f →
        AllHOperatorConvexOnInterval.{u} (Set.Ioi (0 : ℝ)) g := by
    intro hconc K _ _ _ _ _ A B t hA hB ht0 ht1 hσA hσB
    let C : L K := (1 - t) • A + t • B
    have hC_sa : IsSelfAdjoint C := by
      simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
    have hσC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
      simpa [C] using
        spectrum_convexCombo_Ioi (ℋ := K) (A := A) (B := B) (t := t) hA hB ht0 ht1 hσA hσB
    have hcfA_sa : IsSelfAdjoint (cfcR (ℋ := K) f A) := by
      simp [cfcR]
    have hcfB_sa : IsSelfAdjoint (cfcR (ℋ := K) f B) := by
      simp [cfcR]
    have hcfC_sa : IsSelfAdjoint (cfcR (ℋ := K) f C) := by
      simp [cfcR]
    have hcfAσ : spectrum ℝ (cfcR (ℋ := K) f A) ⊆ Set.Ioi (0 : ℝ) :=
      spectrum_cfc_subset_Ioi_of_continuous_pos (K := K) hA hσA hf hpos
    have hcfBσ : spectrum ℝ (cfcR (ℋ := K) f B) ⊆ Set.Ioi (0 : ℝ) :=
      spectrum_cfc_subset_Ioi_of_continuous_pos (K := K) hB hσB hf hpos
    have hcfCσ : spectrum ℝ (cfcR (ℋ := K) f C) ⊆ Set.Ioi (0 : ℝ) :=
      spectrum_cfc_subset_Ioi_of_continuous_pos (K := K) hC_sa hσC hf hpos
    have hconc_base :
        (1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B ≤ cfcR (ℋ := K) f C := by
      have hbase := hconc K hA hB ht0 ht1 hσA hσB
      simpa [OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn, cfc_neg, C,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    have hmix_sa :
        IsSelfAdjoint ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B) := by
      simpa using
        ((IsSelfAdjoint.all (1 - t)).smul hcfA_sa).add ((IsSelfAdjoint.all t).smul hcfB_sa)
    have hmixσ :
        spectrum ℝ ((1 - t) • cfcR (ℋ := K) f A +
          t • cfcR (ℋ := K) f B) ⊆ Set.Ioi (0 : ℝ) := by
      simpa using
        spectrum_convexCombo_Ioi (ℋ := K) (A := cfcR (ℋ := K) f A)
          (B := cfcR (ℋ := K) f B) (t := t) hcfA_sa hcfB_sa ht0 ht1
          hcfAσ hcfBσ
    let idf : ℝ → ℝ := fun x : ℝ ↦ x
    have hmix_ne0 :
        ∀ x ∈ spectrum ℝ ((1 - t) • cfcR (ℋ := K) f A +
          t • cfcR (ℋ := K) f B),
        idf x ≠ 0 := by
      intro x hx
      exact (show 0 < x by simpa [idf, Set.mem_Ioi] using hmixσ hx).ne'
    have hcfC_ne0 : ∀ x ∈ spectrum ℝ (cfcR (ℋ := K) f C), idf x ≠ 0 := by
      intro x hx
      exact (show 0 < x by simpa [idf, Set.mem_Ioi] using hcfCσ hx).ne'
    let uMix : (L K)ˣ :=
      cfcUnits (R := ℝ) (A := L K) (p := IsSelfAdjoint) idf
        ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B) hmix_ne0 (ha := hmix_sa)
    let uC : (L K)ˣ :=
      cfcUnits (R := ℝ) (A := L K) (p := IsSelfAdjoint) idf
        (cfcR (ℋ := K) f C) hcfC_ne0 (ha := hcfC_sa)
    have huMix_val :
        (uMix : L K) = (1 - t) • cfcR (ℋ := K) f A +
          t • cfcR (ℋ := K) f B := by
      simp [uMix, idf, cfcUnits, cfcR, cfc_id' (R := ℝ)
        (a := ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B)) (ha := hmix_sa)]
    have huC_val : (uC : L K) = cfcR (ℋ := K) f C := by
      simp [uC, idf, cfcUnits, cfcR, cfc_id' (R := ℝ) (a := cfcR (ℋ := K) f C) (ha := hcfC_sa)]
    have huMix_nonneg : 0 ≤ (uMix : L K) := by
      simpa [huMix_val] using
        nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi (ℋ := K) hmix_sa hmixσ
    have huMix_le_huC : (uMix : L K) ≤ (uC : L K) := by
      simpa [huMix_val, huC_val] using hconc_base
    /- Step 6: Use inversion order reversal on positive endpoint units. -/
    have hanti :
        cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f C) ≤
          cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x)
            ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B) := by
      have hinv : ((uC⁻¹ : (L K)ˣ) : L K) ≤ ((uMix⁻¹ : (L K)ˣ) : L K) := by
        simpa using
          (CStarAlgebra.inv_le_inv (A := L K) (a := uMix) (b := uC)
            huMix_nonneg huMix_le_huC)
      simpa [uMix, uC, idf, cfcUnits, cfcR, one_div] using hinv
    have hconv_inv :
        cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x)
            ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B) ≤
          (1 - t) • cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f A) +
            t • cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f B) := by
      exact (one_div_operatorConvexOnInterval_Ioi (ℋ := K)) hcfA_sa hcfB_sa ht0 ht1 hcfAσ hcfBσ
    have hcompA :
        cfcR (ℋ := K) g A = cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f A) := by
      simpa [g] using cfc_inv_comp_of_pos_Ioi (K := K) hA hσA hf hpos rfl
    have hcompB :
        cfcR (ℋ := K) g B = cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f B) := by
      simpa [g] using cfc_inv_comp_of_pos_Ioi (K := K) hB hσB hf hpos rfl
    have hcompC :
        cfcR (ℋ := K) g C = cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f C) := by
      simpa [g] using cfc_inv_comp_of_pos_Ioi (K := K) hC_sa hσC hf hpos rfl
    /- Step 7: Chain anti-monotonicity, reciprocal convexity, and CFC composition. -/
    calc
      cfcR (ℋ := K) g C = cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f C) := hcompC
      _ ≤ cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x)
            ((1 - t) • cfcR (ℋ := K) f A + t • cfcR (ℋ := K) f B) := hanti
      _ ≤ (1 - t) • cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f A) +
            t • cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f B) := hconv_inv
      _ = (1 - t) • cfcR (ℋ := K) g A + t • cfcR (ℋ := K) g B := by
        rw [hcompA, hcompB]
  refine ⟨h12, ?_, h34⟩
  exact h12.symm.trans h13

end Corollary511

end NormalCFC510Plus

end HansenPedersen
