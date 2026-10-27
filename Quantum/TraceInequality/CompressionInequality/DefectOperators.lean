import Quantum.TraceInequality.UnitaryBlockMatrix
import Quantum.TraceInequality.Core
import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.CompressionInequality.BlockMatrix

/-!
# Defect operators for contractions

This module defines the right and left defect operators associated to a
contraction `C`, namely the continuous-functional-calculus square roots of
`1 - C* C` and `1 - C C*`.  These operators supply the unitary dilation and
intertwining identities used in the compression inequality implications.

## Main results

* `defectRight` and `defectLeft`: the two defect operators of a contraction.
* `defectRight_sq` and `defectLeft_sq`: their squares are the expected
  positive complements.
* `defect_intertwine` and `star_defect_intertwine`: the two defect operators
  commute with `C` and `C*` in the standard Julia-operator way.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u v

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

open scoped ComplexOrder

section DefectOperators

@[fun_prop] private lemma sqrtOneSub_continuousOn_unit :
    ContinuousOn (fun t : ℝ ↦ Real.sqrt (1 - t)) (Set.Icc (0 : ℝ) 1) := by
  simpa [sub_eq_add_neg] using (continuousOn_const.sub continuousOn_id).sqrt

private lemma spectrum_star_mul_self_subset_unit {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    spectrum ℝ (star C * C) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hC2 : ‖star C * C‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg C, hC]
  refine HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := star C * C) (α := 0) (β := 1) (IsSelfAdjoint.star_mul_self C)
    (by simp [zero_smul]) ?_
  simpa [one_smul] using
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg C)).1 hC2

private lemma spectrum_mul_star_self_subset_unit {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    spectrum ℝ (C * star C) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hC2 : ‖C * star C‖ ≤ 1 := by
    have hnorm : ‖C * star C‖ = ‖C‖ * ‖C‖ := by
      simpa [norm_star] using (CStarRing.norm_star_mul_self (x := star C))
    rw [hnorm]
    nlinarith [norm_nonneg C, hC]
  refine HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := C * star C) (α := 0) (β := 1) (IsSelfAdjoint.mul_star_self C)
    (by simp [zero_smul]) ?_
  simpa [one_smul] using
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg C)).1 hC2

/-- If `C` is a contraction, then `C* C` is bounded above by the identity. -/
lemma star_mul_self_le_one_of_norm_le_one {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    star C * C ≤ (1 : L K) := by
  have hC2 : ‖star C * C‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg C, hC]
  simpa [one_smul] using
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg C)).1 hC2

/-- Right defect operator of `C`, defined as `(1 - C* C)^(1/2)` by real
functional calculus. -/
noncomputable def defectRight {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (C : L K) : L K :=
  cfcR (ℋ := K) (fun t : ℝ ↦ Real.sqrt (1 - t)) (star C * C)

/-- Left defect operator of `C`, defined as `(1 - C C*)^(1/2)` by real
functional calculus. -/
noncomputable def defectLeft {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (C : L K) : L K :=
  cfcR (ℋ := K) (fun t : ℝ ↦ Real.sqrt (1 - t)) (C * star C)

/-- The right defect operator is self-adjoint. -/
lemma defectRight_selfAdjoint {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (C : L K) :
    IsSelfAdjoint (defectRight C) := by
  simp [defectRight, cfcR]

/-- The left defect operator is self-adjoint. -/
lemma defectLeft_selfAdjoint {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (C : L K) :
    IsSelfAdjoint (defectLeft C) := by
  simp [defectLeft, cfcR]

/-- For a contraction `C`, the square of the right defect operator is
`1 - C* C`. -/
lemma defectRight_sq {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    defectRight C * defectRight C = (1 : L K) - star C * C := by
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 - t)
  have hg : ContinuousOn g (spectrum ℝ (star C * C)) := by
    exact sqrtOneSub_continuousOn_unit.mono (spectrum_star_mul_self_subset_unit hC)
  calc
    defectRight C * defectRight C = cfcR (ℋ := K) (fun t : ℝ ↦ g t * g t) (star C * C) := by
      dsimp [defectRight, g, cfcR]
      rw [← cfc_mul _ _ _ hg hg]
    _ = cfcR (ℋ := K) (fun t : ℝ ↦ 1 - t) (star C * C) := by
      apply cfc_congr
      intro x hx
      have hx' := spectrum_star_mul_self_subset_unit (K := K) hC hx
      dsimp [g]
      have hnonneg : 0 ≤ 1 - x := by linarith [hx'.1, hx'.2]
      nlinarith [Real.sq_sqrt hnonneg]
    _ = (1 : L K) - star C * C := by
      dsimp [cfcR]
      change cfc (R := ℝ) (fun t : ℝ ↦ (1 : ℝ) - t) (star C * C) =
        (1 : L K) - star C * C
      rw [cfc_sub (R := ℝ) (A := L K) (p := IsSelfAdjoint)
        (f := fun _ : ℝ ↦ 1) (g := fun t : ℝ ↦ t)
        (a := star C * C) (hf := continuousOn_const) (hg := continuousOn_id),
        cfc_const_one (R := ℝ) (a := star C * C), cfc_id' (R := ℝ) (a := star C * C)]

/-- For a contraction `C`, the square of the left defect operator is
`1 - C C*`. -/
lemma defectLeft_sq {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    defectLeft C * defectLeft C = (1 : L K) - C * star C := by
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 - t)
  have hg : ContinuousOn g (spectrum ℝ (C * star C)) := by
    exact sqrtOneSub_continuousOn_unit.mono (spectrum_mul_star_self_subset_unit hC)
  calc
    defectLeft C * defectLeft C = cfcR (ℋ := K) (fun t : ℝ ↦ g t * g t) (C * star C) := by
      dsimp [defectLeft, g, cfcR]
      rw [← cfc_mul _ _ _ hg hg]
    _ = cfcR (ℋ := K) (fun t : ℝ ↦ 1 - t) (C * star C) := by
      apply cfc_congr
      intro x hx
      have hx' := spectrum_mul_star_self_subset_unit (K := K) hC hx
      dsimp [g]
      have hnonneg : 0 ≤ 1 - x := by linarith [hx'.1, hx'.2]
      nlinarith [Real.sq_sqrt hnonneg]
    _ = (1 : L K) - C * star C := by
      dsimp [cfcR]
      change cfc (R := ℝ) (fun t : ℝ ↦ (1 : ℝ) - t) (C * star C) =
        (1 : L K) - C * star C
      rw [cfc_sub (R := ℝ) (A := L K) (p := IsSelfAdjoint)
        (f := fun _ : ℝ ↦ 1) (g := fun t : ℝ ↦ t)
        (a := C * star C) (hf := continuousOn_const) (hg := continuousOn_id),
        cfc_const_one (R := ℝ) (a := C * star C), cfc_id' (R := ℝ) (a := C * star C)]

/-- The contraction intertwines its right and left defect operators:
`C D_C = D_{C*} C`. -/
lemma defect_intertwine {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    C * defectRight C = defectLeft C * C := by
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 - t)
  have hnormsq_le : ‖C‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg C, hC]
  have hg_norm : ContinuousOn g (Set.Icc (0 : ℝ) (‖C‖ ^ 2)) := by
    refine sqrtOneSub_continuousOn_unit.mono ?_
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hnormsq_le⟩
  simpa [defectRight, defectLeft, g] using
    (cfcR_star_mul_self_intertwine (ℋ := K) (A := C) (f := g) hg_norm)

/-- Star-adjoint form of `defect_intertwine`, moving the intertwining identity
to `C*`. -/
lemma star_defect_intertwine {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    star C * defectLeft C = defectRight C * star C := by
  have hDstar : star (defectRight C) = defectRight C :=
    (defectRight_selfAdjoint (K := K) C).star_eq
  have hEstar : star (defectLeft C) = defectLeft C :=
    (defectLeft_selfAdjoint (K := K) C).star_eq
  have h := defect_intertwine (K := K) hC
  have hstar := congrArg star h
  have hstar' : defectRight C * star C = star C * defectLeft C := by
    simpa [hDstar, hEstar, mul_assoc] using hstar
  simpa [eq_comm] using hstar'

/-- The left defect operator of a contraction is itself a contraction. -/
lemma defectLeft_norm_le_one {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    ‖defectLeft C‖ ≤ 1 := by
  have hsq_le : defectLeft C * defectLeft C ≤ (1 : L K) := by
    calc
      defectLeft C * defectLeft C = (1 : L K) - C * star C :=
        defectLeft_sq (K := K) hC
      _ ≤ (1 : L K) := sub_le_self _ (mul_star_self_nonneg C)
  have hsq_norm : ‖defectLeft C * defectLeft C‖ ≤ 1 := by
    have hnonneg : (0 : L K) ≤ defectLeft C * defectLeft C := by
      simpa [(defectLeft_selfAdjoint (K := K) C).star_eq] using
        star_mul_self_nonneg (defectLeft C)
    simpa [one_smul] using
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg).2 hsq_le
  have hnorm_mul : ‖defectLeft C * defectLeft C‖ = ‖defectLeft C‖ * ‖defectLeft C‖ := by
    simpa [(defectLeft_selfAdjoint (K := K) C).star_eq] using
      (CStarRing.norm_star_mul_self (x := defectLeft C))
  rw [hnorm_mul] at hsq_norm
  nlinarith [norm_nonneg (defectLeft C)]

end DefectOperators

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
