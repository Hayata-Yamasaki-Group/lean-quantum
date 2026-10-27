/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.HSBridgeCore

namespace LiebAndoTrace

universe u

/-!
# Geometry of positive-definite operators

Convex combinations, powers and order on the positive-definite cone.
-/

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

-- Under transparency-respecting defeq, synthesizing `NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ)`
-- from scratch exceeds the default typeclass budget and is re-run at every
-- `nonneg_iff_spectrum_nonneg`-style step (it is not cached across tactic steps).
-- Register the C⋆-algebra instance once so each search is a direct hit.
local instance geometryNonnegSpectrumClass : NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ) :=
  CStarAlgebra.instNonnegSpectrumClass

/-! ### Positive-definite cone closure and rpow API -/
omit [FiniteDimensional ℂ ℋ] in
/-- Convex combinations preserve `pdSet` (strict positivity). -/
lemma pdSet_convexCombo_transport {A B : (ℋ →L[ℂ] ℋ)} {t : ℝ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  obtain ⟨r, hr, hrA⟩ :=
    (CFC.exists_pos_algebraMap_le_iff (A := (ℋ →L[ℂ] ℋ)) (a := A) hA_sa).2 hA_spec
  have hA_strict : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hA_sa, (CFC.exists_pos_algebraMap_le_iff (a := A) hA_sa).1 ⟨r, hr, hrA⟩⟩
  have hB_strict : IsStrictlyPositive B :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr ⟨hB_sa, hB_spec⟩
  have hcombo : IsStrictlyPositive ((1 - t) • A + t • B) := by
    by_cases ht : t = 1
    · subst t
      simpa using hB_strict
    · exact (IsStrictlyPositive.smul (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hA_strict).add_nonneg
        (smul_nonneg ht0 hB_strict.nonneg)
  change IsSelfAdjoint ((1 - t) • A + t • B) ∧
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi 0
  simpa [Set.subset_def] using
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hcombo

omit [FiniteDimensional ℂ ℋ] in
lemma pdSet_rpow_of_mem_Icc_zero_one_transport
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : (ℋ →L[ℂ] ℋ)} (hA : A ∈ pdSet (ℋ := ℋ)) :
    A ^ p ∈ pdSet (ℋ := ℋ) := by
  rcases hp with ⟨_, _⟩
  rcases hA with ⟨hA_sa, hA_spec⟩
  obtain ⟨r, hr, hrA⟩ :=
    (CFC.exists_pos_algebraMap_le_iff (A := (ℋ →L[ℂ] ℋ)) (a := A) hA_sa).2 hA_spec
  have hstrict : IsStrictlyPositive A := by
    apply CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
    exact ⟨hA_sa,
      (CFC.exists_pos_algebraMap_le_iff (A := (ℋ →L[ℂ] ℋ)) (a := A) hA_sa).1
        ⟨r, hr, hrA⟩⟩
  change IsSelfAdjoint (A ^ p) ∧ spectrum ℝ (A ^ p) ⊆ Set.Ioi 0
  simpa [Set.subset_def] using
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hstrict.rpow

end LiebAndoTrace
