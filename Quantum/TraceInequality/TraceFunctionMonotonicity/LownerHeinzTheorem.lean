/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.Defs
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.RpowZeroOne

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

-- Cached `Algebra ℝ (ℋ →L[ℂ] ℋ)` keeps this deep superclass/instance search within
-- the default instance budget.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexId_quantum

/-- Fixed-space operator monotonicity on `s` for the Hilbert space `ℋ`. -/
abbrev OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotoneOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator monotonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorMonotoneOn (ℋ := K) s f

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Hilbert-space specialization of
`LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici`
in `LownerHeinz/RpowZeroOne.lean`. See the Core theorem's docstring for sources. -/
theorem power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using
    (LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

end LownerHeinzTheorem
