/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LownerHeinz.RpowOneTwo
import Quantum.TraceInequality.LiebAndo.LownerHeinz.RpowZeroOne
import Quantum.TraceInequality.LiebAndo.OperatorGeometricMean

namespace OperatorGeometricMean

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/--
Theorem 1.1, convex range: the operator `(α, β)`-power mean is jointly convex on
strictly positive operators for `1 ≤ α ≤ 2` and `0 ≤ β ≤ 1`.

Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.1 (convex range).
In the form with the operator arguments of the source interchanged, this corresponds to the closed
exponent range 1≤α≤2, 0≤β≤1 on the positive definite cone.
-/
theorem operatorPowerMean_jointlyConvexOn_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconv :=
    theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hf := by
        refine ⟨?_, ?_, ?_⟩
        · intro K _ _ _ _
          exact LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici
            (𝓐 := (K →L[ℂ] K)) α hα
        · exact rpow_continuousOn_Ici α (by linarith [hα.1])
        · have hα0 : α ≠ 0 := by linarith [hα.1]
          simp [Real.zero_rpow hα0]
      )
      (hconc := by
        exact operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici
            (𝓐 := (ℋ →L[ℂ] ℋ)) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconv (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (pdSet_subset_psdSet (ℋ := ℋ) hA₁) (pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1

end OperatorGeometricMean
