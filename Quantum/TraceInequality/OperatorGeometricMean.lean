/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.GeneralizedPerspectiveFunction

/-!
# Operator geometric and power means

Operator power means are defined through the generalized perspective. This module
proves their joint concavity and order properties from the operator convexity and
concavity of real powers.
-/

namespace OperatorGeometricMean

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `(α, β)`-power mean, realized as a generalized perspective.

Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, p. 532. Corresponds to M(α,β;A,B)=B
#_(α,β) A, with the operator arguments of the source exchanged. Defined everywhere via CFC. -/
noncomputable def operatorPowerMean (α β : ℝ) (A B : QuantumState.B ℋ) : QuantumState.B ℋ :=
  generalizedPerspective (fun x : ℝ ↦ x ^ α) (fun x : ℝ ↦ x ^ β) A B

private lemma rpow_continuousOn_Ici (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (fun x : ℝ ↦ x ^ p) (Set.Ici (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt

omit [Nontrivial ℋ] in
private lemma operatorConcaveOn_Ioi_of_Ici {f : ℝ → ℝ}
    (h : OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f) :
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B t hA hB ht0 ht1 hAs hBs
  exact h hA hB ht0 ht1 (Set.Subset.trans hAs Set.Ioi_subset_Ici_self)
      (Set.Subset.trans hBs Set.Ioi_subset_Ici_self)

omit [Nontrivial ℋ] in
private lemma pdSet_subset_psdSet : pdSet (ℋ := ℋ) ⊆ psdSet (ℋ := ℋ) := by
  intro A hA
  rcases hA with ⟨hA_sa, hA_spec⟩
  exact ⟨hA_sa, Set.Subset.trans hA_spec Set.Ioi_subset_Ici_self⟩

private lemma rpow_pos_on_Ioi (p : ℝ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < x ^ p := by
  intro x hx
  exact Real.rpow_pos_of_pos hx p

/--
Theorem 1.1, concave range: the operator `(α, β)`-power mean is jointly concave on
strictly positive operators for `0 ≤ α, β ≤ 1`.

Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.1 (concave range).
With the operator arguments of the source exchanged, this corresponds to the closed exponent
range 0≤α,β≤1 on the positive definite cone.
-/
theorem jointlyConcaveOn_operatorPowerMean_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConcaveOn pdSet pdSet
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconc :=
    jointlyConcaveOn_generalizedPerspective_psdSet_pdSet
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hfconc := by
        intro K _ _ _ _
        exact LownerHeinzCore.operatorConcaveOn_rpow_Ici
          (𝓐 := (K →L[ℂ] K)) α hα)
      (hfcont := rpow_continuousOn_Ici α hα.1)
      (hf0 := by
        exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by simp) α)
      (hconc := by
        exact operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (LownerHeinzCore.operatorConcaveOn_rpow_Ici
            (𝓐 := (ℋ →L[ℂ] ℋ)) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconc (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (pdSet_subset_psdSet (ℋ := ℋ) hA₁) (pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1

/--
Theorem 1.1, convex range: the operator `(α, β)`-power mean is jointly convex on
strictly positive operators for `1 ≤ α ≤ 2` and `0 ≤ β ≤ 1`.

Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.1 (convex range).
With the operator arguments of the source exchanged, this corresponds to the closed exponent
range 1≤α≤2, 0≤β≤1 on the positive definite cone.
-/
theorem jointlyConvexOn_operatorPowerMean_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConvexOn pdSet pdSet
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconv :=
    jointlyConvexOn_generalizedPerspective_psdSet_pdSet
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hf := by
        refine ⟨?_, ?_, ?_⟩
        · intro K _ _ _ _
          exact LownerHeinzCore.operatorConvexOn_rpow_Ici
            (𝓐 := (K →L[ℂ] K)) α hα
        · exact rpow_continuousOn_Ici α (by linarith [hα.1])
        · have hα0 : α ≠ 0 := by linarith [hα.1]
          simp [Real.zero_rpow hα0]
      )
      (hconc := by
        exact operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (LownerHeinzCore.operatorConcaveOn_rpow_Ici
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
