/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.JensenOperatorInequalityRetained
import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.LiebAndo.GeneralizedPerspectiveFunction

namespace GeneralizedPerspectiveFunction

universe u

open LownerHeinzTheorem
open JensenOperatorInequality

section Theorem25Forward

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

section CondVCore
-- The normalization proof below expands several nested CFC products, and every tactic
-- step re-derives the real-scalar structure of `L ℋ` (obtained from the complex one by
-- restriction of scalars) from scratch: the searches for derived classes such as
-- `NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ)`, `StarModule ℝ (ℋ →L[ℂ] ℋ)`,
-- `PosSMulMono ℝ (ℋ →L[ℂ] ℋ)` all
-- repeatedly re-solve the `Module ℝ (ℋ →L[ℂ] ℋ)` / `Algebra ℝ (ℋ →L[ℂ] ℋ)`
-- subgoals, which are not
-- cached across tactic steps and cost hundreds of milliseconds per occurrence.  Caching
-- the two root instances at section level keeps the declaration within the default
-- heartbeat budget.
attribute [local instance] instModuleRealContinuousLinearMapComplexId_quantum
attribute [local instance] instAlgebraRealContinuousLinearMapComplexId_quantum

end CondVCore

-- Restricted forward form of Theorem 2.5 on the positive cone.
/--
Source: arXiv:2607.05492v1, §3.

On a nontrivial space only the zero function satisfies the hypothesis on `f` (see
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` in `LownerHeinz/GlobalDegeneracy.lean`), so
this statement has no nonzero instances. For the standard statement, see the localized version
`GeneralizedPerspectiveFunction.theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici`. -/
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd
    {f h : ℝ → ℝ}
    (hf : OperatorConvexAllNonposAtZero.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hcoreV : JensenContractiveColumnCondition (ℋ := ℋ) f :=
    jensenColumn_of_opConvexAllNonposZero (ℋ := ℋ) (f := f) hf
  exact theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    (ℋ := ℋ) (f := f) (h := h) hcoreV hconc hcont hpos

/-- Restricted forward form of Corollary 2.6 on the positive cone.

Source: arXiv:2607.05492v1, §3.
Source: A. Ebadian, I. Nikoufar, M. Eshaghi Gordji, "Perspectives of matrix convex functions",
PNAS 108 (2011), 7313–7314, Corollary 2.6.

On a nontrivial space only the zero function satisfies the hypothesis on `f` (see
`LownerHeinzTheorem.OperatorConcaveAll.eq_zero` in `LownerHeinz/GlobalDegeneracy.lean`), so this
statement has no nonzero instances. For the standard statement, see the localized version
`GeneralizedPerspectiveFunction.theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici`. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveAll.{u} f)
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  have hfneg : OperatorConvexAllNonposAtZero.{u} (fun x : ℝ ↦ -f x) := by
    refine ⟨?_, ?_⟩
    · intro K _ _ _ _
      simpa [OperatorConcave] using (hfconc (K := K))
    · simpa using (neg_nonpos.mpr hf0)
  have hconv_neg :
      JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
        (fun A B ↦ -((f Δ h) A B)) := by
    simpa [generalizedPerspective_neg] using
      (theorem_2_5_forward_jointlyConvexOn_psd_pd
        (ℋ := ℋ) (f := fun x : ℝ ↦ -f x) (h := h) hfneg hconc hcont hpos)
  exact jointlyConvexOn_neg (ℋ := ℋ) hconv_neg

end Theorem25Forward

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Perspectives of matrix convex functions,
-- page 1, DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- For any qudit ℋ, any A ∈ Herm(ℋ), any B ∈ Pd(ℋ),
-- any real-valued continuous function f, any positive-valued continuous function h>0,
-- (fΔh)(A,B) := h(B)^{1/2} f(h(B)^{-1/2} A h(B)^{-1/2}) h(B)^{1/2}

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Theorem 2.5,
-- DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≤ 0, and h is a continuous function with h > 0.
-- If f is operator convex and h is operator concave,
-- then fΔh is jointly convex

end GeneralizedPerspectiveFunction
