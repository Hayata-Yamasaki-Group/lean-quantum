/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Max-relative entropy on ordered cones

This file defines max-relative entropy on ordered cones.  It
uses the extended-real convention already used by the classical divergence
layer, the subset direction familiar from testing-region data processing, and
the existing `ProperCone.positive` realization of an ordered module's positive
cone.

Watrous, Lecture 2, Definition 2.1 / Eq. (2.5), defines the matrix quantity
`D_max(rho || Q) = inf {lam : rho <= 2 ^ lam Q}`.  The definitions below
abstract this quantity to any ordered real module; they are an abstraction of
the cited matrix definition, not a verbatim definition from Watrous.
-/

namespace OPT
namespace OrderedCone

noncomputable section

universe u v

variable {V : Type u} [AddCommMonoid V] [PartialOrder V] [Module ℝ V]

/-- The extended-real image of the exponents that dominate `x` by a scaled
`y`: `x <= (2 ^ lam) • y`.

This is the ordered-cone abstraction of Watrous, Lecture 2, Definition 2.1 /
Eq. (2.5).  Only finite real exponents occur in the set; its infimum can still
be `bot` or `top` in `EReal`. -/
def dominationSet (x y : V) : Set EReal :=
  {z | ∃ lam : ℝ, z = (lam : EReal) ∧ x ≤ ((2 : ℝ) ^ lam) • y}

/-- Max-relative entropy on an ordered real module.

Following Watrous, Lecture 2, Definition 2.1 / Eq. (2.5), this is the infimum
of the real exponents satisfying `x <= (2 ^ lam) • y`.  Taking the infimum in
`EReal` makes an empty domination set equal to `top`.  The arbitrary
ordered-cone formulation is an abstraction of Watrous's matrix definition.

The exponent is base 2 (bits). For operators, `x = 0` and a positive semidefinite `y` allow
every real exponent, so the value is `⊥`. -/
noncomputable def maxRelEntropy (x y : V) : EReal :=
  sInf (dominationSet x y)

/-- Every explicit domination exponent bounds max-relative entropy from
above.

This is the exact `sInf_le` step for Watrous, Lecture 2, Definition 2.1 /
Eq. (2.5): a feasible exponent is an element of the set whose infimum defines
`D_max`. -/
theorem maxRelEntropy_le_of_domination {x y : V} {lam : ℝ}
    (hxy : x ≤ ((2 : ℝ) ^ lam) • y) :
    maxRelEntropy x y ≤ (lam : EReal) := by
  exact sInf_le ⟨lam, rfl, hxy⟩

/-- If no real exponent dominates `x` by `y`, max-relative entropy is `top`.

This records the empty-feasible-set boundary of the extended-value form of
Watrous, Lecture 2, Definition 2.1 / Eq. (2.5). -/
theorem maxRelEntropy_eq_top_of_dominationSet_empty {x y : V}
    (hempty : dominationSet x y = ∅) :
    maxRelEntropy x y = ⊤ := by
  rw [maxRelEntropy, hempty, sInf_empty]
  rfl

/-- A nonempty, bounded-below domination set attains max-relative entropy when
the scalar action is continuous and the order is closed.

This supplies the exact infimum-attainment step for the ordered-cone
abstraction of Watrous, Lecture 2, Definition 2.1 / Eq. (2.5).  The hypotheses
exclude the genuine `top` and `bot` boundary cases of the extended-value
definition. -/
theorem maxRelEntropy_attained
    {V : Type u} [AddCommMonoid V] [PartialOrder V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousSMul ℝ V] [OrderClosedTopology V]
    (x y : V)
    (hne : {lam : ℝ | x ≤ ((2 : ℝ) ^ lam) • y}.Nonempty)
    (hbdd : BddBelow {lam : ℝ | x ≤ ((2 : ℝ) ^ lam) • y}) :
    ∃ lam : ℝ,
      maxRelEntropy x y = (lam : EReal) ∧
        x ≤ ((2 : ℝ) ^ lam) • y := by
  let S : Set ℝ := {lam | x ≤ ((2 : ℝ) ^ lam) • y}
  change S.Nonempty at hne
  change BddBelow S at hbdd
  have hclosed : IsClosed S := by
    apply isClosed_le continuous_const
    exact (Real.continuous_const_rpow (by norm_num)).smul continuous_const
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  refine ⟨sInf S, ?_, hmem⟩
  apply le_antisymm
  · exact maxRelEntropy_le_of_domination hmem
  · unfold maxRelEntropy
    apply le_sInf
    rintro z ⟨lam, rfl, hlam⟩
    exact_mod_cast csInf_le hbdd hlam

variable {W : Type v} [AddCommMonoid W] [PartialOrder W] [Module ℝ W]

end

end OrderedCone
end OPT
