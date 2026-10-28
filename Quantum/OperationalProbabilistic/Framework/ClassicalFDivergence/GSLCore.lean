/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Probability.ProbabilityMassFunction.Constructions


open scoped BigOperators ENNReal NNReal Topology
open Filter Set

/-!
# Classical f-divergence of finite probability mass functions

This file is the fail-closed definition layer for finite classical
f-divergences.  A generator explicitly carries its positive-axis convexity,
normalization, right endpoint value, and recession slope.  The latter two
values live in `EReal`, so `+∞` is retained at either boundary while `-∞` is
excluded.

The closed perspective uses nonnegative finite masses.  This is exactly the
setting needed for values of a finite PMF and avoids assigning accidental
semantics to an `ENNReal` input equal to `∞`.  The public PMF divergence is the
`ENNReal` projection of the finite sum of closed-perspective terms.
-/

namespace OPT

noncomputable section

/-- Explicit data for a normalized convex f-divergence generator on the
positive real axis.

`zeroValue` is `f(0+)`, and `recessionSlope` is
`lim t -> infinity, f(t) / t`.  Both endpoints may be `+∞`, but not `-∞`.
The limit fields record that the supplied endpoint data really are the
corresponding one-sided limits. -/
structure FDivGenerator where
  /-- The real-valued generator.  Only its values on `(0, infinity)` enter the
  interior branch of the closed perspective. -/
  f : ℝ → ℝ
  /-- Convexity on the positive real axis. -/
  convexOn_pos : ConvexOn ℝ (Ioi 0) f
  /-- Standard normalization of an f-divergence generator. -/
  map_one : f 1 = 0
  /-- The extended right limit `f(0+)`. -/
  zeroValue : EReal
  /-- Properness excludes `-∞` at the zero endpoint. -/
  zeroValue_ne_bot : zeroValue ≠ ⊥
  /-- The supplied zero endpoint is the right limit of the generator. -/
  tendsto_zeroValue :
    Tendsto (fun t : ℝ ↦ ((f t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 zeroValue)
  /-- The extended recession slope `f'∞`. -/
  recessionSlope : EReal
  /-- Properness excludes `-∞` for the recession slope. -/
  recessionSlope_ne_bot : recessionSlope ≠ ⊥
  /-- The supplied recession slope is `lim t -> infinity, f(t) / t`. -/
  tendsto_recessionSlope :
    Tendsto (fun t : ℝ ↦ ((f t / t : ℝ) : EReal)) atTop (𝓝 recessionSlope)

/-- The closed perspective of a generator on two finite nonnegative masses.

The four branches are, respectively, `(0,0)`, `(0,b)`, `(a,0)`, and the
positive interior.  In particular, the `b = 0 < a` branch uses the recession
slope rather than a fabricated value of `f(a / 0)`. -/
noncomputable def closedPerspective (g : FDivGenerator) (a b : ℝ≥0) : EReal :=
  if a = 0 then
    if b = 0 then 0
    else ((b : ℝ) : EReal) * g.zeroValue
  else if b = 0 then
    ((a : ℝ) : EReal) * g.recessionSlope
  else
    (((b : ℝ) * g.f ((a : ℝ) / (b : ℝ)) : ℝ) : EReal)

@[simp]
theorem closedPerspective_zero_zero (g : FDivGenerator) :
    closedPerspective g 0 0 = 0 := by
  simp [closedPerspective]

theorem closedPerspective_zero_left (g : FDivGenerator) (b : ℝ≥0)
    (hb : b ≠ 0) :
    closedPerspective g 0 b = ((b : ℝ) : EReal) * g.zeroValue := by
  simp [closedPerspective, hb]

theorem closedPerspective_zero_right (g : FDivGenerator) (a : ℝ≥0)
    (ha : a ≠ 0) :
    closedPerspective g a 0 = ((a : ℝ) : EReal) * g.recessionSlope := by
  simp [closedPerspective, ha]

theorem closedPerspective_of_ne_zero (g : FDivGenerator) (a b : ℝ≥0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    closedPerspective g a b =
      (((b : ℝ) * g.f ((a : ℝ) / (b : ℝ)) : ℝ) : EReal) := by
  simp [closedPerspective, ha, hb]

/-- A closed-perspective term never takes the forbidden value `-∞`. -/
theorem closedPerspective_ne_bot (g : FDivGenerator) (a b : ℝ≥0) :
    closedPerspective g a b ≠ ⊥ := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    · simp [closedPerspective, ha, hb, EReal.mul_ne_bot,
        g.zeroValue_ne_bot]
  · by_cases hb : b = 0
    · simp [closedPerspective, ha, hb, EReal.mul_ne_bot,
        g.recessionSlope_ne_bot]
    · rw [closedPerspective, if_neg ha, if_neg hb]
      exact EReal.coe_ne_bot _

@[simp]
theorem closedPerspective_self (g : FDivGenerator) (a : ℝ≥0) :
    closedPerspective g a a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [closedPerspective, ha, g.map_one]

/-- The `EReal` sum of closed-perspective terms for two finite PMFs. -/
noncomputable def classicalFDivSum {iota : Type} [Fintype iota]
    (g : FDivGenerator) (p q : PMF iota) : EReal :=
  ∑ i, closedPerspective g (p i).toNNReal (q i).toNNReal

/-- Classical f-divergence of two finite PMFs.

The boundary convention is entirely contained in `closedPerspective`.  The
final `toENNReal` exposes the standard nonnegative extended-real codomain;
nonnegativity of the raw sum is proved from convexity as
`classicalFDivSum_nonnegative` (`ClassicalFDivDPI/GSLCore.lean`). -/
noncomputable def classicalFDivPMF {iota : Type} [Fintype iota]
    (g : FDivGenerator) (p q : PMF iota) : ℝ≥0∞ :=
  (classicalFDivSum g p q).toENNReal

end

end OPT
