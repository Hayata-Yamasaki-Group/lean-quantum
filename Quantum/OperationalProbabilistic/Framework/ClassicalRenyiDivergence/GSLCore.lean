/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Quantum.OperationalProbabilistic.MeasuredRelativeEntropy.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators ENNReal
open MeasureTheory

/-!
# Classical Rényi divergence of finite probability mass functions

This file implements the purely classical finite-PMF kernel used by measured
Rényi divergences.  Orders are positive and include `1`; the order-one branch
is definitionally tied to the existing natural-logarithm KL convention in
`classicalRelEntropyPMF`.

For orders above one, failure of `support p ⊆ support q` gives `∞`.  Below one,
the power sum uses `ENNReal.rpow`, including `0 ^ positive = 0` and
`0 ^ negative = ∞`; a zero power sum (in particular for disjoint supports)
gives `∞` after multiplication by the negative reciprocal order offset.
-/

namespace OPT

noncomputable section

/-- A finite positive Rényi order.  The endpoint orders `0` and `∞` are not
part of this first classical kernel. -/
abbrev RenyiOrder := {alpha : ℝ // 0 < alpha}

namespace RenyiOrder

/-- The KL order. -/
def one : RenyiOrder :=
  ⟨1, zero_lt_one⟩

@[simp]
theorem coe_one : (one : ℝ) = 1 :=
  rfl

/-- Every positive finite order lies below, at, or above the KL order. -/
theorem lt_one_or_eq_one_or_one_lt (alpha : RenyiOrder) :
    (alpha : ℝ) < 1 ∨ (alpha : ℝ) = 1 ∨ 1 < (alpha : ℝ) :=
  lt_trichotomy (alpha : ℝ) 1

end RenyiOrder

/-- The extended nonnegative-real Rényi power sum
`∑ i, p i ^ alpha * q i ^ (1 - alpha)`.

The `ENNReal.rpow` boundary convention records zero probabilities without
first coercing them to finite real numbers. -/
noncomputable def renyiPowerSum (alpha : RenyiOrder)
    {iota : Type} [Fintype iota] (p q : PMF iota) : ℝ≥0∞ :=
  ∑ i, (p i) ^ (alpha : ℝ) * (q i) ^ (1 - (alpha : ℝ))

/-- Failure of absolute continuity for a pair of finite PMFs. -/
def renyiSupportMismatch {iota : Type} (p q : PMF iota) : Prop :=
  ¬p.support ⊆ q.support

/-- The extended-real logarithmic quotient in the non-KL Rényi formula. -/
noncomputable def renyiLogQuotient (alpha : RenyiOrder)
    {iota : Type} [Fintype iota] (p q : PMF iota) : EReal :=
  (((alpha : ℝ) - 1)⁻¹ : EReal) * ENNReal.log (renyiPowerSum alpha p q)

/-- Classical Rényi divergence of two finite PMFs, with natural logarithms.

At order one this is exactly `classicalRelEntropyPMF`.  Above one, support
mismatch is explicitly assigned `∞`.  Below one, a zero power sum is assigned
`∞`.  On the remaining non-KL branch the extended-real logarithmic quotient
is returned in `ℝ≥0∞`. -/
noncomputable def classicalRenyiDivPMF (alpha : RenyiOrder)
    {iota : Type} [Fintype iota] (p q : PMF iota) : ℝ≥0∞ := by
  classical
  exact if (alpha : ℝ) = 1 then
      classicalRelEntropyPMF p q
    else if 1 < (alpha : ℝ) ∧ renyiSupportMismatch p q then
      ⊤
    else if (alpha : ℝ) < 1 ∧ renyiPowerSum alpha p q = 0 then
      ⊤
    else
      (renyiLogQuotient alpha p q).toENNReal

@[simp]
theorem classicalRenyiDivPMF_one {iota : Type} [Fintype iota]
    (p q : PMF iota) :
    classicalRenyiDivPMF RenyiOrder.one p q = classicalRelEntropyPMF p q := by
  simp [classicalRenyiDivPMF]

theorem classicalRenyiDivPMF_of_one_lt_of_supportMismatch
    {iota : Type} [Fintype iota] (alpha : RenyiOrder) (p q : PMF iota)
    (halpha : 1 < (alpha : ℝ)) (hmismatch : renyiSupportMismatch p q) :
    classicalRenyiDivPMF alpha p q = ⊤ := by
  simp [classicalRenyiDivPMF, halpha.ne', halpha, hmismatch]

theorem classicalRenyiDivPMF_of_lt_one_of_powerSum_eq_zero
    {iota : Type} [Fintype iota] (alpha : RenyiOrder) (p q : PMF iota)
    (halpha : (alpha : ℝ) < 1) (hsum : renyiPowerSum alpha p q = 0) :
    classicalRenyiDivPMF alpha p q = ⊤ := by
  simp [classicalRenyiDivPMF, halpha.ne, halpha, hsum]

theorem renyiPowerSum_eq_zero_of_disjoint_support
    {iota : Type} [Fintype iota] (alpha : RenyiOrder) (p q : PMF iota)
    (halpha : (alpha : ℝ) < 1) (hdisjoint : Disjoint p.support q.support) :
    renyiPowerSum alpha p q = 0 := by
  unfold renyiPowerSum
  apply Finset.sum_eq_zero
  intro i _
  by_cases hp : p i = 0
  · simp [hp, ENNReal.zero_rpow_of_pos alpha.property]
  · have hi_not_q : i ∉ q.support :=
      Set.disjoint_left.1 hdisjoint ((p.mem_support_iff i).2 hp)
    have hq : q i = 0 := (q.apply_eq_zero_iff i).2 hi_not_q
    simp [hq, ENNReal.zero_rpow_of_pos (sub_pos.2 halpha)]

theorem classicalRenyiDivPMF_of_lt_one_of_disjoint_support
    {iota : Type} [Fintype iota] (alpha : RenyiOrder) (p q : PMF iota)
    (halpha : (alpha : ℝ) < 1) (hdisjoint : Disjoint p.support q.support) :
    classicalRenyiDivPMF alpha p q = ⊤ :=
  classicalRenyiDivPMF_of_lt_one_of_powerSum_eq_zero alpha p q halpha
    (renyiPowerSum_eq_zero_of_disjoint_support alpha p q halpha hdisjoint)

end

end OPT
