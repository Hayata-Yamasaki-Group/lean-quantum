/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite iid probability mass functions

This file develops the elementary finite probability layer used by finite
multi-hypothesis discrimination.  It deliberately contains no operational or
quantum imports.
-/

open Filter Set Topology
open scoped BigOperators ENNReal

namespace OPT.PMF

noncomputable section

universe u v

variable {ι : Type u} {κ : Type v}

/-- The `n`-fold iid product of a finite probability mass function. -/
def iid [Fintype ι] (n : ℕ) (p : PMF ι) : PMF (Fin n → ι) :=
  PMF.ofFintype (fun x => ∏ j, p (x j)) (by
    rw [← Fintype.sum_pow]
    have hp : ∑ a, p a = 1 := by
      simpa only [tsum_fintype] using p.tsum_coe
    rw [hp, one_pow])

@[simp]
theorem iid_apply [Fintype ι] (n : ℕ) (p : PMF ι) (x : Fin n → ι) :
    iid n p x = ∏ j, p (x j) :=
  rfl

/-- The real-valued mass function associated to a finite PMF. -/
def realMass (p : PMF ι) (a : ι) : ℝ :=
  (p a).toReal

@[simp]
theorem iid_apply_toReal [Fintype ι] (n : ℕ) (p : PMF ι) (x : Fin n → ι) :
    (iid n p x).toReal = ∏ j, realMass p (x j) := by
  simp [iid_apply, realMass, ENNReal.toReal_prod]

end

end OPT.PMF
