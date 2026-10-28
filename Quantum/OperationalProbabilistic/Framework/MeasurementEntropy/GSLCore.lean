/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open CategoryTheory
open scoped BigOperators ENNReal MonoidalCategory

/-!
# Shannon entropy of finite PMFs in bits

`shannonBits` is the Shannon entropy of a finite PMF with the base-two logarithm, with its
explicit sum formula.
-/

namespace OPT

noncomputable section

universe u v

/-! ## Finite-PMF Shannon entropy -/

/-- The Shannon entropy in bits of a probability mass function on a finite
outcome type. -/
noncomputable def shannonBits {ι : Type*} [Fintype ι] (p : PMF ι) : ℝ :=
  (∑ i, Real.negMulLog (p i).toReal) / Real.log 2

/-- The definition agrees term by term with the conventional
`-p log₂ p` finite sum, including the zero-probability convention. -/
theorem shannonBits_eq_sum_neg_mul_logb {ι : Type*} [Fintype ι] (p : PMF ι) :
    shannonBits p =
      ∑ i, -(p i).toReal * Real.logb 2 (p i).toReal := by
  rw [shannonBits, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Real.log_div_log]
  simp only [Real.negMulLog]
  ring

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

end


end OPT
