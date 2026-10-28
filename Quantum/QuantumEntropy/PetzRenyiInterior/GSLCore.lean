/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzTracePower.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Punctured Petz quantum Rényi divergence

This file defines Gour's Petz quantum Rényi divergence away from the orders
zero and one.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy

universe u

/-- The Petz quantum Rényi divergence away from orders zero and one. -/
noncomputable def petzRenyiPunctured
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (halpha_zero : (alpha : ℝ) ≠ 0) (halpha_one : (alpha : ℝ) ≠ 1) : EReal := by
  classical
  exact if hadmissible : suppLE rho sigma ∨
        ((alpha : ℝ) < 1 ∧ rho * sigma ≠ 0) then
      let q : {x : ℝ // 0 < x} :=
        ⟨petzTracePower alpha rho sigma hrho hsigma,
          (petzTracePower_real_and_pos_of_admissible alpha rho sigma hrho hsigma
            halpha_zero halpha_one hadmissible).2⟩
      ((((alpha : ℝ) - 1)⁻¹ * Real.logb 2 (q : ℝ) : ℝ) : EReal)
    else
      ⊤

end OPT
