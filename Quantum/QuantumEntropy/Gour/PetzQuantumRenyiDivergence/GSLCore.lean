/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiEndpointLimits.GSLCore

/-!
# Gour's Petz quantum Rényi divergence

This file defines the all-order Petz quantum Rényi divergence from Gour's
Definition 6.6, using the punctured family and its uniquely determined
endpoint limits.
-/

namespace OPT

open QuantumState

universe u

/-- Gour's Petz quantum Rényi divergence on the closed order interval. -/
noncomputable def petzQuantumRenyiDivergence
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (alpha : PetzRenyiOrder) (rho sigma : L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) : EReal :=
  if halpha_zero : (alpha : ℝ) = 0 then
    Classical.choose
      (petzRenyiEndpointLimits_existsUnique rho sigma hrho hsigma).1.exists
  else if halpha_one : (alpha : ℝ) = 1 then
    Classical.choose
      (petzRenyiEndpointLimits_existsUnique rho sigma hrho hsigma).2.exists
  else
    petzRenyiPunctured alpha rho sigma hrho hsigma
      halpha_zero halpha_one

end OPT
