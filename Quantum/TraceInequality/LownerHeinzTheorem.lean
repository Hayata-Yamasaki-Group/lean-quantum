/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.LownerHeinz.Defs

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : (ℋ →L[ℂ] ℋ)) : (ℋ →L[ℂ] ℋ) :=
  LownerHeinzCore.cfcR (𝓐 := (ℋ →L[ℂ] ℋ)) f A

/-- Fixed-space operator convexity on `s` for the Hilbert space `ℋ`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this development, it corresponds to standard operator convexity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
abbrev OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this development, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
abbrev OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

end LownerHeinzTheorem
