/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Löwner-Heinz core definitions


Unrestricted operator convexity/concavity, in fixed-algebra and `All` forms,
degenerates to the zero function on nontrivial complex C*-algebras; see
`GlobalDegeneracy.lean`. Localized predicates use self-adjoint inputs with spectra
in an interval `I`: with continuity on `I` and a fixed ambient algebra, nonzero
examples exist, such as `x²` for convexity on `[0, ∞)`; `OnAll` quantifies over algebras.

References to Carlen 2009 (also written Carlen09) in the comments of these files are to the
lecture notes *Trace Inequalities and Quantum Entropy: An Introductory Course*, manuscript
version of May 3, 2009; the published version appeared in Contemporary Mathematics 529 (2010),
73–140.
-/

namespace LownerHeinzCore

universe u

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]

/-! ### Functional calculus abbreviation and operator predicates -/

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : 𝓐) : 𝓐 :=
  cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A

/-- Fixed-space operator convexity on `s` for the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and the spectral
domain is made explicit.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator convexity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
/- Operator convexity on a spectral set
    (Carlen 2009, Definition 2.1, formula (2.2)) -/
/- (Carlen 2009, Definition 2.1, formula (2.2)) A function
    $f \colon (0,\infty) \to \mathbb{R}$ is said to be *operator convex* in case for all
    $n$ and all $A,B \in \mathbf{H}_n^+$, and $0 < t < 1$,
    \[
      f((1-t)A+tB) \leq (1-t)f(A)+t f(B).
    \]
    Carlen09's displayed formula (2.2) prints the right-hand coefficients as
    $t f(A)+(1-t)f(B)$; this appears to interchange the coefficients, so the symmetric intended
    form is recorded here.
    *Lean deviation*: the formalization generalizes this to an arbitrary
    $s \subseteq \mathbb{R}$ over a fixed unital $C^*$-algebra, for self-adjoint $A,B$ with
    spectra contained in $s$, using non-strict order and $t \in [0,1]$. The predicate does not
    separately require the spectrum of $(1-t)A+tB$ to remain in $s$; in this file $s$ is an
    interval, where this agrees with the intended operator-convex setting. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator concavity on `s` for the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and the spectral
domain is made explicit.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
/- Operator concavity on a spectral set
    (Carlen 2009, Definition 2.1, immediately after formula (2.2)) -/
/- (Carlen 2009, Definition 2.1, immediately after formula (2.2)) A function $f$ is operator
    concave if $-f$ is operator convex.
    *Lean deviation*: the formalization states this on an arbitrary
    $s \subseteq \mathbb{R}$ by requiring $-f$ to satisfy the definition of `OperatorConvexOn`.
    Thus it inherits the same fixed-$C^*$-algebra, self-adjointness, spectrum-in-$s$,
    non-strict-order, and arbitrary-$s$ caveats as the definition of `OperatorConvexOn`; for the
    intervals used here this is the Carlen-style operator-concavity notion. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOn (𝓐 := 𝓐) (s : Set ℝ) (fun x => - f x)

end Pure

end LownerHeinzCore
