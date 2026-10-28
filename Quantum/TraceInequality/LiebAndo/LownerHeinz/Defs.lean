/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Quantum.TraceInequality.LownerHeinz.Defs

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

/-- Fixed-space operator monotonicity on the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and positive definite
inputs are extended to nonnegative inputs. -/
/- Operator monotonicity on the closed positive cone
    (Carlen 2009, Definition 2.1, formula (2.1)) -/
/- (Carlen 2009, Definition 2.1, formula (2.1)) A function
    $f \colon (0,\infty) \to \mathbb{R}$ is said to be *operator monotone* in case whenever
    for all $n$, and all $A,B \in \mathbf{H}_n^+$, $A \geq B$ implies $f(A) \geq f(B)$.
    *Lean deviation*: this declaration is the closed-positive-cone helper predicate over a
    fixed unital $C^*$-algebra $\mathcal{A}$: for $0 \leq B \leq A$ it asserts
    $f(B) \leq f(A)$ via continuous functional calculus. The Carlen09 matrix notion is represented
    more directly by the definition of `OperatorMonotoneOn` with $s = (0,\infty)$. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A → cfcR f B ≤ cfcR f A

/-- Fixed-space operator antitonicity on the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and positive definite
inputs are extended to nonnegative inputs. -/
/- Operator antitonicity on the closed positive cone
    (Carlen 2009, Definition 2.1, equivalent antitone form of formula (2.1)) -/
/- (Carlen 2009, Definition 2.1, equivalent antitone form of formula (2.1))
    Applying the source definition to $-f$ gives this form. A function
    $f \colon (0,\infty) \to \mathbb{R}$ is said to be *operator monotone* in case whenever
    for all $n$, and all $A,B \in \mathbf{H}_n^+$, $A \geq B$ implies $f(A) \geq f(B)$;
    the decreasing version is equivalently that $-f$ is operator monotone.
    *Lean deviation*: this declaration packages the decreasing version as an
    operator-antitone predicate on the closed positive cone of a fixed unital $C^*$-algebra:
    for $0 \leq B \leq A$ it asserts $f(A) \leq f(B)$. The Carlen-style spectrum-restricted
    predicate is the definition of `OperatorAntitoneOn` with $s=(0,\infty)$. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator antitonicity on `s` for the ambient algebra `𝓐`.

The elements are assumed self-adjoint with spectrum contained in `s`. For `s ⊆ [0, ∞)`,
the self-adjointness assumptions can equivalently be replaced by `0 ≤ A` and `0 ≤ B`,
while retaining both `spectrum ℝ A ⊆ s` and `spectrum ℝ B ⊆ s`.
The right-hand side of `operatorAntitoneOn_iff_of_subset_Ici` retains these spectral conditions.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and the spectral
domain is made explicit. -/
/- Operator antitonicity on a spectral set
    (Carlen 2009, Definition 2.1, equivalent antitone form of formula (2.1)) -/
/- (Carlen 2009, Definition 2.1, equivalent antitone form of formula (2.1))
    Applying the source definition to $-f$ gives this form. A function
    $f \colon (0,\infty) \to \mathbb{R}$ is said to be *operator monotone* in case whenever
    for all $n$, and all $A,B \in \mathbf{H}_n^+$, $A \geq B$ implies $f(A) \geq f(B)$;
    the decreasing version is equivalently that $-f$ is operator monotone.
    *Lean deviation*: the formalization generalizes this decreasing notion to a predicate
    parametrized by $s \subseteq \mathbb{R}$ over a fixed unital $C^*$-algebra $\mathcal{A}$:
    for self-adjoint $A,B$ with spectra contained in $s$, $B \leq A$ implies $f(A) \leq f(B)$
    (non-strict order, continuous functional calculus). Carlen's domain is the case
    $s=(0,\infty)$. -/
def OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    IsSelfAdjoint A → IsSelfAdjoint B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator convexity on the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
This is a helper predicate that quantifies even over non-self-adjoint inputs in a fixed algebra, and
differs from standard operator convexity and concavity in the source.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
/- Operator convexity on the ambient algebra
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
    *Lean deviation*: this declaration is an unrestricted total helper predicate over a
    fixed unital $C^*$-algebra, with no self-adjointness or spectral hypotheses on $A,B$, and
    with $t \in [0,1]$. The spectrum-restricted Carlen-style predicate is
    the definition of `OperatorConvexOn`. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator concavity on the ambient algebra `𝓐`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
This is a helper predicate that quantifies even over non-self-adjoint inputs in a fixed algebra, and
differs from standard operator convexity and concavity in the source.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator concavity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
/- Operator concavity on the ambient algebra
    (Carlen 2009, Definition 2.1, immediately after formula (2.2)) -/
/- (Carlen 2009, Definition 2.1, immediately after formula (2.2)) A function $f$ is operator
    concave if $-f$ is operator convex.
    *Lean deviation*: this declaration uses the unrestricted Lean helper
    `OperatorConvex`; hence it is again a nonstandard total predicate over a fixed
    unital $C^*$-algebra. The spectrum-restricted Carlen-style predicate is
    the definition of `OperatorConcaveOn`. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  OperatorConvex (𝓐 := 𝓐) (fun x => - f x)

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity over all ambient algebras in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorMonotone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity over all ambient algebras in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorAntitone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorAntitoneOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity over all ambient algebras in universe `u`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorConvex (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity on `s` over all ambient algebras in universe `u`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator convexity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorConvexOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity over all ambient algebras in universe `u`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator concavity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorConcave (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity on `s` over all ambient algebras in universe `u`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorConcaveOn (𝓐 := 𝓑) s f

/-! ### Basic API for the operator-inequality predicates

The lemmas below characterize the predicates above without unfolding them, so that proofs
(and future redefinitions) do not need to depend on the exact shape of the definitions. -/

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- `OperatorConcave` is, by definition, `OperatorConvex` of the negated function. -/
theorem operatorConcave_iff_operatorConvex_neg (f : ℝ → ℝ) :
    OperatorConcave (𝓐 := 𝓐) f ↔ OperatorConvex (𝓐 := 𝓐) (fun x ↦ -f x) :=
  Iff.rfl

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- `OperatorConcaveOn` is, by definition, `OperatorConvexOn` of the negated function. -/
theorem operatorConcaveOn_iff_operatorConvexOn_neg (s : Set ℝ) (f : ℝ → ℝ) :
    OperatorConcaveOn (𝓐 := 𝓐) s f ↔ OperatorConvexOn (𝓐 := 𝓐) s (fun x ↦ -f x) :=
  Iff.rfl

omit [Nontrivial 𝓐] in
/-- `f` is operator antitone iff `-f` is operator monotone. -/
theorem operatorAntitone_iff_operatorMonotone_neg (f : ℝ → ℝ) :
    OperatorAntitone (𝓐 := 𝓐) f ↔ OperatorMonotone (𝓐 := 𝓐) (fun x ↦ -f x) := by
  constructor
  · intro h A B hA0 hB0 hBA
    simpa [cfcR, cfc_neg] using neg_le_neg (h hA0 hB0 hBA)
  · intro h A B hA0 hB0 hBA
    have h' : -cfcR f B ≤ -cfcR f A := by simpa [cfcR, cfc_neg] using h hA0 hB0 hBA
    exact neg_le_neg_iff.mp h'

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Operator antitonicity on `t` restricts to any subset `s ⊆ t`. -/
theorem OperatorAntitoneOn.mono {s t : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorAntitoneOn (𝓐 := 𝓐) t f) (hst : s ⊆ t) :
    OperatorAntitoneOn (𝓐 := 𝓐) s f :=
  fun _ _ hA0 hB0 hBA hsA hsB ↦ h hA0 hB0 hBA (hsA.trans hst) (hsB.trans hst)

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Operator convexity on `t` restricts to any subset `s ⊆ t`. -/
theorem OperatorConvexOn.mono {s t : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorConvexOn (𝓐 := 𝓐) t f) (hst : s ⊆ t) :
    OperatorConvexOn (𝓐 := 𝓐) s f :=
  fun _ _ _ hA hB ht0 ht1 hsA hsB ↦ h hA hB ht0 ht1 (hsA.trans hst) (hsB.trans hst)

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Operator concavity on `t` restricts to any subset `s ⊆ t`. -/
theorem OperatorConcaveOn.mono {s t : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorConcaveOn (𝓐 := 𝓐) t f) (hst : s ⊆ t) :
    OperatorConcaveOn (𝓐 := 𝓐) s f :=
  OperatorConvexOn.mono h hst

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorMonotoneAll` to a single ambient algebra. -/
theorem OperatorMonotoneAll.operatorMonotone {f : ℝ → ℝ} (h : OperatorMonotoneAll.{u} f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorMonotone (𝓐 := 𝓑) f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorAntitoneAll` to a single ambient algebra. -/
theorem OperatorAntitoneAll.operatorAntitone {f : ℝ → ℝ} (h : OperatorAntitoneAll.{u} f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorAntitone (𝓐 := 𝓑) f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorAntitoneOnAll` to a single ambient algebra. -/
theorem OperatorAntitoneOnAll.operatorAntitoneOn {s : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorAntitoneOnAll.{u} s f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorAntitoneOn (𝓐 := 𝓑) s f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorConvexAll` to a single ambient algebra. -/
theorem OperatorConvexAll.operatorConvex {f : ℝ → ℝ} (h : OperatorConvexAll.{u} f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorConvex (𝓐 := 𝓑) f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorConvexOnAll` to a single ambient algebra. -/
theorem OperatorConvexOnAll.operatorConvexOn {s : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorConvexOnAll.{u} s f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorConvexOn (𝓐 := 𝓑) s f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorConcaveAll` to a single ambient algebra. -/
theorem OperatorConcaveAll.operatorConcave {f : ℝ → ℝ} (h : OperatorConcaveAll.{u} f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorConcave (𝓐 := 𝓑) f := h

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorConcaveOnAll` to a single ambient algebra. -/
theorem OperatorConcaveOnAll.operatorConcaveOn {s : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorConcaveOnAll.{u} s f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorConcaveOn (𝓐 := 𝓑) s f := h

end Pure

end LownerHeinzCore
