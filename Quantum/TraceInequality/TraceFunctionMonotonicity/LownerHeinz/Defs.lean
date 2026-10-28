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

/-- Fixed-space operator monotonicity on `s` for the ambient algebra `𝓐`.

The elements are assumed self-adjoint with spectrum contained in `s`. For `s ⊆ [0, ∞)`,
the self-adjointness assumptions can equivalently be replaced by `0 ≤ A` and `0 ≤ B`,
while retaining both `spectrum ℝ A ⊆ s` and `spectrum ℝ B ⊆ s`.
The right-hand side of `operatorMonotoneOn_iff_of_subset_Ici` retains these spectral conditions.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Definition 2.1.
Quantification over all matrix sizes is restricted to a single fixed algebra, and the spectral
domain is made explicit. -/
/- Operator monotonicity on a spectral set
    (Carlen 2009, Definition 2.1, formula (2.1)) -/
/- (Carlen 2009, Definition 2.1, formula (2.1)) A function $f \colon (0,\infty) \to
    \mathbb{R}$ is said to be *operator monotone* in case whenever for all $n$, and all
    positive definite $A, B \in \mathbf{H}_n^+$, $A \geq B$ implies $f(A) \geq f(B)$.
    *Lean deviation*: the formalization generalizes this to a predicate parametrized by
    $s \subseteq \mathbb{R}$ over a fixed unital $C^*$-algebra $\mathcal{A}$ — for all
    self-adjoint $A, B \in \mathcal{A}$ with spectra contained in $s$, $B \leq A$ implies
    $f(B) \leq f(A)$ (non-strict order, continuous functional calculus). For each fixed matrix
    size $n$, Carlen's condition is recovered by taking $\mathcal{A} = M_n(\mathbb{C})$ and
    $s = (0, \infty)$; Carlen's full definition additionally quantifies over all $n$. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    IsSelfAdjoint A → IsSelfAdjoint B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f B ≤ cfcR f A

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint],
    OperatorMonotoneOn (𝓐 := 𝓑) s f

omit [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Operator monotonicity on `t` restricts to any subset `s ⊆ t`. -/
theorem OperatorMonotoneOn.mono {s t : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorMonotoneOn (𝓐 := 𝓐) t f) (hst : s ⊆ t) :
    OperatorMonotoneOn (𝓐 := 𝓐) s f :=
  fun _ _ hA0 hB0 hBA hsA hsB ↦ h hA0 hB0 hBA (hsA.trans hst) (hsB.trans hst)

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Specialize `OperatorMonotoneOnAll` to a single ambient algebra. -/
theorem OperatorMonotoneOnAll.operatorMonotoneOn {s : Set ℝ} {f : ℝ → ℝ}
    (h : OperatorMonotoneOnAll.{u} s f)
    {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] :
    OperatorMonotoneOn (𝓐 := 𝓑) s f := h

end Pure

end LownerHeinzCore
