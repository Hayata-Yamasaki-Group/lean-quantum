/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumEntropy.CFCTransport
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# von Neumann entropy

The von Neumann entropy `S(ρ) = -Re Tr(ρ log ρ)` of an operator on a
finite-dimensional complex Hilbert space, via the continuous functional
calculus logarithm `CFC.log` (the same logarithm used by `umegakiNorm`).

The definition is total: no positivity or normalization hypotheses are
required, matching the convention of `umegakiNorm`.  Its meaning as an
entropy is asserted only for density operators (`0 ≤ ρ`, `Tr ρ = 1`).
-/

namespace VonNeumann

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/- \textbf{Main result and proof route.}
This chapter proves strong subadditivity (SSA) of von Neumann entropy on finite-dimensional complex
Hilbert spaces.
The proof starts from the data-processing inequality for the sandwiched Rényi divergence of
nonnegative operators.
First, taking the limit $\alpha\to1^+$ for positive definite operators gives the
data-processing inequality for normalized Umegaki relative entropy. This chapter distinguishes the
following two kinds of perturbation. First,
$\varepsilon I$ perturbations of operators and faithful approximations of channels extend the
data-processing inequality for the normalized Umegaki quantity,
obtained for positive definite inputs, to pairs of nonnegative operators satisfying support
inclusion. Applying this to the partial trace over the third system
and expanding both sides in terms of von Neumann entropy gives strong subadditivity with faithful
marginals.

Second, mixing the state with the normalized identity operator, taking the limit as the mixing
coefficient tends to $0$, and using continuity of entropy
yields the general-state version from the version with faithful marginals.

\textbf{The version with faithful marginals and the general-state version.}
This chapter proves strong subadditivity in two stages. First,
`strongSubadditivity` proves the version with faithful marginals, assuming only that the marginal
operators satisfy
\[
  \rho_A>0,\qquad \rho_{BC}>0.
\]
Even at this stage, faithfulness of $\rho_{ABC}$ and $\rho_{AB}$ is
not assumed, and $\rho_B>0$ is derived by taking the partial trace of $\rho_{BC}>0$.

In `strongSubadditivity_of_state`, the mixture with the normalized identity operator
\[
  \rho_\lambda=(1-\lambda)\rho+\lambda d^{-1}I
\]
and continuity of von Neumann entropy also remove the faithfulness assumptions on the marginal
operators, yielding the general version for arbitrary
finite-dimensional tripartite states.

\textbf{Notation.}
The logarithms in this formalization are natural logarithms. In general, let $b>1$ and denote
entropy and
relative entropy defined using logarithms to base $b$ by $S_b,D_b$, respectively. Then
\[
  S_b(\rho)=\frac{S_{\ln}(\rho)}{\ln b},\qquad
  D_b(\rho\Vert\sigma)=\frac{D_{\ln}(\rho\Vert\sigma)}{\ln b}.
\]
Equivalently, $S_{\ln}=(\ln b)S_b$, and for $b=2$,
\[
  S_{\ln}=(\ln 2)S_2.
\]
Since $1/\ln b>0$, the direction and equality conditions of each inequality, including strong
subadditivity,
are unchanged by a change of logarithm base.

\textbf{Correspondence with the literature.}
The roles are distinguished as follows. The historical source of strong subadditivity is
Lieb--Ruskai (1973).
The statement reference for the final general-state version is Carlen (2025), Theorem 7.58, formula
(7.5.1).
The reference for the proof route deriving strong subadditivity from the data-processing inequality
is Carlen (2010), Theorem 6.6,
formulas (6.12)--(6.14). In Lean, this proof route is first implemented as the version with faithful
marginals, in which $\rho_A$ and $\rho_{BC}$ are
positive definite, and is then extended to the general-state version using mixtures with the
normalized identity operator and continuity of
entropy.

\textbf{Bibliography.}
The full bibliographic details of the references cited in this chapter are as follows (the text uses
abbreviated references by author, year, and theorem number).
E.~H.~Lieb and M.~B.~Ruskai, ``Proof of the strong subadditivity of quantum-mechanical entropy,''
J.~Math.~Phys.~14, 1938--1941 (1973).
E.~Carlen, ``Trace Inequalities and Quantum Entropy: An Introductory Course,''
Contemporary Mathematics 529, AMS, 73--140 (2010).
E.~Carlen, ``Inequalities in Matrix Algebras,'' Graduate Studies in Mathematics 251, AMS (2025).
R.~L.~Frank and E.~H.~Lieb, ``Monotonicity of a relative R\'enyi entropy,''
J.~Math.~Phys.~54, 122201 (2013), arXiv:1306.5358v3.
M.~M\"uller-Lennert, F.~Dupuis, O.~Szehr, S.~Fehr, and M.~Tomamichel,
``On quantum R\'enyi entropies: a new generalization and some properties,''
J.~Math.~Phys.~54, 122203 (2013), arXiv:1306.3142v4. -/

/-- **von Neumann entropy** `S(ρ) := -Re Tr(ρ log ρ)`, where `log` is evaluated
directly on `ρ : L ℋ` using the continuous-functional-calculus instances
transported once and for all to `L ℋ`.  Total on all operators;
entropy-theoretic statements assume `0 ≤ ρ` and `Tr ρ = 1`. -/
noncomputable def vonNeumannEntropy (ρ : L ℋ) : ℝ :=
  -(Tr (ρ * CFC.log ρ)).re

section

-- Give Mathlib's bounded-operator C*-algebra instance local priority for
-- `CFCTransport.cfc_log_toCLM`.
attribute [local instance 2000]
  instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace

lemma vonNeumannEntropy_def (ρ : L ℋ) :
    vonNeumannEntropy ρ = -(Tr ((ρ.toContinuousLinearMap *
      CFC.log ρ.toContinuousLinearMap : B ℋ) : L ℋ)).re :=
  by
    rw [vonNeumannEntropy, ← CFCTransport.cfc_log_toCLM ρ]
    rfl

end

end VonNeumann
