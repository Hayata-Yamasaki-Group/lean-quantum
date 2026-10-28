import Quantum.QuantumEntropy.VonNeumann.SSA
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneLimit
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupportLimit
import Quantum.QuantumEntropy.SandwichedRenyi.TripartiteSSA
import Quantum.TraceInequality.JensenOperatorInequalityInterval
import Quantum.TraceInequality.LownerHeinz.GlobalDegeneracy
import Quantum.TraceInequality.JensenOperatorInequalityFinite
import Quantum.QuantumEntropy.SandwichedRenyi.Theorem1

/-!
# Additional extraction roots for the public Paper 1 candidate

This is an import-and-#check list, not a comparator or an extraction certificate.
No theorem is redeclared here. An extractor must explicitly consume these roots;
merely importing this file does not certify the candidate dependency closure.
The general alpha-one limit root includes the two-sided limit for nonzero PSD inputs
with support inclusion.
The Petz-type trace-power quotient lemma is intentionally not listed here; it is not a paper claim
and its statement depends on the Hiai–Petz layer.
-/

/-! General-state von Neumann strong subadditivity — Source: arXiv:2607.05492v1, main.tex:219–224.
General density-operator von Neumann SSA, with no faithful-marginal assumptions.
Original statement: Lieb–Ruskai (1973).
The basic route of this proof follows Carlen's lecture notes (version of May 3, 2009), p. 47, proof
of Theorem 6.6. The printed inequality in Theorem 6.6, S(ρ13) + S(ρ23) ≥ S(ρ123) + S(ρ3),
becomes S(ρ_AB) + S(ρ_BC) ≥ S(ρ_ABC) + S(ρ_B) under (1, 2, 3) = (A, C, B),
with the tensor factors permuted into the A ⊗ (B ⊗ C) order used in Lean.
The formalization uses the partial trace over the third system directly instead of the
conditional-expectation presentation, and states the required positivity and support inclusions
explicitly. The existing SSA proof uses Umegaki DPI and faithful mixing. The two-sided Rényi
alpha-one limit on the nonzero PSD support domain is formalized separately by the general
support-domain alpha-one limit root below. -/
#check VonNeumann.strongSubadditivity_of_state

/-! Positive-definite-input right-hand alpha-one limit — Source: main.tex:219.
Sandwiched Rényi → normalized Umegaki, positive-definite inputs, alpha → 1⁺.
Original source: Müller-Lennert et al. (2013), arXiv:1306.3142v4, alpha-one analysis.
This restricted root is retained; the general support-domain root below covers singular inputs. -/
#check SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_umegaki

/-! Positive-definite-input two-sided alpha-one limit — Source: main.tex:219.
Two-sided punctured alpha → 1, still with both inputs positive definite.
Original source: Müller-Lennert et al. (2013), arXiv:1306.3142v4, alpha-one analysis.
This restricted root is retained alongside the general support-domain root below. -/
#check SandwichedRenyiRelativeEntropy.sandwichedRenyi_tendsto_umegaki_of_pd

/-! Nonzero PSD support-domain two-sided alpha-one limit — Source: main.tex:219.
Two-sided punctured alpha → 1 for ρ≥0, ρ≠0, σ≥0 and ker σ⊆ker ρ.
The limit is normalized Umegaki; no trace normalization or positive definiteness is required.
Original source: Müller-Lennert et al. (2013), arXiv:1306.3142v4, alpha-one analysis. -/
#check SandwichedRenyiRelativeEntropy.sandwichedRenyi_tendsto_umegakiNorm_of_support

/-! Tripartite Rényi inequality (NN/EReal) — Source: main.tex:204–218, Eq. intro-generalized-ssa.
NN/EReal tripartite inequality, alpha ≥ 1/2 and alpha ≠ 1, arbitrary PSD input.
Original source: Frank–Lieb (2013), Theorem 1, applied to the CPTP partial trace. -/
#check SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_tripartiteSSA

/-! Tripartite Rényi inequality (finite domain) — Source: main.tex:204–218,
Eq. intro-generalized-ssa.
Real-valued tripartite inequality: positive-definite input reference, explicit
nonzero input/output Re Q and Re Tr conditions. The input state may be singular.
Original source: Frank–Lieb (2013), Theorem 1, finite branch. -/
#check SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tripartiteSSA

/-! P1 Eq. jensen-finite, general-interval roots — Source: main.tex:945–955; Hansen–Pedersen (2003).
Finite contractive Jensen on an arbitrary order-connected real interval containing zero.
Open intervals: no continuity assumption. Intervals with included endpoints: continuity
within the interval at those endpoints is assumed; interior continuity is derived.
The existing half-line root `jensenFinite_of_opConvexIciAll` is unchanged. -/
#check JensenOperatorInequality.jensenFinite_of_opConvexOnAll_of_isOpen
#check JensenOperatorInequality.jensenFinite_of_opConvexOnAll_of_endpoints

/-! Diagnostic roots for global-predicate degeneracy and the localized Jensen theorem
(carried over from the public candidate v2.4 root list).
The four `eq_zero` results show that unrestricted operator convexity/concavity, in the
fixed-algebra and `All` forms, degenerates on nontrivial complex C*-algebras; `x^2` is a
nonzero localized example. `jensenFinite_of_opConvexIciAll` is the half-line finite Jensen
interface (now a specialization of the interval theorem above). `sandwichedRenyiDivNN_theorem1`
is the Theorem 1 wrapper for density inputs. -/
#check LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial
#check LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial
#check LownerHeinzTheorem.OperatorConvexAll.eq_zero
#check LownerHeinzTheorem.OperatorConcaveAll.eq_zero
#check LownerHeinzTheorem.operatorConvexOnAll_Ici_sq
#check JensenOperatorInequality.jensenFinite_of_opConvexIciAll
#check SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_theorem1
