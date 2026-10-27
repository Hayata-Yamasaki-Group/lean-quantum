<p align="right"><img alt="English" src="https://img.shields.io/badge/English-0f4c81?style=for-the-badge"> <a href="README.ja.md"><img alt="日本語" src="https://img.shields.io/badge/%E6%97%A5%E6%9C%AC%E8%AA%9E-lightgrey?style=for-the-badge"></a></p>

# lean-quantum

Lean formalization of quantum information theory and quantum computation.

> **Visitors from the IBIS 2026 poster:** the formalization presented there (from the theorems of Löwner and Hiai–Petz to the generalized quantum Stein's lemma) is on the [`paper2`](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/paper2) branch.

<!-- BEGIN BADGES -->
<p align="center">
<a href="https://lean-lang.org/"><img alt="Lean 4.29.0--rc6" src="https://img.shields.io/badge/Lean-4.29.0--rc6-0f4c81.svg?style=flat-square"></a>
<a href="https://arxiv.org/abs/2607.05492"><img alt="arXiv 2607.05492" src="https://img.shields.io/badge/arXiv-2607.05492-b31b1b.svg?style=flat-square"></a>
<a href="LICENSE"><img alt="Apache 2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square"></a>
</p>
<!-- END BADGES -->

## Updates

- **2026-10.** The formalization reported in the second Lean-Quantum paper (Paper 2, in preparation for submission) is available on the [`paper2`](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/paper2) branch.
- **2026-10.** The code was updated to accompany version 2 of arXiv:2607.05492 (to be submitted). It adopts several of [Mathlib's values](https://leanprover-community.github.io/contribute/values.html), the principles of the standard mathematical library, for example by splitting large files into smaller ones organized by topic and by renaming declarations to follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html), with a few exceptions. Some definitions and theorems were also restated. The 34 theorems listed in [Results](#results) can now be checked independently with Comparator. The code accompanying arXiv v1 remains available at commit [`bf1c4f6`](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/bf1c4f6aaec84948f1a1c76c0728432813404a0f).

## Contents

- [What is covered](#what-is-covered)
- [Linear and bounded linear operators](#linear-and-bounded-linear-operators)
- [How to run](#how-to-run)
- [Independent proof checking](#independent-proof-checking)
- [Results](#results)
- [Poster presentation (AQIS 2026)](#poster-presentation-aqis-2026)
- [How to cite](#how-to-cite)

## What is covered

The library currently provides foundations mainly for finite-dimensional quantum information theory (some operator inequalities also in infinite dimension),
checked by Lean's kernel (the small core of Lean that checks proofs), including:

- quantum systems, states, and completely positive trace-preserving (CPTP) maps;
- partial traces on tensor-product spaces, Choi operators, Kraus representations, and
  Stinespring representations;
- operator monotonicity and convexity, the Löwner–Heinz theorem, Jensen's
  operator inequality, generalized perspectives, operator geometric means,
  Hilbert-Schmidt operator spaces, and Lieb-Ando trace inequalities;
- sandwiched Renyi relative entropy and its data-processing inequality (DPI),
  together with non-negativity and its limits to Umegaki and max-relative entropy;
- von Neumann entropy, the DPI for Umegaki relative entropy, and strong subadditivity; and
- supporting lemmas on the continuous functional calculus (such as powers of
  tensor products and derivatives of powers in the exponent), trace Young
  inequalities, and averages over the Haar measure on unitary groups.

The module [`Quantum.lean`](Quantum.lean) imports every module (Lean file) in the
[`Quantum/`](Quantum/) directory, so `import Quantum` makes all public declarations
of the library available.

## Linear and bounded linear operators

On a finite-dimensional Hilbert space every linear operator is bounded, so the linear
operators $\mathcal L(\mathcal H)$ and the bounded linear operators $\mathcal B(\mathcal H)$ can be
identified. In Lean, however, they are different types (`ℋ →ₗ[ℂ] ℋ` and `ℋ →L[ℂ] ℋ`).
Mathlib treats $\mathcal B(\mathcal H)$ as a C*-algebra, on which the continuous functional calculus `cfc` (used to define operator powers and logarithms)
and Haar measure on unitary groups are available. This repository also equips $\mathcal L(\mathcal H)$ with the C*-algebra structure transferred from $\mathcal B(\mathcal H)$, and the proofs move
operators to $\mathcal B(\mathcal H)$ where these tools are needed; the Hilbert–Schmidt inner
product is also built on it. By definition, `cfc` returns $0$ on elements that do not satisfy its precondition (for real functions, non-self-adjoint elements); the table of [Definitions used in the theorems](#definitions-used-in-the-theorems) therefore also gives values outside the intended inputs. The main finite-dimensional theorems (on complete
positivity, Lieb–Ando, entropies and the DPI, among others) are stated for
$\mathcal L(\mathcal H)$. The theorems on operator powers are stated in general C*-algebras. Those on
Jensen's operator inequality and generalized perspectives are stated for $\mathcal B(\mathcal H)$ on
Hilbert spaces of any dimension, including infinite dimension.

## How to run

These steps compile and check the code on your own computer; they are not needed for reading this README. If Lean is not installed, first [install it with `elan`](https://lean-lang.org/install/).

```bash
git clone https://github.com/Hayata-Yamasaki-Group/lean-quantum.git
cd lean-quantum
lake exe cache get   # download the prebuilt files of Mathlib
lake build           # check every proof with Lean's kernel
```

- The Lean version and the dependencies are fixed by [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json); the only mathematics library dependency is Mathlib (Comparator is a verification tool).
- Do not run `lake update` (it would change the pinned versions of the dependencies).
- `lake build` succeeds even with `sorry`, which only produces a warning. The library and the solution file contain no `sorry` (the statements-only file uses it on purpose as a placeholder for omitted proofs); the axioms a theorem depends on can be checked with `#print axioms` followed by its name (a proof using `sorry` shows `sorryAx`).

## Independent proof checking

**Guarantee**: [Comparator](https://github.com/leanprover/comparator) lets the user conclude, without trusting the
whole codebase but only the statements-only file [`Paper1.lean`](ComparatorChallenges/Paper1.lean) (the challenge, in Comparator's terms), the
modules it imports, the check configuration ([`Paper1.json`](ComparatorChallenges/Paper1.json)), and the build configuration (lakefile), that, when the check succeeds, the 34 theorems stated in `Paper1.lean` (listed under
[Results](#results)) are proved (see the [Comparator README](https://github.com/leanprover/comparator/blob/a4f696825c583ed8a5b4060d9a0faa5b882d365b/README.md) for its other assumptions).

**How it checks**: It builds the solution file [`Paper1Solution.lean`](ComparatorChallenges/Paper1Solution.lean) (the solution, in Comparator's terms) in a sandbox (landrun) that restricts where it can write,
checks that each theorem has the same statement as in `Paper1.lean` (including the definitions the statement
uses) and uses only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`; a proof using `sorry` fails here), and rechecks
the proofs with both Lean's kernel and the independent nanoda kernel.

**What is trusted**: For the imported modules, the user needs to trust only the meaning of the terms they define (checked with the table of [Definitions used in the theorems](#definitions-used-in-the-theorems)) and that they contain no program that alters what is checked or how it is checked when the files are built (Lean files can run programs during the build), because Comparator also rechecks the proofs in those modules that the 34 theorems depend on.

**Run**: For this version, Comparator was run on Linux with Landlock enabled, building the solution file in the sandbox, and all 34 theorems were accepted by both Lean's kernel and nanoda.

**What it cannot check**: Comparator cannot check whether the statements
of the Lean theorems (including implicit arguments and type-class instances), and the definitions they use, state what the paper intends; this has to be checked by the user, for which the definitions are listed below in a table under
[Definitions used in the theorems](#definitions-used-in-the-theorems).
See [ComparatorChallenges/README.md](ComparatorChallenges/README.md) for setup and
execution instructions (running it isolated requires Linux with Landlock enabled).

## Results

The 34 theorems, chosen as the targets of the Comparator check rather than all theorems of the library, are shown in the tables of the following subsections.

1. [Complete positivity and channel representations](#1-complete-positivity-and-channel-representations) (6)
2. [Operator monotone and convex powers](#2-operator-monotone-and-convex-powers) (5)
3. [Jensen's operator inequality and generalized perspectives](#3-jensens-operator-inequality-and-generalized-perspectives) (6)
4. [Lieb–Ando trace inequalities](#4-liebando-trace-inequalities) (3)
5. [Sandwiched Rényi data processing and consequences](#5-sandwiched-rényi-data-processing-and-consequences) (9)
6. [Diagnostic results](#6-diagnostic-results) (5)
- [Definitions used in the theorems](#definitions-used-in-the-theorems)

The tables in subsections 1–6 below have the following three columns.

- **Paper location**
  - In subsections 1–5, a link to the equation or the passage of the text (not the Lean code listed in the paper) where our paper ([arXiv:2607.05492](https://arxiv.org/abs/2607.05492)) refers to the theorem
  - In subsection 6, a link to the section where the paper introduces predicates such as operator convexity
  - Passages of the text are quoted before each table by their first and last words joined by “…”
  - Until version 2 is public, locations give the arXiv v1 sections, equation numbers and text and link to arXiv v1 (we plan to replace them with those of version 2 once it appears)
- **Statement**
  - In subsections 1–5, the mathematical theorem taken up by version 2 of the paper (to be submitted); most have original sources, which, together with their proofs, are the basis of the formalization
  - Where the assumptions or scope differ from the original sources or the paper in order to state the theorem in Lean, this is said in this column of each table and in the text of the subsection
- **Lean declaration**
  - The formalization of the theorem in Lean
  - The link opens the declaration in the statements-only file [`Paper1.lean`](ComparatorChallenges/Paper1.lean)
  - The proof can be followed from the theorem of the same name in [`Paper1Solution.lean`](ComparatorChallenges/Paper1Solution.lean)

The user compares each Statement with the Lean statement of its Lean declaration, and, where the Lean statement uses definitions of this repository, also with the table of [Definitions used in the theorems](#definitions-used-in-the-theorems). The user checks that the Lean statement (including implicit arguments and type-class instances) is the intended formalization; that it is proved is checked by Comparator (see [Independent proof checking](#independent-proof-checking) for what Comparator relies on).

Of the 34 theorems, 29 formalize some of the theorems stated in Sections 1.5 and 2–4 of the paper, sometimes splitting one theorem into several Lean theorems. The other five show the grounds on which we defined operator convexity and concavity only for self-adjoint elements ([6. Diagnostic results](#6-diagnostic-results)) and are not theorems of the paper. Each subsection first shows one of its theorems as an example, states the assumptions common to the subsection, and lists its theorems in the table. Below, PSD means that an operator (in subsection 2, an element of a C*-algebra) is positive semidefinite, and PD that it is positive semidefinite and invertible.

### 1. Complete positivity and channel representations

CP is complete positivity in the sense of Mathlib (`IsCompletelyPositive` in [Definitions used in the theorems](#definitions-used-in-the-theorems)). Choose a basis $b=(b_i)$ of the input space $\mathcal H_1$ (not necessarily orthonormal) and set $\mathrm{vec}_b(I)=\sum_ib_i\otimes b_i$; the characterization by the Choi operator $C_\Phi$ (Choi's theorem) then reads:

$$\mathrm{CP}(\Phi) \iff C_\Phi\ge0,\qquad C_\Phi:=(\Phi\otimes\mathrm{id})[\mathrm{vec}_b(I)\mathrm{vec}_b(I)^\dagger].$$

The theorems in this subsection concern complex-linear maps $\Phi:L(\mathcal H_1)\to L(\mathcal H_2)$ between the operator spaces of finite-dimensional complex Hilbert spaces $\mathcal H_1,\mathcal H_2$ (also called superoperators). The paper states the following six equivalences together in one paragraph of Section 2.2.

Quoted paper locations:

- [Section 2.2](https://arxiv.org/html/2607.05492v1#S2.SS2.p13): “The main equivalence theorem relates … rank Stinespring representations.”

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 2.2](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff $\Phi\otimes\mathrm{id}_{L(\mathcal H_1)}$ is positive. | [`cp_iff_tensor`](ComparatorChallenges/Paper1.lean#L62) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff the Choi operator $C_\Phi\ge0$. | [`cp_iff_choi`](ComparatorChallenges/Paper1.lean#L71) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff $\Phi(X)=\sum_{a\in J}A_aXA_a^\dagger$ for finite $J$. | [`cp_iff_kraus`](ComparatorChallenges/Paper1.lean#L83) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff $\lvert J\rvert=\mathrm{rank}C_\Phi$ for some Kraus representation. | [`cp_iff_rank_kraus`](ComparatorChallenges/Paper1.lean#L91) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff $\Phi(X)=\mathrm{Tr}_E[AXA^\dagger]$ for finite-dimensional $E$. | [`cp_iff_stinespring`](ComparatorChallenges/Paper1.lean#L103) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S2.SS2.p13) | $\mathrm{CP}(\Phi)$ iff $\dim E=\mathrm{rank}C_\Phi$ for some Stinespring representation. | [`cp_iff_rank_stinespring`](ComparatorChallenges/Paper1.lean#L119) |

### 2. Operator monotone and convex powers

For elements $A,B$ of an ordered complex C*-algebra and a real number $p$, the Löwner–Heinz inequality reads:

$$0\le p\le1, 0\le B\le A \implies B^p\le A^p.$$

The theorems in this subsection concern elements of an ordered complex C*-algebra; real powers are defined by the continuous functional calculus (on PSD elements for nonnegative powers and PD elements for negative powers).

Quoted paper locations:

- [Section 3.1 (positive powers)](https://arxiv.org/html/2607.05492v1#S3.SS1.p8): “These express the standard facts that … for $1\le p\le2$.”
- [Section 3.1 (negative powers)](https://arxiv.org/html/2607.05492v1#S3.SS1.p9): “The current Core interface also includes negative-power results, … trace inequalities:”

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 3.1 (positive powers)](https://arxiv.org/html/2607.05492v1#S3.SS1.p8) | $x\mapsto x^p$ is operator monotone on $[0,\infty)$ for $0\le p\le1$. | [`power_Icc_zero_one_operatorMonotoneOn_Ici`](ComparatorChallenges/Paper1.lean#L138) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1.p8) | $x\mapsto x^p$ is operator concave on $[0,\infty)$ for $0\le p\le1$. | [`operatorConcaveOn_rpow_Ici`](ComparatorChallenges/Paper1.lean#L146) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1.p8) | $x\mapsto x^p$ is operator convex on $[0,\infty)$ for $1\le p\le2$. | [`operatorConvexOn_rpow_Ici`](ComparatorChallenges/Paper1.lean#L155) |
| [Section 3.1 (negative powers)](https://arxiv.org/html/2607.05492v1#S3.SS1.p9) | $x\mapsto-x^p$ is operator monotone on $(0,\infty)$ for $-1\le p\le0$. | [`power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi`](ComparatorChallenges/Paper1.lean#L164) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1.p9) | $x\mapsto-x^p$ is operator concave on $(0,\infty)$ for $-1\le p\le0$. | [`operatorConcaveOn_neg_rpow_Ioi`](ComparatorChallenges/Paper1.lean#L173) |

### 3. Jensen's operator inequality and generalized perspectives

Jensen's operator inequality for finitely many operators reads as follows: for bounded operators $A_j,X_j\in\mathcal B(\mathcal H)$ on a complex Hilbert space $\mathcal H$ (finitely many $j$) with $A_j$ PSD and $\sum_jX_j^\dagger X_j\le I$, and a real function $f$ uniformly operator convex on $[0,\infty)$ (operator convex on every complex Hilbert space), continuous, with $f(0)\le0$,

$$f[\sum_jX_j^\dagger A_jX_j]\le\sum_jX_j^\dagger f[A_j]X_j.$$

The theorems in this subsection use complex Hilbert spaces without a finite-dimensional assumption.

Quoted paper locations:

- [Section 3.4](https://arxiv.org/html/2607.05492v1#S3.SS4.p2): “The main theorem packages the implication … two-operator Jensen form:”
- [Section 3.5 (convexity)](https://arxiv.org/html/2607.05492v1#S3.SS5.p5): “Thus, if $f$ is operator convex … positive-definite domains.”
- [Section 3.5 (concavity)](https://arxiv.org/html/2607.05492v1#S3.SS5.p7): “The corresponding concavity theorem is obtained … to $-f$:”

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 3.4](https://arxiv.org/html/2607.05492v1#S3.SS4.p2) | The two-operator Jensen inequality holds for PSD inputs with a contractive column, that is, $X^\dagger X+Y^\dagger Y\le I$. | [`jensenColumn_of_opConvexIciAll`](ComparatorChallenges/Paper1.lean#L182) |
| [Section 3.5 (convexity)](https://arxiv.org/html/2607.05492v1#S3.SS5.p5) | The generalized perspective $(f\Delta h)(A,B)$ is jointly convex for PSD $A$ and PD $B$; $f$ is uniformly operator convex and continuous on $[0,\infty)$ with $f(0)\le0$, and $h$ is operator concave, continuous and positive on $(0,\infty)$. | [`jointlyConvexOn_generalizedPerspective_psdSet_pdSet`](ComparatorChallenges/Paper1.lean#L191) |
| [Section 3.5 (concavity)](https://arxiv.org/html/2607.05492v1#S3.SS5.p7) | The generalized perspective $(f\Delta h)(A,B)$ is jointly concave for PSD $A$ and PD $B$; $f$ is uniformly operator concave and continuous on $[0,\infty)$ with $f(0)\ge0$, and $h$ is as in the convexity row. | [`jointlyConcaveOn_generalizedPerspective_psdSet_pdSet`](ComparatorChallenges/Paper1.lean#L206) |
| [Section 3.4, Eq. (30)](https://arxiv.org/html/2607.05492v1#S3.E30) | The finite Jensen inequality holds for $f$ uniformly operator convex and continuous on $[0,\infty)$ with $f(0)\le0$. | [`jensenFinite_of_opConvexIciAll`](ComparatorChallenges/Paper1.lean#L413) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.E30) | The finite Jensen inequality holds for self-adjoint $A_j$ with spectra in an open interval $I$ containing zero (not necessarily PSD) and $f$ uniformly operator convex on $I$ with $f(0)\le0$. | [`jensenFinite_of_opConvexOnAll_of_isOpen`](ComparatorChallenges/Paper1.lean#L457) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.E30) | The finite Jensen inequality holds for self-adjoint $A_j$ with spectra in an interval $I$ containing zero and $f$ uniformly operator convex on $I$ with $f(0)\le0$ and continuity from within $I$ at included endpoints. | [`jensenFinite_of_opConvexOnAll_of_endpoints`](ComparatorChallenges/Paper1.lean#L473) |

### 4. Lieb–Ando trace inequalities

For operators $A,B,K\in L(\mathcal H)$ on a finite-dimensional complex Hilbert space $\mathcal H$ with $A,B$ PD, and $0<s<1$, the following real-valued Lieb functional is jointly concave (Lieb's concavity theorem):

$$(A,B)\mapsto\mathrm{Re}\mathrm{Tr}[A^sK^\dagger B^{1-s}K].$$

The theorems in this subsection use finite-dimensional complex Hilbert spaces.

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 3.7, Eq. (39)](https://arxiv.org/html/2607.05492v1#S3.E39) | The Lieb functional is jointly concave for $0<s<1$. | [`jointlyConcaveOn_liebTraceMap_pdSetLM`](ComparatorChallenges/Paper1.lean#L223) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.E39) | The Lieb functional is jointly convex for $1\le s\le2$. | [`jointlyConvexOn_liebTraceMap_pdSetLM`](ComparatorChallenges/Paper1.lean#L233) |
| [Section 3.7, Eq. (40)](https://arxiv.org/html/2607.05492v1#S3.E40) | $\mathrm{Re}\mathrm{Tr}[A^qK^\dagger B^{-r}K]$ is jointly convex for $1\le q\le2$, $0\le r\le1$, $1\le q-r$. | [`jointlyConvexOn_andoTraceMap_pdSetLM`](ComparatorChallenges/Paper1.lean#L243) |

### 5. Sandwiched Rényi data processing and consequences

Theorem 1 is the data-processing inequality (DPI) for the sandwiched Rényi relative entropy: for density operators $\rho,\sigma$ on $\mathcal H_1$ ($\sigma$ PD), a CPTP map $\Phi:L(\mathcal H_1)\to L(\mathcal H_2)$, and $\alpha\in[1/2,1)\cup(1,\infty)$,

$$D_\alpha(\Phi[\rho]\Vert\Phi[\sigma])\le D_\alpha(\rho\Vert\sigma).$$

The two tripartite strong subadditivity (SSA) rows state $D_\alpha(\rho_{BC}\Vert\rho_B\otimes\tau_C)\le D_\alpha(\rho_{ABC}\Vert\rho_{AB}\otimes\tau_C)$ with $\tau_C=I_C/\dim C$. The theorems in this subsection use finite-dimensional complex Hilbert spaces. All DPI maps are CPTP, and the DPI and Rényi SSA statements use the range of $\alpha$ stated above. Divergences are real-valued, except that the `NN` versions are the extended-real-valued versions for PSD inputs (Theorem 1 is stated with the `NN` version).

Quoted paper locations:

- [Section 4.4](https://arxiv.org/html/2607.05492v1#S4.SS4.p3): “The development also formalizes … DPI for positive semidefinite operators.”
- [Section 1.5](https://arxiv.org/html/2607.05492v1#S1.SS5.p1): “In the limit $\alpha\to1$, the sandwiched Rényi … Umegaki relative entropy”

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 4.4](https://arxiv.org/html/2607.05492v1#Thmtheorem1) | The real-valued DPI holds for PD inputs and outputs (the core of the proof of Theorem 1). | [`sandwichedRenyiDiv_monotone`](ComparatorChallenges/Paper1.lean#L257) |
| [Section 4.4](https://arxiv.org/html/2607.05492v1#S4.SS4.p3) | The extended-real DPI holds for arbitrary PSD inputs. | [`sandwichedRenyiDivNN_monotone`](ComparatorChallenges/Paper1.lean#L272) |
| [Section 4.4, Eq. (65), Theorem 1](https://arxiv.org/html/2607.05492v1#S4.E65) | The DPI holds for density inputs with positive definite $\sigma$ (Theorem 1). | [`sandwichedRenyiDivNN_monotone_of_isDensity`](ComparatorChallenges/Paper1.lean#L430) |
| [Section 1.5, Eq. (4)](https://arxiv.org/html/2607.05492v1#S1.E4) | $S(\rho_{ABC})+S(\rho_B)$ $\le S(\rho_{AB})+S(\rho_{BC})$ holds for states. | [`strongSubadditivity_of_state`](ComparatorChallenges/Paper1.lean#L287) |
| [Section 1.5](https://arxiv.org/html/2607.05492v1#S1.SS5.p1) | For PD inputs, the sandwiched Rényi relative entropy converges as $\alpha\to1^+$ to the Umegaki relative entropy divided by $\mathrm{Tr}\,\rho$. | [`tendsto_sandwichedRenyiDiv_umegakiNorm_right`](ComparatorChallenges/Paper1.lean#L305) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S1.SS5.p1) | For PD inputs, the sandwiched Rényi relative entropy converges as $\alpha\to1$, $\alpha\ne1$, to the Umegaki relative entropy divided by $\mathrm{Tr}\,\rho$. | [`tendsto_sandwichedRenyiDiv_umegakiNorm_of_pd`](ComparatorChallenges/Paper1.lean#L317) |
| [Section 1.5, Eq. (3)](https://arxiv.org/html/2607.05492v1#S1.E3) | The extended-real tripartite SSA holds for arbitrary PSD input. | [`sandwichedRenyiDivNN_tripartiteSSA`](ComparatorChallenges/Paper1.lean#L328) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S1.E3) | The real-valued tripartite SSA holds when $\rho_{AB}\otimes\tau_C$ is PD and $\mathrm{Re}\,Q_\alpha$ on both sides and $\mathrm{Re}\,\mathrm{Tr}\rho$ are nonzero. | [`sandwichedRenyiDiv_tripartiteSSA`](ComparatorChallenges/Paper1.lean#L343) |
| [Section 1.5](https://arxiv.org/html/2607.05492v1#S1.SS5.p1) | For PSD inputs with $\rho\ne0$ and $\mathrm{supp}\rho\subseteq\mathrm{supp}\sigma$, the sandwiched Rényi relative entropy converges as $\alpha\to1$, $\alpha\ne1$, to the Umegaki relative entropy divided by $\mathrm{Tr}\,\rho$. | [`tendsto_sandwichedRenyiDiv_umegakiNorm_of_supportLE`](ComparatorChallenges/Paper1.lean#L445) |

### 6. Diagnostic results

The five theorems in this subsection show the grounds on which we defined operator convexity and concavity only for self-adjoint elements, and are not theorems asserted by the paper. [`OperatorConvex`](#def-operatorconvex) and [`OperatorConcave`](#def-operatorconcave) are predicates quantified over all elements of a complex C*-algebra, including non-self-adjoint ones, and [`OperatorConvexAll`](#def-operatorconvexall) and [`OperatorConcaveAll`](#def-operatorconcaveall) impose them on every complete, nontrivial complex Hilbert space; by definition, `cfc` returns $0$ on non-self-adjoint elements, so only $f=0$ satisfies them (for a nontrivial C*-algebra):

$$\mathrm{OperatorConvexAll}(f) \implies f=0.$$

Hence, with these predicates as hypotheses, the hypothesis fails for $f\ne0$ and the theorem holds only vacuously. The theorems on Jensen's operator inequality and generalized perspectives therefore use predicates that quantify only over self-adjoint elements with spectrum in an interval $s$ (such as `OperatorConvexOn`); for example, operator convexity restricted to $s=[0,\infty)$ (PSD elements) admits $x\mapsto x^2$. The paper locations below point to Section 3.1, where the paper introduces predicates such as operator convexity.

| Paper location | Statement | Lean declaration |
|---|---|---|
| [Section 3.1](https://arxiv.org/html/2607.05492v1#S3.SS1) | `OperatorConvex` forces $f(x)=0$ for every real $x$. | [`OperatorConvex.eq_zero_of_nontrivial`](ComparatorChallenges/Paper1.lean#L367) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1) | `OperatorConcave` forces $f(x)=0$ for every real $x$. | [`OperatorConcave.eq_zero_of_nontrivial`](ComparatorChallenges/Paper1.lean#L378) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1) | `OperatorConvexAll` forces $f=0$. | [`OperatorConvexAll.eq_zero`](ComparatorChallenges/Paper1.lean#L388) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1) | `OperatorConcaveAll` forces $f=0$. | [`OperatorConcaveAll.eq_zero`](ComparatorChallenges/Paper1.lean#L396) |
| [Same as above](https://arxiv.org/html/2607.05492v1#S3.SS1) | $x\mapsto x^2$ is uniformly operator convex on $[0,\infty)$. | [`operatorConvexOnAll_Ici_sq`](ComparatorChallenges/Paper1.lean#L404) |

### Definitions used in the theorems

The table below explains, in the order in which the subsections of the [results](#results) mention them, the definitions that appear in the statements of the 34 theorems of [`Paper1.lean`](ComparatorChallenges/Paper1.lean); definitions from Mathlib are not listed. Each entry states what the Lean definition says, including its value outside the intended inputs.

| Lean&nbsp;definition | What the definition says |
|---|---|
| **Common** | |
| [`Qudit`](Quantum/QuantumMechanics/QuantumState.lean#L20) | Type class for a finite-dimensional complex inner-product space (normed and complete). Dimension $0$ is allowed; nonzero dimension is the separate assumption `Nontrivial` |
| [`L`](Quantum/QuantumMechanics/OperatorNotation.lean#L26) | The type `L ℋ` of complex-linear maps `ℋ →ₗ[ℂ] ℋ`. Its order is Mathlib's Löwner order: $X\le Y$ iff $Y-X$ is positive semidefinite |
| [`B`](Quantum/QuantumMechanics/OperatorNotation.lean#L29) | The type `B ℋ` of bounded (continuous) complex-linear operators `ℋ →L[ℂ] ℋ`, with the Löwner order |
| [`Tr`](Quantum/QuantumMechanics/QuantumState.lean#L39) | The trace `LinearMap.trace ℂ ℋ` on `L ℋ`, complex-valued |
| [`T`](Quantum/QuantumMechanics/Channel/Basic.lean#L31) | The type `T ℋ₁ ℋ₂` of complex-linear maps `L ℋ₁ →ₗ[ℂ] L ℋ₂`, with no positivity or trace condition |
| **1. Complete positivity and channel representations** | |
| [`IsCompletelyPositive`](Quantum/QuantumMechanics/Channel/AmplificationCore.lean#L111) | $\Phi$ is completely positive in Mathlib's sense (`CompletelyPositiveMap`): for every $k$, applying $\Phi$ entrywise sends each positive $k\times k$ matrix over the C*-algebra `L ℋ₁` to a positive matrix |
| [`AmplificationPositive`](Quantum/QuantumMechanics/Channel/TensorModel.lean#L282) | $\Phi\otimes\mathrm{id}_{L(\mathcal H_1)}$, from $L(\mathcal H_1\otimes\mathcal H_1)$ to $L(\mathcal H_2\otimes\mathcal H_1)$, sends positive semidefinite operators to positive semidefinite operators |
| [`ChoiPositive`](Quantum/QuantumMechanics/Channel/Representations.lean#L36) | For a basis $b$ of $\mathcal H_1$ (not necessarily orthonormal), $(\Phi\otimes\mathrm{id})(\lvert\Omega_b\rangle\langle\Omega_b\rvert)\ge0$ in $L(\mathcal H_2\otimes\mathcal H_1)$, where $\Omega_b=\sum_ib_i\otimes b_i=\mathrm{vec}_b(I)$ |
| [`HasKraus`](Quantum/QuantumMechanics/Channel/Representations.lean#L68) | There are a finite index type $\kappa$ (possibly empty, in the universe of $\mathcal H_1$) and linear maps $A_a:\mathcal H_1\to\mathcal H_2$ with $\Phi(X)=\sum_{a\in\kappa}A_aXA_a^\dagger$ for all $X$ |
| [`HasRankKraus`](Quantum/QuantumMechanics/Channel/Representations.lean#L72) | `HasKraus` with, in addition, $\lvert\kappa\rvert$ equal to `choiRank b Φ` (below) |
| [`traceOutRight`](Quantum/QuantumMechanics/Channel/Representations.lean#L232) | Partial trace over the right factor: the linear map $L(\mathcal H_2\otimes\mathcal H_3)\to L(\mathcal H_2)$ with $X\otimes Y\mapsto\mathrm{Tr}(Y)X$ (defined as `traceOutLeft` (below) after swapping the factors) |
| [`choiRank`](Quantum/QuantumMechanics/Channel/Representations.lean#L60) | The rank (dimension of the range) of the Choi operator $(\Phi\otimes\mathrm{id})(\lvert\Omega_b\rangle\langle\Omega_b\rvert)$ of `ChoiPositive`, a natural number |
| **2. Operator monotone and convex powers** | |
| [`OperatorMonotoneOn`](Quantum/TraceInequality/LownerHeinz/Defs.lean#L79) | In a fixed ordered C*-algebra: for all self-adjoint $A,B$ with spectra in $s$ and $B\le A$, $f(B)\le f(A)$, where $f(A)$ is Mathlib's continuous functional calculus `cfc f A` |
| [`LownerHeinzCore.OperatorConcaveOn`](Quantum/TraceInequality/LownerHeinz/Defs.lean#L241) | `OperatorConvexOn s (-f)` (below) in the same algebra |
| [`OperatorConvexOn`](Quantum/TraceInequality/LownerHeinz/Defs.lean#L191) | In a fixed ordered C*-algebra: for all self-adjoint $A,B$ with spectra in $s$ and $t\in[0,1]$, $f((1-t)A+tB)\le(1-t)f(A)+tf(B)$ (`cfc`); the spectrum of $(1-t)A+tB$ is not separately constrained |
| **3. Jensen's operator inequality and generalized perspectives** | |
| [`OperatorConvexIciAllContNonposAtZero`](Quantum/TraceInequality/JensenOperatorInequalityIImpIV.lean#L75) | `OperatorConvexOnAll (Set.Ici 0) f` (below), continuity of $f$ on $[0,\infty)$, and $f(0)\le0$ |
| [`JensenContractiveColumnCondition`](Quantum/TraceInequality/JensenOperatorInequalityIImpIV.lean#L84) | On a fixed Hilbert space: for self-adjoint $A,B$ in `B ℋ` with spectra in $[0,\infty)$ and all $X,Y$ with $X^\dagger X+Y^\dagger Y\le I$, $f(X^\dagger AX+Y^\dagger BY)\le X^\dagger f(A)X+Y^\dagger f(B)Y$ (`cfcR`, below) |
| [`LownerHeinzTheorem.OperatorConcaveOn`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L91) | `LownerHeinzCore.OperatorConcaveOn s f` in the C*-algebra `B ℋ` of the given Hilbert space $\mathcal H$ |
| [`JointlyConvexOn`](Quantum/TraceInequality/GeneralizedPerspectiveFunction.lean#L32) | For $A_1,A_2\in s$, $B_1,B_2\in t$ and $\theta\in[0,1]$, with $A_\theta=(1-\theta)A_1+\theta A_2$ and $B_\theta=(1-\theta)B_1+\theta B_2$, $\Phi(A_\theta,B_\theta)$ is at most $(1-\theta)\Phi(A_1,B_1)+\theta\Phi(A_2,B_2)$; $s,t$ need not be convex |
| [`psdSet`](Quantum/TraceInequality/GeneralizedPerspectiveFunction.lean#L97) | The set of self-adjoint $A$ in `B ℋ` with spectrum in $[0,\infty)$ |
| [`pdSet`](Quantum/TraceInequality/GeneralizedPerspectiveFunction.lean#L101) | The set of self-adjoint $A$ in `B ℋ` with spectrum in $(0,\infty)$ (positive semidefinite and invertible) |
| [`generalizedPerspective`](Quantum/TraceInequality/GeneralizedPerspectiveFunction.lean#L81) | $h(B)^{1/2}f(h(B)^{-1/2}Ah(B)^{-1/2})h(B)^{1/2}$ with $h(B)^{\pm1/2}$ = `cfcR (fun x ↦ h x ^ (±1/2)) B` (`cfcR` below); defined for all $A,B$, and positivity and invertibility of $h(B)$ are assumed in the theorems |
| [`OperatorConcaveOnAll`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L204) | `LownerHeinzTheorem.OperatorConcaveOn s f` on every nontrivial complete complex Hilbert space $K$ in universe `u`, of any dimension |
| [`JointlyConcaveOn`](Quantum/TraceInequality/GeneralizedPerspectiveFunction.lean#L44) | `JointlyConvexOn` with the inequality reversed |
| [`cfcR`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L37) | `cfcR f A` is Mathlib's `cfc f A` for $A$ in `B ℋ` (real functional calculus $f(A)$); it is $0$ if $A$ is not self-adjoint or $f$ is not continuous on its spectrum |
| [`OperatorConvexOnAll`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L169) | `LownerHeinzCore.OperatorConvexOn s f` in `B K` for every nontrivial complete complex Hilbert space $K$ in universe `u`, of any dimension |
| **4. Lieb–Ando trace inequalities** | |
| [`pdSetLM`](Quantum/QuantumEntropy/Common/PositiveDefiniteSet.lean#L47) | The set of $A$ in `L ℋ` whose bounded version lies in `pdSet`: self-adjoint with spectrum in $(0,\infty)$, that is, positive definite |
| [`liebTraceMap`](Quantum/TraceInequality/LiebAndo/TraceMapLM.lean#L21) | `liebTraceMap s K A B` $=\mathrm{Re}\,\mathrm{Tr}[A^sK^\dagger B^{1-s}K]\in\mathbb R$, with Mathlib's real powers `CFC.rpow` ($0$ on arguments that are not positive semidefinite) |
| [`andoTraceMap`](Quantum/TraceInequality/LiebAndo/TraceMapLM.lean#L26) | `andoTraceMap q r K A B` $=\mathrm{Re}\,\mathrm{Tr}[A^qK^\dagger B^{-r}K]\in\mathbb R$, with the same powers |
| **5. Sandwiched Rényi data processing and consequences** | |
| [`CPTP`](Quantum/QuantumMechanics/Channel/Basic.lean#L40) | Structure: a completely positive map `L ℋ₁ → L ℋ₂` (Mathlib's `CompletelyPositiveMap`) with $\mathrm{Tr}\,\Phi(\rho)=\mathrm{Tr}\,\rho$ for all $\rho$; `Φ.toFun` is the map |
| [`sandwichedRenyiDiv`](Quantum/QuantumEntropy/SandwichedRenyi/DefinitionCore.lean#L79) | Real-valued $\frac{1}{\alpha-1}\log\frac{\mathrm{Re}\,Q_\alpha(\rho\Vert\sigma)}{\mathrm{Re}\,\mathrm{Tr}\rho}$ with $Q_\alpha$ = `sandwichedQuasi` (below); Lean's `Real.log` has $\log0=0$, no support condition is imposed, and the value at $\alpha=1$ is $0$ |
| [`sandwichedRenyiDivNN`](Quantum/QuantumEntropy/SandwichedRenyi/NonNeg/Defs.lean#L43) | Extended-real: $+\infty$ if $\alpha>1$ and `SupportLE ρ σ` (below) fails, or if $\alpha<1$, $\rho\ne0$ and $\mathrm{Re}\,Q_\alpha(\rho\Vert\sigma)=0$; otherwise `sandwichedRenyiDiv α ρ σ`. In particular $D_\alpha(0\Vert\sigma)=0$ |
| [`IsDensity`](Quantum/QuantumMechanics/QuantumState.lean#L59) | $X$ is positive semidefinite (`IsPositive`) and $\mathrm{Tr}X=1$ |
| [`IsPositiveDefinite`](Quantum/QuantumMechanics/QuantumState.lean#L51) | $X$ is positive semidefinite and $\det X\ne0$ |
| [`vonNeumannEntropy`](Quantum/QuantumEntropy/VonNeumann/Basic.lean#L115) | $S(\rho)=-\mathrm{Re}\,\mathrm{Tr}[\rho\log\rho]\in\mathbb R$, with Mathlib's `CFC.log` (`cfc Real.log`, so $\log0=0$ on the kernel); defined for every operator |
| [`traceOutLeft`](Quantum/QuantumMechanics/Channel/Basic.lean#L89) | Partial trace over the left factor: the linear map $L(\mathcal H_1\otimes\mathcal H_2)\to L(\mathcal H_2)$ with $X\otimes Y\mapsto\mathrm{Tr}(X)Y$ |
| [`traceOutThird`](Quantum/QuantumEntropy/VonNeumann/PartialTraceThirdCPTP.lean#L96) | From $L(\mathcal H_1\otimes(\mathcal H_2\otimes\mathcal H_3))$ to $L(\mathcal H_1\otimes\mathcal H_2)$: regroup by the associator, then apply `traceOutRight` ($\rho_{ABC}\mapsto\rho_{AB}$) |
| [`umegakiNorm`](Quantum/QuantumEntropy/UmegakiDPI/AlphaOneCore.lean#L30) | Real-valued $\mathrm{Re}\,\mathrm{Tr}[\rho(\log\rho-\log\sigma)]$ divided by $\mathrm{Re}\,\mathrm{Tr}\,\rho$, with `CFC.log`; no support condition is imposed |
| [`tripartiteReference`](ComparatorChallenges/Paper1.lean#L42) | `tripartiteReference X Y` is $X\otimes Y\in L((A\otimes B)\otimes C)$ moved to $L(A\otimes(B\otimes C))$ by the associator |
| [`sandwichedQuasi`](Quantum/QuantumEntropy/SandwichedRenyi/DefinitionCore.lean#L33) | $Q_\alpha(\rho\Vert\sigma)=\mathrm{Tr}[(\sigma^{\gamma}\rho\sigma^{\gamma})^{\alpha}]\in\mathbb C$ with $\gamma=(1-\alpha)/(2\alpha)$ and powers by `CFC.rpow` (for positive semidefinite $\sigma$, a negative power is taken on the support and is $0$ on the kernel) |
| [`SupportLE`](Quantum/QuantumEntropy/Common/Support.lean#L26) | $\ker\sigma\subseteq\ker\rho$ (for self-adjoint $\rho,\sigma$, this is $\mathrm{supp}\rho\subseteq\mathrm{supp}\sigma$) |
| **6. Diagnostic results** | |
| <a id="def-operatorconvex"></a>[`OperatorConvex`](Quantum/TraceInequality/LownerHeinz/Defs.lean#L159) | For all $A,B$ in a fixed ordered C*-algebra, not necessarily self-adjoint, and $t\in[0,1]$, $f((1-t)A+tB)\le(1-t)f(A)+tf(B)$ with `cfc` ($0$ on elements that are not self-adjoint) |
| <a id="def-operatorconcave"></a>[`OperatorConcave`](Quantum/TraceInequality/LownerHeinz/Defs.lean#L218) | `OperatorConvex (-f)` |
| <a id="def-operatorconvexall"></a>[`OperatorConvexAll`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L152) | `OperatorConvex f` in `B K` for every nontrivial complete complex Hilbert space $K$ in universe `u` |
| <a id="def-operatorconcaveall"></a>[`OperatorConcaveAll`](Quantum/TraceInequality/LownerHeinzTheorem.lean#L187) | `OperatorConcave f` in `B K` for every nontrivial complete complex Hilbert space $K$ in universe `u` |

## Poster presentation (AQIS 2026)

Click the thumbnail to view the poster presented at AQIS 2026.

This presentation is preserved as published and includes plans, examples, and
build statistics of our development branch (not public) at that time. For the scope of this
repository, see [What is covered](#what-is-covered).

<p align="center">
  <a href="poster/aqis2026.pdf">
    <img src="poster/aqis2026-thumbnail.png" alt="AQIS 2026 poster: Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information" width="480">
  </a>
</p>

## How to cite

If you use this library, please cite the accompanying
[paper](https://arxiv.org/abs/2607.05492):

```bibtex
@article{kasaura2026leanquantum,
  title         = {Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information},
  author        = {Kasaura, Kazumi and Tsukamoto, Kei and Mori, Kento and
                   Mizuno, Lisa and Namatame, Takahiro and Oriike, Yuta and
                   Taniguchi, Masaya and Sonoda, Sho and Yamasaki, Hayata},
  year          = {2026},
  eprint        = {2607.05492},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  doi           = {10.48550/arXiv.2607.05492}
}
```
