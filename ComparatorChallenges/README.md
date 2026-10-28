# Comparator checks for Paper 2

In the names of the configurations, H1 and H2 are the two proofs of the Hiai–Petz theorem (via the Hansen–Pedersen theorem and via Löwner's theorem), and A and B the two proof routes of the sandwiched DPI and of the Petz DPI (A: through the Lieb–Ando trace inequalities, B: through the Hiai–Petz theorem). SSA is strong subadditivity, GSL the generalized quantum Stein lemma, H–Y the paper of Hayashi and Yamasaki, DPI a data-processing inequality, and CPTP completely positive and trace preserving.

Paper 2 has 19 theorem targets: the 11 theorems in the tables of the [main theorems of the README](../README.md#main-theorems-formalized-in-this-code) and 8 theorems that give the Hiai–Petz theorem with each of its two proofs and the Umegaki DPI as a limit of the sandwiched DPI and of the Petz DPI.
[Paper2.lean](Paper2.lean) states them with 19 intentional `sorry` placeholders using shared vocabulary imports.
[Paper2Solution.lean](Paper2Solution.lean) delegates each proof to the corresponding public theorem;
it does not import the challenge. The 16 provider/selector/interface definitions are excluded from theorem comparison.

| Configuration | Expected result |
|---|---|
| [Paper2.json](Paper2.json) | Exit 0, acceptance by Lean and nanoda. |
| [Paper2-weak.json](Paper2-weak.json) | Exit 1, theorem-statement mismatch for `ComparatorChallenges.Paper2.gsl_y54`; error interval narrowed from (0,1) to (1/2,1). |
| [Paper2-axiom.json](Paper2-axiom.json) | Exit 1, illegal `sorryAx` in the otherwise identical `gsl_y54` statement. |

With the tool versions and environment setup below, the three configurations are run with the commands at the end of [Verified tool versions and builds](#verified-tool-versions-and-builds). A run agrees with the table above only when both its exit status and the diagnostic in its output match.
The [configuration with the H1 solution](config.json) and the [configuration with the H2 solution](config-loewner.json) of the earlier core challenge of this development ([Challenge.lean](Challenge.lean)) cover its 14 declarations; they are additional configurations, not part of the 19-target Paper 2 control run.
The [configuration of the first paper's challenge](Paper1.json) ([Paper1.lean](Paper1.lean), with the solution [Paper1Solution.lean](Paper1Solution.lean)) covers its 34 declarations; it is likewise an additional configuration, with the same permitted axioms and nanoda enabled. This challenge is the first paper's challenge as adapted in this version: three of its statements, `cp_iff_tensor`, `cp_iff_kraus` and `cp_iff_stinespring`, have fewer instance hypotheses than in the first paper's version, because unused instance arguments were removed. This comparison retains the declaration names used in the source extraction.
The Comparator runs of this version are summarized under [Checking with Comparator](../README.md#checking-with-comparator) in the root README.
The GSL configurations below are retained unchanged; Paper 2 additionally covers `gsl_y55`.

## Generalized quantum Stein's lemma: Comparator scope

The [root README](../README.md#generalized-quantum-steins-lemma--the-proof-follows-hayashiyamasaki) (with the definitions in its [table of definitions](../README.md#definitions-used-in-the-statements)) explains the central theorems, and [formalization.yaml](../formalization.yaml) lists the numbered statements of the sources. This page shows the 26 verification target declarations, including intermediate results of the proof, definitions and foundations. The retained `gsl.json` configuration compares the two central theorems directly.

The Comparator check compares the types of the theorems stated separately in the Challenge with the types, dependencies, permitted axioms and kernel acceptance of the proofs given by the Solution. The Challenge shares the definitions such as the relative entropies with the main formalization, so the independence of this check does not mean an independent reformalization of the definitions. Whether the shared definitions express the intent of the sources is a matter of human review: the descriptions in the tables were compared with the Lean types.

## Comparator configuration and execution

| Component | Role |
|---|---|
| [GslChallenge.lean](GslChallenge.lean) | Directly imports only Definitions and states the types of the two central theorems independently. The two `sorry` are the holes of the problem. |
| [GslSolution.lean](GslSolution.lean) | Positive solution supplying `GourResource.gsl_y54` and `GourResource.gsl_y53`. |
| [GslSolutionWeak.lean](GslSolutionWeak.lean) | Negative solution for the type check, narrowing the ε range of the former to (0,1/2). |
| [GslSolutionAxiom.lean](GslSolutionAxiom.lean) | Negative solution for the permitted-axiom check, replacing the latter by `sorry`. |
| [gsl.json](gsl.json) | Positive configuration. |
| [gsl-weak.json](gsl-weak.json) | Configuration expecting rejection because of a type mismatch. |
| [gsl-axiom.json](gsl-axiom.json) | Configuration expecting rejection because of `sorryAx`. |

The targets of the three configurations are `ComparatorChallenges.Gsl.y54` and `ComparatorChallenges.Gsl.y53`. The permitted axioms are `propext`, `Quot.sound` and `Classical.choice`, with `enable_nanoda=true`. The Challenge and the Solution have declarations with the same names, so they are checked separately.

### Verified tool versions and builds

| Tool | Official source | Verified commit | Build environment |
|---|---|---|---|
| comparator | [leanprover/comparator](https://github.com/leanprover/comparator) | `2312244ac716564a61cc0bf4e107d9abf1757a61` | `lean-toolchain` (Lean `v4.34.0-rc2`) and `lake-manifest.json` in the clone |
| lean4export | [leanprover/lean4export](https://github.com/leanprover/lean4export) | `71f41350675895dda791b8ff9c1dfb77d18b3585` | Lean `v4.29.0-rc6`, the same as the target sources |
| nanoda | [ammkrn/nanoda_lib](https://github.com/ammkrn/nanoda_lib) | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` | Rust / Cargo `1.98.1`, `Cargo.lock` |

The Lean used to build comparator itself is distinguished from the Lean of lean4export that reads the target. The exporter of a different version bundled with comparator is not reused for the target project; the independent lean4export in the table above is specified.

The following is an example of fetching and building, run at the repository root. The first fetch requires a network connection. If the pinned build dependencies are already present, the build can be rerun offline by passing `--no-cache` to Lake and `--offline` to Cargo.

```sh
GSL_TOOLS="$(pwd)/../gsl-tools"
mkdir -p "$GSL_TOOLS"
git clone https://github.com/leanprover/comparator.git "$GSL_TOOLS/comparator"
git -C "$GSL_TOOLS/comparator" checkout --detach 2312244ac716564a61cc0bf4e107d9abf1757a61
(cd "$GSL_TOOLS/comparator" && lake build comparator)
git clone https://github.com/leanprover/lean4export.git "$GSL_TOOLS/lean4export"
git -C "$GSL_TOOLS/lean4export" checkout --detach 71f41350675895dda791b8ff9c1dfb77d18b3585
(cd "$GSL_TOOLS/lean4export" && lake build)
git clone https://github.com/ammkrn/nanoda_lib.git "$GSL_TOOLS/nanoda_lib"
git -C "$GSL_TOOLS/nanoda_lib" checkout --detach 4c544ed4099c8227f07d5de77ad1e69fb0740a27
(cd "$GSL_TOOLS/nanoda_lib" && cargo build --release --locked)
export COMPARATOR_NANODA="$GSL_TOOLS/nanoda_lib/target/release/nanoda_bin"
```

comparator normally requires [Landrun](https://github.com/Zouuup/landrun) of Linux on `PATH`. For the procedure and OS prerequisites for checking unknown solutions in isolation, follow the [official README of the pinned version](https://github.com/leanprover/comparator/blob/2312244ac716564a61cc0bf4e107d9abf1757a61/README.md). The recorded runs were made on Linux (Ubuntu 24.04 on GitHub Actions) with Landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (version 0.1.18, run with `--best-effort`, the form in which Comparator itself calls it) as `COMPARATOR_LANDRUN`, and each of the nine Comparator invocations (five positive and four negative) was also enclosed by `systemd-run`, with Unix-domain sockets blocked and no new privileges allowed. The separate challenge-export/nanoda negative control ran outside these wrappers. Only Mathlib and the statement side were built beforehand; Comparator built the modules used only by the solutions inside the Landrun sandbox. In these runs, on 2026-10-28, all 83 targets of the five positive configurations were accepted by Lean and nanoda, and the five negative controls were rejected for the expected reasons. These runs check the known solutions of this repository; they are not a guarantee of isolation for unknown solutions. The workflow started each Comparator invocation with `lake env` outside the sandbox, so Lake outside the sandbox read again the shared `.lake` that the earlier solution builds could write, and the separate negative control also ran its export outside the sandbox. Without Linux, for example on macOS, known sources can still be checked by specifying `scripts/fake-landrun.sh`, bundled with the same comparator, as `COMPARATOR_LANDRUN`. This script does not isolate anything, is not meant for safely running unknown solutions and was not used for the recorded runs.

```sh
# check of the known solutions of this repository without isolation (for example on macOS)
export COMPARATOR_LANDRUN="$GSL_TOOLS/comparator/scripts/fake-landrun.sh"
lake build ComparatorChallenges.GslChallenge ComparatorChallenges.GslSolution \
  ComparatorChallenges.GslSolutionWeak ComparatorChallenges.GslSolutionAxiom
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/gsl.json
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/gsl-weak.json
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/gsl-axiom.json
```

The three Paper 2 configurations in the table at the top of this page are run in the same way, likewise as a check of the known solutions without isolation:

```sh
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/Paper2.json
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/Paper2-weak.json
./ComparatorChallenges/run-comparator "$GSL_TOOLS/comparator/.lake/build/bin/comparator" \
  "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" ComparatorChallenges/Paper2-axiom.json
```

### Expected exit status and diagnostics

`lake env lean ComparatorChallenges/GslChallenge.lean` exits with 0 but prints "declaration uses `sorry`" twice. This confirms that the types of the problem can be read; it is not an acceptance of proofs. The elaboration of `GslSolution.lean` exits with 0. With Comparator, the following results are confirmed.

| Configuration | Exit status | Diagnostics |
|---|---|---|
| `gsl.json` (Solution) | exit 0 | `Lean default kernel accepts the solution`, `nanoda kernel accepts the solution`, `Your solution is okay!` |
| `gsl-weak.json` | exit 1 | `Challenge and solution theorem statement do not match: 'ComparatorChallenges.Gsl.y54'` |
| `gsl-axiom.json` | exit 1 | `Illegal axiom detected: 'sorryAx'` |

To use the Challenge itself as a negative control for an independent kernel, export the same two declarations and pass them to nanoda. It was confirmed that this export exits with 0, and nanoda returns **exit 1** with `Error: export file declares unpermitted axiom "sorryAx"`.

```sh
lake --no-cache env "$GSL_TOOLS/lean4export/.lake/build/bin/lean4export" \
  ComparatorChallenges.GslChallenge -- ComparatorChallenges.Gsl.y54 ComparatorChallenges.Gsl.y53 \
  > .lake/gsl-challenge.ndjson
cat > .lake/gsl-challenge-nanoda.json <<'JSON'
{
  "export_file_path": ".lake/gsl-challenge.ndjson",
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "unpermitted_axiom_hard_error": true,
  "num_threads": 2,
  "nat_extension": true,
  "string_extension": true
}
JSON
"$COMPARATOR_NANODA" .lake/gsl-challenge-nanoda.json
```

A nonzero exit of a negative configuration is judged to be the expected rejection only when the reason agrees with the one shown in the table. A nonzero exit caused by a missing tool, an export failure or a compatibility error is not a successful verification.

## Complete correspondence table of the 26 verification target declarations

The 2 central theorems, 7 surrounding results, 8 definitions and 9 foundations in [Claims.lean](../Quantum/QuantumEntropy/GourResource/Claims.lean) are listed. They are the starting points of the dependency checks, and it is not claimed that all 26 are independent mathematical theorems. This inventory is not a claims table: it keeps a signature column and links the public declarations; the claims tables with links to Comparator Challenge statements are in the [root README](../README.md#main-theorems-formalized-in-this-code). The signature SHA-256 is information for confirming the type part. Declaration links point to source locations of the version of this README being viewed. In the column "Location in the source", the kind of correspondence (same statement, upper-bound part only, step of a proof, consequence, etc.) is given in parentheses. For definitions and foundations, the column gives the kind of row (Definition or Foundation) instead of a source location.

Common setting: A is a nonzero finite-dimensional complex Hilbert space (in Lean, `Qudit A` and `Nontrivial A`), ρ a density operator on it, Fₙ a set of free states consisting of density operators on n copies, and the base-2 convention is used. $D_{\min}^{\epsilon}(R\Vert S)=-\log_2\beta_\epsilon(R,S)$ is the hypothesis-testing relative entropy and $D^{\mathrm{reg}}(\rho\Vert F)$ the regularized relative entropy, as defined in [Definitions.lean](../Quantum/QuantumEntropy/GourResource/Definitions.lean) (see also the [table of definitions](../README.md#definitions-used-in-the-statements) of the root README). "The four conditions" are the four conditions of Gour §11.3 (`valid` in Lean), counted separately from the density-operator condition. "The three conditions" are the conditions without permutation invariance (`hyValid` in Lean), which require, in addition to the density-operator condition, closedness and convexity, closedness under tensor products for positive numbers of copies, and existence of a positive definite free state in F₁. All rates take values in the extended reals (`EReal` in Lean), and limits and upper and lower limits are interpreted on the extended reals. The rate at zero copies is 0. In the foundation rows, "the standard model" means the finite-dimensional quantum systems given by matrices (the systems of `QuantumModel` in Lean). The definition rows describe the content of the definitions themselves, and state so when the definition itself does not assume density or nonemptiness.

For $n\geq1$, $h_n^\epsilon$ is the infimum over free states of the hypothesis-testing relative entropy divided by n, $b_n^\epsilon$ is the negative logarithm of the optimal type-II error of the composite test divided by n, and $u_n$ is the infimum of the Umegaki relative entropy with respect to free states divided by n. Under the assumptions of the theorem, the minimax equality gives $h_n^\epsilon=b_n^\epsilon$. $m_n^\epsilon$ is the rate obtained by minimizing over free states the max-relative entropy smoothed by density operators within trace distance ε of the state of the null hypothesis, divided by n (in Lean, $u_n$ is written `uRate` and $m_n^\epsilon$ is written `mRate`). All are in bits per copy. The quantity before dividing by the number of copies, $a_n=\inf_{\sigma\in F_n}D(\rho^{\otimes n}\Vert\sigma)$, is subadditive ($a_{n+m}\leq a_n+a_m$) and finite, so by Fekete's lemma $D^{\mathrm{reg}}(\rho\Vert F)=\inf_{n\geq1}u_n$ also equals the limit of $u_n$. Under the assumptions of the main theorem, the regularized value and the limit value of the main theorem are finite nonnegative real numbers.

<!-- gsl-claims-full:start -->

#### Gour's generalized quantum Stein's lemma

| Location in the source | Statement | Lean declaration | Signature SHA-256 |
|---|---|---|---|
| [Gour Theorem 11.4 (same statement)](https://arxiv.org/pdf/2402.05474v2#nameddest=theorem.11.4) | Under the density-operator condition and the four conditions, $\lim_{n\to\infty}h_n^\epsilon=D^{\mathrm{reg}}(\rho\Vert F)$ for every fixed $\epsilon\in(0,1)$, where $h_n^\epsilon=\frac{1}{n}\inf_{\sigma\in F_n}D_{\min}^{\epsilon}(\rho^{\otimes n}\Vert\sigma)$. | [`GourResource.gsl_y54`](../Quantum/QuantumEntropy/GourResource/GeneralizedStein.lean#L141) | `e69ff0388cba353d7ce2b3bd4b1e73aef175d065966815b75f8c2c5cd8afe303` |
| [Discussion immediately after Gour Theorem 11.4 (auxiliary upper bound)](https://arxiv.org/pdf/2402.05474v2#nameddest=theorem.11.4) | Under the three conditions, for every fixed $\epsilon\in(0,1)$, the upper limit of $h_n^\epsilon$ is at most $D^{\mathrm{reg}}(\rho\Vert F)$. This is an auxiliary upper bound via the smoothed max-relative entropy; the upper bound of the main theorem is obtained directly from the strong converse upper bound. | [`GourResource.gsl_c27`](../Quantum/QuantumEntropy/GourResource/GSLUpperRetained.lean#L53) | `6773c0e1c4dfd10b5eff9c1cd0cd0f80b3014cd296df33026163b638690f9adf` |
| [Gour Lemma 11.3 (upper-bound part only, without assuming permutation invariance)](https://arxiv.org/pdf/2402.05474v2#nameddest=lemma.11.3) | Under the three conditions, $\limsup_{n\to\infty}m_n^\epsilon\leq D^{\mathrm{reg}}(\rho\Vert F)$ for every fixed $\epsilon\in(0,1)$, where $m_n^\epsilon$ is the smoothed max-relative entropy rate. Only this upper-bound part of the lemma in the source is formalized, without assuming permutation invariance; it is not the full AEP equality. | [`GourResource.gsl_c26`](../Quantum/QuantumEntropy/GourResource/GeneralizedAEPUpper.lean#L58) | `ba83d85e25afecf22ace7e4b1372b678738ac8575e98bf92462734555e3b9c33` |

#### Hayashi–Yamasaki

| Location in the source | Statement | Lean declaration | Signature SHA-256 |
|---|---|---|---|
| [H–Y Theorem 1 (same statement)](https://arxiv.org/html/2408.02722v3#Thmtheorem1) | Under the three conditions (closedness and convexity, closedness under tensor products, and existence of a positive definite free state), $\lim_{n\to\infty}b_n^\epsilon=D^{\mathrm{reg}}(\rho\Vert F)$ for every fixed $\epsilon\in(0,1)$, where $b_n^\epsilon$ is the composite testing rate. Permutation invariance and closedness under partial traces are not assumed. | [`GourResource.gsl_y53`](../Quantum/QuantumEntropy/GourResource/GeneralizedStein.lean#L53) | `70358188dc55d5b530192caa489847e6360ac2c578c37becb55ebfd083c7a1c8` |
| [H–Y Theorem 4 (same statement, with the tensor power supplied)](https://arxiv.org/html/2408.02722v3#Thmtheorem4) | Under the same assumptions, for every fixed $\epsilon\in(0,1)$ there is a real $r\geq0$ with $D^{\mathrm{reg}}(\rho\Vert F)=r$, $\lim_{n\to\infty}b_n^\epsilon=r$ and $\lim_{n\to\infty}u_n=r$. The value $r$ does not depend on $\epsilon$. | [`GourResource.gsl_y55`](../Quantum/QuantumEntropy/GourResource/GeneralizedStein.lean#L114) | `339edcc1356ab56c5bb030c82d455b24a090b5c2c05db94f423d45cb848b8ba6` |
| [Proof of H–Y Theorem 4 (auxiliary result: from nonnegativity, the upper bound and finiteness of the regularized value)](https://arxiv.org/html/2408.02722v3#Thmtheorem4) / [H–Y Lemma 5 (used in the proof)](https://arxiv.org/html/2408.02722v3#Thmtheorem5) | Under the three conditions, for every fixed $\epsilon\in(0,1)$, the lower limit of $h_n^\epsilon$ is a finite nonnegative real number. | [`GourResource.gsl_c65`](../Quantum/QuantumEntropy/GourResource/GSLUpper.lean#L63) | `ccff0acee634e341ada5d233d94a4e4b87edeb427bfa0700439e64b0ce88c9c3` |
| [Proof of H–Y Theorem 4 (lower bound on the direct side)](https://arxiv.org/html/2408.02722v3#Thmtheorem4) / [H–Y Lemma 7 (consequence of iterating it)](https://arxiv.org/html/2408.02722v3#Thmtheorem7) | Under the three conditions, for every fixed $\epsilon\in(0,1)$, $D^{\mathrm{reg}}(\rho\Vert F)$ is at most the lower limit of $h_n^\epsilon$. | [`GourResource.gsl_y51`](../Quantum/QuantumEntropy/GourResource/DirectBound.lean#L19) | `0533e8fcf072f8f98d8b5cea4daa968e5d28a6d78d1f08d351b6829b14bc9c6a` |
| [Proof of H–Y Theorem 4 (combining the lower and upper bounds, before minimax)](https://arxiv.org/html/2408.02722v3#Thmtheorem4) | Under the three conditions, for every fixed $\epsilon\in(0,1)$, $h_n^\epsilon$ converges to $D^{\mathrm{reg}}(\rho\Vert F)$. | [`GourResource.gsl_y52`](../Quantum/QuantumEntropy/GourResource/GeneralizedStein.lean#L31) | `d8dfae5c4f94ba6f5a5a763e59a64e8619540a5f3c4e32a9a84f3851568fd6d7` |
| [Proof of H–Y Theorem 4 (upper bound on the strong converse side, including ε=0)](https://arxiv.org/html/2408.02722v3#Thmtheorem4) / [H–Y Lemma 6 (consequence of optimizing the fixed-block estimate)](https://arxiv.org/html/2408.02722v3#Thmtheorem6) | Under the three conditions, for every fixed $\epsilon\in[0,1)$, the upper limit of $h_n^\epsilon$ is at most $D^{\mathrm{reg}}(\rho\Vert F)$. The case $\epsilon=0$ is included. | [`GourResource.gsl_y10`](../Quantum/QuantumEntropy/GourResource/BlockConverse.lean#L20) | `5772233cc61b9f156c436aa07f36792ecafcdb926fb49e4df2f9a2444298e28c` |

#### Definitions and foundations

| Location in the source | Statement | Lean declaration | Signature SHA-256 |
|---|---|---|---|
| Definition | The predicate combining the density-operator condition ($F_n$ consists of density operators for every positive number of copies $n$) with the four conditions of Gour (closedness and convexity, closedness under permutations, closedness under tensor products for positive numbers of copies, and existence of a positive definite state in $F_1$). The density-operator condition is counted separately from the four conditions, and no condition is imposed on $F_0$. | [`GourResource.valid`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L99) | `95658542060e953f17b29e356782a9477554d01c7e8fa760d5785a6815ee8cbe` |
| Definition | The predicate adding to the density-operator condition the three conditions of closedness and convexity, closedness under tensor products for positive numbers of copies, and existence of a positive definite state in $F_1$. Permutation invariance and closedness under partial traces are not included. | [`GourResource.hyValid`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L232) | `e4bc80e925aa07688e7bac37d81d91b807cf4123ea6e055140693b41b05fe098` |
| Definition | The rate that is $h_n^\epsilon=\frac{1}{n}\inf_{\sigma\in F_n}D_{\min}^{\epsilon}(\rho^{\otimes n}\Vert\sigma)$ for $n\geq1$ and 0 for $n=0$. The optimal type-II error $\beta$ is defined as a real infimum, and with the negative logarithm of $\beta\leq0$ and the infimum over an empty free-state set taken to be $+\infty$, the value is defined for every real $\epsilon$. | [`GourResource.hRate`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L146) | `bd6806fcae8296988256e4e2bff631b4ce2fffcae1367892d6225f1cc574be59` |
| Definition | Returns the infimum over positive integers $n$ of $u_n=\frac{1}{n}\inf_{\sigma\in F_n}D(\rho^{\otimes n}\Vert\sigma)$. Here $D$ is the base-2 Umegaki relative entropy, which is $+\infty$ for pairs of density operators violating the support inclusion, and the infimum over an empty free-state set is $+\infty$. | [`GourResource.reg`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L159) | `12aca503a94359742d63e095c288a6bde7032aa9bcb3e7be5f5e1f6f7069b966` |
| Definition | For an operator $\rho$, a set of operators $F$ and a real number $\epsilon$, returns the base-2 negative logarithm of the real infimum of $\sup_{\sigma\in F}\mathrm{Re}\,\mathrm{Tr}(\sigma M)$ over $M$ with $0\leq M\leq I$ and $1-\epsilon\leq\mathrm{Re}\,\mathrm{Tr}(\rho M)$, and $+\infty$ if that infimum is at most 0. The definition itself assumes neither density, nonemptiness, closedness and convexity, nor a range of $\epsilon$. | [`GourResource.dSet`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L257) | `9b5de4e038f61a90b2ed48649e685a47478e535c7d8296da5e188e26795e7512` |
| Definition | Returns the $n$-copy tensor power $\rho^{\otimes n}$ of a state $\rho$ as a density operator on the $n$-copy space. | [`GourResource.pow`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L61) | `0e224aab3ea39e62c8f43966f8cd4b27626393c2dec172b5e898c03eb88e935d` |
| Definition | The type assigning to each $n$ a set of operators on the $n$-copy space. Density and closedness and convexity are not required by the type itself. | [`GourResource.Family`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L58) | `6465410a65cad0dd725b8ba45e05175ebbcf90af8c0c2fb892cb1285c5f1d788` |
| Definition | The subtype of density operators (positive semidefinite operators of trace 1). Nonzeroness of the space is not required by the type itself but separately in the central theorem. | [`GourResource.State`](../Quantum/QuantumEntropy/GourResource/Definitions.lean#L52) | `ff680194bb882dd517fc82a7e6bb7227c3758c54ced7b560be5a6a1a63cb009c` |
| Foundation | Moves a finite-dimensional space to the standard-model space of the same dimension by a linear isometric isomorphism, giving a bijection of states and the preservation of density, positivity, trace and support inclusion. It also collects the compactness of the set of density operators and of the set of effect operators. | [`GourResource.gsl_b01`](../Quantum/QuantumEntropy/GourResource/KWCarrierBridge.lean#L105) | `75d432c2cc66357928b1e379e07cf50bcaf3499f22b1c44c10ed888320de444b` |
| Foundation | For pairs of density operators of the standard model, gives the correspondence of $\beta$, the hypothesis-testing relative entropy and effect operators, and their transport by isometric isomorphisms and quantum channels. It includes the existence of optimal tests and of tests accepting with equality for $\epsilon\in[0,1)$, monotonicity in the error, the value $-\log_2(1-\epsilon)$ on self-pairs, and the data-processing inequality for quantum channels. | [`GourResource.gsl_b02`](../Quantum/QuantumEntropy/GourResource/KWTestingBridge.lean#L305) | `edf004cf02e8373efa795ecf71475cbc5ad69d2e7fbc6ae080b4ba3bfd30b224` |
| Foundation | For pairs of density operators of the standard model, gives the correspondence and isometric transport of the Umegaki relative entropy, the sandwiched Rényi relative entropy for $\alpha>1$, and the Petz Rényi relative entropy for $0<\alpha<1$, keeping the case distinctions for infinity. It also gives the upper bound on the testing quantity by the sandwiched Rényi quantity for $\epsilon\in[0,1)$ and $\alpha>1$, and $(1-\epsilon)D_{\min}^{\epsilon}\leq D+h(\epsilon)$ for $\epsilon\in(0,1)$ ($h$ the binary entropy). | [`GourResource.gsl_b03`](../Quantum/QuantumEntropy/GourResource/KWEntropyBridge.lean#L326) | `f61c04e8d5ca394dbd84c86d7aa43ab4563bb69d90aba582fa4a65ea75670db2` |
| Foundation | For pairs of density operators of the standard model, gives the correspondence and isometric transport of the trace distance and the square-root fidelity. It gives contraction under quantum channels, the bound of the trace distance by the square root of 1 minus the square of the square-root fidelity, and the distance formula for pure states given by pairs of unit vectors. | [`GourResource.gsl_b04`](../Quantum/QuantumEntropy/GourResource/KWMetricBridge.lean#L172) | `ad889f9b442cd34c42c18128a8211eab70e720dd0c6cd229b909851558f0d0e4` |
| Foundation | For a linear isometric isomorphism $U$ between a finite-dimensional space and the standard-model space, for each $n$ there is an isomorphism $U_n$ between the $n$-copy space and the $n$-fold tensor product of the standard model, and the same $U_n$ transports the tensor powers of all states corresponding under $U$. | [`GourResource.gsl_b05`](../Quantum/QuantumEntropy/GourResource/KWTensorBridge.lean#L83) | `7b34f6c04dcdc6e0406edda8a0df3db01b533542aeb3201f151c91a5413e292f` |
| Foundation | From the achievability and strong converse rates in the standard model, obtains estimates of the lower and upper limits at a fixed $\epsilon\in(0,1)$. If the states $\rho,\sigma$ satisfy the support inclusion, the rate of the simple test converges to the Umegaki relative entropy. | [`GourResource.gsl_b06`](../Quantum/QuantumEntropy/GourResource/KWSteinBridge.lean#L182) | `e8beae73d4a18662dc5188c97a084f6cf1d78b92ae9688d8d313ca07c61ea93c` |
| Foundation | For positive operators $X,Y$ and $\alpha\in[0,1]$, $(\mathrm{Re}\,\mathrm{Tr}\,X+\mathrm{Re}\,\mathrm{Tr}\,Y-\Vert X-Y\Vert_1)/2\leq\mathrm{Re}\,\mathrm{Tr}(X^{1-\alpha}Y^{\alpha})$ holds. The endpoints $\alpha=0,1$ are included. | [`GourResource.gsl_b07`](../Quantum/QuantumEntropy/GourResource/KWAudenaertBridge.lean#L121) | `cc8eb7a6a8087f4bc709544d2ecd4d528d3e8aa10899cdd928ea9b300f6164b4` |
| Foundation | For a density operator $\rho$ of the standard model, a positive operator $\sigma$ and a probability level $\epsilon$, there exists an optimal test attaining the type-II error $\beta$ of the simple test. | `QuantumModel.NativeHypothesisTesting.`<br>[`exists_betaOptimal`](../Quantum/QuantumModel/KW/Distances/HypothesisTestingCore/Basic.lean#L332) | `b5bafd3187b2c9c7a13dbd4e3f31ce4d7854e256e865572e87985b207c7022ef` |
| Foundation | For a pair $\rho,\sigma$ of density operators of the standard model, the limit of the sandwiched Rényi relative entropy as $\alpha$ tends to 1 from above equals the Umegaki relative entropy. This includes the value $+\infty$ when the support inclusion fails, and positive definiteness is not required. | `QuantumModel.NativeStein.`<br>[`sandwichedRenyiDivBits_tendsto_umegaki`](../Quantum/QuantumModel/KW/Entropies/SteinPrerequisites.lean#L103) | `2210fc61ca6a2bef5b2ed0294d9792e5ffdc5c48409acfb88055967fef625188` |

<!-- gsl-claims-full:end -->
