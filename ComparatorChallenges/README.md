# Comparator challenges

Follow the [Comparator setup guide](https://github.com/leanprover/comparator/blob/a4f696825c583ed8a5b4060d9a0faa5b882d365b/README.md).
This repository pins Comparator `a4f696825c583ed8a5b4060d9a0faa5b882d365b` in
[`lake-manifest.json`](../lake-manifest.json); the lean4export
`048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d` pinned there is only a library dependency
of Comparator and is not used to export the target. Install
[landrun](https://github.com/Zouuup/landrun) on Linux with Landlock (running
Comparator isolated requires Linux). Build the lean4export that exports the target at
`71f41350675895dda791b8ff9c1dfb77d18b3585` (Lean `v4.29.0-rc6`, the same as the target
sources) with `lake build`, and add its `.lake/build/bin` to `PATH`.
Comparator calls landrun with `--best-effort`, so on a kernel without Landlock it runs
without isolation. To check with isolation, run it on Linux with Landlock enabled, as an
unprivileged user, and do not build the solution beforehand without isolation.
Build [nanoda](https://github.com/ammkrn/nanoda_lib) with `cargo build --release`
and add `target/release` to `PATH` to expose `nanoda_bin`.
Use the Lean version in [`lean-toolchain`](../lean-toolchain).
The nanoda revision is not pinned here; record it for each new run.
Then, from the repository root:

```sh
lake exe cache get
lake exe comparator ComparatorChallenges/Paper1.json
```

The configuration checks the 34 declarations in `Paper1.lean` against
`Paper1Solution.lean`, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and enables the nanoda kernel in addition to Lean's kernel.
The challenge contains statement placeholders and is built separately from the
default targets.
