/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.OrthogonalSubmodule
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
Local matrix and two-block ambient Hilbert-space instances.

This module re-exports, under `open scoped HiaiPetz.AmbientInstances`, the
instance witnesses that are repeatedly activated by the two-block ambient
transport files.  The single source of truth for the matrix-level instances is
`HiaiPetz/Core.lean` (the four scoped `instMatrix*` instances); the wrappers
here only re-point to it and to the named definitions in
`HiaiPetz/AmbientSubmodule.lean`.
-/

namespace HiaiPetz.AmbientInstances

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

/-- Ambient-scoped alias for the normed additive group structure on the paired transport space
`twoBlockDiagOrthogonalPairSpace n`. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroupBase {n : ℕ} :
    NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n) :=
  HiaiPetz.instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroup (n := n)

/-- Ambient-scoped alias for the complex normed-space structure on the paired transport space
`twoBlockDiagOrthogonalPairSpace n`. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceNormedSpaceBase {n : ℕ} :
    NormedSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
  HiaiPetz.instTwoBlockDiagOrthogonalPairSpaceNormedSpace (n := n)

/-- Ambient-scoped alias for the complex inner-product-space structure on the paired transport space
`twoBlockDiagOrthogonalPairSpace n`. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceInnerProductSpaceBase {n : ℕ} :
    InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
  HiaiPetz.instTwoBlockDiagOrthogonalPairSpaceInnerProductSpace (n := n)

/-- Ambient-scoped alias for completeness of the paired transport space
`twoBlockDiagOrthogonalPairSpace n`. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceCompleteSpaceBase {n : ℕ} :
    CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
  HiaiPetz.instTwoBlockDiagOrthogonalPairSpaceCompleteSpace (n := n)

/-- Ambient-scoped normed additive group instance on the `L²` matrix pair `WithLp 2 (Mₙ n × Mₙ n)`.
-/
noncomputable scoped instance instWithLpMatrixPairNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := by
  infer_instance

/-- Ambient-scoped complex normed-space instance on the `L²` matrix pair `WithLp 2 (Mₙ n × Mₙ n)`.
-/
noncomputable scoped instance instWithLpMatrixPairNormedSpace' {n : ℕ} :
    NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
  instWithLpMatrixPairNormedSpace (k := n)

/-- Ambient-scoped complex inner-product-space instance on the `L²` matrix pair `WithLp 2 (Mₙ n × Mₙ
n)`. -/
noncomputable scoped instance instWithLpMatrixPairInnerProductSpace' {n : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
  instWithLpMatrixPairInnerProductSpace (k := n)

/-- Ambient-scoped completeness instance on the `L²` matrix pair `WithLp 2 (Mₙ n × Mₙ n)`. -/
noncomputable scoped instance instWithLpMatrixPairCompleteSpace' {n : ℕ} :
    CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) :=
  instWithLpMatrixPairCompleteSpace (k := n)

end MatrixScopedInstances

end HiaiPetz.AmbientInstances
