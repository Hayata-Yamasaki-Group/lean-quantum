/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Hilbert-space instances for two-block diagonal transport

This module provides the Hilbert-Schmidt pair space used by the two-block
diagonal CFC transport layer, delegating instance construction to
`Ambient/MatrixInstances.lean`.

## Main results

* `hsBlockSpace`: the `WithLp 2` Hilbert-Schmidt pair space `M_n × M_n`.
* `hsDiagMapCLM`: the block-diagonal continuous linear map induced by two
  Hilbert-Schmidt operators.

## References

* Internal infrastructure for the finite-dimensional Hiai-Petz two-block
  diagonal construction.
-/

namespace HiaiPetz

open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Inner product on the `WithLp 2` product of two matrix Hilbert-Schmidt spaces,
kept under the historical Hilbert-space transport name. -/
noncomputable abbrev instWithLpMatrixPairInnerProductSpaceHilbertSpace {k : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ k × Mₙ k)) :=
  HiaiPetz.instWithLpMatrixPairInnerProductSpace (k := k)

/-- The Hilbert-Schmidt pair space used to encode a two-block diagonal operator
as an operator on `Mₙ n × Mₙ n` with the `L²` product norm. -/
noncomputable def hsBlockSpace (n : ℕ) : Type :=
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  WithLp 2 (Mₙ n × Mₙ n)

noncomputable local instance instHsBlockSpaceNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (hsBlockSpace n) := by
  unfold hsBlockSpace
  exact WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ n) (β := Mₙ n)

noncomputable local instance instHsBlockSpaceNormedSpace {n : ℕ} :
    NormedSpace ℂ (hsBlockSpace n) := by
  unfold hsBlockSpace
  exact WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ n) (β := Mₙ n)

noncomputable local instance instHsBlockSpaceInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ (hsBlockSpace n) := by
  unfold hsBlockSpace
  exact instWithLpMatrixPairInnerProductSpaceHilbertSpace (k := n)

noncomputable local instance instHsBlockSpaceCompleteSpace {n : ℕ} :
    CompleteSpace (hsBlockSpace n) := by
  unfold hsBlockSpace
  exact WithLp.instProdCompleteSpace (p := 2) (α := Mₙ n) (β := Mₙ n)

/-- Diagonal action of two Hilbert-Schmidt operators on the pair space:
the first operator acts on the first component and the second on the second. -/
noncomputable def hsDiagMapCLM {n : ℕ} (a b : HSOp n) :
    hsBlockSpace n →L[ℂ] hsBlockSpace n := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  unfold hsBlockSpace
  change (WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] WithLp 2 (Mₙ n × Mₙ n)
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)).symm :
      Mₙ n × Mₙ n →L[ℂ] WithLp 2 (Mₙ n × Mₙ n)).comp <|
    (a.prodMap b).comp ((WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)) :
      WithLp 2 (Mₙ n × Mₙ n) →L[ℂ] Mₙ n × Mₙ n)

end MatrixScopedInstances

end HiaiPetz
