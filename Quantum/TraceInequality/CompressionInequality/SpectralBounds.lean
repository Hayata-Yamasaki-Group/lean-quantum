import Quantum.TraceInequality.Core
import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.CompressionInequality.BlockMatrix

/-!
# Spectral bounds for compression inequalities

This file collects the spectral-domain lemmas used in the proof of
Hiai–Yanagi Theorem 5.1.7.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section SpectralBounds

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Order comparison of block diagonal operators implies the corresponding
order comparison of their first diagonal entries. -/
lemma diagMapCLM_fst_le_of_le {a b c d : L K}
    (ha : IsSelfAdjoint a) (hc : IsSelfAdjoint c)
    (h : HansenPedersen.Internal.diagMapCLM a b ≤ HansenPedersen.Internal.diagMapCLM c d) :
    a ≤ c := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact hc.sub ha
  · intro x
    have hx := h.inner_nonneg_left (WithLp.toLp 2 (x, 0))
    simpa [HansenPedersen.Internal.diagMapCLM_sub,
      HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

end SpectralBounds

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
