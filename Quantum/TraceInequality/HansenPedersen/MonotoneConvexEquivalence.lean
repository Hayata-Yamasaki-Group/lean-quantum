/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Basic
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.VI2Instances
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.ConditionVIToII
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Surface
/-!
# Import surface for monotone--convex equivalences

This module preserves the original import surface after splitting
`MonotoneConvexEquivalence` into smaller implementation files. It has no
declarations of its own; downstream files import it to obtain the condition
definitions, instance caches, proof plumbing, and the final surface theorems
for the operator-convexity characterizations.

## Main results

* `operatorConvexity_characterizations_top`: the bundled Theorem 5.1.8
  surface theorem, re-exported from `Surface`.
* `allHOperatorMonotone_iff_concave_of_nonneg`: the Corollary 5.1.9 surface
  theorem, re-exported from `Surface`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Theorem 5.1.8 and Corollary 5.1.9.
-/
