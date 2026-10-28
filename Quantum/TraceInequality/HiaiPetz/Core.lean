/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HansenPedersen.Core.JOperatorPositivity
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity
import Quantum.TraceInequality.HiaiPetz.Core.Homogeneity
import Quantum.TraceInequality.CoreRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Hiai-Petz core aggregate

This module preserves the original import surface after splitting `Core`.

## Main results

* `Core.Basic`: finite-dimensional Hilbert--Schmidt matrix infrastructure and
  the basic `jOperator`/quasi-entropy definitions.
* `Core.JOperatorPositivity`: positivity facts for the `J`-operator.
* `Core.Homogeneity`: homogeneity identities used by later data-processing
  reductions.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Section 6.1.
-/
