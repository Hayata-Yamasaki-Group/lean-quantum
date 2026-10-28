/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.BlockExtensionLimit
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionLimit
import Quantum.TraceInequality.CoreRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Functional-calculus entry point for finite-dimensional block extensions

The proof payload lives in `BlockExtensionLimit`, which keeps the heavy
finite-span limiting argument behind a separate `.olean` boundary while
preserving this historical import path.

## Main results

This module intentionally exports no new declarations.  It re-exports the
block-extension functional-calculus bridge through the historical file name.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Proposition 5.1.5.
-/
