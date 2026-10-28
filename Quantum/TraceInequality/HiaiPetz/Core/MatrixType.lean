/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-!
# Canonical finite matrix type for Hiai--Petz

This small predecessor module owns the matrix type shared by the Hiai--Petz
core and the older Hansen--Pedersen-facing matrix API.  Keeping the type here
lets `Quantum.TraceInequality.Basic` reuse it without introducing the import
cycle that would result from importing the full Hiai--Petz core.
-/

namespace HiaiPetz

/-- Finite complex `n × n` matrices, used as the ambient matrix algebra for
the Hiai--Petz finite-dimensional formalization. -/
abbrev Mₙ (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

end HiaiPetz
