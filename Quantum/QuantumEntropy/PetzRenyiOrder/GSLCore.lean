/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Real.Basic

/-!
# Petz quantum Rényi orders

This file defines the closed real order interval used by Gour's Petz quantum
Rényi divergence.
-/

namespace OPT

/-- Petz quantum Rényi orders in the closed interval from zero to two. -/
abbrev PetzRenyiOrder := {alpha : ℝ // 0 ≤ alpha ∧ alpha ≤ 2}

end OPT
