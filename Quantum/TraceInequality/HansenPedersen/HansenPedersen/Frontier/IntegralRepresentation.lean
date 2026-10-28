/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.HansenPedersen.IntegralRepresentation
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-! # Frontier statement for the two Stieltjes integral representations -/

namespace HansenPedersen

namespace Frontier

open MeasureTheory

/-- Formalization-frontier statement collecting both identities in Hiai--Yanagi
Example 5.1.18.  This is only a statement and currently has no proof term. -/
def StieltjesIntegralRepresentationsStatement : Prop :=
  (∀ {p x : ℝ}, 0 < p → p < 1 → 0 < x →
      x ^ p = Real.sin (p * Real.pi) / Real.pi *
        ∫ t in Set.Ioi (0 : ℝ), x * t ^ (p - 1) / (x + t)) ∧
  (∀ {t : ℝ}, 0 < t →
      Real.log (1 + t) = ∫ x in Set.Ici (1 : ℝ), t / (x * (t + x)))


end Frontier

end HansenPedersen
