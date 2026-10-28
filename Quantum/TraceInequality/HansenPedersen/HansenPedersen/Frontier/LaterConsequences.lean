/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Quantum.TraceInequality.LaterConsequencesRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Frontier statements for later Hansen--Pedersen consequences

This module contains statement-only propositions that are intentionally absent
from the completed Hansen--Pedersen chapter aggregate.
-/

namespace HansenPedersen

namespace Frontier

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Formalization-frontier statement collecting all seven parts of Hiai--Yanagi
Example 5.1.12.  This is only a statement and currently has no proof term. -/
def OperatorMonotoneConvexExamplesStatement : Prop :=
  (∀ {α β : ℝ}, 0 ≤ α →
      OperatorMonotoneOnInterval (ℋ := ℋ) Set.univ (fun t : ℝ ↦ α * t + β)) ∧
  (∀ {α β c : ℝ}, c ∉ Set.Ioo α β →
      OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioo α β) (fun t : ℝ ↦ 1 / (c - t))) ∧
  (∀ {p : ℝ}, p ∈ Set.Icc (0 : ℝ) 1 →
      OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t ^ p) ∧
      OperatorConcaveOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t ^ p)) ∧
  (∀ {p : ℝ}, p ∈ Set.Icc (1 : ℝ) 2 →
      OperatorConvexOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t ^ p)) ∧
  OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ))
    (fun t : ℝ ↦ if t = 0 then 0 else if t = 1 then 1 else (t - 1) / Real.log t) ∧
  (OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log ∧
    OperatorConcaveOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log) ∧
  OperatorConvexOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t * Real.log t)

/-- Formalization-frontier statement of Hiai--Yanagi Theorem 5.1.19 (Furuta
inequality), written with `opRpow`.  This is only a statement and currently has no proof term. -/
def FurutaInequalityStatement : Prop :=
  ∀ {p r q : ℝ}, 0 ≤ p → 0 ≤ r → 1 ≤ q →
    p + 2 * r ≤ (1 + 2 * r) * q →
    ∀ {A B : L ℋ}, 0 ≤ A → A ≤ B →
      opRpow (ℋ := ℋ) ((p + 2 * r) / q) A ≤
        opRpow (ℋ := ℋ) (1 / q)
          (opRpow (ℋ := ℋ) r A * opRpow (ℋ := ℋ) p B * opRpow (ℋ := ℋ) r A) ∧
      opRpow (ℋ := ℋ) (1 / q)
          (opRpow (ℋ := ℋ) r B * opRpow (ℋ := ℋ) p A * opRpow (ℋ := ℋ) r B) ≤
        opRpow (ℋ := ℋ) ((p + 2 * r) / q) B


end Frontier

end HansenPedersen
