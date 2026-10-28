import Quantum.TraceInequality.Loewner.Koranyi.CayleyPushforward
import Quantum.TraceInequality.Loewner.Koranyi.RatioFunctionalSubseq

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal

noncomputable section

/-!
Step 19 (bridge): subsequential convergence after pushing forward by the Cayley map.

Given a sequence of finite measures on `ℝ` with a uniform mass bound, we push them forward to
finite measures on the compact space `ENNReal` via `t ↦ ENNReal.ofReal (cayley t)` and apply the
weak compactness package from Step 14 to obtain a subsequence along which all `ratioFunctional`
values converge.

This is a packaging lemma; matching these limits with the diagonal Pick limit from Step 7 is
handled in later steps.
-/

/--
A uniformly mass-bounded sequence has a Cayley-push-forward subsequence whose
ratio functionals converge pointwise.
-/
theorem exists_subseq_tendsto_ratioFunctional_cayleyPushforward_forall
    (μs : ℕ → FiniteMeasure ℝ) (C : ℝ≥0) (hC : ∀ n, (μs n).mass ≤ C) :
    ∃ (ν : FiniteMeasure ENNReal) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto ((fun n => cayleyPushforward (μs n)) ∘ φ) atTop (𝓝 ν) ∧
        ∀ x : ℝ≥0,
          Tendsto (fun n => ratioFunctional (cayleyPushforward (μs (φ n))) x) atTop
            (𝓝 (ratioFunctional ν x)) := by
  classical
  -- Apply Step 14 to the pushed-forward measures on `ENNReal`.
  let νs : ℕ → FiniteMeasure ENNReal := fun n => cayleyPushforward (μs n)
  have hνsC : ∀ n, (νs n).mass ≤ C := by
    intro n
    simpa [νs, cayleyPushforward_mass] using hC n
  rcases exists_subseq_tendsto_ratioFunctional_forall (μs := νs) (C := C) hνsC with
    ⟨ν, φ, hφ, ht, hall⟩
  refine ⟨ν, φ, hφ, ?_, ?_⟩
  · simpa [νs, Function.comp] using ht
  · intro x
    simpa [νs] using hall x


end

end Quantum.TraceInequality.Loewner
