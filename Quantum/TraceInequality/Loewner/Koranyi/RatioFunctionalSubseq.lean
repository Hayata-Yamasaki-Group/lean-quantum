import Quantum.TraceInequality.Loewner.Koranyi.RatioFunctional

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal

noncomputable section

/-!
Step 14 (bridge): subsequential convergence of `ratioFunctional` for all `x : ℝ≥0`.
-/

/-- Under a uniform mass bound, a subsequence of finite measures on `ENNReal` can be chosen so that
`ratioFunctional` converges at every `x : ℝ≥0`. -/
theorem exists_subseq_tendsto_ratioFunctional_forall
    (μs : ℕ → FiniteMeasure ENNReal) (C : ℝ≥0) (hC : ∀ n, (μs n).mass ≤ C) :
    ∃ (μ : FiniteMeasure ENNReal) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
        ∀ x : ℝ≥0,
          Tendsto (fun n => ratioFunctional (μs (φ n)) x) atTop (𝓝 (ratioFunctional μ x)) := by
  classical
  rcases
      exists_subseq_tendsto_ratioKernelBCNN_forall (μs := μs) (C := C) hC with
    ⟨μ, φ, hφ, ht, hall⟩
  refine ⟨μ, φ, hφ, ht, ?_⟩
  intro x
  simpa [ratioFunctional] using hall x

end

end Quantum.TraceInequality.Loewner

