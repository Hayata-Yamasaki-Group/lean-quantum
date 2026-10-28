import Quantum.TraceInequality.Loewner.Koranyi.RatioWeakLimit

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal

noncomputable section

/-!
Step 11 (utility): a subsequence of measures giving convergence of all ratio-kernel integrals.

This packages Step 9 (subsequence weak limit) together with Step 8 (weak convergence implies
convergence against bounded continuous nonnegative test functions) for the specific ratio kernel
`x/(x+λ)`.

The statement is tailored to `x : ℝ≥0` to avoid the `x ≠ ⊤` side condition.
-/

/-- Under a uniform mass bound, a single subsequence of finite measures on `ENNReal` converges
weakly and against the ratio kernel for every `x : ℝ≥0`. -/
theorem exists_subseq_tendsto_ratioKernelBCNN_forall
    (μs : ℕ → FiniteMeasure ENNReal) (C : ℝ≥0) (hC : ∀ n, (μs n).mass ≤ C) :
    ∃ (μ : FiniteMeasure ENNReal) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
        ∀ x : ℝ≥0,
          Tendsto
              (fun n => (μs (φ n)).testAgainstNN
                (ratioKernelBCNN (x : ENNReal) (by simp)))
              atTop
              (𝓝 (μ.testAgainstNN (ratioKernelBCNN (x : ENNReal) (by simp)))) := by
  classical
  rcases
      exists_subseq_tendsto_finiteMeasure_ENNReal_of_mass_le (μs := μs) (C := C) hC with
    ⟨μ, φ, hφ, hμ⟩
  refine ⟨μ, φ, hφ, ?_, ?_⟩
  · simpa [Function.comp] using hμ
  intro x
  have hx : (x : ENNReal) ≠ ⊤ := by simp
  have ht :=
    tendsto_testAgainstNN_ratioKernelBCNN (μs := fun n => μs (φ n)) (μ := μ) hμ (x : ENNReal) hx
  simpa using ht

end

end Quantum.TraceInequality.Loewner
