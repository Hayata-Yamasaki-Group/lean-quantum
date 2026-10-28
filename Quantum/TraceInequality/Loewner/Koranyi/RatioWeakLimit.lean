import Quantum.TraceInequality.Loewner.Koranyi.RatioKernel
import Quantum.Analysis.Measure.FiniteMeasureWeakCompactness

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Sequences


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped NNReal

noncomputable section

/-!
Step 9 (bridge): extracting weakly convergent subsequences of finite measures on `ENNReal`.

For later ratio-kernel integral representations, we want subsequences of measures on the compact
space `ENNReal` (`[0,∞]`). We implement a standard compactness argument:

* extract a convergent subsequence of the total masses (in `Icc (0,C)`),
* if the mass limit is `0`, conclude weak convergence to `0`,
* otherwise extract a convergent subsequence of the normalized probability measures and
  reassemble a finite-measure limit.
-/

/-- Under a uniform mass bound, every sequence of finite measures on `ENNReal` has a weakly
convergent subsequence. -/
theorem exists_subseq_tendsto_finiteMeasure_ENNReal_of_mass_le
    (μs : ℕ → FiniteMeasure ENNReal) (C : ℝ≥0) (hC : ∀ n, (μs n).mass ≤ C) :
    ∃ (μ : FiniteMeasure ENNReal) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  exact exists_subseq_tendsto_finiteMeasure_of_mass_le μs C hC

end

end Quantum.TraceInequality.Loewner
