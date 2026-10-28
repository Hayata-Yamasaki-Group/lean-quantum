import Quantum.TraceInequality.Loewner.Koranyi.CayleyPushforwardSubseq

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal

noncomputable section

/-!
Step 20 (bridge): from the mass-bound hypothesis used in Step 6/7 (`Measure ℝ`) to the
ratio-kernel subsequence package on `ENNReal` (`FiniteMeasure ENNReal`).

This converts a sequence of measures `μn : ℕ → Measure ℝ` with a uniform bound on
`μn n univ` into a sequence of finite measures `μnFM : ℕ → FiniteMeasure ℝ`, then applies
Step 19.
-/

/-- Convert a uniformly mass-bounded sequence of real measures into a Cayley-pushforward
subsequence on `ENNReal` along which `ratioFunctional` converges for every `x : ℝ≥0`. -/
theorem exists_subseq_tendsto_ratioFunctional_cayleyPushforward_forall_of_measure_univ_le
    (μn : ℕ → Measure ℝ) (M0 : ENNReal) (hM0 : M0 < ⊤)
    (hμle : ∀ n, μn n Set.univ ≤ M0) :
    ∃ (ν : FiniteMeasure ENNReal) (φ : ℕ → ℕ),
      StrictMono φ ∧
        Tendsto
          ((fun n =>
              cayleyPushforward
                (⟨μn n, ⟨lt_of_le_of_lt (hμle n) hM0⟩⟩ : FiniteMeasure ℝ)) ∘
            φ)
          atTop (𝓝 ν) ∧
          ∀ x : ℝ≥0,
            Tendsto
                (fun n =>
                  ratioFunctional
                    (cayleyPushforward
                      (⟨μn (φ n),
                          ⟨lt_of_le_of_lt (hμle (φ n)) hM0⟩⟩ : FiniteMeasure ℝ))
                    x)
                atTop (𝓝 (ratioFunctional ν x)) := by
  classical
  -- Build a sequence of finite measures from the bound `μn n univ ≤ M0 < ∞`.
  have hfin : ∀ n, IsFiniteMeasure (μn n) := by
    intro n
    refine ⟨lt_of_le_of_lt (hμle n) hM0⟩
  let μnFM : ℕ → FiniteMeasure ℝ := fun n => ⟨μn n, hfin n⟩
  -- A uniform bound for `FiniteMeasure.mass`.
  have hC : ∀ n, (μnFM n).mass ≤ M0.toNNReal := by
    intro n
    -- Compare after coercion to `ENNReal`, then apply `toNNReal_mono`.
    have hleENN : ((μnFM n).mass : ENNReal) ≤ M0 := by
      simpa [μnFM, MeasureTheory.FiniteMeasure.ennreal_mass] using hμle n
    have hto :
        (((μnFM n).mass : ENNReal).toNNReal) ≤ M0.toNNReal :=
      ENNReal.toNNReal_mono (by simpa using hM0.ne) hleENN
    -- `toNNReal` of a coerced `ℝ≥0` is the identity.
    simpa using hto
  -- Apply Step 19 to obtain a subsequence with convergence of all ratio functionals.
  rcases exists_subseq_tendsto_ratioFunctional_cayleyPushforward_forall (μs := μnFM)
      (C := M0.toNNReal) hC with
    ⟨ν, φ, hφ, ht, hall⟩
  refine ⟨ν, φ, hφ, ?_, ?_⟩
  · simpa [μnFM, Function.comp] using ht
  · intro x
    simpa [μnFM] using hall x


end

end Quantum.TraceInequality.Loewner
