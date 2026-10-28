import Quantum.TraceInequality.Loewner.Koranyi.PickLimitRatioSubseq
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimination
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimKernel
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Subsequences with support elimination

Steps of the Korányi construction: along a subsequence, the support-eliminated Pick limits
converge together with the Korányi-kernel integrals, and the Stieltjes transforms of the
support-eliminated measures are rewritten as explicit differences.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section



/-- Extract a subsequence with support-eliminated Pick limits and Koranyi-kernel convergence. -/
theorem exists_subseq_tendsto_lintegral_koranyiKernel_supportElim_with_tendsto
    (μn : ℕ → Measure ℝ)
    (M0 : ENNReal) (hM0 : M0 < ⊤) (hμle : ∀ n, μn n Set.univ ≤ M0) :
    ∃ (φ : ℕ → ℕ) (F : ℍ → ℂ) (ν : FiniteMeasure ENNReal),
      StrictMono φ ∧
        (∀ m : ℕ,
          TendstoUniformly (fun n (z : KmHT m) => stieltjes (supportElimMeasure (μn (φ n))) z.1)
            (fun z => F z.1) atTop) ∧
        (∀ z : ℍ, 0 ≤ (F z).im) ∧
        Tendsto
            (fun n =>
              cayleyPushforward
                (⟨supportElimMeasure (μn (φ n)),
                    ⟨lt_of_le_of_lt
                        ((supportElimMeasure_univ_le (μ := μn (φ n))).trans
                          (hμle (φ n)))
                        hM0⟩⟩ :
                  FiniteMeasure ℝ))
            atTop (𝓝 ν) ∧
        ∀ x : ℝ,
          x ∈ Set.Ioo (-1 : ℝ) 1 →
            Tendsto
              (fun n =>
                ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
                  ∂(supportElimMeasure (μn (φ n))))
              atTop
              (𝓝 ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal)) := by
  classical
  -- Apply Step 21' to the transformed measures.
  have hμle' : ∀ n, supportElimMeasure (μn n) Set.univ ≤ M0 := by
    intro n
    exact (supportElimMeasure_univ_le (μ := μn n)).trans (hμle n)
  rcases
      exists_subseq_pick_limit_and_ratioFunctional_subseq_with_tendsto
        (μn := fun n => supportElimMeasure (μn n)) (M0 := M0) hM0 hμle' with
    ⟨φ, F, ν, hφ, hconvF, hFpick, ht, hratio⟩
  refine ⟨φ, F, ν, hφ, ?_, hFpick, ?_, ?_⟩
  · intro m
    -- Just unfold the transformed sequence in `hconvF`.
    simpa using hconvF m
  · -- Unfold the transformed sequence in `ht`.
    simpa using ht
  · intro x hx
    let x0 : ℝ≥0 := Real.toNNReal (cayley x)
    have h0 : Tendsto
        (fun n =>
          ratioFunctional
            (cayleyPushforward
                (⟨supportElimMeasure (μn (φ n)),
                    ⟨lt_of_le_of_lt
                        ((supportElimMeasure_univ_le (μ := μn (φ n))).trans
                          (hμle (φ n)))
                        hM0⟩⟩ :
                  FiniteMeasure ℝ))
            x0)
        atTop (𝓝 (ratioFunctional ν x0)) := hratio x0
    have h0e :
        Tendsto
          (fun n =>
            (ratioFunctional
                (cayleyPushforward
                    (⟨supportElimMeasure (μn (φ n)),
                        ⟨lt_of_le_of_lt
                            ((supportElimMeasure_univ_le (μ := μn (φ n))).trans
                              (hμle (φ n)))
                            hM0⟩⟩ :
                      FiniteMeasure ℝ))
                x0 : ENNReal))
          atTop (𝓝 (ratioFunctional ν x0 : ENNReal)) :=
      ((ENNReal.continuous_coe.tendsto (ratioFunctional ν x0))).comp h0
    have heq :
        (fun n =>
            (ratioFunctional
                (cayleyPushforward
                    (⟨supportElimMeasure (μn (φ n)),
                        ⟨lt_of_le_of_lt
                            ((supportElimMeasure_univ_le (μ := μn (φ n))).trans
                              (hμle (φ n)))
                            hM0⟩⟩ :
                      FiniteMeasure ℝ))
                x0 : ENNReal)) =ᶠ[atTop]
          fun n =>
            ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
              ∂(supportElimMeasure (μn (φ n))) := by
      refine (Eventually.of_forall ?_)
      intro n
      -- Step 31 identifies the ratio-functional with the Korányi-kernel `lintegral`.
      let μfin : FiniteMeasure ℝ := ⟨μn (φ n), ⟨lt_of_le_of_lt (hμle (φ n)) hM0⟩⟩
      have hstep31 :=
        ratioFunctional_cayleyPushforward_supportElimMeasure_eq_lintegral_koranyiKernel
          (μ := μfin) (x := x) hx
      simpa [x0, μfin] using hstep31
    -- Transfer the limit along the eventual equality.
    simpa [x0] using h0e.congr' heq

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section



/-- Along the support-elimination subsequence, rewrite the Stieltjes transforms as explicit
integrals over the outside part `[-1, 1]ᶜ`, recording their uniform convergence on compacts and
Pick positivity of the limit. [simon2019] -/
theorem exists_subseq_supportElim_stieltjesDiff_with_tendsto
    (μn : ℕ → Measure ℝ)
    (M0 : ENNReal) (hM0 : M0 < ⊤) (hμle : ∀ n, μn n Set.univ ≤ M0) :
    ∃ (φ : ℕ → ℕ) (F : ℍ → ℂ) (ν : FiniteMeasure ENNReal),
      StrictMono φ ∧
        (∀ m : ℕ,
          TendstoUniformly
              (fun n (z : KmHT m) =>
                stieltjes (supportElimMeasure (μn (φ n))) z.1)
              (fun z => F z.1) atTop) ∧
        (∀ m : ℕ,
          TendstoUniformly
              (fun n (z : KmHT m) =>
                ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z.1 : ℂ)⁻¹)))
                  ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
              (fun z => F z.1) atTop) ∧
        (∀ z : ℍ, 0 ≤ (F z).im) ∧
        Tendsto
            (fun n =>
              cayleyPushforward
                (⟨supportElimMeasure (μn (φ n)),
                    ⟨lt_of_le_of_lt
                        ((supportElimMeasure_univ_le (μ := μn (φ n))).trans (hμle (φ n))) hM0⟩⟩ :
                  FiniteMeasure ℝ))
            atTop (𝓝 ν) ∧
        ∀ x : ℝ,
          x ∈ Set.Ioo (-1 : ℝ) 1 →
            Tendsto
              (fun n =>
                ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
                  ∂(supportElimMeasure (μn (φ n))))
              atTop
              (𝓝 ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal)) := by
  classical
  rcases
      exists_subseq_tendsto_lintegral_koranyiKernel_supportElim_with_tendsto (μn := μn)
        (M0 := M0) hM0 hμle with
    ⟨φ, F, ν, hφ, hconvF, hFpick, ht, hKoranyi⟩
  refine ⟨φ, F, ν, hφ, hconvF, ?_, hFpick, ht, hKoranyi⟩
  intro m
  -- Rewrite the sequence pointwise (for all `n` and `z`) using Step 51, then transfer uniform
  -- convergence along the resulting eventual equality.
  have hEq :
      (fun n => fun z : KmHT m =>
          stieltjes (supportElimMeasure (μn (φ n))) z.1) =ᶠ[atTop]
        fun n => fun z : KmHT m =>
          ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z.1 : ℂ)⁻¹)))
            ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
    refine Eventually.of_forall (fun n => ?_)
    funext z
    simpa using
      (stieltjes_supportElimMeasure_eq_integral_diff (μ := μn (φ n)) (z := z.1))
  have hiff :=
    (tendstoUniformly_congr
      (F := fun n (z : KmHT m) => stieltjes (supportElimMeasure (μn (φ n))) z.1)
      (F' := fun n (z : KmHT m) =>
        ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z.1 : ℂ)⁻¹)))
          ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
      (f := fun z : KmHT m => F z.1) (p := atTop) hEq)
  exact hiff.1 (hconvF m)

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section



/-- Along a support-elimination subsequence, the Stieltjes transforms of the support-eliminated
measures converge uniformly on the compact sets `KmHT m` and pointwise to a limit `F`, together with
the explicit outside-integral representation. [simon2019] -/
theorem exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
    (μn : ℕ → Measure ℝ)
    (M0 : ENNReal) (hM0 : M0 < ⊤) (hμle : ∀ n, μn n Set.univ ≤ M0) :
    ∃ (φ : ℕ → ℕ) (F : ℍ → ℂ) (ν : FiniteMeasure ENNReal),
      StrictMono φ ∧
        (∀ m : ℕ,
          TendstoUniformly
              (fun n (z : KmHT m) =>
                stieltjes (supportElimMeasure (μn (φ n))) z.1)
              (fun z => F z.1) atTop) ∧
        (∀ m : ℕ,
          TendstoUniformly
              (fun n (z : KmHT m) =>
                ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z.1 : ℂ)⁻¹)))
                  ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
              (fun z => F z.1) atTop) ∧
        (∀ z : ℍ,
          Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) z) atTop (𝓝 (F z))) ∧
        (∀ z : ℍ,
          Tendsto
              (fun n =>
                ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z : ℂ)⁻¹)))
                  ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
              atTop (𝓝 (F z))) ∧
        (∀ z : ℍ, 0 ≤ (F z).im) ∧
        Tendsto
            (fun n =>
              cayleyPushforward
                (⟨supportElimMeasure (μn (φ n)),
                    ⟨lt_of_le_of_lt
                        ((supportElimMeasure_univ_le (μ := μn (φ n))).trans (hμle (φ n))) hM0⟩⟩ :
                  FiniteMeasure ℝ))
            atTop (𝓝 ν) ∧
        ∀ x : ℝ,
          x ∈ Set.Ioo (-1 : ℝ) 1 →
            Tendsto
              (fun n =>
                ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
                  ∂(supportElimMeasure (μn (φ n))))
              atTop
              (𝓝 ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal)) := by
  classical
  rcases
      exists_subseq_supportElim_stieltjesDiff_with_tendsto (μn := μn) (M0 := M0) hM0 hμle with
    ⟨φ, F, ν, hφ, hconvSt, hconvDiff, hFpick, ht, hKoranyi⟩
  refine ⟨φ, F, ν, hφ, hconvSt, hconvDiff, ?_, ?_, hFpick, ht, hKoranyi⟩
  · intro z
    rcases mem_some_KmH z with ⟨m, hz⟩
    let z' : KmHT m := ⟨z, hz⟩
    have :
        Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) z'.1) atTop (𝓝 (F z'.1)) :=
      (hconvSt m).tendsto_at z'
    simpa [z'] using this
  · intro z
    rcases mem_some_KmH z with ⟨m, hz⟩
    let z' : KmHT m := ⟨z, hz⟩
    have :
        Tendsto
            (fun n =>
              ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z'.1 : ℂ)⁻¹)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
            atTop (𝓝 (F z'.1)) :=
      (hconvDiff m).tendsto_at z'
    simpa [z'] using this

end

end Quantum.TraceInequality.Loewner
