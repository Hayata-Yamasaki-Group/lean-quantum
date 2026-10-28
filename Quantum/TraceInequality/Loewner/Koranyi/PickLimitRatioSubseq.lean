import Quantum.TraceInequality.Loewner.Koranyi.PickLimit
import Quantum.TraceInequality.Loewner.Koranyi.RatioSubseqFromMeasureBound
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesPickPositivity



namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section

/-!
Step 21' (variant): keep the measure-level convergence on `ENNReal`.

It is useful for later steps that need access to the limiting measure itself.
-/

/-- Common subsequence that also retains convergence of the Cayley push-forward measures. -/
theorem exists_subseq_pick_limit_and_ratioFunctional_subseq_with_tendsto
    (μn : ℕ → Measure ℝ)
    (M0 : ENNReal) (hM0 : M0 < ⊤) (hμle : ∀ n, μn n Set.univ ≤ M0) :
    ∃ (φ : ℕ → ℕ) (F : ℍ → ℂ) (ν : FiniteMeasure ENNReal),
      StrictMono φ ∧
        (∀ m : ℕ,
          TendstoUniformly
            (fun n (z : KmHT m) => stieltjes (μn (φ n)) z.1)
            (fun z => F z.1) atTop) ∧
        (∀ z : ℍ, 0 ≤ (F z).im) ∧
        Tendsto
            (fun n =>
              cayleyPushforward
                (⟨μn (φ n), ⟨lt_of_le_of_lt (hμle (φ n)) hM0⟩⟩ :
                  FiniteMeasure ℝ))
            atTop (𝓝 ν) ∧
        (∀ x : ℝ≥0,
          Tendsto
              (fun n =>
                ratioFunctional
                  (cayleyPushforward
                    (⟨μn (φ n), ⟨lt_of_le_of_lt (hμle (φ n)) hM0⟩⟩ :
                      FiniteMeasure ℝ))
                  x)
              atTop (𝓝 (ratioFunctional ν x))) := by
  classical
  -- Pick property for each `μn n` follows from finiteness (Step 28).
  have hpick : ∀ n : ℕ, ∀ z : ℍ, 0 ≤ (stieltjes (μn n) z).im := by
    intro n z
    have hfin : μn n Set.univ < ⊤ := lt_of_le_of_lt (hμle n) hM0
    haveI : IsFiniteMeasure (μn n) := ⟨hfin⟩
    exact stieltjes_im_nonneg_of_isFiniteMeasure (μ := μn n) z
  -- Step 7: diagonal Pick limit subsequence.
  have hmass' : (∃ M0' : ENNReal, M0' < ⊤ ∧ ∀ n, μn n Set.univ ≤ M0') :=
    ⟨M0, hM0, hμle⟩
  rcases exists_diagonal_pick_limit_function (μn := μn) (hpick := hpick) hmass' with
    ⟨φ0, hφ0, F, hconvF, hFpick⟩
  -- Step 20: measure-level subsequence for the Cayley push-forwards along `φ0`.
  let μn' : ℕ → Measure ℝ := fun n => μn (φ0 n)
  have hμle' : ∀ n, μn' n Set.univ ≤ M0 := by
    intro n
    simpa [μn'] using hμle (φ0 n)
  rcases
      exists_subseq_tendsto_ratioFunctional_cayleyPushforward_forall_of_measure_univ_le
        (μn := μn') (M0 := M0) hM0 hμle' with
    ⟨ν, ψ, hψ, ht, hall⟩
  let φ : ℕ → ℕ := fun n => φ0 (ψ n)
  have hφ : StrictMono φ := hφ0.comp hψ
  refine ⟨φ, F, ν, hφ, ?_, hFpick, ?_, ?_⟩
  · -- Uniform convergence from Step 7 is preserved under precomposition with `ψ`.
    intro m
    have hT : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have :=
      _root_.Quantum.TraceInequality.Loewner.TendstoUniformly.comp_tendsto_atTop
        (h := hconvF m) (hg := hT)
    simpa [φ, Function.comp] using this
  · -- `ht` is already a measure-level convergence statement; unfold `μn'`/`φ`.
    simpa [μn', φ, Function.comp] using ht
  · intro x
    have hx := hall x
    simpa [μn', φ, Function.comp] using hx

end

end Quantum.TraceInequality.Loewner
