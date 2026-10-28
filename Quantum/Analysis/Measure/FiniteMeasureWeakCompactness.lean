import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Sequences

/-!
# Weak compactness for uniformly bounded finite measures

This module factors the common mass/normalization argument for extracting a
weakly convergent subsequence of finite measures.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology NNReal

noncomputable section

/-- Finite measures with uniformly bounded mass have a convergent subsequence whenever the
corresponding space of probability measures is compact. -/
theorem exists_subseq_tendsto_finiteMeasure_of_mass_le
    {α : Type*} [Nonempty α] [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [CompactSpace (ProbabilityMeasure α)]
    [FirstCountableTopology (ProbabilityMeasure α)]
    (μs : ℕ → FiniteMeasure α) (C : ℝ≥0) (hC : ∀ n, (μs n).mass ≤ C) :
    ∃ (μ : FiniteMeasure α) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  classical
  have hm_in_real : ∀ n, ((μs n).mass : ℝ) ∈ Set.Icc (0 : ℝ) C := by
    intro n
    exact ⟨NNReal.coe_nonneg _, hC n⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (C : ℝ))).tendsto_subseq hm_in_real with
    ⟨mR, hmR, φ₁, hφ₁, hmass₁R⟩
  let m : ℝ≥0 := ⟨mR, hmR.1⟩
  let μ₁ : ℕ → FiniteMeasure α := fun n => μs (φ₁ n)
  have hmass₁' : Tendsto (fun n => (μ₁ n).mass) atTop (𝓝 m) := by
    rw [← NNReal.tendsto_coe]
    simpa [μ₁, Function.comp, m] using hmass₁R
  by_cases hm0 : m = 0
  · refine ⟨0, φ₁, hφ₁, ?_⟩
    have hmass_zero : Tendsto (fun n => (μ₁ n).mass) atTop (𝓝 (0 : ℝ≥0)) := by
      simpa [hm0] using hmass₁'
    simpa [μ₁, Function.comp] using
      (MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
        (μs := μ₁) hmass_zero)
  · rcases (CompactSpace.tendsto_subseq (fun n => (μ₁ n).normalize)) with
      ⟨ν, φ₂, hφ₂, hnorm₂⟩
    let φ : ℕ → ℕ := fun n => φ₁ (φ₂ n)
    have hφ : StrictMono φ := hφ₁.comp hφ₂
    let μ₂ : ℕ → FiniteMeasure α := fun n => μs (φ n)
    have hmass₂ : Tendsto (fun n => (μ₂ n).mass) atTop (𝓝 m) := by
      have hφ₂_atTop : Tendsto φ₂ atTop atTop := hφ₂.tendsto_atTop
      simpa [μ₂, μ₁, φ] using hmass₁'.comp hφ₂_atTop
    have hnorm₂' : Tendsto (fun n => (μ₂ n).normalize) atTop (𝓝 ν) := by
      simpa [μ₂, μ₁, φ, Function.comp] using hnorm₂
    let μ : FiniteMeasure α := m • ν.toFiniteMeasure
    have hμ_mass : μ.mass = m := by
      rw [MeasureTheory.FiniteMeasure.mass]
      change (m • ν.toFiniteMeasure) univ = m
      rw [MeasureTheory.FiniteMeasure.smul_apply]
      have hνuniv : ν.toFiniteMeasure univ = 1 := by
        have h : ν.toFiniteMeasure.mass = 1 := ProbabilityMeasure.mass_toFiniteMeasure ν
        unfold MeasureTheory.FiniteMeasure.mass at h
        exact h
      simp [hνuniv, smul_eq_mul]
    have hμ_ne0 : μ ≠ 0 := by
      have : μ.mass ≠ 0 := by simpa [hμ_mass] using hm0
      exact (MeasureTheory.FiniteMeasure.mass_nonzero_iff μ).1 this
    have hμ_norm : μ.normalize = ν := by
      have h_toFinite : μ.normalize.toFiniteMeasure = ν.toFiniteMeasure := by
        have hn : μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ :=
          MeasureTheory.FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
            (μ := μ) hμ_ne0
        calc
          μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ := hn
          _ = m⁻¹ • (m • ν.toFiniteMeasure) := by
                simp [μ, hμ_mass]
          _ = (m⁻¹ * m) • ν.toFiniteMeasure := by
                simp [smul_smul]
          _ = (1 : ℝ≥0) • ν.toFiniteMeasure := by
                simp [inv_mul_cancel₀ hm0]
          _ = ν.toFiniteMeasure := by simp
      exact (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding α).injective h_toFinite
    have hnorm₂'' : Tendsto (fun n => (μ₂ n).normalize) atTop (𝓝 μ.normalize) := by
      simpa [hμ_norm] using hnorm₂'
    have hmass₂' : Tendsto (fun n => (μ₂ n).mass) atTop (𝓝 μ.mass) := by
      simpa [hμ_mass] using hmass₂
    have ht : Tendsto μ₂ atTop (𝓝 μ) :=
      MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
        (μ := μ) (μs := μ₂) hnorm₂'' hmass₂'
    refine ⟨μ, φ, hφ, ?_⟩
    simpa [μ₂, φ, Function.comp] using ht

end

end Quantum.TraceInequality.Loewner
