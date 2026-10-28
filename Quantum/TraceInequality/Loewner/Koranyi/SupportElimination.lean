import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped NNReal

/-!
Step 26 (utility): eliminate a support assumption by an explicit measure transform.

This file defines a measure transform that takes the part of a measure supported outside `[-1,1]`
and maps it into `(-1,1)` using the inversion map `y ↦ 1 / y`, with a `1 / y^2` density.

The key property is that the resulting measure is automatically supported on `(-1,1)`, so it can
be fed to later steps that require an `ae` hypothesis on `(-1,1)`.
-/

/-- The inversion map used in the support-elimination transform. -/
def supportElimInv (y : ℝ) : ℝ :=
  y⁻¹

/-- The `1 / y^2` weight used in the support-elimination transform (as an `ℝ≥0∞` density). -/
def supportElimWeight (y : ℝ) : ENNReal :=
  ENNReal.ofReal ((y ^ (2 : ℕ))⁻¹)

/-- The support-elimination transform of a measure on `ℝ`. -/
def supportElimMeasure (μ : Measure ℝ) : Measure ℝ :=
  ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight).map supportElimInv

/-- The inversion map `y ↦ y⁻¹` is measurable. -/
lemma measurable_supportElimInv : Measurable supportElimInv := by
  simpa [supportElimInv] using (measurable_id.inv : Measurable fun y : ℝ => y⁻¹)

/-- The `1/y²` density is measurable. -/
lemma measurable_supportElimWeight : Measurable supportElimWeight := by
  have hpow : Measurable fun y : ℝ => y ^ (2 : ℕ) := by
    simpa using (measurable_id.pow_const (2 : ℕ))
  have hinv : Measurable fun y : ℝ => (y ^ (2 : ℕ))⁻¹ :=
    hpow.inv
  simpa [supportElimWeight] using (ENNReal.measurable_ofReal.comp hinv)

/-- The inversion map sends `[-1, 1]ᶜ` into `(-1, 1)`. -/
lemma supportElimInv_mem_Ioo_of_mem_Icc_compl {y : ℝ} (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    supportElimInv y ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hy_abs : 1 < |y| := by
    -- If `|y| ≤ 1`, then `y ∈ [-1,1]`, contradicting `hy`.
    have : ¬ |y| ≤ (1 : ℝ) := by
      intro hle
      have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := by
        have habs : (- (1 : ℝ)) ≤ y ∧ y ≤ 1 := by
          simpa [abs_le] using hle
        exact habs
      exact hy hyIcc
    exact lt_of_not_ge this
  have hinv_abs : |supportElimInv y| < 1 := by
    -- `|1/y| = |y|⁻¹` and `|y| > 1`.
    have : (|y|)⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ hy_abs
    simpa [supportElimInv, abs_div, abs_one, one_div, div_eq_mul_inv, abs_inv] using this
  have hlt : - (1 : ℝ) < supportElimInv y ∧ supportElimInv y < 1 := by
    simpa [abs_lt] using hinv_abs
  exact hlt

/-- The support-elimination transform of `μ` is supported on `(-1, 1)`: its mass on `(-1, 1)ᶜ` is
zero. -/
lemma supportElimMeasure_compl_Ioo (μ : Measure ℝ) :
    supportElimMeasure μ (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Ioo (-1 : ℝ) 1)ᶜ) :=
    (isOpen_Ioo.measurableSet).compl
  -- Reduce to showing the preimage is `μ.restrict`-null, then use absolute continuity.
  have hpre :
      supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    by_contra hyIcc
    have : supportElimInv y ∈ Set.Ioo (-1 : ℝ) 1 := by
      exact supportElimInv_mem_Ioo_of_mem_Icc_compl (y := y)
        (by simpa [Set.mem_compl_iff] using hyIcc)
    exact hy this
  have hμ0 :
      (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)
        (supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ) = 0 := by
    have hmeas : MeasurableSet (supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ) :=
      hS.preimage measurable_supportElimInv
    -- The set is disjoint from the restricting set `(Icc)ᶜ` since it lies in `Icc`.
    have hinter :
        (supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ) ∩ (Set.Icc (-1 : ℝ) 1)ᶜ = ∅ := by
      ext y
      constructor
      · intro hy'
        exact hy'.2 (hpre hy'.1)
      · intro hy'
        simp at hy'
    have hinter' :
        ((supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1))ᶜ) ∩
          (Set.Icc (-1 : ℝ) 1)ᶜ = ∅ := by
      simpa [Set.preimage_compl] using hinter
    -- Evaluate the restricted measure.
    calc
      (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ)
          = μ
              ((supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ) ∩
                (Set.Icc (-1 : ℝ) 1)ᶜ) := by
              simp
      _ = μ ∅ := by
            simp [hinter']
      _ = 0 := by simp
  have hac :
      (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight ≪
        (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hwd0 :
      ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)
          (supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1)ᶜ) = 0 :=
    hac hμ0
  have hwd0' :
      ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)
          ((supportElimInv ⁻¹' (Set.Ioo (-1 : ℝ) 1))ᶜ) = 0 := by
    simpa [Set.preimage_compl] using hwd0
  -- Apply the map formula.
  simp [supportElimMeasure, Measure.map_apply, measurable_supportElimInv, hS, hwd0',
    Set.preimage_compl]

/-- On `[-1, 1]ᶜ`, the `1/y²` density is at most `1`. -/
lemma supportElimWeight_le_one_of_mem_Icc_compl {y : ℝ} (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    supportElimWeight y ≤ 1 := by
  have hy_abs : 1 < |y| := by
    -- If `|y| ≤ 1`, then `y ∈ [-1,1]`, contradicting `hy`.
    have : ¬ |y| ≤ (1 : ℝ) := by
      intro hle
      have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := by
        have habs : (- (1 : ℝ)) ≤ y ∧ y ≤ 1 := by
          simpa [abs_le] using hle
        exact habs
      exact hy hyIcc
    exact lt_of_not_ge this
  have hy_abs_le : (1 : ℝ) ≤ |y| := le_of_lt hy_abs
  have hpow : (1 : ℝ) ≤ |y| ^ (2 : ℕ) := by
    -- Use monotonicity of `x ↦ x^2` on `ℝ≥0`.
    simpa using (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by positivity) hy_abs_le (2 : ℕ))
  have hy_sq : (1 : ℝ) ≤ y ^ (2 : ℕ) := by
    -- `|y|^2 = y^2`.
    simpa [sq_abs] using hpow
  have hinv : (y ^ (2 : ℕ))⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hy_sq
  -- `ofReal` is monotone.
  simpa [supportElimWeight] using (ENNReal.ofReal_le_ofReal hinv)

/-- The support-elimination transform does not increase total mass. -/
lemma supportElimMeasure_univ_le (μ : Measure ℝ) :
    supportElimMeasure μ Set.univ ≤ μ Set.univ := by
  have hs : MeasurableSet ((Set.Icc (-1 : ℝ) 1)ᶜ) :=
    (isClosed_Icc.measurableSet).compl
  have hmap :
      supportElimMeasure μ Set.univ =
        ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) Set.univ := by
    simp [supportElimMeasure, Measure.map_apply, measurable_supportElimInv]
  -- Bound the `withDensity` mass by comparing the density to `1`.
  have hle_ae :
      (∀ᵐ y ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ), supportElimWeight y ≤ 1) := by
    filter_upwards [ae_restrict_mem hs] with y hy
    exact supportElimWeight_le_one_of_mem_Icc_compl (y := y) (by simpa using hy)
  have hwith :
      ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) Set.univ ≤
        (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ := by
    -- Use `withDensity_apply` and compare the densities pointwise a.e.
    classical
    have hw :
        ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) Set.univ =
          ∫⁻ y, supportElimWeight y ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
      simp [MeasureTheory.withDensity_apply]
    have hone :
        (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ =
          ∫⁻ _y, (1 : ENNReal) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
      simp
    -- Compare the two `lintegral`s.
    have hlin :
        (∫⁻ y, supportElimWeight y ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) ≤
          ∫⁻ _y, (1 : ENNReal) ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
      exact lintegral_mono_ae hle_ae
    -- Put things together by rewriting both sides.
    -- (Avoid `simp` here to keep the rewrite predictable.)
    rw [hw, hone]
    exact hlin
  -- Finish with `restrict_le_self`.
  calc
    supportElimMeasure μ Set.univ
        = ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) Set.univ := hmap
    _ ≤ (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ := hwith
    _ ≤ μ Set.univ := by
          simpa using
            (Measure.restrict_le_self (μ := μ) (s := (Set.Icc (-1 : ℝ) 1)ᶜ) Set.univ)

end

end Quantum.TraceInequality.Loewner
