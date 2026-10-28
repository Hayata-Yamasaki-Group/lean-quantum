import Quantum.TraceInequality.Loewner.Koranyi.OutsideRecovery
import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra
import Quantum.Analysis.Measure.FiniteMeasureWeakCompactness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped Topology
open scoped NNReal
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
# Book-route finite approximants for Chapter 27 Theorem 27.5

This file starts the Chapter 27 Theorem 27.5 book route.  It packages the
finite outside Stieltjes approximants from Proposition 27.4 as interval
measures on `[-1,1]`, using the book change of variables `t = -1 / y`.
The weak-limit extraction is then done directly on the compact interval subtype.
-/

namespace AugmentedLoewnerLocalConstruction

variable {f : ℝ → ℝ} {m : ℕ}

/-- The compact interval used by the book weak-limit construction. -/
abbrev BookInterval : Type :=
  Set.Icc (-1 : ℝ) 1

/-- The book weak-limit interval `[-1, 1]` is nonempty. -/
instance : Nonempty BookInterval :=
  ⟨⟨0, by norm_num⟩⟩

/-- The book change of variables from the outside line to the interval side. -/
def bookIntervalMap (y : ℝ) : ℝ :=
  -(y⁻¹)

/-- The density used when moving the outside measure to the interval side. -/
def bookIntervalWeight (y : ℝ) : ENNReal :=
  ENNReal.ofReal ((y ^ (2 : ℕ))⁻¹)

private theorem measurable_bookIntervalMap : Measurable bookIntervalMap := by
  change Measurable fun y : ℝ => -(y⁻¹)
  exact measurable_id.inv.neg

private theorem measurable_bookIntervalWeight : Measurable bookIntervalWeight := by
  have hpow : Measurable fun y : ℝ => y ^ (2 : ℕ) := by
    simpa using (measurable_id.pow_const (2 : ℕ))
  have hinv : Measurable fun y : ℝ => (y ^ (2 : ℕ))⁻¹ :=
    hpow.inv
  simpa [bookIntervalWeight] using (ENNReal.measurable_ofReal.comp hinv)

/--
The interval measure attached to the outside restriction in Theorem 27.5:
apply the density `1 / y^2` and push forward by `y ↦ -1 / y`.
-/
def bookIntervalMeasure (C : AugmentedLoewnerLocalConstruction f m) : Measure ℝ :=
  (C.bookOutsideMeasure.withDensity bookIntervalWeight).map bookIntervalMap

/-- The finite Theorem 3.8-style approximant associated with the outside part. -/
def bookIntervalApproximant (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) : ℝ :=
  C.bookOutsideStieltjesReal 0 +
    ∫ t, x / (1 + t * x) ∂C.bookIntervalMeasure

private theorem bookIntervalMap_mem_Icc_of_mem_Icc_compl {y : ℝ}
    (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    bookIntervalMap y ∈ Set.Icc (-1 : ℝ) 1 := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_mem_Icc_compl hy
  have h_inv : |bookIntervalMap y| ≤ (1 : ℝ) := by
    have h : |y|⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hy_abs
    simpa [bookIntervalMap, abs_neg, abs_inv] using h
  simpa [Set.mem_Icc] using (abs_le.mp h_inv)

private theorem ne_zero_of_mem_Icc_compl {y : ℝ}
    (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    y ≠ 0 := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_mem_Icc_compl hy
  exact abs_pos.mp (lt_of_lt_of_le zero_lt_one hy_abs)

/-- The interval measure has no mass outside `[-1,1]`. -/
theorem bookIntervalMeasure_support_Icc
    (C : AugmentedLoewnerLocalConstruction f m) :
    C.bookIntervalMeasure (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Icc (-1 : ℝ) 1)ᶜ) :=
    isClosed_Icc.measurableSet.compl
  have hpre0 :
      C.bookOutsideMeasure (bookIntervalMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy hpre
    exact hpre (bookIntervalMap_mem_Icc_of_mem_Icc_compl hy)
  have hac :
      C.bookOutsideMeasure.withDensity bookIntervalWeight ≪ C.bookOutsideMeasure :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hwd0 :
      C.bookOutsideMeasure.withDensity bookIntervalWeight
          (bookIntervalMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) = 0 :=
    hac hpre0
  calc
    C.bookIntervalMeasure (Set.Icc (-1 : ℝ) 1)ᶜ =
        C.bookOutsideMeasure.withDensity bookIntervalWeight
          (bookIntervalMap ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ) := by
          rw [bookIntervalMeasure, Measure.map_apply measurable_bookIntervalMap hS]
    _ = 0 := hwd0

/-- The total mass of the interval measure is bounded by the original derivative at `0`. -/
theorem bookIntervalMeasure_univ_le_deriv
    (C : AugmentedLoewnerLocalConstruction f m) :
    C.bookIntervalMeasure Set.univ ≤ ENNReal.ofReal (deriv f 0) := by
  have hmass :
      C.bookIntervalMeasure Set.univ =
        ∫⁻ y, _root_.Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y
          ∂C.bookOutsideMeasure := by
    calc
      C.bookIntervalMeasure Set.univ =
          C.bookOutsideMeasure.withDensity bookIntervalWeight Set.univ := by
            simp [bookIntervalMeasure, Measure.map_apply, measurable_bookIntervalMap]
      _ = ∫⁻ y, bookIntervalWeight y ∂C.bookOutsideMeasure := by
            simp [MeasureTheory.withDensity_apply]
      _ = ∫⁻ y, _root_.Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y
            ∂C.bookOutsideMeasure := by
            apply lintegral_congr_ae
            filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy
            exact ofReal_inv_sq_eq_sqInvDist_zero (ne_zero_of_mem_Icc_compl hy)
  rw [hmass]
  exact C.bookOutside_sqInvDist_zero_le_deriv

/-- The interval measure as a finite measure on the real line. -/
def bookIntervalFiniteMeasure (C : AugmentedLoewnerLocalConstruction f m) : FiniteMeasure ℝ :=
  ⟨C.bookIntervalMeasure, by
    exact ⟨(C.bookIntervalMeasure_univ_le_deriv).trans_lt (by simp)⟩⟩

/-- The book interval measure pulled back to the compact subtype `[-1,1]`. -/
def bookIntervalSubtypeFiniteMeasure
    (C : AugmentedLoewnerLocalConstruction f m) : FiniteMeasure BookInterval :=
  (C.bookIntervalFiniteMeasure).comap ((↑) : BookInterval → ℝ)

private theorem ae_bookIntervalMeasure_mem_Icc
    (C : AugmentedLoewnerLocalConstruction f m) :
    ∀ᵐ t ∂C.bookIntervalMeasure, t ∈ Set.Icc (-1 : ℝ) 1 := by
  change Set.Icc (-1 : ℝ) 1 ∈ ae C.bookIntervalMeasure
  rw [MeasureTheory.mem_ae_iff]
  exact C.bookIntervalMeasure_support_Icc

/--
Pushing the subtype version of the book interval measure back to the real line recovers the
original measure, since it is supported on `[-1,1]`.
-/
theorem bookIntervalSubtypeFiniteMeasure_pushforward_eq
    (C : AugmentedLoewnerLocalConstruction f m) :
    ((C.bookIntervalSubtypeFiniteMeasure).map ((↑) : BookInterval → ℝ) : Measure ℝ) =
      C.bookIntervalMeasure := by
  have hS : MeasurableSet (Set.Icc (-1 : ℝ) 1) := isClosed_Icc.measurableSet
  have hRestrict :
      C.bookIntervalMeasure.restrict (Set.Icc (-1 : ℝ) 1) =
        C.bookIntervalMeasure :=
    Measure.restrict_eq_self_of_ae_mem C.ae_bookIntervalMeasure_mem_Icc
  calc
    ((C.bookIntervalSubtypeFiniteMeasure).map ((↑) : BookInterval → ℝ) : Measure ℝ)
        = (Measure.comap ((↑) : BookInterval → ℝ) C.bookIntervalMeasure).map
            ((↑) : BookInterval → ℝ) := by
            rfl
    _ = C.bookIntervalMeasure.restrict (Set.Icc (-1 : ℝ) 1) := by
          exact map_comap_subtype_coe hS C.bookIntervalMeasure
    _ = C.bookIntervalMeasure := hRestrict

private theorem bookIntervalSubtypeFiniteMeasure_univ_eq
    (C : AugmentedLoewnerLocalConstruction f m) :
    ((C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval) Set.univ) =
      C.bookIntervalMeasure Set.univ := by
  have hpush := C.bookIntervalSubtypeFiniteMeasure_pushforward_eq
  have h :=
    congrArg (fun μ : Measure ℝ => μ Set.univ) hpush
  simpa [Measure.map_apply, measurable_subtype_coe] using h

/-- A derivative bound gives the corresponding mass bound on the subtype interval measure. -/
theorem bookIntervalSubtypeFiniteMeasure_mass_le
    (C : AugmentedLoewnerLocalConstruction f m) {K : ℝ≥0}
    (hK : ENNReal.ofReal (deriv f 0) ≤ (K : ENNReal)) :
    (C.bookIntervalSubtypeFiniteMeasure).mass ≤ K := by
  rw [← ENNReal.coe_le_coe]
  calc
    ((C.bookIntervalSubtypeFiniteMeasure).mass : ENNReal)
        = C.bookIntervalMeasure Set.univ := by
          change ((C.bookIntervalSubtypeFiniteMeasure Set.univ : ℝ≥0) : ENNReal) =
            C.bookIntervalMeasure Set.univ
          rw [MeasureTheory.FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          exact C.bookIntervalSubtypeFiniteMeasure_univ_eq
    _ ≤ ENNReal.ofReal (deriv f 0) := C.bookIntervalMeasure_univ_le_deriv
    _ ≤ (K : ENNReal) := hK

/-- Weak compactness of probability measures on the book interval. -/
theorem exists_subseq_tendsto_probabilityMeasure_BookInterval
    (νs : ℕ → ProbabilityMeasure BookInterval) :
    ∃ (ν : ProbabilityMeasure BookInterval) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (𝓝 ν) := by
  classical
  simpa using (CompactSpace.tendsto_subseq νs)

/-- Weak compactness of finite measures on the book interval with uniformly bounded mass. -/
theorem exists_subseq_tendsto_finiteMeasure_BookInterval_of_mass_le
    (μs : ℕ → FiniteMeasure BookInterval) (K : ℝ≥0)
    (hK : ∀ n, (μs n).mass ≤ K) :
    ∃ (μ : FiniteMeasure BookInterval) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  exact exists_subseq_tendsto_finiteMeasure_of_mass_le μs K hK

/--
The book interval measures admit a weakly convergent subsequence under a uniform derivative
bound.
-/
theorem exists_subseq_tendsto_bookIntervalSubtypeFiniteMeasure_of_uniform_bound
    (Cs : (n : ℕ) → AugmentedLoewnerLocalConstruction f n) (K : ℝ≥0)
    (hK : ∀ _ : ℕ, ENNReal.ofReal (deriv f 0) ≤ (K : ENNReal)) :
    ∃ (ν : FiniteMeasure BookInterval) (φ : ℕ → ℕ),
      StrictMono φ ∧
        Tendsto (fun n => bookIntervalSubtypeFiniteMeasure (Cs (φ n))) atTop (𝓝 ν) := by
  classical
  let μs : ℕ → FiniteMeasure BookInterval := fun n =>
    bookIntervalSubtypeFiniteMeasure (Cs n)
  have hμs : ∀ n, (μs n).mass ≤ K := by
    intro n
    exact bookIntervalSubtypeFiniteMeasure_mass_le (Cs n) (hK n)
  rcases exists_subseq_tendsto_finiteMeasure_BookInterval_of_mass_le
      (μs := μs) (K := K) hμs with
    ⟨ν, φ, hφ, hν⟩
  refine ⟨ν, φ, hφ, ?_⟩
  simpa [μs, Function.comp] using hν

private theorem bookIntervalKernel_den_ne {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (t : BookInterval) :
    1 + (t : ℝ) * x ≠ 0 := by
  have hx_abs : |x| < (1 : ℝ) := abs_lt.mpr hx
  have ht_abs : |(t : ℝ)| ≤ (1 : ℝ) := by
    exact abs_le.mpr t.property
  have hmul_abs : |(t : ℝ) * x| < (1 : ℝ) := by
    calc
      |(t : ℝ) * x| = |(t : ℝ)| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := by
            gcongr
      _ = |x| := one_mul _
      _ < 1 := hx_abs
  have hgt : -(1 : ℝ) < (t : ℝ) * x := (abs_lt.mp hmul_abs).1
  have hpos : 0 < 1 + (t : ℝ) * x := by linarith
  exact ne_of_gt hpos

/-- The book kernel `x / (1 + t * x)` as a continuous function on `[-1,1]`. -/
def bookIntervalKernel (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    C(BookInterval, ℝ) where
  toFun t := x / (1 + (t : ℝ) * x)
  continuous_toFun := by
    have hden : Continuous fun t : BookInterval => 1 + (t : ℝ) * x :=
      continuous_const.add (continuous_subtype_val.mul continuous_const)
    exact continuous_const.div hden (bookIntervalKernel_den_ne hx)

/-- Weak convergence of interval measures gives convergence of the book kernel integrals. -/
theorem bookIntervalKernel_integral_tendsto_of_measure_tendsto
    {νs : ℕ → FiniteMeasure BookInterval} {ν : FiniteMeasure BookInterval}
    (hν : Tendsto νs atTop (𝓝 ν)) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n => ∫ t : BookInterval, bookIntervalKernel x hx t ∂(νs n : Measure BookInterval))
      atTop
      (𝓝 (∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval))) := by
  exact
    ((MeasureTheory.FiniteMeasure.continuous_integral_continuousMap
      (f := bookIntervalKernel x hx)).tendsto ν).comp hν

/-- The subtype interval integral is the original real-line interval-measure integral. -/
theorem bookIntervalSubtype_integral_eq_intervalMeasure_integral
    (C : AugmentedLoewnerLocalConstruction f m) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t : BookInterval, bookIntervalKernel x hx t
        ∂(C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval)) =
      ∫ t : ℝ, x / (1 + t * x) ∂C.bookIntervalMeasure := by
  have hpush :
      Measure.map ((↑) : BookInterval → ℝ)
          (C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval) =
        C.bookIntervalMeasure := by
    simpa using C.bookIntervalSubtypeFiniteMeasure_pushforward_eq
  have hf :
      AEStronglyMeasurable (fun t : ℝ => x / (1 + t * x))
        (Measure.map ((↑) : BookInterval → ℝ)
          (C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval)) :=
    (measurable_const.div
      (measurable_const.add (measurable_id.mul measurable_const))).aestronglyMeasurable
  have hmap :=
    MeasureTheory.integral_map
      (μ := (C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval))
      (φ := ((↑) : BookInterval → ℝ))
      measurable_subtype_coe.aemeasurable
      (f := fun t : ℝ => x / (1 + t * x)) hf
  calc
    (∫ t : BookInterval, bookIntervalKernel x hx t
        ∂(C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval))
        = ∫ t : BookInterval, x / (1 + (t : ℝ) * x)
            ∂(C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval) := rfl
    _ = ∫ t : ℝ, x / (1 + t * x)
          ∂(Measure.map ((↑) : BookInterval → ℝ)
            (C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval)) := by
          exact hmap.symm
    _ = ∫ t : ℝ, x / (1 + t * x) ∂C.bookIntervalMeasure := by
          rw [hpush]

/-- Push a weak-limit measure on the subtype interval back to the real line. -/
def bookWeakLimitFiniteMeasure (ν : FiniteMeasure BookInterval) : FiniteMeasure ℝ :=
  ν.map ((↑) : BookInterval → ℝ)

/-- The pushed-forward weak-limit measure is supported on `[-1,1]`. -/
theorem bookWeakLimitFiniteMeasure_support_Icc
    (ν : FiniteMeasure BookInterval) :
    (bookWeakLimitFiniteMeasure ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Icc (-1 : ℝ) 1)ᶜ) :=
    isClosed_Icc.measurableSet.compl
  change (Measure.map ((↑) : BookInterval → ℝ) (ν : Measure BookInterval))
      (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  rw [Measure.map_apply measurable_subtype_coe hS]
  simp [BookInterval]

/-- Integrating the book kernel against the real-line pushforward is the subtype integral. -/
theorem bookWeakLimitIntegral_eq_subtypeIntegral
    (ν : FiniteMeasure BookInterval) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t : ℝ, x / (1 + t * x) ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ)) =
      ∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval) := by
  have hf :
      AEStronglyMeasurable (fun t : ℝ => x / (1 + t * x))
        (Measure.map ((↑) : BookInterval → ℝ) (ν : Measure BookInterval)) :=
    (measurable_const.div
      (measurable_const.add (measurable_id.mul measurable_const))).aestronglyMeasurable
  have hmap :=
    MeasureTheory.integral_map
      (μ := (ν : Measure BookInterval))
      (φ := ((↑) : BookInterval → ℝ))
      measurable_subtype_coe.aemeasurable
      (f := fun t : ℝ => x / (1 + t * x)) hf
  calc
    (∫ t : ℝ, x / (1 + t * x) ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ))
        = ∫ t : ℝ, x / (1 + t * x)
            ∂(Measure.map ((↑) : BookInterval → ℝ) (ν : Measure BookInterval)) := by
          rfl
    _ = ∫ t : BookInterval, x / (1 + (t : ℝ) * x) ∂(ν : Measure BookInterval) :=
          hmap
    _ = ∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval) := rfl

private theorem interval_integral_eq_outside_stieltjes_diff_integral
    (C : AugmentedLoewnerLocalConstruction f m) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t, x / (1 + t * x) ∂C.bookIntervalMeasure) =
      ∫ y, ((1 / (y - x) : ℝ) - (1 / y)) ∂C.bookOutsideMeasure := by
  classical
  have hmap :
      (∫ t, x / (1 + t * x) ∂C.bookIntervalMeasure) =
        ∫ y, x / (1 + bookIntervalMap y * x)
          ∂(C.bookOutsideMeasure.withDensity bookIntervalWeight) := by
    set μ0 : Measure ℝ := C.bookOutsideMeasure.withDensity bookIntervalWeight
    have hφ : AEMeasurable bookIntervalMap μ0 :=
      measurable_bookIntervalMap.aemeasurable
    have hf :
        AEStronglyMeasurable (fun t : ℝ => x / (1 + t * x))
          (Measure.map bookIntervalMap μ0) :=
      (measurable_const.div
        (measurable_const.add (measurable_id.mul measurable_const))).aestronglyMeasurable
    have h :=
      MeasureTheory.integral_map (μ := μ0) (φ := bookIntervalMap) hφ
        (f := fun t : ℝ => x / (1 + t * x)) hf
    simpa [bookIntervalMeasure, μ0] using h
  have hwd :
      (∫ y, x / (1 + bookIntervalMap y * x)
          ∂(C.bookOutsideMeasure.withDensity bookIntervalWeight)) =
        ∫ y, (bookIntervalWeight y).toReal *
          (x / (1 + bookIntervalMap y * x)) ∂C.bookOutsideMeasure := by
    have htop :
        ∀ᵐ y ∂C.bookOutsideMeasure, bookIntervalWeight y < (⊤ : ENNReal) :=
      MeasureTheory.ae_of_all (μ := C.bookOutsideMeasure) (fun y => by
        simp [bookIntervalWeight])
    have h :=
      integral_withDensity_eq_integral_toReal_smul
        (μ := C.bookOutsideMeasure) (f := bookIntervalWeight)
        measurable_bookIntervalWeight htop
        (g := fun y : ℝ => x / (1 + bookIntervalMap y * x))
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hEq :
      (fun y : ℝ =>
          (bookIntervalWeight y).toReal * (x / (1 + bookIntervalMap y * x))) =ᵐ[
          C.bookOutsideMeasure]
        fun y : ℝ => (1 / (y - x) : ℝ) - (1 / y) := by
    filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy
    have hyIcc : ¬ y ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.mem_compl_iff] using hy
    have hy0 : y ≠ 0 := ne_zero_of_mem_Icc_compl hy
    have hyx : y ≠ x := by
      intro h
      apply hyIcc
      have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      simpa [h] using hxIcc
    have h48 :
        (1 / (y - x) : ℝ) - 1 / y =
          (x / (1 + (-(y⁻¹)) * x)) * (y ^ (2 : ℕ))⁻¹ :=
      _root_.Quantum.TraceInequality.Loewner.one_div_sub_one_div_eq_mul_inv_sq
        (x := x) (y := y) hy0 hyx
    have hwt :
        (bookIntervalWeight y).toReal = (y ^ (2 : ℕ))⁻¹ := by
      have h0 : 0 ≤ (y ^ (2 : ℕ))⁻¹ := by
        have : 0 ≤ y ^ (2 : ℕ) := by simpa using (pow_two_nonneg y)
        exact inv_nonneg.2 this
      simpa [bookIntervalWeight] using (ENNReal.toReal_ofReal h0)
    calc
      (bookIntervalWeight y).toReal * (x / (1 + bookIntervalMap y * x)) =
          (y ^ (2 : ℕ))⁻¹ * (x / (1 + (-(y⁻¹)) * x)) := by
            simp [hwt, bookIntervalMap, mul_comm]
      _ = (x / (1 + (-(y⁻¹)) * x)) * (y ^ (2 : ℕ))⁻¹ := by
            rw [mul_comm]
      _ = (1 / (y - x) : ℝ) - (1 / y) := by
            simpa [h48] using h48.symm
  calc
    (∫ t, x / (1 + t * x) ∂C.bookIntervalMeasure)
        = ∫ y, x / (1 + bookIntervalMap y * x)
            ∂(C.bookOutsideMeasure.withDensity bookIntervalWeight) := hmap
    _ = ∫ y, (bookIntervalWeight y).toReal * (x / (1 + bookIntervalMap y * x))
            ∂C.bookOutsideMeasure := hwd
    _ = ∫ y, ((1 / (y - x) : ℝ) - (1 / y)) ∂C.bookOutsideMeasure := by
          exact MeasureTheory.integral_congr_ae hEq

/--
For each finite outside approximant, the Stieltjes difference from `0` is the
Theorem 3.8 interval integral.
-/
theorem bookOutsideStieltjesReal_sub_zero_eq_intervalIntegral
    (C : AugmentedLoewnerLocalConstruction f m) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    C.bookOutsideStieltjesReal x - C.bookOutsideStieltjesReal 0 =
      ∫ t, x / (1 + t * x) ∂C.bookIntervalMeasure := by
  have hIntx := C.integrable_bookOutsideStieltjesKernelReal x
  have hInt0 := C.integrable_bookOutsideStieltjesKernelReal 0
  have hDiff :
      C.bookOutsideStieltjesReal x - C.bookOutsideStieltjesReal 0 =
        ∫ y, ((1 / (y - x) : ℝ) - (1 / y)) ∂C.bookOutsideMeasure := by
    calc
      C.bookOutsideStieltjesReal x - C.bookOutsideStieltjesReal 0 =
          ∫ y, ((1 / (y - x) : ℝ) - (1 / (y - 0)))
            ∂C.bookOutsideMeasure := by
            change
              (∫ y, (1 / (y - x) : ℝ) ∂C.bookOutsideMeasure) -
                  ∫ y, (1 / (y - 0) : ℝ) ∂C.bookOutsideMeasure =
                ∫ y, ((1 / (y - x) : ℝ) - (1 / (y - 0)))
                  ∂C.bookOutsideMeasure
            rw [← integral_sub hIntx hInt0]
      _ = ∫ y, ((1 / (y - x) : ℝ) - (1 / y)) ∂C.bookOutsideMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => by simp
  rw [hDiff]
  exact (interval_integral_eq_outside_stieltjes_diff_integral C hx).symm

/-- The finite outside Stieltjes transform as its value at `0` plus a subtype integral. -/
theorem bookOutsideStieltjesReal_eq_zero_add_subtypeIntegral
    (C : AugmentedLoewnerLocalConstruction f m) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    C.bookOutsideStieltjesReal x =
      C.bookOutsideStieltjesReal 0 +
        ∫ t : BookInterval, bookIntervalKernel x hx t
          ∂(C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval) := by
  have hdiff := C.bookOutsideStieltjesReal_sub_zero_eq_intervalIntegral hx
  have hsub := C.bookIntervalSubtype_integral_eq_intervalMeasure_integral hx
  calc
    C.bookOutsideStieltjesReal x =
        C.bookOutsideStieltjesReal 0 +
          (C.bookOutsideStieltjesReal x - C.bookOutsideStieltjesReal 0) := by
          ring
    _ = C.bookOutsideStieltjesReal 0 +
          ∫ t : ℝ, x / (1 + t * x) ∂C.bookIntervalMeasure := by
          rw [hdiff]
    _ = C.bookOutsideStieltjesReal 0 +
          ∫ t : BookInterval, bookIntervalKernel x hx t
            ∂(C.bookIntervalSubtypeFiniteMeasure : Measure BookInterval) := by
          rw [hsub]

/-- The finite interval approximant is exactly the real outside Stieltjes transform. -/
theorem bookIntervalApproximant_eq_outsideStieltjesReal
    (C : AugmentedLoewnerLocalConstruction f m) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    C.bookIntervalApproximant x = C.bookOutsideStieltjesReal x := by
  have h := C.bookOutsideStieltjesReal_sub_zero_eq_intervalIntegral hx
  rw [bookIntervalApproximant]
  linarith

/-- The explicit ENNReal prefactor in the dyadic outside Stieltjes error estimate. -/
def bookDyadicOutsideErrorBound (K : ℝ≥0) (m : ℕ) : ENNReal :=
  ((K : ENNReal) *
      (ENNReal.ofReal (8 * dyadicGridRadius m) * (K : ENNReal))) ^
    (1 / 2 : ℝ)

private theorem bookDyadicOutsideErrorBound_ne_top
    (K : ℝ≥0) (m : ℕ) :
    bookDyadicOutsideErrorBound K m ≠ ⊤ := by
  unfold bookDyadicOutsideErrorBound
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))

/-- The explicit Proposition 27.4 dyadic prefactor tends to zero along subsequences. -/
theorem bookOutsideStieltjes_dyadicErrorBound_prefactor_tendsto_zero
    (K : ℝ≥0) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n : ℕ => bookDyadicOutsideErrorBound K (φ n))
      atTop (𝓝 (0 : ENNReal)) := by
  have hradius :
      Tendsto (fun n : ℕ => dyadicGridRadius (φ n)) atTop (𝓝 (0 : ℝ)) := by
    have h0 :
        Tendsto (fun m : ℕ => dyadicGridRadius m) atTop (𝓝 (0 : ℝ)) := by
      simpa [dyadicGridRadius] using
        _root_.Quantum.TraceInequality.Loewner.tendsto_dyadicRadius_zero
    exact h0.comp hφ.tendsto_atTop
  have h8 :
      Tendsto (fun n : ℕ => 8 * dyadicGridRadius (φ n)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hradius.const_mul (8 : ℝ)
  have hofReal :
      Tendsto (fun n : ℕ => ENNReal.ofReal (8 * dyadicGridRadius (φ n)))
        atTop (𝓝 (0 : ENNReal)) := by
    simpa using ENNReal.tendsto_ofReal h8
  have hinner :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal (8 * dyadicGridRadius (φ n)) * (K : ENNReal))
        atTop (𝓝 (0 : ENNReal)) := by
    simpa using
      ENNReal.Tendsto.mul_const hofReal (Or.inr ENNReal.coe_ne_top)
  have hprod :
      Tendsto
        (fun n : ℕ => (K : ENNReal) *
          (ENNReal.ofReal (8 * dyadicGridRadius (φ n)) * (K : ENNReal)))
        atTop (𝓝 (0 : ENNReal)) := by
    simpa using
      ENNReal.Tendsto.const_mul hinner (Or.inr ENNReal.coe_ne_top)
  have hrpow :
      Tendsto
        (fun a : ENNReal => a ^ (1 / 2 : ℝ)) (𝓝 (0 : ENNReal)) (𝓝 (0 : ENNReal)) := by
    simpa using (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ENNReal)
  simpa [bookDyadicOutsideErrorBound] using hrpow.comp hprod

private theorem bookOutsideStieltjes_tendsto_f_complex_of_dyadic_selector
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {x : ℝ}
    (idx : (n : ℕ) → Fin (nonzeroInteriorDyadicPointCount (φ n) + 1))
    (hidx : ∀ᶠ n in atTop, zeroAnchoredDyadicPointFamily (φ n) (idx n) = x) :
    Tendsto (fun n : ℕ => (Cs (φ n)).bookOutsideStieltjes x)
      atTop (𝓝 (f x : ℂ)) := by
  have hB :
      Tendsto (fun n : ℕ => bookDyadicOutsideErrorBound K (φ n))
        atTop (𝓝 (0 : ENNReal)) :=
    bookOutsideStieltjes_dyadicErrorBound_prefactor_tendsto_zero K hφ
  have hBReal :
      Tendsto (fun n : ℕ => (bookDyadicOutsideErrorBound K (φ n)).toReal)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hB
  have hnorm_le :
      ∀ᶠ n in atTop,
        ‖(Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)‖ ≤
          (bookDyadicOutsideErrorBound K (φ n)).toReal := by
    filter_upwards [hidx] with n hn
    have hBound :=
      (Cs (φ n)).bookOutsideStieltjes_dyadicErrorBound_prefactor
        K (hK (φ n)) (idx n)
    have hEnorm :
        ‖(Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)‖ₑ ≤
          bookDyadicOutsideErrorBound K (φ n) := by
      simpa [bookDyadicOutsideErrorBound, hn] using hBound
    have hReal :=
      ENNReal.toReal_mono (bookDyadicOutsideErrorBound_ne_top K (φ n)) hEnorm
    have hLeft :
        (‖(Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)‖ₑ).toReal =
          ‖(Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)‖ := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.toReal_ofReal (norm_nonneg _)
    simpa [hLeft] using hReal
  have hnorm0 :
      Tendsto
        (fun n : ℕ => ‖(Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)‖)
        atTop (𝓝 (0 : ℝ)) := by
    exact squeeze_zero'
      (Eventually.of_forall fun n =>
        norm_nonneg ((Cs (φ n)).bookOutsideStieltjes x - (f x : ℂ)))
      hnorm_le hBReal
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm0

/-- Prop. 27.4 dyadic error makes the real outside Stieltjes approximants converge to `f`
along a selector which is eventually equal to the fixed dyadic point. -/
theorem bookOutsideStieltjesReal_tendsto_f_of_dyadic_selector
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {x : ℝ}
    (idx : (n : ℕ) → Fin (nonzeroInteriorDyadicPointCount (φ n) + 1))
    (hidx : ∀ᶠ n in atTop, zeroAnchoredDyadicPointFamily (φ n) (idx n) = x) :
    Tendsto (fun n : ℕ => (Cs (φ n)).bookOutsideStieltjesReal x)
      atTop (𝓝 (f x)) := by
  have hComplex :=
    bookOutsideStieltjes_tendsto_f_complex_of_dyadic_selector
      Cs K hK hφ idx hidx
  have hRe :
      Tendsto (fun n : ℕ => ((Cs (φ n)).bookOutsideStieltjes x).re)
        atTop (𝓝 ((f x : ℂ).re)) :=
    (Complex.continuous_re.tendsto (f x : ℂ)).comp hComplex
  refine Tendsto.congr' ?_ (by simpa using hRe)
  exact Eventually.of_forall fun n => by
    have h :=
      (Cs (φ n)).bookOutsideStieltjesReal_ofReal_eq_bookOutsideStieltjes (x := x)
    simpa using (congrArg Complex.re h).symm

/-- The same convergence at the base point `0`. -/
theorem bookOutsideStieltjesReal_zero_tendsto_f_zero
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n : ℕ => (Cs (φ n)).bookOutsideStieltjesReal 0)
      atTop (𝓝 (f 0)) := by
  refine bookOutsideStieltjesReal_tendsto_f_of_dyadic_selector
    Cs K hK hφ (x := 0) (fun n => (0 : Fin (nonzeroInteriorDyadicPointCount (φ n) + 1))) ?_
  exact Eventually.of_forall fun n => zeroAnchoredDyadicPointFamily_zero (φ n)

/--
On a dyadic selector, the weak-limit measure already gives the final
Theorem 27.5 integral representation on the subtype interval.
-/
theorem bookWeakLimit_integralRep_on_dyadic_selector
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (idx : (n : ℕ) → Fin (nonzeroInteriorDyadicPointCount (φ n) + 1))
    (hidx : ∀ᶠ n in atTop, zeroAnchoredDyadicPointFamily (φ n) (idx n) = x) :
    f x =
      f 0 + ∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval) := by
  have hOutX :=
    bookOutsideStieltjesReal_tendsto_f_of_dyadic_selector
      Cs K hK hφ idx hidx
  have hOut0 :=
    bookOutsideStieltjesReal_zero_tendsto_f_zero Cs K hK hφ
  have hInt :=
    bookIntervalKernel_integral_tendsto_of_measure_tendsto hν hx
  have hFinite :
      Tendsto
        (fun n : ℕ =>
          (Cs (φ n)).bookOutsideStieltjesReal 0 +
            ∫ t : BookInterval, bookIntervalKernel x hx t
              ∂(bookIntervalSubtypeFiniteMeasure (Cs (φ n)) : Measure BookInterval))
        atTop
        (𝓝 (f 0 +
          ∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval))) :=
    hOut0.add hInt
  have hFinite' :
      Tendsto (fun n : ℕ => (Cs (φ n)).bookOutsideStieltjesReal x)
        atTop
        (𝓝 (f 0 +
          ∫ t : BookInterval, bookIntervalKernel x hx t ∂(ν : Measure BookInterval))) := by
    refine Tendsto.congr' ?_ hFinite
    exact Eventually.of_forall fun n =>
      (Cs (φ n)).bookOutsideStieltjesReal_eq_zero_add_subtypeIntegral hx |>.symm
  exact tendsto_nhds_unique hOutX hFinite'

/--
The same selector-form limit identification, pushed forward to a real-line measure supported
on `[-1,1]`.
-/
theorem bookWeakLimit_integralRep_on_dyadic_selector_realLine
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (idx : (n : ℕ) → Fin (nonzeroInteriorDyadicPointCount (φ n) + 1))
    (hidx : ∀ᶠ n in atTop, zeroAnchoredDyadicPointFamily (φ n) (idx n) = x) :
    f x =
      f 0 + ∫ t : ℝ, x / (1 + t * x)
        ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ) := by
  have hSubtype :=
    bookWeakLimit_integralRep_on_dyadic_selector
      Cs K hK hφ hν hx idx hidx
  have hpush := bookWeakLimitIntegral_eq_subtypeIntegral ν hx
  simpa [hpush] using hSubtype

/-- The numerator that represents a fixed dyadic point on a finer dyadic grid. -/
def dyadicScaledNumerator (ℓ m : ℕ) (k : ℤ) : ℤ :=
  k * (2 : ℤ) ^ (m - ℓ)

/-- Scaling the numerator preserves the underlying dyadic point. -/
theorem dyadicGridPoint_scaledNumerator_eq {ℓ m : ℕ} (hℓm : ℓ ≤ m) (k : ℤ) :
    dyadicGridPoint m (dyadicScaledNumerator ℓ m k) = dyadicGridPoint ℓ k := by
  have hpow_split :
      (2 : ℝ) ^ m = (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (m - ℓ) := by
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ (ℓ + (m - ℓ)) := by
        rw [Nat.add_sub_of_le hℓm]
      _ = (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (m - ℓ) := by
        rw [pow_add]
  have hpowℓ : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
  have hpowdiff : (2 : ℝ) ^ (m - ℓ) ≠ 0 := by positivity
  simp [dyadicScaledNumerator, dyadicGridPoint, _root_.Quantum.TraceInequality.Loewner.dyadicCenter,
    hpow_split, mul_div_mul_right _ _ hpowdiff]

/--
If a numerator is an interior nonzero dyadic numerator at level `ℓ`, then its
scaled numerator is an interior nonzero numerator at every finer level.
-/
theorem dyadicScaledNumerator_mem_nonzeroInteriorDyadicIndices {ℓ m : ℕ}
    (hℓm : ℓ ≤ m) {k : ℤ} (hk : k ∈ nonzeroInteriorDyadicIndices ℓ) :
    dyadicScaledNumerator ℓ m k ∈ nonzeroInteriorDyadicIndices m := by
  rcases (mem_nonzeroInteriorDyadicIndices_iff ℓ k).1 hk with
    ⟨_hk_grid, hk_lower, hk_upper, hk_ne⟩
  let q : ℤ := (2 : ℤ) ^ (m - ℓ)
  have hq_pos : 0 < q := by positivity
  have hpow_split : (2 : ℤ) ^ m = (2 : ℤ) ^ ℓ * q := by
    calc
      (2 : ℤ) ^ m = (2 : ℤ) ^ (ℓ + (m - ℓ)) := by
        rw [Nat.add_sub_of_le hℓm]
      _ = (2 : ℤ) ^ ℓ * q := by
        simp [q, pow_add]
  have hk_lower_scaled : -((2 : ℤ) ^ m) < k * q := by
    have hmul := mul_lt_mul_of_pos_right hk_lower hq_pos
    rwa [neg_mul, ← hpow_split] at hmul
  have hk_upper_scaled : k * q < (2 : ℤ) ^ m := by
    have hmul := mul_lt_mul_of_pos_right hk_upper hq_pos
    rwa [← hpow_split] at hmul
  have hk_ne_scaled : k * q ≠ 0 := by
    exact mul_ne_zero hk_ne (ne_of_gt hq_pos)
  have hk_mem_scaled : k * q ∈ dyadicGridIndices m := by
    change k * q ∈
      Finset.Icc (-((2 : ℤ) ^ (m + 1))) ((2 : ℤ) ^ (m + 1))
    rw [Finset.mem_Icc]
    have hpow_pos : 0 < (2 : ℤ) ^ m := by positivity
    have hpow_succ : (2 : ℤ) ^ m < (2 : ℤ) ^ (m + 1) := by
      rw [pow_succ]
      nlinarith
    constructor
    · have hneg : -((2 : ℤ) ^ (m + 1)) < -((2 : ℤ) ^ m) := by
        exact neg_lt_neg hpow_succ
      exact (lt_trans hneg hk_lower_scaled).le
    · exact (lt_trans hk_upper_scaled hpow_succ).le
  exact (mem_nonzeroInteriorDyadicIndices_iff m (dyadicScaledNumerator ℓ m k)).2
    ⟨by simpa [dyadicScaledNumerator, q] using hk_mem_scaled,
      by simpa [dyadicScaledNumerator, q] using hk_lower_scaled,
      by simpa [dyadicScaledNumerator, q] using hk_upper_scaled,
      by simpa [dyadicScaledNumerator, q] using hk_ne_scaled⟩

/-- The concrete selector that keeps a fixed dyadic point on every sufficiently fine grid. -/
noncomputable def fixedDyadicPointSelector
    (ℓ : ℕ) (k : ℤ) (hk : k ∈ nonzeroInteriorDyadicIndices ℓ)
    (φ : ℕ → ℕ) (n : ℕ) : Fin (nonzeroInteriorDyadicPointCount (φ n) + 1) :=
  if hℓφ : ℓ ≤ φ n then
    (nonzeroInteriorDyadicPointIndex (φ n) (dyadicScaledNumerator ℓ (φ n) k)
      (dyadicScaledNumerator_mem_nonzeroInteriorDyadicIndices hℓφ hk)).succ
  else
    0

/-- A strictly increasing subsequence eventually reaches every fixed dyadic level. -/
private theorem eventually_le_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) (ℓ : ℕ) :
    ∀ᶠ n in atTop, ℓ ≤ φ n :=
  hφ.tendsto_atTop.eventually (eventually_ge_atTop ℓ)

/-- The concrete fixed-dyadic selector is eventually exactly the target dyadic point. -/
theorem fixedDyadicPointSelector_eventually_eq
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {ℓ : ℕ} {k : ℤ}
    (hk : k ∈ nonzeroInteriorDyadicIndices ℓ) :
    ∀ᶠ n in atTop,
      zeroAnchoredDyadicPointFamily (φ n) (fixedDyadicPointSelector ℓ k hk φ n) =
        dyadicGridPoint ℓ k := by
  filter_upwards [eventually_le_strictMono hφ ℓ] with n hℓφ
  calc
    zeroAnchoredDyadicPointFamily (φ n) (fixedDyadicPointSelector ℓ k hk φ n) =
        dyadicGridPoint (φ n) (dyadicScaledNumerator ℓ (φ n) k) := by
        simpa [fixedDyadicPointSelector, hℓφ] using
          zeroAnchoredDyadicPointFamily_succ_openIndex (φ n)
            (dyadicScaledNumerator ℓ (φ n) k)
            (dyadicScaledNumerator_mem_nonzeroInteriorDyadicIndices hℓφ hk)
    _ = dyadicGridPoint ℓ k := dyadicGridPoint_scaledNumerator_eq hℓφ k

/-- The selector-form weak-limit theorem specialized to a fixed nonzero dyadic point. -/
theorem bookWeakLimit_integralRep_on_fixed_dyadicGridPoint
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    {ℓ : ℕ} {k : ℤ} (hk : k ∈ nonzeroInteriorDyadicIndices ℓ) :
    f (dyadicGridPoint ℓ k) =
      f 0 + ∫ t : ℝ, dyadicGridPoint ℓ k / (1 + t * dyadicGridPoint ℓ k)
        ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ) := by
  exact
    bookWeakLimit_integralRep_on_dyadic_selector_realLine
      Cs K hK hφ hν (nonzeroInteriorDyadicIndices_subset_Ioo ℓ k hk)
      (fixedDyadicPointSelector ℓ k hk φ)
      (fixedDyadicPointSelector_eventually_eq hφ hk)

/-- The set of book dyadic points used in Theorem 27.5. -/
def bookDyadicPointSet : Set ℝ :=
  {x | ∃ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
    x = zeroAnchoredDyadicPointFamily m i}

/-- Every book dyadic point lies in the open unit interval. -/
theorem bookDyadicPointSet_subset_Ioo :
    bookDyadicPointSet ⊆ Set.Ioo (-1 : ℝ) 1 := by
  rintro x ⟨m, i, rfl⟩
  exact zeroAnchoredDyadicPointFamily_mem_Ioo m i

/-- The book dyadic points are dense in the open unit interval. -/
theorem Ioo_subset_closure_bookDyadicPointSet :
    Set.Ioo (-1 : ℝ) 1 ⊆ closure bookDyadicPointSet := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hradius :
      Tendsto (fun m : ℕ => dyadicGridRadius m) atTop (𝓝 (0 : ℝ)) := by
    simpa [dyadicGridRadius] using
      _root_.Quantum.TraceInequality.Loewner.tendsto_dyadicRadius_zero
  have hevent : ∀ᶠ m in atTop, dyadicGridRadius m < ε :=
    hradius.eventually (Iio_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hevent with ⟨m, hm⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  rcases exists_zeroAnchoredDyadicPointFamily_dist_le m x hxIcc with ⟨i, hi⟩
  refine ⟨zeroAnchoredDyadicPointFamily m i, ⟨m, i, rfl⟩, ?_⟩
  exact lt_of_le_of_lt hi (hm m le_rfl)

/-- The real-line weak-limit kernel integral is continuous on the open unit interval. -/
theorem bookWeakLimitIntegral_continuousOn_Ioo
    (ν : FiniteMeasure BookInterval) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ t : ℝ, x / (1 + t * x) ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ))
      (Set.Ioo (-1 : ℝ) 1) := by
  let U : Set ℝ := Set.Ioo (-1 : ℝ) 1
  haveI : LocallyCompactSpace U := by
    dsimp [U]
    exact isOpen_Ioo.locallyCompactSpace
  have hSub :
      Continuous
        (fun x : U =>
          ∫ t : BookInterval, ((x : ℝ) / (1 + (t : ℝ) * (x : ℝ)))
            ∂(ν : Measure BookInterval)) := by
    have huncurry :
        Continuous
          (Function.uncurry
            (fun x : U => fun t : BookInterval =>
              ((x : ℝ) / (1 + (t : ℝ) * (x : ℝ)) : ℝ))) := by
      have hxcont : Continuous fun p : U × BookInterval => ((p.1 : U) : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have htcont : Continuous fun p : U × BookInterval => ((p.2 : BookInterval) : ℝ) :=
        continuous_subtype_val.comp continuous_snd
      exact hxcont.div
        (continuous_const.add (htcont.mul hxcont))
        (fun p => bookIntervalKernel_den_ne p.1.property p.2)
    have hparam :=
      continuous_parametric_integral_of_continuous
        (μ := (ν : Measure BookInterval))
        (f := fun x : U => fun t : BookInterval =>
          ((x : ℝ) / (1 + (t : ℝ) * (x : ℝ)) : ℝ))
        huncurry (s := Set.univ) isCompact_univ
    simpa [MeasureTheory.setIntegral_univ] using hparam
  rw [continuousOn_iff_continuous_restrict]
  refine hSub.congr ?_
  intro x
  exact (bookWeakLimitIntegral_eq_subtypeIntegral ν x.property).symm

/-- The real-line weak-limit representation holds on every book dyadic point. -/
theorem bookWeakLimit_integralRep_on_bookDyadicPointSet_realLine
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν)) :
    Set.EqOn
      (fun x : ℝ => f x)
      (fun x : ℝ =>
        f 0 + ∫ t : ℝ, x / (1 + t * x)
          ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ))
      bookDyadicPointSet := by
  rintro x ⟨m, i, rfl⟩
  cases i using Fin.cases with
  | zero =>
      simp
  | succ j =>
      let k : ℤ := (nonzeroInteriorDyadicIndices m).orderEmbOfFin rfl j
      have hk : k ∈ nonzeroInteriorDyadicIndices m :=
        (nonzeroInteriorDyadicIndices m).orderEmbOfFin_mem rfl j
      have hfixed :=
        bookWeakLimit_integralRep_on_fixed_dyadicGridPoint
          Cs K hK hφ hν hk
      simpa [k, zeroAnchoredDyadicPointFamily_succ] using hfixed

/--
The weak-limit real-line integral representation extends from dyadic points to
all of `(-1,1)` by density and continuity.
-/
theorem bookWeakLimitIntegralRep_on_Ioo_realLine
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    (hf_cont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      f x =
        f 0 + ∫ t : ℝ, x / (1 + t * x)
          ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ) := by
  intro x hx
  have hEqDyadic :=
    bookWeakLimit_integralRep_on_bookDyadicPointSet_realLine
      Cs K hK hφ hν
  have hRightCont :
      ContinuousOn
        (fun x : ℝ =>
          f 0 + ∫ t : ℝ, x / (1 + t * x)
            ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ))
        (Set.Ioo (-1 : ℝ) 1) :=
    continuousOn_const.add (bookWeakLimitIntegral_continuousOn_Ioo ν)
  have hEqIoo :
      Set.EqOn
        (fun x : ℝ => f x)
        (fun x : ℝ =>
          f 0 + ∫ t : ℝ, x / (1 + t * x)
            ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ))
        (Set.Ioo (-1 : ℝ) 1) :=
    Set.EqOn.of_subset_closure hEqDyadic hf_cont hRightCont
      bookDyadicPointSet_subset_Ioo Ioo_subset_closure_bookDyadicPointSet
  exact hEqIoo hx

/-- Real weak-limit kernel integral, named to keep coercions to `ℂ` unambiguous. -/
def bookWeakLimitRealKernelIntegral (ν : FiniteMeasure BookInterval) (x : ℝ) : ℝ :=
  ∫ t : ℝ, x / (1 + t * x) ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ)

/-- The complex book kernel integral is the complexification of the real kernel integral. -/
theorem bookWeakLimit_complexIntegral_eq_ofReal
    (ν : FiniteMeasure BookInterval) (x : ℝ) :
    (∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
        ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ)) =
      (bookWeakLimitRealKernelIntegral ν x : ℂ) := by
  let μ : Measure ℝ := bookWeakLimitFiniteMeasure ν
  let g : ℝ → ℝ := fun t => x / (1 + t * x)
  calc
    (∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x)) ∂μ) =
        ∫ t : ℝ, (g t : ℂ) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by
            simp [g, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul]
    _ = (bookWeakLimitRealKernelIntegral ν x : ℂ) := by
          let J : ℝ := ∫ t : ℝ, g t ∂μ
          have hOfReal0 :
              (∫ t : ℝ, (g t : ℂ) ∂μ) = (J : ℂ) := by
            have hBase :
                (∫ t : ℝ, (g t : ℂ) ∂μ) =
                  (((∫ t : ℝ, (g t : ℝ) ∂μ) : ℝ) : ℂ) := by
              exact
                (integral_ofReal
                  (𝕜 := ℂ)
                  (μ := μ)
                  (f := g))
            simpa [J] using hBase
          have hOfReal :
              (∫ t : ℝ, (g t : ℂ) ∂μ) =
                (bookWeakLimitRealKernelIntegral ν x : ℂ) := by
            simpa [J, bookWeakLimitRealKernelIntegral, μ, g] using hOfReal0
          exact hOfReal

/--
The dense-extension weak-limit representation in the complex form used by
`IntegralRepOnUnitInterval`.
-/
theorem bookWeakLimitIntegralRep_on_Ioo_complex
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    (hf_cont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      (f x : ℂ) =
        (f 0 : ℂ) +
          ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
            ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ) := by
  intro x hx
  have hreal :=
    bookWeakLimitIntegralRep_on_Ioo_realLine
      Cs K hK hφ hν hf_cont hx
  have hreal' :
      f x = f 0 + bookWeakLimitRealKernelIntegral ν x := by
    simpa [bookWeakLimitRealKernelIntegral] using hreal
  have hcomplex :
      (f x : ℂ) = (f 0 : ℂ) + (bookWeakLimitRealKernelIntegral ν x : ℂ) := by
    simpa [Complex.ofReal_add] using congrArg (fun r : ℝ => (r : ℂ)) hreal'
  calc
    (f x : ℂ) = (f 0 : ℂ) + (bookWeakLimitRealKernelIntegral ν x : ℂ) := hcomplex
    _ = (f 0 : ℂ) +
        ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
          ∂(bookWeakLimitFiniteMeasure ν : Measure ℝ) := by
          rw [← bookWeakLimit_complexIntegral_eq_ofReal]

/--
Explicit-input Theorem 27.5 package: once the local constructions, the uniform dyadic
derivative bound, and the weak-limit subsequence are supplied, the book route returns the
public interval integral representation.
-/
noncomputable def bookWeakLimit_integralRepPackage_of_uniform_deriv_bound
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    {ν : FiniteMeasure BookInterval} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hν :
      Tendsto (fun n : ℕ => bookIntervalSubtypeFiniteMeasure (Cs (φ n)))
        atTop (𝓝 ν))
    (hf_cont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f where
  ν := bookWeakLimitFiniteMeasure ν
  support := bookWeakLimitFiniteMeasure_support_Icc ν
  formula := by
    intro x hx
    exact bookWeakLimitIntegralRep_on_Ioo_complex Cs K hK hφ hν hf_cont hx

/--
Compactness-extracted explicit-input Theorem 27.5 package: the weak-limit subsequence is
obtained from the uniform dyadic derivative bound.
-/
noncomputable def bookWeakLimit_integralRepPackage_of_uniform_deriv_bound_compactness
    (Cs : (m : ℕ) → AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    (hf_cont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f := by
  classical
  have hK0 : ∀ m : ℕ, ENNReal.ofReal (deriv f 0) ≤ (K : ENNReal) := by
    intro m
    simpa [zeroAnchoredDyadicPointFamily_zero] using
      hK m (0 : Fin (nonzeroInteriorDyadicPointCount m + 1))
  let hsub :=
    exists_subseq_tendsto_bookIntervalSubtypeFiniteMeasure_of_uniform_bound
      (Cs := Cs) (K := K) hK0
  let ν : FiniteMeasure BookInterval := Classical.choose hsub
  let hsubν := Classical.choose_spec hsub
  let φ : ℕ → ℕ := Classical.choose hsubν
  have hφν := Classical.choose_spec hsubν
  exact
    bookWeakLimit_integralRepPackage_of_uniform_deriv_bound
      (ν := ν) (φ := φ) Cs K hK hφν.1 hφν.2 hf_cont

end AugmentedLoewnerLocalConstruction

end

end Quantum.TraceInequality.Loewner
