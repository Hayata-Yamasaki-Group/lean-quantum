import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Discrete Bochner data and finite-window bounds

This file is the discrete-time, measure-first part of Bochner--Herglotz theory needed by
autocorrelation estimates.  The frequency torus is `ℝ / (2πℤ)`.  Mathlib's character
`fourier j` then has the concrete value `exp (I * j * ω)` on every real representative `ω`.

No existence theorem constructing the spectral measure is asserted here: the measure and its
Fourier representation are fields of `SpectralCovarianceData`.
-/

namespace Quantum
namespace Analysis
namespace Spectral

open Complex MeasureTheory Metric Set
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

noncomputable section

/-- The angular frequency torus, with period `2π`. -/
abbrev FrequencyTorus := AddCircle (2 * Real.pi)

local instance frequencyTorusPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos zero_lt_two Real.pi_pos⟩

/-- The integer character `ω ↦ exp (I j ω)` on the angular frequency torus.

The displayed exponential formula is literal after choosing any real representative; see
`spectralCharacter_coe`. -/
def spectralCharacter (j : ℤ) : C(FrequencyTorus, ℂ) :=
  fourier j

@[simp]
theorem spectralCharacter_coe (j : ℤ) (ω : ℝ) :
    spectralCharacter j (ω : FrequencyTorus) = Complex.exp (Complex.I * j * ω) := by
  rw [spectralCharacter, fourier_coe_apply]
  push_cast
  field_simp [Real.pi_ne_zero]

@[simp]
theorem spectralCharacter_zero (ω : FrequencyTorus) : spectralCharacter 0 ω = 1 := by
  simp [spectralCharacter]

@[simp]
theorem spectralCharacter_neg (j : ℤ) (ω : FrequencyTorus) :
    spectralCharacter (-j) ω = conj (spectralCharacter j ω) := by
  exact fourier_neg

theorem spectralCharacter_add (j k : ℤ) (ω : FrequencyTorus) :
    spectralCharacter (j + k) ω = spectralCharacter j ω * spectralCharacter k ω := by
  exact fourier_add

@[simp]
theorem norm_spectralCharacter (j : ℤ) (ω : FrequencyTorus) :
    ‖spectralCharacter j ω‖ = 1 := by
  exact Circle.norm_coe _

/-- The canonical representative in `(-π, π]`. -/
def centeredAngle (ω : FrequencyTorus) : ℝ :=
  (AddCircle.equivIoc (2 * Real.pi) (-Real.pi) ω).1

theorem centeredAngle_mem (ω : FrequencyTorus) :
    centeredAngle ω ∈ Set.Ioc (-Real.pi) Real.pi := by
  have h := (AddCircle.equivIoc (2 * Real.pi) (-Real.pi) ω).2
  convert h using 1
  ring_nf

theorem centeredAngle_coe (ω : FrequencyTorus) :
    (centeredAngle ω : FrequencyTorus) = ω := by
  have h := (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).symm_apply_apply ω
  exact h

theorem norm_eq_abs_centeredAngle (ω : FrequencyTorus) :
    ‖ω‖ = |centeredAngle ω| := by
  calc
    ‖ω‖ = ‖(centeredAngle ω : FrequencyTorus)‖ :=
      congrArg norm (centeredAngle_coe ω).symm
    _ = |centeredAngle ω| := by
      apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).2
      have h := centeredAngle_mem ω
      simpa [abs_of_pos Real.pi_pos] using (abs_le.2 ⟨h.1.le, h.2⟩)

theorem spectralCharacter_one_eq_exp_centeredAngle (ω : FrequencyTorus) :
    spectralCharacter 1 ω = Complex.exp (Complex.I * centeredAngle ω) := by
  calc
    spectralCharacter 1 ω = spectralCharacter 1 (centeredAngle ω : FrequencyTorus) :=
      congrArg (spectralCharacter 1) (centeredAngle_coe ω).symm
    _ = Complex.exp (Complex.I * centeredAngle ω) := by
      rw [spectralCharacter_coe]
      norm_num

private theorem spectralCharacter_integrable (F : FiniteMeasure FrequencyTorus) (j : ℤ) :
    Integrable (spectralCharacter j) (F : Measure FrequencyTorus) := by
  apply Integrable.of_bound (spectralCharacter j).continuous.aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simp

private theorem spectralCharacter_memLp (F : FiniteMeasure FrequencyTorus) (j : ℤ) :
    MemLp (spectralCharacter j) 2 (F : Measure FrequencyTorus) := by
  apply MemLp.of_bound (spectralCharacter j).continuous.aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simp

/-- Discrete positive definiteness with subtraction order matching `Matrix.PosSemidef`:
the `(i,j)` entry is `C (x j - x i)`. -/
def IsPositiveDefiniteInt (C : ℤ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℤ),
    (Matrix.of fun i j => C (x j - x i)).PosSemidef

/-- Certified spectral representation of a discrete stationary covariance sequence.

The sign convention is
`C j = ∫ ω, exp (I * j * ω) ∂F`; equivalently, the integrand is Mathlib's
`spectralCharacter j = fourier j` on `AddCircle (2π)`.
-/
structure SpectralCovarianceData where
  /-- Finite positive spectral measure on the angular frequency torus. -/
  F : FiniteMeasure FrequencyTorus
  /-- Complex covariance sequence indexed by integer time lag. -/
  C : ℤ → ℂ
  /-- The chosen positive-exponent Fourier representation. -/
  repr : ∀ j : ℤ, C j = ∫ ω, spectralCharacter j ω ∂(F : Measure FrequencyTorus)

namespace SpectralCovarianceData

variable (d : SpectralCovarianceData)

/-- The zero-lag covariance is the (real) total spectral mass. -/
theorem zero_eq_mass : d.C 0 = (d.F.mass : ℂ) := by
  rw [d.repr]
  simp only [spectralCharacter_zero, integral_const, FiniteMeasure.mass]
  change (((d.F Set.univ : ℝ≥0) : ℝ) : ℂ) * 1 =
    ((d.F Set.univ : ℝ≥0) : ℂ)
  simp

/-- In particular, the zero-lag covariance has zero imaginary part. -/
@[simp]
theorem zero_im : (d.C 0).im = 0 := by
  rw [d.zero_eq_mass]
  simp

/-- In particular, the real zero-lag covariance is the total spectral mass. -/
theorem zero_re_eq_mass : (d.C 0).re = d.F.mass := by
  rw [d.zero_eq_mass]
  simp

/-- Covariances represented by a positive spectral measure have Hermitian symmetry. -/
theorem neg_eq_conj (j : ℤ) : d.C (-j) = conj (d.C j) := by
  rw [d.repr, d.repr]
  simp_rw [spectralCharacter_neg]
  exact integral_conj

/-- The represented covariance sequence is positive definite on integer lags. -/
theorem isPositiveDefiniteInt : IsPositiveDefiniteInt d.C := by
  intro n x
  let v : Fin n → FrequencyTorus →₂[(d.F : Measure FrequencyTorus)] ℂ := fun i =>
    (spectralCharacter_memLp d.F (x i)).toLp (spectralCharacter (x i))
  have hgram : (Matrix.gram ℂ v).PosSemidef := Matrix.posSemidef_gram ℂ v
  convert hgram using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.gram_apply]
  rw [MeasureTheory.L2.inner_def, d.repr]
  apply integral_congr_ae
  have hvi : (v i : FrequencyTorus → ℂ) =ᵐ[(d.F : Measure FrequencyTorus)]
      spectralCharacter (x i) := by
    dsimp [v]
    exact (spectralCharacter_memLp d.F (x i)).coeFn_toLp
  have hvj : (v j : FrequencyTorus → ℂ) =ᵐ[(d.F : Measure FrequencyTorus)]
      spectralCharacter (x j) := by
    dsimp [v]
    exact (spectralCharacter_memLp d.F (x j)).coeFn_toLp
  filter_upwards [hvi, hvj] with ω hi hj
  rw [hi, hj]
  simp only [RCLike.inner_apply]
  rw [← spectralCharacter_neg, ← spectralCharacter_add]
  congr 2

end SpectralCovarianceData

/-- A certificate that the spectral measure is locally dominated by `M` times normalized Haar
measure on the open angular ball of radius `δ` around frequency zero.

The field `bound` is deliberately stated for every measurable subset.  Thus it can be checked
without supplying a density or a Radon--Nikodym derivative. -/
structure LocalSpectralDensityBound (d : SpectralCovarianceData) where
  /-- Radius of the certified low-frequency arc. -/
  δ : ℝ
  /-- Certified local density ceiling relative to normalized Haar measure. -/
  M : ℝ
  δ_pos : 0 < δ
  M_nonneg : 0 ≤ M
  bound : ∀ S : Set FrequencyTorus, MeasurableSet S → S ⊆ ball 0 δ →
    (d.F : Measure FrequencyTorus) S ≤
      ENNReal.ofReal M * AddCircle.haarAddCircle S

namespace LocalSpectralDensityBound

variable {d : SpectralCovarianceData} (h : LocalSpectralDensityBound d)

/-- Measure-order form of the local certificate. -/
theorem restrict_le :
    (d.F : Measure FrequencyTorus).restrict (ball 0 h.δ) ≤
      ENNReal.ofReal h.M • AddCircle.haarAddCircle := by
  refine Measure.le_iff.2 fun S hS => ?_
  rw [Measure.restrict_apply hS]
  change (d.F : Measure FrequencyTorus) (S ∩ ball 0 h.δ) ≤
    ENNReal.ofReal h.M * AddCircle.haarAddCircle S
  refine (h.bound (S ∩ ball 0 h.δ) (hS.inter measurableSet_ball) inter_subset_right).trans ?_
  gcongr
  exact inter_subset_left

end LocalSpectralDensityBound

/-- Squared modulus of the equal-weight Fourier window.  This is the Fejér kernel divided by
`n`; at `n = 0` the field convention makes it identically zero. -/
def fejerLike (n : ℕ) (ω : FrequencyTorus) : ℝ :=
  ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ^ 2 / (n : ℝ) ^ 2

theorem continuous_fejerLike (n : ℕ) : Continuous (fejerLike n) := by
  unfold fejerLike
  fun_prop

theorem fejerLike_nonneg (n : ℕ) (ω : FrequencyTorus) : 0 ≤ fejerLike n ω := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The normalized window is bounded by one at every frequency. -/
theorem fejerLike_le_one (n : ℕ) (ω : FrequencyTorus) : fejerLike n ω ≤ 1 := by
  by_cases hn : n = 0
  · simp [fejerLike, hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm : ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ≤ (n : ℝ) := by
    calc
      ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ≤
          ∑ k ∈ Finset.range n, ‖spectralCharacter (k : ℤ) ω‖ :=
        norm_sum_le _ _
      _ = (n : ℝ) := by simp
  have hsquare : ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ^ 2 ≤
      (n : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω)]
  rw [fejerLike]
  exact (div_le_one (sq_pos_of_pos hnpos)).2 hsquare

theorem spectralCharacter_nat_eq_pow (k : ℕ) (ω : FrequencyTorus) :
    spectralCharacter (k : ℤ) ω = (spectralCharacter 1 ω) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.cast_succ, spectralCharacter_add, ih]
      exact (pow_succ _ _).symm

/-- Chord length controls angular distance on `ℝ / (2πℤ)`. -/
theorem two_div_pi_mul_norm_le_chord (ω : FrequencyTorus) :
    2 / Real.pi * ‖ω‖ ≤ ‖spectralCharacter 1 ω - 1‖ := by
  let x := centeredAngle ω
  have hx : |x / 2| ≤ Real.pi / 2 := by
    have hmem := centeredAngle_mem ω
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_le.2 ⟨hmem.1.le, hmem.2⟩) (by norm_num)
  have hsin := Real.mul_abs_le_abs_sin hx
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
  rw [spectralCharacter_one_eq_exp_centeredAngle,
    Complex.norm_exp_I_mul_ofReal_sub_one, norm_eq_abs_centeredAngle]
  change 2 / Real.pi * |x| ≤ |2 * Real.sin (x / 2)|
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- A geometric window sum is controlled by inverse angular distance. -/
theorem norm_windowSum_le_pi_div_norm (n : ℕ) (ω : FrequencyTorus) (hω : 0 < ‖ω‖) :
    ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ≤ Real.pi / ‖ω‖ := by
  let z := spectralCharacter 1 ω
  have hz : ‖z‖ = 1 := norm_spectralCharacter 1 ω
  have hgeom :
      (∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω) * (z - 1) = z ^ n - 1 := by
    simpa [z, spectralCharacter_nat_eq_pow] using geom_sum_mul z n
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [hz]
  have hprod :
      ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hnum
  have hchord : 2 / Real.pi * ‖ω‖ ≤ ‖z - 1‖ :=
    two_div_pi_mul_norm_le_chord ω
  have hsmall :
      ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ *
          (2 / Real.pi * ‖ω‖) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hchord (norm_nonneg _)).trans hprod
  have hden : 0 < 2 / Real.pi * ‖ω‖ := mul_pos (div_pos zero_lt_two Real.pi_pos) hω
  apply (le_div_iff₀ hω).2
  calc
    ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ * ‖ω‖ =
        (Real.pi / 2) *
          (‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ *
            (2 / Real.pi * ‖ω‖)) := by field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * 2 := by gcongr
    _ = Real.pi := by ring

/-- Off zero, the Fejér-like kernel has the explicit inverse-square tail `π²/(n²‖ω‖²)`. -/
theorem fejerLike_le_pi_sq_div (n : ℕ) (ω : FrequencyTorus) (hω : 0 < ‖ω‖) :
    fejerLike n ω ≤ Real.pi ^ 2 / ((n : ℝ) ^ 2 * ‖ω‖ ^ 2) := by
  by_cases hn : n = 0
  · simp [fejerLike, hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsum := norm_windowSum_le_pi_div_norm n ω hω
  have hsquare :
      ‖∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω‖ ^ 2 ≤
        (Real.pi / ‖ω‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range n, spectralCharacter (k : ℤ) ω),
      div_nonneg Real.pi_pos.le hω.le]
  rw [fejerLike]
  calc
    _ ≤ (Real.pi / ‖ω‖) ^ 2 / (n : ℝ) ^ 2 := by gcongr
    _ = Real.pi ^ 2 / ((n : ℝ) ^ 2 * ‖ω‖ ^ 2) := by
      field_simp [hω.ne', hnpos.ne']

/-- Combined pointwise envelope used by the low/high-frequency split. -/
theorem fejerLike_le_min (n : ℕ) (ω : FrequencyTorus) (hω : 0 < ‖ω‖) :
    fejerLike n ω ≤
      min 1 (Real.pi ^ 2 / ((n : ℝ) ^ 2 * ‖ω‖ ^ 2)) := by
  exact le_min (fejerLike_le_one n ω) (fejerLike_le_pi_sq_div n ω hω)

private theorem fejerLike_integrable (F : FiniteMeasure FrequencyTorus) (n : ℕ) :
    Integrable (fejerLike n) (F : Measure FrequencyTorus) := by
  apply Integrable.of_bound (continuous_fejerLike n).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerLike_nonneg n ω)]
    exact fejerLike_le_one n ω

private theorem fejerLike_integrable_haar (n : ℕ) :
    Integrable (fejerLike n) AddCircle.haarAddCircle := by
  apply Integrable.of_bound (continuous_fejerLike n).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerLike_nonneg n ω)]
    exact fejerLike_le_one n ω

/-- Complex expansion of the normalized Fejér-like kernel into its two Fourier indices. -/
theorem ofReal_fejerLike_eq_doubleSum (n : ℕ) (ω : FrequencyTorus) :
    (fejerLike n ω : ℂ) =
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        spectralCharacter ((j : ℤ) - (k : ℤ)) ω) / (n : ℂ) ^ 2 := by
  unfold fejerLike
  push_cast
  rw [← Complex.mul_conj']
  simp_rw [map_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply congrArg (fun z : ℂ => z / (n : ℂ) ^ 2)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [sub_eq_add_neg, spectralCharacter_add, spectralCharacter_neg]

/-- Real form of the two-index Fourier expansion. -/
theorem fejerLike_eq_doubleSum_re (n : ℕ) (ω : FrequencyTorus) :
    fejerLike n ω =
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re) / (n : ℝ) ^ 2 := by
  have h := congrArg Complex.re (ofReal_fejerLike_eq_doubleSum n ω)
  simp only [Complex.ofReal_re] at h
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow] at h
  rw [Complex.div_ofReal_re] at h
  simpa only [Complex.re_sum] using h

private theorem spectralCharacter_integrable_haar (j : ℤ) :
    Integrable (spectralCharacter j) AddCircle.haarAddCircle := by
  apply Integrable.of_bound (spectralCharacter j).continuous.aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simp

/-- Orthogonality against the constant character for normalized Haar measure. -/
theorem integral_spectralCharacter_haar (j : ℤ) :
    ∫ ω : FrequencyTorus, spectralCharacter j ω ∂AddCircle.haarAddCircle =
      if j = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (orthonormal_fourier (T := 2 * Real.pi))) (0 : ℤ) j
  rw [ContinuousMap.inner_toLp] at h
  simpa [spectralCharacter, RCLike.inner_apply, eq_comm] using h

/-- The normalized Haar integral of `fejerLike n` is `1/n` (with value zero at `n = 0`). -/
theorem integral_fejerLike_haar (n : ℕ) :
    ∫ ω : FrequencyTorus, fejerLike n ω ∂AddCircle.haarAddCircle = (n : ℝ)⁻¹ := by
  have hchar (j k : ℕ) :
      Integrable (fun ω : FrequencyTorus =>
        (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re)
        AddCircle.haarAddCircle :=
    (spectralCharacter_integrable_haar _).re
  rw [integral_congr_ae (ae_of_all _ fun ω => fejerLike_eq_doubleSum_re n ω)]
  rw [integral_div]
  rw [integral_finset_sum]
  · simp_rw [integral_finset_sum (μ := AddCircle.haarAddCircle)
      (Finset.range n) (fun k hk => hchar _ k)]
    have hint (m : ℤ) :
        ∫ ω : FrequencyTorus, (spectralCharacter m ω).re ∂AddCircle.haarAddCircle =
          if m = 0 then 1 else 0 := by
      calc
        _ = (∫ ω : FrequencyTorus, spectralCharacter m ω
              ∂AddCircle.haarAddCircle).re := by
            simpa using integral_re (spectralCharacter_integrable_haar m)
        _ = (if m = 0 then (1 : ℂ) else 0).re :=
          congrArg Complex.re (integral_spectralCharacter_haar m)
        _ = if m = 0 then 1 else 0 := by split <;> simp
    simp_rw [hint]
    simp_rw [sub_eq_zero, Int.ofNat_inj]
    have hcount :
        (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          if j = k then (1 : ℝ) else 0) = n := by
      calc
        _ = ∑ j ∈ Finset.range n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hj]
        _ = n := by simp
    rw [hcount]
    by_cases hn : n = 0
    · simp [hn]
    · field_simp
  · intro j hj
    exact integrable_finset_sum _ fun k hk => hchar j k

/-- Real quadratic form for the variance of an equal-weight window of length `n`.

Because `C` is complex-valued, the definition records the realification explicitly.  Hermitian
symmetry (or, equivalently, the spectral identity below) shows that this loses no information from
the double sum. -/
def windowQuadratic (d : SpectralCovarianceData) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
    d.C ((j : ℤ) - (k : ℤ))).re / (n : ℝ) ^ 2

/-- The window quadratic form is exactly the integral of the normalized Fejér-like kernel. -/
theorem windowQuadratic_eq_integral (d : SpectralCovarianceData) (n : ℕ) :
    windowQuadratic d n =
      ∫ ω, fejerLike n ω ∂(d.F : Measure FrequencyTorus) := by
  have hchar (j k : ℕ) :
      Integrable (fun ω : FrequencyTorus =>
        (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re) (d.F : Measure FrequencyTorus) :=
    (spectralCharacter_integrable d.F _).re
  have hintegral_re (j k : ℕ) :
      (∫ ω : FrequencyTorus, spectralCharacter ((j : ℤ) - (k : ℤ)) ω
          ∂(d.F : Measure FrequencyTorus)).re =
        ∫ ω : FrequencyTorus, (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re
          ∂(d.F : Measure FrequencyTorus) :=
    (integral_re (spectralCharacter_integrable d.F _)).symm
  have hsum :
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          ∫ ω, (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re
            ∂(d.F : Measure FrequencyTorus)) =
        ∫ ω, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          (spectralCharacter ((j : ℤ) - (k : ℤ)) ω).re
            ∂(d.F : Measure FrequencyTorus) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum]
      exact fun k hk => hchar j k
    · intro j hj
      exact integrable_finset_sum _ fun k hk => hchar j k
  unfold windowQuadratic
  simp_rw [Complex.re_sum, d.repr]
  simp_rw [hintegral_re]
  rw [hsum, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with ω
  have h := congrArg Complex.re (ofReal_fejerLike_eq_doubleSum n ω)
  simp only [Complex.ofReal_re] at h
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow] at h
  rw [Complex.div_ofReal_re] at h
  simpa only [Complex.re_sum] using h.symm

/-- Complex form of the same spectral identity, before realification of the covariance sum. -/
theorem doubleSum_div_eq_integral (d : SpectralCovarianceData) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      d.C ((j : ℤ) - (k : ℤ))) / (n : ℂ) ^ 2 =
        ∫ ω, (fejerLike n ω : ℂ) ∂(d.F : Measure FrequencyTorus) := by
  have hchar (j k : ℕ) : Integrable
      (spectralCharacter ((j : ℤ) - (k : ℤ))) (d.F : Measure FrequencyTorus) :=
    spectralCharacter_integrable d.F _
  have hsum :
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          ∫ ω, spectralCharacter ((j : ℤ) - (k : ℤ)) ω
            ∂(d.F : Measure FrequencyTorus)) =
        ∫ ω, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          spectralCharacter ((j : ℤ) - (k : ℤ)) ω
            ∂(d.F : Measure FrequencyTorus) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum]
      exact fun k hk => hchar j k
    · intro j hj
      exact integrable_finset_sum _ fun k hk => hchar j k
  simp_rw [d.repr]
  rw [hsum]
  calc
    _ = ∫ ω, (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          spectralCharacter ((j : ℤ) - (k : ℤ)) ω) / (n : ℂ) ^ 2
          ∂(d.F : Measure FrequencyTorus) :=
      (integral_div (μ := (d.F : Measure FrequencyTorus)) ((n : ℂ) ^ 2)
        (fun ω => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          spectralCharacter ((j : ℤ) - (k : ℤ)) ω)).symm
    _ = _ := integral_congr_ae
      (ae_of_all _ fun ω => (ofReal_fejerLike_eq_doubleSum n ω).symm)

/-- The real definition of `windowQuadratic` is exactly the complex expression
`n⁻² ∑_{j,k<n} C (j-k)` from the paper contract. -/
theorem ofReal_windowQuadratic_eq_doubleSum (d : SpectralCovarianceData) (n : ℕ) :
    (windowQuadratic d n : ℂ) =
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        d.C ((j : ℤ) - (k : ℤ))) / (n : ℂ) ^ 2 := by
  rw [windowQuadratic_eq_integral, ← integral_complex_ofReal]
  exact (doubleSum_div_eq_integral d n).symm

namespace LocalSpectralDensityBound

variable {d : SpectralCovarianceData} (h : LocalSpectralDensityBound d)

/-- The locally dominated part costs at most `M/n`.  The constant `1` is exact because the
normalized Haar integral of `fejerLike` is `1/n`. -/
theorem integral_fejerLike_ball_le (n : ℕ) :
    ∫ ω, fejerLike n ω
        ∂((d.F : Measure FrequencyTorus).restrict (ball 0 h.δ)) ≤ h.M / (n : ℝ) := by
  have hscaled : Integrable (fejerLike n)
      (ENNReal.ofReal h.M • AddCircle.haarAddCircle) :=
    (fejerLike_integrable_haar n).smul_measure ENNReal.ofReal_ne_top
  have hmono := integral_mono_measure h.restrict_le
    (ae_of_all _ fun ω => fejerLike_nonneg n ω) hscaled
  rw [integral_smul_measure, ENNReal.toReal_ofReal h.M_nonneg,
    integral_fejerLike_haar] at hmono
  simpa [div_eq_mul_inv] using hmono

/-- The complement of the certified arc costs at most
`π² F(univ)/(n² δ²)`. -/
theorem integral_fejerLike_ball_compl_le (n : ℕ) :
    ∫ ω, fejerLike n ω
        ∂((d.F : Measure FrequencyTorus).restrict (ball 0 h.δ)ᶜ) ≤
      Real.pi ^ 2 * (d.F.mass : ℝ) / ((n : ℝ) ^ 2 * h.δ ^ 2) := by
  by_cases hn : n = 0
  · simp [fejerLike, hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let A : ℝ := Real.pi ^ 2 / ((n : ℝ) ^ 2 * h.δ ^ 2)
  have hA : 0 ≤ A := by
    exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpoint : ∀ᵐ ω ∂((d.F : Measure FrequencyTorus).restrict (ball 0 h.δ)ᶜ),
      ‖fejerLike n ω‖ ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ω hωmem
    have hδnorm : h.δ ≤ ‖ω‖ := by
      rw [mem_compl_iff, mem_ball, dist_zero_right] at hωmem
      exact le_of_not_gt hωmem
    have hnorm : 0 < ‖ω‖ := h.δ_pos.trans_le hδnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerLike_nonneg n ω)]
    calc
      fejerLike n ω ≤ Real.pi ^ 2 / ((n : ℝ) ^ 2 * ‖ω‖ ^ 2) :=
        fejerLike_le_pi_sq_div n ω hnorm
      _ ≤ A := by
        dsimp [A]
        have hsquare : h.δ ^ 2 ≤ ‖ω‖ ^ 2 :=
          (sq_le_sq₀ h.δ_pos.le (norm_nonneg _)).2 hδnorm
        apply (div_le_div_iff₀
          (mul_pos (sq_pos_of_pos hnpos) (sq_pos_of_pos hnorm))
          (mul_pos (sq_pos_of_pos hnpos) (sq_pos_of_pos h.δ_pos))).2
        gcongr
  have hnormIntegral := norm_integral_le_of_norm_le_const hpoint
  have hintegral_nonneg :
      0 ≤ ∫ ω, fejerLike n ω
        ∂((d.F : Measure FrequencyTorus).restrict (ball 0 h.δ)ᶜ) :=
    integral_nonneg_of_ae (ae_of_all _ fun ω => fejerLike_nonneg n ω)
  rw [Real.norm_eq_abs, abs_of_nonneg hintegral_nonneg,
    measureReal_restrict_apply_univ] at hnormIntegral
  calc
    _ ≤ A * (d.F : Measure FrequencyTorus).real ((ball 0 h.δ)ᶜ) := hnormIntegral
    _ ≤ A * (d.F : Measure FrequencyTorus).real Set.univ := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono (μ := (d.F : Measure FrequencyTorus)) (subset_univ _)) hA
    _ = Real.pi ^ 2 * (d.F.mass : ℝ) / ((n : ℝ) ^ 2 * h.δ ^ 2) := by
      rw [FiniteMeasure.measureReal_eq_coe_coeFn]
      dsimp [A, FiniteMeasure.mass]
      field_simp [hnpos.ne', h.δ_pos.ne']

/-- Certified finite-window bound with explicit universal constants
`c₁ = 1` and `c₂ = π²`. -/
theorem windowQuadratic_le (n : ℕ) :
    windowQuadratic d n ≤
      h.M / (n : ℝ) +
        Real.pi ^ 2 * (d.F.mass : ℝ) / ((n : ℝ) ^ 2 * h.δ ^ 2) := by
  by_cases hn : n = 0
  · simp [windowQuadratic, hn]
  rw [windowQuadratic_eq_integral,
    ← integral_add_compl measurableSet_ball (fejerLike_integrable d.F n)]
  exact add_le_add (h.integral_fejerLike_ball_le n) (h.integral_fejerLike_ball_compl_le n)

end LocalSpectralDensityBound

end

end Spectral
end Analysis
end Quantum
