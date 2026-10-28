/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.UpperHalfPlane.PoissonBoundary.FiniteBoundaryAPI

/-!
# Uniqueness core for upper-half-plane Poisson boundary data

Source correspondence: the Nevanlinna representation uniqueness stage, covering
slope recovery, finite-measure reduction, producer interfaces, Cauchy
approximate identities, and the Cauchy-to-Poisson-to-Stieltjes core producers.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open MeasureTheory Set
open Filter
open scoped UpperHalfPlane Topology Manifold ContDiff
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Poisson boundary uniqueness as Nevanlinna uniqueness -/

namespace PoissonBoundaryMeasureData

/-- The weighted integrability hypothesis gives integrability of the real weight. -/
theorem integrable_nevanlinnaWeight_toReal
    {u : ℂ → ℝ} (data : PoissonBoundaryMeasureData u) :
    Integrable (fun t : ℝ => (nevanlinnaWeight t).toReal) data.boundaryMeasure := by
  exact MeasureTheory.integrable_toReal_of_lintegral_ne_top
    measurable_nevanlinnaWeight.aemeasurable data.weight_lintegral_lt_top.ne

/--
On the imaginary axis, the Poisson kernel normalized by the height is the
resolvent-type kernel used to read the slope at infinity.
-/
theorem upperHalfPlanePoissonKernel_zero_div_nat_succ (t : ℝ) (n : ℕ) :
    upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ) =
      1 / (t ^ (2 : ℕ) + (n + 1 : ℝ) ^ (2 : ℕ)) := by
  unfold upperHalfPlanePoissonKernel
  have hy : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hy]
  ring

/-- The normalized imaginary-axis Poisson kernel is dominated by the Nevanlinna weight. -/
theorem poissonKernel_zero_div_nat_succ_bound (t : ℝ) (n : ℕ) :
    ‖upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ)‖ ≤
      (nevanlinnaWeight t).toReal := by
  have hkernel := upperHalfPlanePoissonKernel_zero_div_nat_succ t n
  have hweight : (nevanlinnaWeight t).toReal = (1 + t ^ (2 : ℕ))⁻¹ := by
    rw [nevanlinnaWeight, ENNReal.toReal_ofReal]
    positivity
  rw [hkernel, hweight]
  have hnonneg : 0 ≤ 1 / (t ^ (2 : ℕ) + (n + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hle_y : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (2 : ℕ) := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [sq_nonneg ((n + 1 : ℝ) - 1)]
  have hle : 1 + t ^ (2 : ℕ) ≤ t ^ (2 : ℕ) + (n + 1 : ℝ) ^ (2 : ℕ) := by
    nlinarith
  simpa [one_div] using
    one_div_le_one_div_of_le (by positivity : 0 < 1 + t ^ (2 : ℕ)) hle

/-- The normalized imaginary-axis Poisson kernel tends pointwise to zero. -/
theorem tendsto_poissonKernel_zero_div_nat_succ (t : ℝ) :
    Tendsto (fun n : ℕ =>
      upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hy : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hnat
  have hy2mul :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
        atTop atTop :=
    hy.atTop_mul_atTop₀ hy
  have hy2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))
      atTop atTop := by
    simpa [pow_two] using hy2mul
  have hden :
      Tendsto (fun n : ℕ => t ^ (2 : ℕ) + ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))
        atTop atTop :=
    tendsto_const_nhds.add_atTop hy2
  have hlim :
      Tendsto (fun n : ℕ =>
        (1 : ℝ) / (t ^ (2 : ℕ) + ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)))
        atTop (𝓝 0) :=
    hden.const_div_atTop 1
  simpa [upperHalfPlanePoissonKernel_zero_div_nat_succ] using hlim

/-- The normalized imaginary-axis Poisson integral tends to zero. -/
theorem tendsto_integral_poissonKernel_zero_div_nat_succ
    {u : ℂ → ℝ} (data : PoissonBoundaryMeasureData u) :
    Tendsto (fun n : ℕ =>
      ∫ t : ℝ,
        upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ)
          ∂data.boundaryMeasure)
      atTop (𝓝 0) := by
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := data.boundaryMeasure)
    (F := fun (n : ℕ) (t : ℝ) =>
      upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ))
    (f := fun _t : ℝ => (0 : ℝ))
    (fun t : ℝ => (nevanlinnaWeight t).toReal)
    (by
      intro n
      exact
        ((measurable_upperHalfPlanePoissonKernel 0 (n + 1 : ℝ)).div_const _).aestronglyMeasurable)
    (integrable_nevanlinnaWeight_toReal data)
    (by
      intro n
      exact ae_of_all _ fun t => poissonKernel_zero_div_nat_succ_bound t n)
    (by
      exact ae_of_all _ fun t => tendsto_poissonKernel_zero_div_nat_succ t)
  simpa using hdc

/-- The normalized values on the imaginary axis converge to the slope. -/
theorem tendsto_axis_value_div_nat_succ
    {u : ℂ → ℝ} (data : PoissonBoundaryMeasureData u) :
    Tendsto (fun n : ℕ =>
      u (((0 : ℝ) : ℂ) + ((n + 1 : ℝ) : ℂ) * Complex.I) / (n + 1 : ℝ))
      atTop (𝓝 (data.slope : ℝ)) := by
  have haxis : ∀ n : ℕ,
      u (((0 : ℝ) : ℂ) + ((n + 1 : ℝ) : ℂ) * Complex.I) / (n + 1 : ℝ) =
        (data.slope : ℝ) +
          ∫ t : ℝ,
            upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ)
              ∂data.boundaryMeasure := by
    intro n
    have hy_pos : 0 < (n + 1 : ℝ) := by positivity
    have hy_ne : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [data.poisson_formula 0 (n + 1 : ℝ) hy_pos]
    calc
      ((data.slope : ℝ) * (n + 1 : ℝ) +
            ∫ t : ℝ, upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ)
              ∂data.boundaryMeasure) /
          (n + 1 : ℝ) =
          (data.slope : ℝ) +
            (∫ t : ℝ, upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ)
              ∂data.boundaryMeasure) / (n + 1 : ℝ) := by
            field_simp [hy_ne]
      _ = (data.slope : ℝ) +
          ∫ t : ℝ,
            upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ)
              ∂data.boundaryMeasure := by
            rw [MeasureTheory.integral_div]
  have hlim := (tendsto_const_nhds (x := (data.slope : ℝ))).add
    (tendsto_integral_poissonKernel_zero_div_nat_succ data)
  have hlim' :
      Tendsto (fun n : ℕ =>
        (data.slope : ℝ) +
          ∫ t : ℝ,
            upperHalfPlanePoissonKernel t 0 (n + 1 : ℝ) / (n + 1 : ℝ)
              ∂data.boundaryMeasure) atTop (𝓝 (data.slope : ℝ)) := by
    simpa using hlim
  exact hlim'.congr' (Eventually.of_forall fun n => (haxis n).symm)

/-- Two Poisson boundary data for the same function have the same slope. -/
theorem slope_eq_of_same_function
    {u : ℂ → ℝ} (data₁ data₂ : PoissonBoundaryMeasureData u) :
    data₁.slope = data₂.slope := by
  apply NNReal.coe_injective
  exact tendsto_nhds_unique
    (tendsto_axis_value_div_nat_succ data₁)
    (tendsto_axis_value_div_nat_succ data₂)

/-- Two Poisson boundary data for the same function have the same Poisson formula value. -/
theorem poisson_formula_eq_of_same_function
    {u : ℂ → ℝ} (data₁ data₂ : PoissonBoundaryMeasureData u)
    (x y : ℝ) (hy : 0 < y) :
    (data₁.slope : ℝ) * y +
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure =
      (data₂.slope : ℝ) * y +
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure := by
  rw [← data₁.poisson_formula x y hy, ← data₂.poisson_formula x y hy]

/--
Once the slope terms agree, equality of the two Poisson formulas gives equality
of the Poisson-kernel integrals.
-/
theorem poissonKernel_integral_eq_of_slope_eq
    {u : ℂ → ℝ} {data₁ data₂ : PoissonBoundaryMeasureData u}
    (hslope : data₁.slope = data₂.slope) :
    ∀ (x y : ℝ), 0 < y →
      (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure) =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure := by
  intro x y hy
  have h := poisson_formula_eq_of_same_function data₁ data₂ x y hy
  rw [hslope] at h
  exact add_left_cancel h

/--
Equality of the finite measures obtained by weighting two Poisson boundary
measures recovers equality of the original boundary measures.
-/
theorem boundaryMeasure_eq_of_finiteBoundaryMeasure_eq
    {u : ℂ → ℝ} {data₁ data₂ : PoissonBoundaryMeasureData u}
    (hν :
      nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
          data₁.weight_lintegral_lt_top =
        nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
          data₂.weight_lintegral_lt_top) :
    data₁.boundaryMeasure = data₂.boundaryMeasure := by
  calc
    data₁.boundaryMeasure =
        nevanlinnaWeightedMeasure
          (nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
            data₁.weight_lintegral_lt_top) := by
          exact (nevanlinnaWeightedMeasure_nevanlinnaFiniteMeasureOfWeighted
            data₁.boundaryMeasure data₁.weight_lintegral_lt_top).symm
    _ = nevanlinnaWeightedMeasure
          (nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
            data₂.weight_lintegral_lt_top) := by
          rw [hν]
    _ = data₂.boundaryMeasure :=
          nevanlinnaWeightedMeasure_nevanlinnaFiniteMeasureOfWeighted
            data₂.boundaryMeasure data₂.weight_lintegral_lt_top

/--
The Poisson integral attached to a boundary datum can be read as the
finite-boundary Poisson kernel integrated against the finiteized measure.
-/
theorem poissonKernel_integral_eq_finiteBoundaryPoissonKernel_integral
    {u : ℂ → ℝ} (data : PoissonBoundaryMeasureData u) (x y : ℝ) :
    (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data.boundaryMeasure) =
      ∫ t : ℝ, finiteBoundaryPoissonKernel t x y
        ∂(nevanlinnaFiniteMeasureOfWeighted data.boundaryMeasure
          data.weight_lintegral_lt_top : Measure ℝ) := by
  let ν :=
    nevanlinnaFiniteMeasureOfWeighted data.boundaryMeasure
      data.weight_lintegral_lt_top
  have hμ : nevanlinnaWeightedMeasure ν = data.boundaryMeasure := by
    exact nevanlinnaWeightedMeasure_nevanlinnaFiniteMeasureOfWeighted
      data.boundaryMeasure data.weight_lintegral_lt_top
  calc
    (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data.boundaryMeasure) =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν := by
          rw [hμ]
    _ = ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν : Measure ℝ) :=
          poissonKernel_integral_nevanlinnaWeightedMeasure_eq_finiteBoundaryPoissonKernel
            ν x y

/--
Equality of all original Poisson-kernel integrals gives equality of all
finite-boundary Poisson-kernel integrals.
-/
theorem finiteBoundaryPoissonKernel_integral_eq_of_poissonKernel_integral_eq
    {u : ℂ → ℝ} {data₁ data₂ : PoissonBoundaryMeasureData u}
    (hP : ∀ (x y : ℝ), 0 < y →
      (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure) =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure) :
    ∀ (x y : ℝ), 0 < y →
      (∫ t : ℝ, finiteBoundaryPoissonKernel t x y
          ∂(nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
            data₁.weight_lintegral_lt_top : Measure ℝ)) =
        ∫ t : ℝ, finiteBoundaryPoissonKernel t x y
          ∂(nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
            data₂.weight_lintegral_lt_top : Measure ℝ) := by
  intro x y hy
  calc
    (∫ t : ℝ, finiteBoundaryPoissonKernel t x y
        ∂(nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
          data₁.weight_lintegral_lt_top : Measure ℝ)) =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure := by
          exact (poissonKernel_integral_eq_finiteBoundaryPoissonKernel_integral
            data₁ x y).symm
    _ = ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure :=
          hP x y hy
    _ = ∫ t : ℝ, finiteBoundaryPoissonKernel t x y
        ∂(nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
          data₂.weight_lintegral_lt_top : Measure ℝ) :=
          poissonKernel_integral_eq_finiteBoundaryPoissonKernel_integral
            data₂ x y

end PoissonBoundaryMeasureData

/-! ### Finite-measure uniqueness producer interfaces -/

/--
Producer interface for the Poisson/Stieltjes uniqueness core.

The field isolates the measure-extensionality step: equality of all
upper-half-plane Poisson-kernel integrals determines the boundary measure.  The
uniqueness theorem built through these interfaces is `NevanlinnaRep.unique`
(`UniquenessLift.lean`).
-/
structure UpperHalfPlanePoissonStieltjesUniquenessProducer where
  boundaryMeasure_eq_of_poissonKernel_integrals_eq :
    ∀ {u : ℂ → ℝ} (data₁ data₂ : PoissonBoundaryMeasureData u),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure) =
          ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure) →
        data₁.boundaryMeasure = data₂.boundaryMeasure

/--
Producer interface for the finite-measure core of Poisson boundary uniqueness.
It only has to identify the finite measures obtained by weighting the boundary
measures by `nevanlinnaWeight`.
-/
structure UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer where
  finiteBoundaryMeasure_eq_of_poissonKernel_integrals_eq :
    ∀ {u : ℂ → ℝ} (data₁ data₂ : PoissonBoundaryMeasureData u),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₁.boundaryMeasure) =
          ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂data₂.boundaryMeasure) →
        nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
          data₁.weight_lintegral_lt_top =
        nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
          data₂.weight_lintegral_lt_top

/--
Producer interface for the finite-measure kernel uniqueness core.  It isolates
the measure-extensionality theorem after the boundary measure has been
finiteized.
-/
structure UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer where
  finiteMeasure_eq_of_finiteBoundaryKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₂ : Measure ℝ)) →
        ν₁ = ν₂

/--
Finite measures on `ℝ` are equal once all bounded continuous test-function
integrals agree.
-/
theorem finiteMeasure_eq_of_boundedContinuous_integral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (h : ∀ g : BoundedContinuousFunction ℝ ℝ,
      (∫ t : ℝ, g t ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, g t ∂(ν₂ : Measure ℝ)) :
    ν₁ = ν₂ := by
  exact FiniteMeasure.ext_of_forall_integral_eq h

/--
Finite measures on `ℝ` are equal once their characteristic functions agree.
-/
theorem finiteMeasure_eq_of_charFun_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (h : MeasureTheory.charFun (ν₁ : Measure ℝ) =
      MeasureTheory.charFun (ν₂ : Measure ℝ)) :
    ν₁ = ν₂ := by
  apply FiniteMeasure.toMeasure_injective
  exact Measure.ext_of_charFun h

/--
Equality of all real Fourier exponential test integrals gives equality of the
characteristic functions.
-/
theorem charFun_eq_of_real_fourierIntegral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (h : ∀ ξ : ℝ,
      (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I) ∂(ν₂ : Measure ℝ)) :
    MeasureTheory.charFun (ν₁ : Measure ℝ) =
      MeasureTheory.charFun (ν₂ : Measure ℝ) := by
  funext ξ
  simpa [MeasureTheory.charFun_apply_real, mul_assoc] using h ξ

/--
Producer interface for the bounded-continuous-test-function uniqueness core.
It isolates the approximation or Poisson/Stieltjes inversion step turning
finite-boundary Poisson-kernel integral equality into equality against all
bounded continuous functions.
-/
structure UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer where
  boundedContinuous_integral_eq_of_finiteBoundaryKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₂ : Measure ℝ)) →
        ∀ g : BoundedContinuousFunction ℝ ℝ,
          (∫ t : ℝ, g t ∂(ν₁ : Measure ℝ)) =
            ∫ t : ℝ, g t ∂(ν₂ : Measure ℝ)

/--
Producer interface for the characteristic-function uniqueness core.  It
isolates the Fourier/Stieltjes inversion step turning finite-boundary
Poisson-kernel integral equality into equality of characteristic functions.
-/
structure UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer where
  charFun_eq_of_finiteBoundaryKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₂ : Measure ℝ)) →
        MeasureTheory.charFun (ν₁ : Measure ℝ) =
          MeasureTheory.charFun (ν₂ : Measure ℝ)

/--
Producer interface for the Fourier-exponential uniqueness core.  It isolates
the step turning finite-boundary Poisson-kernel integral equality into equality
against every real Fourier exponential test function.
-/
structure UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer where
  fourierIntegral_eq_of_finiteBoundaryKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ (x y : ℝ), 0 < y →
        (∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν₂ : Measure ℝ)) →
        ∀ ξ : ℝ,
          (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₁ : Measure ℝ)) =
            ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₂ : Measure ℝ)

/--
Producer interface for the Nevanlinna-transform uniqueness core.  It isolates
the inversion step turning equality of imaginary parts of all
finite-measure Nevanlinna transforms into equality against every real Fourier
exponential test function.
-/
structure UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer where
  fourierIntegral_eq_of_nevanlinnaKernel_integral_im_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ z : ℍ,
        (∫ t : ℝ, nevanlinnaKernel t z ∂(ν₁ : Measure ℝ)).im =
          (∫ t : ℝ, nevanlinnaKernel t z ∂(ν₂ : Measure ℝ)).im) →
        ∀ ξ : ℝ,
          (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₁ : Measure ℝ)) =
            ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₂ : Measure ℝ)

/--
Producer interface for the Stieltjes/Fourier uniqueness core after
complexifying the Nevanlinna transform.  It starts from equality of the complex
finite-measure Nevanlinna transforms, not just their imaginary parts.
-/
structure UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer where
  fourierIntegral_eq_of_nevanlinnaKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ z : ℍ, nevanlinnaKernelIntegral ν₁ z = nevanlinnaKernelIntegral ν₂ z) →
        ∀ ξ : ℝ,
          (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₁ : Measure ℝ)) =
            ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₂ : Measure ℝ)

/--
Producer interface for the Stieltjes-transform uniqueness core.  The algebraic
bridge from complex Nevanlinna-transform equality to Stieltjes-transform
equality is proved in Lean; the inversion step is equality of
Fourier test integrals from Stieltjes-transform equality.
-/
structure UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer where
  fourierIntegral_eq_of_stieltjesKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ z : ℍ, z ≠ UpperHalfPlane.I →
        upperHalfPlaneStieltjesKernelIntegral ν₁ z =
          upperHalfPlaneStieltjesKernelIntegral ν₂ z) →
        ∀ ξ : ℝ,
          (∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₁ : Measure ℝ)) =
            ∫ t : ℝ, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)
              ∂(ν₂ : Measure ℝ)

/--
Producer interface for the Stieltjes-transform measure uniqueness core.  This
is the natural target of the Poisson approximate-identity route: first recover
equality of the finite boundary measures, and then obtain Fourier test
integrals by rewriting.
-/
structure UpperHalfPlaneFiniteBoundaryStieltjesMeasureUniquenessProducer where
  finiteMeasure_eq_of_stieltjesKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ z : ℍ, z ≠ UpperHalfPlane.I →
        upperHalfPlaneStieltjesKernelIntegral ν₁ z =
          upperHalfPlaneStieltjesKernelIntegral ν₂ z) →
        ν₁ = ν₂

/--
Producer interface for the Poisson-kernel measure uniqueness core supplied by
the imaginary parts of the Stieltjes transform.
-/
structure UpperHalfPlaneFiniteBoundaryPoissonKernelMeasureUniquenessProducer where
  finiteMeasure_eq_of_poissonKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ z : ℍ, z ≠ UpperHalfPlane.I →
        (∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
            ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
            ∂(ν₂ : Measure ℝ)) →
        ν₁ = ν₂

/--
Producer interface for the Cauchy approximate-identity uniqueness core.  The
kernel equality is restricted to the sequence of positive scales
`stieltjesUniqScale n = 1 / (n + 2)`, which avoids the exceptional point `i`.
-/
structure UpperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer where
  finiteMeasure_eq_of_cauchyKernel_integrals_eq :
    ∀ (ν₁ ν₂ : FiniteMeasure ℝ),
      (∀ (n : ℕ) (x : ℝ),
        (∫ t : ℝ,
            ProbabilityTheory.cauchyPDFReal x
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
            ∂(ν₁ : Measure ℝ)) =
          ∫ t : ℝ,
            ProbabilityTheory.cauchyPDFReal x
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
            ∂(ν₂ : Measure ℝ)) →
        ν₁ = ν₂

/-- The Cauchy density is symmetric in its center and evaluation point. -/
theorem cauchyPDFReal_comm (x t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t =
      ProbabilityTheory.cauchyPDFReal t ⟨ε, hε⟩ x := by
  unfold ProbabilityTheory.cauchyPDFReal
  simp only [NNReal.coe_mk]
  congr 1
  ring_nf

/-- The Cauchy density is nonnegative. -/
theorem cauchyPDFReal_nonneg (x t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t := by
  unfold ProbabilityTheory.cauchyPDFReal
  positivity

/-- The Cauchy average of a bounded continuous `φ` at the scales `1/(n + 2)` converges to `φ(y)`
(Cauchy approximate identity). [simon2019] -/
theorem unitIntervalHerglotz_cauchyAverage_tendsto_stieltjesUniqScale
    (φ : ℝ → ℝ) (y M : ℝ) (hφ_cont : Continuous φ)
    (hM : ∀ x : ℝ, ‖φ x‖ ≤ M) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ,
        φ x * ProbabilityTheory.cauchyPDFReal y
          ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ x)
      atTop (𝓝 (φ y)) := by
  have hbase := unitIntervalHerglotz_cauchyAverage_tendsto φ y M hφ_cont hM
  have hcomp := hbase.comp (tendsto_add_atTop_nat 1)
  change Tendsto
      (fun n : ℕ => ∫ x : ℝ,
        φ x * ProbabilityTheory.cauchyPDFReal y
          ⟨1 / (((n + 1 : ℕ) : ℝ) + 1), by positivity⟩ x)
      atTop (𝓝 (φ y)) at hcomp
  simpa [stieltjesUniqScale, Nat.cast_add, add_assoc, one_div,
    show (1 : ℝ) + 1 = 2 by norm_num] using hcomp

/-! ### Cauchy approximate identity for finite measures -/

/-- The Cauchy density at scale `1/(n + 2)` is jointly continuous in `(center, point)`. -/
theorem continuous_cauchyPDFReal_prod_stieltjesScale (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => ProbabilityTheory.cauchyPDFReal p.1
      ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ p.2) := by
  unfold ProbabilityTheory.cauchyPDFReal
  apply Continuous.mul continuous_const
  apply Continuous.inv₀
  · exact ((((continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)).sub
      continuous_fst).pow 2).add continuous_const)
  · intro p
    have hγpos : 0 < (((⟨stieltjesUniqScale n,
        (stieltjesUniqScale_pos n).le⟩ : ℝ≥0) : ℝ)) := by
      exact stieltjesUniqScale_pos n
    have hγsq : 0 <
        (((⟨stieltjesUniqScale n,
          (stieltjesUniqScale_pos n).le⟩ : ℝ≥0) : ℝ)) ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_pos hγpos]
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg (p.2 - p.1)) hγsq)

/-- The product kernel `g(x) · cauchyPDFReal center (1/(n+2)) x` used in the Cauchy averaging. -/
def stieltjesCauchyAverageKernelProd
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  g p.2 * ProbabilityTheory.cauchyPDFReal p.1
    ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ p.2

/-- The Cauchy average of a bounded continuous function `g` at scale `1/(n + 2)`. -/
def stieltjesCauchyAverage
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, stieltjesCauchyAverageKernelProd g n (t, x)

/-- The Cauchy averaging kernel is integrable in its second variable against Lebesgue measure. -/
theorem stieltjesCauchyAverageKernelProd_integrable_left
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => stieltjesCauchyAverageKernelProd g n (t, x))
      (volume : Measure ℝ) := by
  let γ : ℝ≥0 := ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩
  refine ((ProbabilityTheory.integrable_cauchyPDFReal t (γ := γ)).const_mul ‖g‖).mono'
    ?_ ?_
  · exact (g.continuous.stronglyMeasurable.mul
      (ProbabilityTheory.stronglyMeasurable_cauchyPDFReal t γ)).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    dsimp [stieltjesCauchyAverageKernelProd]
    rw [abs_mul, abs_of_nonneg
      (cauchyPDFReal_nonneg t x (stieltjesUniqScale_pos n).le)]
    simpa [γ, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right
      (BoundedContinuousFunction.norm_coe_le_norm g x)
      (cauchyPDFReal_nonneg t x (stieltjesUniqScale_pos n).le)

/-- The `L¹` norm of the Cauchy averaging kernel is bounded by `‖g‖`. -/
theorem stieltjesCauchyAverageKernelProd_norm_integral_bound
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (t : ℝ) :
    (∫ x : ℝ, ‖stieltjesCauchyAverageKernelProd g n (t, x)‖) ≤ ‖g‖ := by
  let γ : ℝ≥0 := ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩
  have hγ_ne : γ ≠ 0 := by
    exact Subtype.ext_iff.not.mpr (stieltjesUniqScale_pos n).ne'
  calc
    (∫ x : ℝ, ‖stieltjesCauchyAverageKernelProd g n (t, x)‖) ≤
        ∫ x : ℝ, ‖g‖ * ProbabilityTheory.cauchyPDFReal t γ x := by
          refine integral_mono_of_nonneg ?_ ?_ ?_
          · exact ae_of_all _ fun x => norm_nonneg _
          · exact (ProbabilityTheory.integrable_cauchyPDFReal t (γ := γ)).const_mul ‖g‖
          · refine ae_of_all _ fun x => ?_
            dsimp [stieltjesCauchyAverageKernelProd]
            rw [abs_mul, abs_of_nonneg
              (cauchyPDFReal_nonneg t x (stieltjesUniqScale_pos n).le)]
            simpa [γ, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right
              (BoundedContinuousFunction.norm_coe_le_norm g x)
              (cauchyPDFReal_nonneg t x (stieltjesUniqScale_pos n).le)
    _ = ‖g‖ := by
          rw [integral_const_mul]
          simp [γ, ProbabilityTheory.integral_cauchyPDFReal_eq_one t hγ_ne]

/-- The Cauchy average is bounded by `‖g‖`. -/
theorem stieltjesCauchyAverage_bound
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (t : ℝ) :
    ‖stieltjesCauchyAverage g n t‖ ≤ ‖g‖ := by
  calc
    ‖stieltjesCauchyAverage g n t‖ ≤
        ∫ x : ℝ, ‖stieltjesCauchyAverageKernelProd g n (t, x)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ‖g‖ := stieltjesCauchyAverageKernelProd_norm_integral_bound g n t

/-- The Cauchy average of `g` converges pointwise to `g` as the scale shrinks. [simon2019] -/
theorem stieltjesCauchyAverage_tendsto
    (g : BoundedContinuousFunction ℝ ℝ) (t : ℝ) :
    Tendsto (fun n : ℕ => stieltjesCauchyAverage g n t)
      atTop (𝓝 (g t)) := by
  have h := unitIntervalHerglotz_cauchyAverage_tendsto_stieltjesUniqScale
    (fun x : ℝ => g x) t ‖g‖ g.continuous
    (fun x => BoundedContinuousFunction.norm_coe_le_norm g x)
  simpa [stieltjesCauchyAverage, stieltjesCauchyAverageKernelProd] using h

/-- The Cauchy averaging kernel is product-integrable against `ν × volume`. -/
theorem stieltjesCauchyAverageKernelProd_integrable
    (ν : FiniteMeasure ℝ) (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => stieltjesCauchyAverageKernelProd g n p)
      ((ν : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hsm :
      StronglyMeasurable
        (fun p : ℝ × ℝ => stieltjesCauchyAverageKernelProd g n p) := by
    exact ((g.continuous.comp continuous_snd).mul
      (continuous_cauchyPDFReal_prod_stieltjesScale n)).stronglyMeasurable
  rw [integrable_prod_iff hsm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ fun t => stieltjesCauchyAverageKernelProd_integrable_left g n t
  · refine (integrable_const (c := ‖g‖) (μ := (ν : Measure ℝ))).mono' ?_ ?_
    · exact hsm.norm.integral_prod_right'.aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      rw [Real.norm_of_nonneg]
      · exact stieltjesCauchyAverageKernelProd_norm_integral_bound g n t
      · exact integral_nonneg fun x => norm_nonneg _

/-- The integral of the Cauchy average against `ν` converges to the integral of `g` against `ν`.
[simon2019] -/
theorem stieltjesCauchyAverage_integral_tendsto
    (ν : FiniteMeasure ℝ) (g : BoundedContinuousFunction ℝ ℝ) :
    Tendsto
      (fun n : ℕ => ∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν : Measure ℝ))
      atTop (𝓝 (∫ t : ℝ, g t ∂(ν : Measure ℝ))) := by
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (ν : Measure ℝ))
    (F := fun (n : ℕ) (t : ℝ) => stieltjesCauchyAverage g n t)
    (f := fun t : ℝ => g t)
    (fun _t : ℝ => ‖g‖)
    (fun n =>
      (stieltjesCauchyAverageKernelProd_integrable ν g n).integral_prod_left
        |>.aestronglyMeasurable)
    (integrable_const (c := ‖g‖) (μ := (ν : Measure ℝ)))
    (fun n => ae_of_all _ fun t => stieltjesCauchyAverage_bound g n t)
    (ae_of_all _ fun t => stieltjesCauchyAverage_tendsto g t)
  simpa using hdc

/-- Swapping center and point: the `ν`-integral of the averaging kernel equals `g(x)` times the
`ν`-integral of the Cauchy density centered at `x`. -/
theorem stieltjesCauchyAverageKernelProd_integral_center_swap
    (ν : FiniteMeasure ℝ) (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) (x : ℝ) :
    (∫ t : ℝ, stieltjesCauchyAverageKernelProd g n (t, x) ∂(ν : Measure ℝ)) =
      g x * ∫ t : ℝ,
        ProbabilityTheory.cauchyPDFReal x
          ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
        ∂(ν : Measure ℝ) := by
  calc
    (∫ t : ℝ, stieltjesCauchyAverageKernelProd g n (t, x) ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, g x * ProbabilityTheory.cauchyPDFReal x
          ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => by
            simp [stieltjesCauchyAverageKernelProd,
              (cauchyPDFReal_comm x t (stieltjesUniqScale_pos n).le).symm]
    _ = g x * ∫ t : ℝ,
        ProbabilityTheory.cauchyPDFReal x
          ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
        ∂(ν : Measure ℝ) := by
          exact integral_const_mul (r := g x)
            (f := fun t : ℝ => ProbabilityTheory.cauchyPDFReal x
              ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t)

/-- If two finite measures give equal Cauchy-kernel integrals at every scale and center, then they
give equal Cauchy-average integrals for every bounded continuous `g`. -/
theorem stieltjesCauchyAverage_integral_eq_of_cauchyKernel_integrals_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hK : ∀ (n : ℕ) (x : ℝ),
      (∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₂ : Measure ℝ))
    (g : BoundedContinuousFunction ℝ ℝ) (n : ℕ) :
    (∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₁ : Measure ℝ)) =
      ∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₂ : Measure ℝ) := by
  have hswap₁ := integral_integral_swap
    (μ := (ν₁ : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun t x : ℝ => stieltjesCauchyAverageKernelProd g n (t, x))
    (stieltjesCauchyAverageKernelProd_integrable ν₁ g n)
  have hswap₂ := integral_integral_swap
    (μ := (ν₂ : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun t x : ℝ => stieltjesCauchyAverageKernelProd g n (t, x))
    (stieltjesCauchyAverageKernelProd_integrable ν₂ g n)
  calc
    (∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₁ : Measure ℝ)) =
        ∫ x : ℝ, ∫ t : ℝ, stieltjesCauchyAverageKernelProd g n (t, x)
          ∂(ν₁ : Measure ℝ) := by
          simpa [stieltjesCauchyAverage] using hswap₁
    _ = ∫ x : ℝ, g x * ∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₁ : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun x =>
            stieltjesCauchyAverageKernelProd_integral_center_swap ν₁ g n x
    _ = ∫ x : ℝ, g x * ∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₂ : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun x => congrArg (fun a : ℝ => g x * a) (hK n x)
    _ = ∫ x : ℝ, ∫ t : ℝ, stieltjesCauchyAverageKernelProd g n (t, x)
          ∂(ν₂ : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun x =>
            (stieltjesCauchyAverageKernelProd_integral_center_swap ν₂ g n x).symm
    _ = ∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₂ : Measure ℝ) := by
          simpa [stieltjesCauchyAverage] using hswap₂.symm

/-- If two finite measures give equal Cauchy-kernel integrals at every scale and center, then they
integrate every bounded continuous function equally. -/
theorem boundedContinuous_integral_eq_of_cauchyKernel_integrals_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hK : ∀ (n : ℕ) (x : ℝ),
      (∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₂ : Measure ℝ)) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      (∫ t : ℝ, g t ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, g t ∂(ν₂ : Measure ℝ) := by
  intro g
  have hseq : ∀ n : ℕ,
      (∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₂ : Measure ℝ) :=
    fun n => stieltjesCauchyAverage_integral_eq_of_cauchyKernel_integrals_eq hK g n
  have hlim₁ := stieltjesCauchyAverage_integral_tendsto ν₁ g
  have hlim₂ := stieltjesCauchyAverage_integral_tendsto ν₂ g
  have hlim₂' :
      Tendsto
        (fun n : ℕ => ∫ t : ℝ, stieltjesCauchyAverage g n t ∂(ν₁ : Measure ℝ))
        atTop (𝓝 (∫ t : ℝ, g t ∂(ν₂ : Measure ℝ))) :=
    hlim₂.congr' (Eventually.of_forall fun n => (hseq n).symm)
  exact tendsto_nhds_unique hlim₁ hlim₂'

/-- Two finite measures with equal Cauchy-kernel integrals at every scale and center are equal.
[simon2019] -/
theorem finiteMeasure_eq_of_cauchyKernel_integrals_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hK : ∀ (n : ℕ) (x : ℝ),
      (∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ,
          ProbabilityTheory.cauchyPDFReal x
            ⟨stieltjesUniqScale n, (stieltjesUniqScale_pos n).le⟩ t
          ∂(ν₂ : Measure ℝ)) :
    ν₁ = ν₂ :=
  finiteMeasure_eq_of_boundedContinuous_integral_eq
    (boundedContinuous_integral_eq_of_cauchyKernel_integrals_eq hK)

/-! ### Core Cauchy-to-Stieltjes producers -/

/-- The producer packaging Cauchy-kernel measure uniqueness for finite boundary measures. -/
def upperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer :
    UpperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer where
  finiteMeasure_eq_of_cauchyKernel_integrals_eq := by
    intro ν₁ ν₂ hK
    exact finiteMeasure_eq_of_cauchyKernel_integrals_eq hK

/-- Derive Poisson-kernel measure uniqueness from Cauchy-kernel measure uniqueness. -/
def poissonMeasureUniquenessProducer_of_cauchyMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryPoissonKernelMeasureUniquenessProducer where
  finiteMeasure_eq_of_poissonKernel_integrals_eq := by
    intro ν₁ ν₂ hP
    exact producer.finiteMeasure_eq_of_cauchyKernel_integrals_eq ν₁ ν₂
      (fun n x =>
        cauchyPDF_integral_eq_of_poissonKernel_integral_eq
          (ν₁ := ν₁) (ν₂ := ν₂) (x := x) (ε := stieltjesUniqScale n)
          (stieltjesUniqScale_pos n).le
          (by
            let zc : ℂ := (x : ℂ) + (stieltjesUniqScale n : ℂ) * Complex.I
            have hzpos : 0 < zc.im := by
              dsimp [zc]
              simpa using stieltjesUniqScale_pos n
            have hzi :
                UpperHalfPlane.ofComplex zc ≠ UpperHalfPlane.I := by
              dsimp [zc]
              exact upperHalfPlane_ofComplex_ne_I_of_im_lt_one
                (stieltjesUniqScale_pos n) (stieltjesUniqScale_lt_one n)
            have h := hP (UpperHalfPlane.ofComplex zc) hzi
            simpa [zc, UpperHalfPlane.ofComplex_apply_of_im_pos hzpos] using h))

/-- Derive Stieltjes-kernel measure uniqueness from Poisson-kernel measure uniqueness. -/
def stieltjesMeasureUniquenessProducer_of_poissonMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryPoissonKernelMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryStieltjesMeasureUniquenessProducer where
  finiteMeasure_eq_of_stieltjesKernel_integrals_eq := by
    intro ν₁ ν₂ hS
    exact producer.finiteMeasure_eq_of_poissonKernel_integrals_eq ν₁ ν₂
      (fun z hz => poissonKernel_integral_eq_of_stieltjesKernelIntegral_eq hS hz)

/-!
The Stieltjes-measure producer is strictly stronger than the earlier
Fourier-test producer; Fourier equality follows by rewriting along the recovered
finite-measure equality.
-/
/-- Upgrade Stieltjes-measure uniqueness to Stieltjes-kernel (Fourier-test) uniqueness by rewriting
along the recovered finite-measure equality. -/
def stieltjesKernelUniquenessProducer_of_stieltjesMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer where
  fourierIntegral_eq_of_stieltjesKernel_integrals_eq := by
    intro ν₁ ν₂ hS ξ
    have hν : ν₁ = ν₂ :=
      producer.finiteMeasure_eq_of_stieltjesKernel_integrals_eq ν₁ ν₂ hS
    simp [hν]

/-- Poisson-kernel measure uniqueness supplies Stieltjes-kernel uniqueness. -/
def stieltjesKernelUniquenessProducer_of_poissonMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryPoissonKernelMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer :=
  stieltjesKernelUniquenessProducer_of_stieltjesMeasureUniquenessProducer
    (stieltjesMeasureUniquenessProducer_of_poissonMeasureUniquenessProducer
      producer)

/-- Cauchy-kernel measure uniqueness supplies Stieltjes-kernel uniqueness. -/
def stieltjesKernelUniquenessProducer_of_cauchyMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer :=
  stieltjesKernelUniquenessProducer_of_poissonMeasureUniquenessProducer
    (poissonMeasureUniquenessProducer_of_cauchyMeasureUniquenessProducer
      producer)

/-! ### Producer lifts through finite-boundary uniqueness -/

/--
Finite-boundary uniqueness supplies the Poisson/Stieltjes uniqueness
producer by undoing the weight-based finite-measure conversion.
-/
def upperHalfPlanePoissonStieltjesUniquenessProducer_of_finiteBoundaryUniquenessProducer
    (producer : UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer) :
    UpperHalfPlanePoissonStieltjesUniquenessProducer where
  boundaryMeasure_eq_of_poissonKernel_integrals_eq := by
    intro u data₁ data₂ hP
    exact PoissonBoundaryMeasureData.boundaryMeasure_eq_of_finiteBoundaryMeasure_eq
      (producer.finiteBoundaryMeasure_eq_of_poissonKernel_integrals_eq data₁ data₂ hP)

open PoissonBoundaryMeasureData in
/--
Finite-kernel uniqueness supplies finite-boundary uniqueness after rewriting
the original Poisson integrals against finiteized boundary measures.
-/
def poissonFiniteBoundaryUniquenessProducer_of_finiteKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer where
  finiteBoundaryMeasure_eq_of_poissonKernel_integrals_eq := by
    intro u data₁ data₂ hP
    exact producer.finiteMeasure_eq_of_finiteBoundaryKernel_integrals_eq
      (nevanlinnaFiniteMeasureOfWeighted data₁.boundaryMeasure
        data₁.weight_lintegral_lt_top)
      (nevanlinnaFiniteMeasureOfWeighted data₂.boundaryMeasure
        data₂.weight_lintegral_lt_top)
      (finiteBoundaryPoissonKernel_integral_eq_of_poissonKernel_integral_eq
        hP)

/--
Finite-kernel uniqueness supplies the Poisson/Stieltjes uniqueness producer.
-/
def upperHalfPlanePoissonStieltjesUniquenessProducer_of_finiteKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer) :
    UpperHalfPlanePoissonStieltjesUniquenessProducer :=
  upperHalfPlanePoissonStieltjesUniquenessProducer_of_finiteBoundaryUniquenessProducer
    (poissonFiniteBoundaryUniquenessProducer_of_finiteKernelUniquenessProducer
      producer)

/--
Bounded-continuous-test-function uniqueness supplies finite-boundary kernel
uniqueness by finite-measure extensionality.
-/
def upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_boundedContinuousUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer where
  finiteMeasure_eq_of_finiteBoundaryKernel_integrals_eq := by
    intro ν₁ ν₂ hK
    exact finiteMeasure_eq_of_boundedContinuous_integral_eq
      (producer.boundedContinuous_integral_eq_of_finiteBoundaryKernel_integrals_eq
        ν₁ ν₂ hK)

/--
Bounded-continuous-test-function uniqueness supplies finite-boundary Poisson
uniqueness through the finite-kernel bridge.
-/
def upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_boundedContinuousUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  poissonFiniteBoundaryUniquenessProducer_of_finiteKernelUniquenessProducer
    (upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_boundedContinuousUniquenessProducer
      producer)

/--
Characteristic-function uniqueness supplies bounded-continuous-test-function
uniqueness by first identifying the finite measures.
-/
def upperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer_of_charFunUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer where
  boundedContinuous_integral_eq_of_finiteBoundaryKernel_integrals_eq := by
    intro ν₁ ν₂ hK g
    have hν : ν₁ = ν₂ := finiteMeasure_eq_of_charFun_eq
      (producer.charFun_eq_of_finiteBoundaryKernel_integrals_eq ν₁ ν₂ hK)
    rw [hν]

/--
Characteristic-function uniqueness supplies finite-boundary kernel uniqueness.
-/
def upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_charFunUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer :=
  upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_boundedContinuousUniquenessProducer
    (upperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer_of_charFunUniquenessProducer
      producer)

/--
Characteristic-function uniqueness supplies finite-boundary Poisson uniqueness.
-/
def upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_charFunUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  poissonFiniteBoundaryUniquenessProducer_of_finiteKernelUniquenessProducer
    (upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_charFunUniquenessProducer
      producer)

/--
Fourier-exponential uniqueness supplies characteristic-function uniqueness.
-/
def upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer where
  charFun_eq_of_finiteBoundaryKernel_integrals_eq := by
    intro ν₁ ν₂ hK
    exact charFun_eq_of_real_fourierIntegral_eq
      (producer.fourierIntegral_eq_of_finiteBoundaryKernel_integrals_eq ν₁ ν₂ hK)

/--
Fourier-exponential uniqueness supplies bounded-continuous-test-function
uniqueness through characteristic functions.
-/
def boundedContinuousUniquenessProducer_of_fourierIntegralUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer :=
  upperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer_of_charFunUniquenessProducer
    (upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
      producer)

/--
Fourier-exponential uniqueness supplies finite-boundary kernel uniqueness.
-/
def upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_fourierIntegralUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer :=
  upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_charFunUniquenessProducer
    (upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
      producer)

/--
Fourier-exponential uniqueness supplies finite-boundary Poisson uniqueness.
-/
def upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_fourierIntegralUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_charFunUniquenessProducer
    (upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
      producer)

/--
Nevanlinna-transform uniqueness supplies Fourier-exponential uniqueness by
rewriting the finite-boundary kernel as the imaginary part of the Nevanlinna
kernel.
-/
def fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer where
  fourierIntegral_eq_of_finiteBoundaryKernel_integrals_eq := by
    intro ν₁ ν₂ hK ξ
    exact producer.fourierIntegral_eq_of_nevanlinnaKernel_integral_im_eq ν₁ ν₂
      (by
        intro z
        calc
          (∫ t : ℝ, nevanlinnaKernel t z ∂(ν₁ : Measure ℝ)).im =
              ∫ t : ℝ, finiteBoundaryPoissonKernel t (z : ℂ).re (z : ℂ).im
                ∂(ν₁ : Measure ℝ) := by
                exact (finiteBoundaryPoissonKernel_integral_eq_nevanlinnaKernel_integral_im
                  ν₁ z).symm
          _ = ∫ t : ℝ, finiteBoundaryPoissonKernel t (z : ℂ).re (z : ℂ).im
                ∂(ν₂ : Measure ℝ) := by
                exact hK (z : ℂ).re (z : ℂ).im z.coe_im_pos
          _ = (∫ t : ℝ, nevanlinnaKernel t z ∂(ν₂ : Measure ℝ)).im := by
                exact finiteBoundaryPoissonKernel_integral_eq_nevanlinnaKernel_integral_im
                  ν₂ z)
      ξ

/--
Nevanlinna-transform uniqueness supplies characteristic-function uniqueness
through Fourier-exponential uniqueness.
-/
def characteristicFunctionUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer :=
  upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
    (fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
      producer)

/--
Nevanlinna-transform uniqueness supplies bounded-continuous-test-function
uniqueness through Fourier-exponential uniqueness.
-/
def boundedContinuousUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer :=
  boundedContinuousUniquenessProducer_of_fourierIntegralUniquenessProducer
    (fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
      producer)

/--
Nevanlinna-transform uniqueness supplies finite-boundary kernel uniqueness.
-/
def finiteBoundaryKernelUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer :=
  upperHalfPlaneFiniteBoundaryKernelUniquenessProducer_of_fourierIntegralUniquenessProducer
    (fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
      producer)

/--
Nevanlinna-transform uniqueness supplies finite-boundary Poisson uniqueness.
-/
def poissonFiniteBoundaryUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_fourierIntegralUniquenessProducer
    (fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies the Nevanlinna-transform
uniqueness producer.  The imaginary-part equality is upgraded to complex
transform equality by `nevanlinnaKernelIntegral_eq_of_im_eq`.
-/
def nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer where
  fourierIntegral_eq_of_nevanlinnaKernel_integral_im_eq := by
    intro ν₁ ν₂ hIm ξ
    have hEq :
        ∀ z : ℍ,
          nevanlinnaKernelIntegral ν₁ z = nevanlinnaKernelIntegral ν₂ z := by
      apply nevanlinnaKernelIntegral_eq_of_im_eq
      intro z
      simpa [nevanlinnaKernelIntegral] using hIm z
    exact producer.fourierIntegral_eq_of_nevanlinnaKernel_integrals_eq ν₁ ν₂ hEq ξ

/--
Complex Nevanlinna-kernel uniqueness supplies Fourier-exponential uniqueness.
-/
def fourierIntegralUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer :=
  fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies characteristic-function uniqueness.
-/
def characteristicFunctionUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer :=
  characteristicFunctionUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies bounded-continuous-test-function
uniqueness.
-/
def boundedContinuousUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer :=
  boundedContinuousUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies finite-boundary kernel uniqueness.
-/
def finiteBoundaryKernelUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer :=
  finiteBoundaryKernelUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies finite-boundary Poisson uniqueness.
-/
def poissonFiniteBoundaryUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  poissonFiniteBoundaryUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Stieltjes-kernel uniqueness supplies complex Nevanlinna-kernel uniqueness.  The
bridge uses the algebraic decomposition of the Nevanlinna kernel and the value
at `i` to extract the Stieltjes transform.
-/
def nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer where
  fourierIntegral_eq_of_nevanlinnaKernel_integrals_eq := by
    intro ν₁ ν₂ hN ξ
    exact producer.fourierIntegral_eq_of_stieltjesKernel_integrals_eq ν₁ ν₂
      (fun z hz =>
        upperHalfPlaneStieltjesKernelIntegral_eq_of_nevanlinnaKernelIntegral_eq hN hz)
      ξ

/-- Stieltjes-measure uniqueness supplies complex Nevanlinna-kernel uniqueness. -/
def nevanlinnaKernelUniquenessProducer_of_stieltjesMeasureUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesMeasureUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer :=
  nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (stieltjesKernelUniquenessProducer_of_stieltjesMeasureUniquenessProducer
      producer)

/-- Stieltjes-kernel uniqueness supplies Nevanlinna-transform uniqueness. -/
def nevanlinnaTransformUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer :=
  nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/-- Stieltjes-kernel uniqueness supplies Fourier-exponential uniqueness. -/
def fourierIntegralUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer :=
  fourierIntegralUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/-- Stieltjes-kernel uniqueness supplies characteristic-function uniqueness. -/
def characteristicFunctionUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer :=
  characteristicFunctionUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/--
Stieltjes-kernel uniqueness supplies bounded-continuous-test-function
uniqueness.
-/
def boundedContinuousUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer :=
  boundedContinuousUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/-- Stieltjes-kernel uniqueness supplies finite-boundary kernel uniqueness. -/
def finiteBoundaryKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer :=
  finiteBoundaryKernelUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/-- Stieltjes-kernel uniqueness supplies finite-boundary Poisson uniqueness. -/
def poissonFiniteBoundaryUniquenessProducer_of_stieltjesKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer :=
  poissonFiniteBoundaryUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

end

end Loewner
end TraceInequality
end Quantum
