import Quantum.Analysis.CStar.UnitIntervalKernel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Quantum.TraceInequality.Loewner.RealComplexOrder
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.Loewner.Statement

/-!
# Chapter 3 integral representations imply operator monotonicity

This file records the public interface for the book Theorem 3.12 direction:
an interval integral representation implies operator monotonicity on `(-1,1)`.
The analytic/CFC proof of the kernel monotonicity is kept as an explicit input.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open MeasureTheory

/-- The representing measure of an interval integral representation is a.e. on `[-1,1]`. -/
theorem IntegralRepOnUnitInterval.ae_mem_Icc {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) :
    ∀ᵐ lambda ∂(rep.ν : Measure ℝ), lambda ∈ Set.Icc (-1 : ℝ) 1 := by
  exact (mem_ae_iff).mpr rep.support

/-- Restricting the representing measure to `[-1,1]` does not change it. -/
theorem IntegralRepOnUnitInterval.restrict_Icc_eq_self {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) :
    (rep.ν : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1) = (rep.ν : Measure ℝ) :=
  Measure.restrict_eq_self_of_ae_mem rep.ae_mem_Icc

/-- Real form of the normalized interval integral representation. -/
theorem IntegralRepOnUnitInterval.real_formula {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x - f 0 =
      ∫ lambda : ℝ, unitIntervalOperatorKernel lambda x ∂(rep.ν : Measure ℝ) := by
  have hkernel :
      (∫ lambda : ℝ, ((x : ℂ) / (1 + (lambda : ℂ) * x)) ∂(rep.ν : Measure ℝ)) =
        ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda x ∂(rep.ν : Measure ℝ) : ℝ) : ℂ) := by
    calc
      (∫ lambda : ℝ, ((x : ℂ) / (1 + (lambda : ℂ) * x)) ∂(rep.ν : Measure ℝ)) =
          ∫ lambda : ℝ, ((unitIntervalOperatorKernel lambda x : ℝ) : ℂ)
            ∂(rep.ν : Measure ℝ) := by
        refine integral_congr_ae ?_
        filter_upwards with lambda
        exact (unitIntervalOperatorKernel_complex_eq lambda x).symm
      _ = ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda x
              ∂(rep.ν : Measure ℝ) : ℝ) : ℂ) := by
        exact integral_ofReal
  have hcomplex :
      ((f x - f 0 : ℝ) : ℂ) =
        ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda x ∂(rep.ν : Measure ℝ) : ℝ) : ℂ) := by
    calc
      ((f x - f 0 : ℝ) : ℂ) = (f x : ℂ) - (f 0 : ℂ) := by simp
      _ =
          ((f 0 : ℂ) +
              ∫ lambda : ℝ, ((x : ℂ) / (1 + (lambda : ℂ) * x)) ∂(rep.ν : Measure ℝ)) -
            (f 0 : ℂ) := by rw [rep.formula hx]
      _ = ((∫ lambda : ℝ, unitIntervalOperatorKernel lambda x ∂(rep.ν : Measure ℝ) : ℝ) : ℂ) := by
        rw [hkernel]
        abel
  exact Complex.ofReal_injective hcomplex

/-- Real interval formula written as a set integral over `[-1,1]`. -/
theorem IntegralRepOnUnitInterval.real_formula_setIntegral {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x - f 0 =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        unitIntervalOperatorKernel lambda x ∂(rep.ν : Measure ℝ) := by
  rw [rep.restrict_Icc_eq_self]
  exact rep.real_formula hx

/--
The CFC kernel-monotonicity interface for Theorem 3.12.

The scalar fractional-linear core above fixes the book algebra, and the closed
instance below transports the resolvent proof through `Unitization` and back to
`cfcₙ`.
-/
structure IntervalKernelOperatorMonotoneInput : Prop where
  /-- Simon Ch.3 [simon2019]: every interval kernel is operator-monotone. -/
  kernel_operatorMonotone :
    ∀ ⦃lambda : ℝ⦄,
      lambda ∈ Set.Icc (-1 : ℝ) 1 →
        OperatorMonotoneOnUnitInterval.{u} (unitIntervalOperatorKernel lambda)

/-- The interval kernel is operator-monotone on the normalized unit interval. -/
theorem operatorMonotoneOnUnitInterval_unitIntervalOperatorKernel {lambda : ℝ}
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1) :
    OperatorMonotoneOnUnitInterval.{u} (unitIntervalOperatorKernel lambda) := by
  refine ⟨?_⟩
  intro A _ _ _ a ha_mem b hb_mem hab
  rcases ha_mem with ⟨ha, hspeca⟩
  rcases hb_mem with ⟨hb, hspecb⟩
  rcases lt_trichotomy lambda 0 with hneg | hzero | hpos
  · simpa [unitIntervalOperatorKernel_zero] using
      unitIntervalOperatorKernel_cfcₙ_le_of_neg hneg hlambda ha hb hspeca hspecb hab
  · subst lambda
    simpa [unitIntervalOperatorKernel_zero] using
      unitIntervalOperatorKernel_cfcₙ_le_of_zero ha hb hab
  · simpa [unitIntervalOperatorKernel_zero] using
      unitIntervalOperatorKernel_cfcₙ_le_of_pos hpos hlambda ha hb hspeca hspecb hab

/--
Consume the interval-kernel monotonicity input for a fixed parameter.

Lean-deviation: the source input package is unnecessary on this surface because
the existing closed root already supplies the conclusion.
-/
theorem operatorMonotoneOnUnitInterval_unitIntervalOperatorKernel_of_kernelInput
    {lambda : ℝ} (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1) :
    OperatorMonotoneOnUnitInterval.{u} (unitIntervalOperatorKernel lambda) :=
  operatorMonotoneOnUnitInterval_unitIntervalOperatorKernel
    (lambda := lambda) hlambda

/-- The interval-kernel monotonicity input required for Theorem 3.12 is closed. -/
theorem intervalKernelOperatorMonotoneInput_closed :
    IntervalKernelOperatorMonotoneInput.{u} where
  kernel_operatorMonotone := fun {lambda} hlambda =>
    operatorMonotoneOnUnitInterval_unitIntervalOperatorKernel (lambda := lambda) hlambda

private theorem unitIntervalOperatorKernel_exists_bound_on_Icc_quasispectrum
    {A : Type*} [NonUnitalCStarAlgebra A] {a : A}
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    ∃ C : ℝ, ∀ p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ quasispectrum ℝ a,
      ‖unitIntervalOperatorKernel p.1 p.2‖ ≤ C := by
  exact (isCompact_Icc.prod (quasispectrum.isCompact (𝕜 := ℝ) a)).exists_bound_of_continuousOn
    (unitIntervalOperatorKernel_joint_continuousOn_Icc_quasispectrum hspec)

/--
For the interval kernel, the non-unital CFC commutes with the positive finite-measure
set integral over `[-1,1]`.
-/
theorem unitIntervalOperatorKernel_cfcₙ_setIntegral
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsSelfAdjoint a)
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (μ : Measure ℝ) [IsFiniteMeasure (μ.restrict (Set.Icc (-1 : ℝ) 1))] :
    cfcₙ (fun x : ℝ =>
        ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
          unitIntervalOperatorKernel lambda x ∂μ) a =
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        cfcₙ (unitIntervalOperatorKernel lambda) a ∂μ := by
  obtain ⟨C, hC⟩ := unitIntervalOperatorKernel_exists_bound_on_Icc_quasispectrum
    (A := A) (a := a) hspec
  refine cfcₙ_setIntegral
    (s := Set.Icc (-1 : ℝ) 1) (μ := μ)
    (f := fun lambda x => unitIntervalOperatorKernel lambda x)
    (bound := fun _ : ℝ => C) (a := a)
    measurableSet_Icc ?hf ?hzero ?hbound ?hfinite ha
  · exact unitIntervalOperatorKernel_joint_continuousOn_Icc_quasispectrum hspec
  · exact Filter.Eventually.of_forall fun lambda => unitIntervalOperatorKernel_zero lambda
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda z hz
    exact hC (lambda, z) ⟨hlambda, hz⟩
  · exact integrable_const C |>.hasFiniteIntegral

/-- The CFC image of the interval kernel is integrable over the parameter interval. -/
theorem unitIntervalOperatorKernel_cfcₙ_integrableOn
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsSelfAdjoint a)
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (μ : Measure ℝ) [IsFiniteMeasure (μ.restrict (Set.Icc (-1 : ℝ) 1))] :
    IntegrableOn (fun lambda : ℝ => cfcₙ (unitIntervalOperatorKernel lambda) a)
      (Set.Icc (-1 : ℝ) 1) μ := by
  obtain ⟨C, hC⟩ := unitIntervalOperatorKernel_exists_bound_on_Icc_quasispectrum
    (A := A) (a := a) hspec
  refine integrableOn_cfcₙ
    (s := Set.Icc (-1 : ℝ) 1) (μ := μ)
    measurableSet_Icc (fun lambda x => unitIntervalOperatorKernel lambda x)
    (fun _ : ℝ => C) a
    (unitIntervalOperatorKernel_joint_continuousOn_Icc_quasispectrum hspec)
    ?hzero ?hbound ?hfinite ha
  · exact Filter.Eventually.of_forall fun lambda => unitIntervalOperatorKernel_zero lambda
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda z hz
    exact hC (lambda, z) ⟨hlambda, hz⟩
  · exact integrable_const C |>.hasFiniteIntegral

/-- Integrating the interval-kernel CFC preserves order under the spectral hypotheses. -/
theorem unitIntervalOperatorKernel_setIntegral_cfcₙ_le
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hspeca : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hspecb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) (μ : Measure ℝ)
    [IsFiniteMeasure (μ.restrict (Set.Icc (-1 : ℝ) 1))] :
    (∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        cfcₙ (unitIntervalOperatorKernel lambda) a ∂μ) ≤
      ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
        cfcₙ (unitIntervalOperatorKernel lambda) b ∂μ := by
  refine setIntegral_mono_on_ae
    (unitIntervalOperatorKernel_cfcₙ_integrableOn ha hspeca μ)
    (unitIntervalOperatorKernel_cfcₙ_integrableOn hb hspecb μ)
    measurableSet_Icc ?_
  filter_upwards with lambda hlambda
  rcases lt_trichotomy lambda 0 with hneg | hzero | hpos
  · exact unitIntervalOperatorKernel_cfcₙ_le_of_neg hneg hlambda ha hb hspeca hspecb hab
  · subst lambda
    exact unitIntervalOperatorKernel_cfcₙ_le_of_zero ha hb hab
  · exact unitIntervalOperatorKernel_cfcₙ_le_of_pos hpos hlambda ha hb hspeca hspecb hab

/-- Book Theorem 3.12: an interval integral representation is operator-monotone. -/
theorem operatorMonotoneOnUnitInterval_of_integralRep {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval f) :
    OperatorMonotoneOnUnitInterval.{u} f := by
  refine ⟨?_⟩
  intro A _ _ _ a ha_mem b hb_mem hab
  rcases ha_mem with ⟨ha, hspeca⟩
  rcases hb_mem with ⟨hb, hspecb⟩
  let μ : Measure ℝ := rep.ν
  have hcongr_a :
      cfcₙ (fun x : ℝ => f x - f 0) a =
        cfcₙ (fun x : ℝ =>
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            unitIntervalOperatorKernel lambda x ∂μ) a := by
    apply cfcₙ_congr
    intro x hx
    exact rep.real_formula_setIntegral (hspeca hx)
  have hcongr_b :
      cfcₙ (fun x : ℝ => f x - f 0) b =
        cfcₙ (fun x : ℝ =>
          ∫ lambda : ℝ in Set.Icc (-1 : ℝ) 1,
            unitIntervalOperatorKernel lambda x ∂μ) b := by
    apply cfcₙ_congr
    intro x hx
    exact rep.real_formula_setIntegral (hspecb hx)
  change cfcₙ (fun x : ℝ => f x - f 0) a ≤
    cfcₙ (fun x : ℝ => f x - f 0) b
  rw [hcongr_a, hcongr_b]
  rw [unitIntervalOperatorKernel_cfcₙ_setIntegral ha hspeca μ,
    unitIntervalOperatorKernel_cfcₙ_setIntegral hb hspecb μ]
  exact unitIntervalOperatorKernel_setIntegral_cfcₙ_le ha hb hspeca hspecb hab μ

/--
Explicit Theorem 3.12 input for a fixed function.

This contract is discharged below using operator monotonicity of the kernel
`x ↦ x / (1 + λ * x)` and preservation of operator order by positive
finite-measure integrals.
-/
structure Theorem312OperatorMonotoneInput (f : ℝ → ℝ) : Prop where
  /-- Simon Ch.3 [simon2019]: an interval representation implies operator monotonicity. -/
  to_operatorMonotone :
    IntegralRepOnUnitInterval f → OperatorMonotoneOnUnitInterval.{u} f

/-- The book Theorem 3.12 input is discharged by the kernel and finite-measure integral core. -/
theorem theorem312OperatorMonotoneInput_closed (f : ℝ → ℝ) :
    Theorem312OperatorMonotoneInput.{u} f where
  to_operatorMonotone := operatorMonotoneOnUnitInterval_of_integralRep

/--
Consume the Theorem 3.12 input for a concrete integral representation.

Lean-deviation: the source input package is unnecessary on this surface because
the existing closed root already supplies the conclusion.
-/
theorem operatorMonotoneOnUnitInterval_of_integralRep_of_theorem312Input
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    OperatorMonotoneOnUnitInterval.{u} f :=
  operatorMonotoneOnUnitInterval_of_integralRep rep

/--
Consume the Theorem 3.12 input when the integral representation is known to exist.

Lean-deviation: the source input package is unnecessary on this surface because
the existing closed root already supplies the conclusion.
-/
theorem operatorMonotoneOnUnitInterval_of_integralRep_nonempty_of_theorem312Input
    {f : ℝ → ℝ} (hrep : Nonempty (IntegralRepOnUnitInterval f)) :
    OperatorMonotoneOnUnitInterval.{u} f :=
  hrep.elim fun rep =>
    operatorMonotoneOnUnitInterval_of_integralRep rep

end

end Quantum.TraceInequality.Loewner
