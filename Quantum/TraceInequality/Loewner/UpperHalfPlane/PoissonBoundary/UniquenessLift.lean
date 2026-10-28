/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.UpperHalfPlane.PoissonBoundary.PickConstruction
import Quantum.TraceInequality.Loewner.UpperHalfPlane.PoissonBoundary.UniquenessCore

/-!
# Uniqueness lift for upper-half-plane Poisson boundary data

Source correspondence: the Nevanlinna representation uniqueness stage, lifting
finite-boundary and Poisson/Stieltjes uniqueness to theorem-facing wrappers and
Pick-specific Poisson boundary outputs.
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

/--
Producer interface for uniqueness of the upper-half-plane Poisson boundary
measure.  The Nevanlinna uniqueness theorem itself is proved below as
`NevanlinnaRep.unique`, through Cauchy-kernel measure uniqueness.
-/
structure UpperHalfPlanePoissonBoundaryUniquenessProducer where
  boundaryMeasure_eq_of_same_poisson_data :
    ∀ {u : ℂ → ℝ} (data₁ data₂ : PoissonBoundaryMeasureData u),
      data₁.boundaryMeasure = data₂.boundaryMeasure

/--
The lower-level Poisson/Stieltjes uniqueness producer supplies the boundary
measure uniqueness producer.
-/
def upperHalfPlanePoissonBoundaryUniquenessProducer_of_poissonStieltjesUniquenessProducer
    (producer : UpperHalfPlanePoissonStieltjesUniquenessProducer) :
    UpperHalfPlanePoissonBoundaryUniquenessProducer where
  boundaryMeasure_eq_of_same_poisson_data := by
    intro u data₁ data₂
    exact producer.boundaryMeasure_eq_of_poissonKernel_integrals_eq data₁ data₂
      (PoissonBoundaryMeasureData.poissonKernel_integral_eq_of_slope_eq
        (PoissonBoundaryMeasureData.slope_eq_of_same_function data₁ data₂))

/--
The Poisson-boundary uniqueness producer supplies the remaining field of the
Nevanlinna uniqueness producer.
-/
def nevanlinnaRepUniquenessProducer_of_poissonBoundaryUniquenessProducer
    (producer : UpperHalfPlanePoissonBoundaryUniquenessProducer) :
    NevanlinnaRepUniquenessProducer where
  weightedMeasure_eq_of_same_function := by
    intro F rep₁ rep₂
    exact producer.boundaryMeasure_eq_of_same_poisson_data
      (poissonBoundaryMeasureData_of_nevanlinnaRep rep₁)
      (poissonBoundaryMeasureData_of_nevanlinnaRep rep₂)

/--
The Poisson/Stieltjes uniqueness producer supplies the Nevanlinna uniqueness
producer.
-/
def nevanlinnaRepUniquenessProducer_of_poissonStieltjesUniquenessProducer
    (producer : UpperHalfPlanePoissonStieltjesUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_poissonBoundaryUniquenessProducer
    (upperHalfPlanePoissonBoundaryUniquenessProducer_of_poissonStieltjesUniquenessProducer
      producer)

/--
Finite-boundary uniqueness supplies the Nevanlinna uniqueness producer through
the Poisson/Stieltjes bridge.
-/
def nevanlinnaRepUniquenessProducer_of_poissonFiniteBoundaryUniquenessProducer
    (producer : UpperHalfPlanePoissonFiniteBoundaryUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_poissonStieltjesUniquenessProducer
    (upperHalfPlanePoissonStieltjesUniquenessProducer_of_finiteBoundaryUniquenessProducer
      producer)

/--
Finite-kernel uniqueness supplies the Nevanlinna uniqueness producer through
the finite-boundary Poisson bridge.
-/
def nevanlinnaRepUniquenessProducer_of_finiteBoundaryKernelUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryKernelUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_poissonFiniteBoundaryUniquenessProducer
    (poissonFiniteBoundaryUniquenessProducer_of_finiteKernelUniquenessProducer
      producer)

/--
Bounded-continuous-test-function uniqueness supplies the Nevanlinna uniqueness
producer through the finite-boundary kernel bridge.
-/
def nevanlinnaRepUniquenessProducer_of_boundedContinuousUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryBoundedContinuousUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_poissonFiniteBoundaryUniquenessProducer
    (upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_boundedContinuousUniquenessProducer
      producer)

/--
Characteristic-function uniqueness supplies the Nevanlinna uniqueness producer
through the finite-boundary kernel bridge.
-/
def nevanlinnaRepUniquenessProducer_of_charFunUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryCharFunUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_poissonFiniteBoundaryUniquenessProducer
    (upperHalfPlanePoissonFiniteBoundaryUniquenessProducer_of_charFunUniquenessProducer
      producer)

/--
Fourier-exponential uniqueness supplies the Nevanlinna uniqueness producer
through the characteristic-function bridge.
-/
def nevanlinnaRepUniquenessProducer_of_fourierIntegralUniquenessProducer
    (producer : UpperHalfPlaneFiniteBoundaryFourierIntegralUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_charFunUniquenessProducer
    (upperHalfPlaneFiniteBoundaryCharFunUniquenessProducer_of_fourierIntegralUniquenessProducer
      producer)

/--
Nevanlinna-transform uniqueness supplies the Nevanlinna uniqueness producer
through the Fourier-exponential bridge.
-/
def nevanlinnaRepresentationUniqueness_of_nevanlinnaTransformUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaTransformUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepUniquenessProducer_of_fourierIntegralUniquenessProducer
    (fourierIntegralUniquenessProducer_of_nevanlinnaTransformUniquenessProducer
      producer)

/--
Complex Nevanlinna-kernel uniqueness supplies the Nevanlinna uniqueness
producer through the Nevanlinna-transform bridge.
-/
def nevanlinnaRepresentationUniqueness_of_nevanlinnaKernelUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryNevanlinnaKernelUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepresentationUniqueness_of_nevanlinnaTransformUniqueness
    (nevanlinnaTransformUniquenessProducer_of_nevanlinnaKernelUniquenessProducer
      producer)

/--
Stieltjes-kernel uniqueness supplies the Nevanlinna uniqueness producer through
the complex Nevanlinna-kernel bridge.
-/
def nevanlinnaRepresentationUniqueness_of_stieltjesKernelUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesKernelUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepresentationUniqueness_of_nevanlinnaKernelUniqueness
    (nevanlinnaKernelUniquenessProducer_of_stieltjesKernelUniquenessProducer
      producer)

/--
Stieltjes-measure uniqueness supplies the Nevanlinna uniqueness producer through
the Stieltjes-kernel wrapper.
-/
def nevanlinnaRepresentationUniqueness_of_stieltjesMeasureUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryStieltjesMeasureUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepresentationUniqueness_of_stieltjesKernelUniqueness
    (stieltjesKernelUniquenessProducer_of_stieltjesMeasureUniquenessProducer
      producer)

/--
Poisson-kernel measure uniqueness supplies the Nevanlinna uniqueness producer
through the Stieltjes-measure wrapper.
-/
def nevanlinnaRepresentationUniqueness_of_poissonKernelMeasureUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryPoissonKernelMeasureUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepresentationUniqueness_of_stieltjesMeasureUniqueness
    (stieltjesMeasureUniquenessProducer_of_poissonMeasureUniquenessProducer
      producer)

/--
Cauchy-kernel measure uniqueness supplies the Nevanlinna uniqueness producer
through the Poisson-kernel wrapper.
-/
def nevanlinnaRepresentationUniqueness_of_cauchyKernelMeasureUniqueness
    (producer : UpperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer) :
    NevanlinnaRepUniquenessProducer :=
  nevanlinnaRepresentationUniqueness_of_poissonKernelMeasureUniqueness
    (poissonMeasureUniquenessProducer_of_cauchyMeasureUniquenessProducer
      producer)

namespace NevanlinnaRep

/-- Nevanlinna representations of the same Pick function are unique. -/
theorem unique {F : ℍ → ℂ} (rep₁ rep₂ : NevanlinnaRep F) :
    rep₁ = rep₂ := by
  let producer :=
    nevanlinnaRepresentationUniqueness_of_cauchyKernelMeasureUniqueness
      upperHalfPlaneFiniteBoundaryCauchyKernelMeasureUniquenessProducer
  have hν : rep₁.ν = rep₂.ν :=
    nevanlinnaFiniteMeasure_eq_of_weightedMeasure_eq
      (producer.weightedMeasure_eq_of_same_function rep₁ rep₂)
  exact eq_of_fields_eq
    (alpha_eq_of_same_function rep₁ rep₂)
    (beta_eq_of_same_function_of_measure_eq rep₁ rep₂ hν)
    hν

end NevanlinnaRep

/-- Pick-specific Poisson boundary data supplied by the concrete disk Herglotz bridge. -/
def poissonBoundaryMeasure_of_pick
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    PoissonBoundaryMeasureData
      (fun z : ℂ => (F (UpperHalfPlane.ofComplex z)).im) :=
  poissonBoundaryMeasureData_of_nevanlinnaRep
    (nevanlinnaRep_of_pick hF hF_nonneg)

/-- Pick-specific weighted Nevanlinna representation supplied by the concrete bridge. -/
def weightedNevanlinnaRep_of_pick
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    WeightedNevanlinnaRep F :=
  weightedNevanlinnaRep_of_nevanlinnaRep
    (nevanlinnaRep_of_pick hF hF_nonneg)

end

end Loewner
end TraceInequality
end Quantum
