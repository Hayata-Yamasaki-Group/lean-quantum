import Quantum.TraceInequality.Loewner.UnitInterval.Pick.DiskInput

/-!
# Chapter 3 disk Herglotz circle data

This module records the disk-boundary Herglotz representation data and its
producer contract before the boundary Cayley pushforward to the real line.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Disk Herglotz circle representation data -/

/-- The boundary circle used by the disk Herglotz representation. -/
def unitDiskBoundary : Set ℂ :=
  Metric.sphere (0 : ℂ) 1

/--
Book Theorem 3.2 output before the Cayley pushforward to the real line.

This is the disk-boundary representation
`G w = i * Im(G 0) + ∫ K(ξ,w) dμ(ξ)`, together with the mass identity
`μ(∂D) = Re(G 0)`.  The existence theorem producing this data is kept as the
separate producer contract below.
-/
structure UnitDiskHerglotzCircleData (G : ℂ → ℂ) where
  boundaryMeasure : FiniteMeasure ℂ
  boundary_support :
    (boundaryMeasure : Measure ℂ) (unitDiskBoundary : Set ℂ)ᶜ = 0
  mass_eq :
    (boundaryMeasure.mass : ENNReal) = ENNReal.ofReal (G 0).re
  formula :
    ∀ ⦃w : ℂ⦄, w ∈ (unitDiskDomain : Set ℂ) →
      G w =
        Complex.I * ((G 0).im : ℂ) +
          ∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ w
            ∂(boundaryMeasure : Measure ℂ)

/--
Producer interface for book Theorem 3.2 on the unit disk.

It turns the disk-side Carathéodory input into the circle-measure Herglotz
representation.  A producer is constructed from the concrete radial measures as
`unitDiskHerglotzCircleProducer_of_theorem31ConcreteFormula` in
`ConcreteRadialMeasures.lean`.
-/
structure UnitDiskHerglotzCircleProducerFromCaratheodoryInput where
  produce :
    ∀ {G : ℂ → ℂ}, UnitDiskCaratheodoryInput G →
      UnitDiskHerglotzCircleData G

end

end Quantum.TraceInequality.Loewner
