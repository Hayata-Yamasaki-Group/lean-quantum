import Quantum.TraceInequality.Loewner.UnitInterval.Pick.RadialWeakLimit

/-!
# Chapter 3 Theorem 3.1 radial family output

This module records the abstract radial-family output of book Theorem 3.1 and
connects it to the radial weak-limit core.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Theorem 3.1 radial family output -/

/--
The radial boundary-measure output supplied by book Theorem 3.1 in the proof
of Theorem 3.2.

This records the Poisson formula after applying Theorem 3.1 at the radii
`unitDiskHerglotzRadius n`.  These data are constructed from the concrete radial
Poisson formula by `unitDiskTheorem31RadialFamilyData_of_concreteFormulaData` and
`unitDiskTheorem31ConcreteRadialFormulaProducer` in `ConcreteRadialMeasures.lean`.
-/
structure UnitDiskTheorem31RadialFamilyData (G : ℂ → ℂ) where
  radialMeasure : ℕ → FiniteMeasure UnitDiskBoundary
  radialMass : ℝ≥0
  radial_mass_eq : ∀ n : ℕ, (radialMeasure n).mass = radialMass
  mass_eq : (radialMass : ENNReal) = ENNReal.ofReal (G 0).re
  formula :
    ∀ (n : ℕ) ⦃w : ℂ⦄ (hw : w ∈ (unitDiskDomain : Set ℂ)),
      G ((unitDiskHerglotzRadius n : ℂ) * w) =
        Complex.I * ((G 0).im : ℂ) +
          ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
            ∂(radialMeasure n : Measure UnitDiskBoundary)

/-- Theorem 3.1 radial output is exactly the input expected by the radial weak-limit core. -/
def unitDiskRadialHerglotzFamilyData_of_theorem31RadialFamilyData
    {G : ℂ → ℂ} (data : UnitDiskTheorem31RadialFamilyData G) :
    UnitDiskRadialHerglotzFamilyData G where
  radialMeasure := data.radialMeasure
  radialMass := data.radialMass
  radial_mass_eq := data.radial_mass_eq
  mass_eq := data.mass_eq
  formula := data.formula

/-- Producer interface for the radial output of book Theorem 3.1. -/
structure UnitDiskTheorem31RadialFamilyProducerFromCaratheodoryInput where
  produce :
    ∀ {G : ℂ → ℂ}, UnitDiskCaratheodoryInput G →
      UnitDiskTheorem31RadialFamilyData G

/-- A Theorem 3.1 radial producer supplies the producer used by the radial weak-limit core. -/
def unitDiskRadialHerglotzFamilyProducer_of_theorem31RadialFamilyProducer
    (producer : UnitDiskTheorem31RadialFamilyProducerFromCaratheodoryInput) :
    UnitDiskRadialHerglotzFamilyProducerFromCaratheodoryInput where
  produce := by
    intro G hG
    exact unitDiskRadialHerglotzFamilyData_of_theorem31RadialFamilyData
      (producer.produce hG)

/-- Theorem 3.1 radial output and the radial weak-limit core give the disk Herglotz producer. -/
def unitDiskHerglotzCircleProducer_of_theorem31RadialFamilyProducer
    (producer : UnitDiskTheorem31RadialFamilyProducerFromCaratheodoryInput) :
    UnitDiskHerglotzCircleProducerFromCaratheodoryInput :=
  unitDiskHerglotzCircleProducer_of_radialFamilyProducer
    (unitDiskRadialHerglotzFamilyProducer_of_theorem31RadialFamilyProducer
      producer)

end

end Quantum.TraceInequality.Loewner
