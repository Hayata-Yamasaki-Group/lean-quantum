import Quantum.TraceInequality.Loewner.UnitInterval.Pick.EndpointCollar

/-!
# Chapter 3 public Pick/integral correspondence

This module contains the final concrete producer connection and the public
Pick/integral correspondence on the normalized interval.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Concrete producer connection -/

/-- Concrete Corollary 3.6 outside-support producer from Proposition 3.5. -/
def unitDiskCorollary36OutsideSupportProducer_concrete :
    UnitDiskCorollary36OutsideSupportProducerFromPickInput :=
  unitDiskCorollary36OutsideSupportProducer_of_proposition35Producer
    unitIntervalPickHerglotzProposition35Producer_concrete

/-- Concrete reverse direction from a Pick extension to the interval representation. -/
def integralRepOnUnitInterval_of_pickExtension_concrete
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_pickExtension_of_proposition35Producer
    unitIntervalPickHerglotzProposition35Producer_concrete pick

/-! ### Public Pick/integral correspondence -/

/-- Book Theorem 3.8 public correspondence on the normalized interval. -/
theorem unitIntervalPickExtension_iff_integralRep (f : ℝ → ℝ) :
    Nonempty (PickExtensionOnUnitInterval f) ↔
      Nonempty (IntegralRepOnUnitInterval f) := by
  constructor
  · rintro ⟨pick⟩
    exact ⟨integralRepOnUnitInterval_of_pickExtension_concrete pick⟩
  · rintro ⟨rep⟩
    exact ⟨pickExtensionOnUnitInterval_of_integralRep rep⟩
end

end Quantum.TraceInequality.Loewner
