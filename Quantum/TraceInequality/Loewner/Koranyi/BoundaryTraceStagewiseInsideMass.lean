import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceProducer

namespace Quantum.TraceInequality.Loewner

open Filter

open scoped Topology

noncomputable section

/-!
# Stagewise inside-mass bounds

This file is a consumer layer for the 38-c-pre frontier.  It does not produce
the finite-Koranyi inverse-square estimates.  It only records the stable passage
from a real stagewise upper bound tending to zero to the signed-backbone inside
mass decay contract, and then to inside vanishing along a signed axis.
-/

/-- A real stagewise upper bound for the signed-backbone inside mass. -/
structure SignedAxisStagewiseInsideMassBound {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) where
  B : ℕ → ℝ
  nonneg : ∀ᶠ n in atTop, 0 ≤ B n
  bound : ∀ᶠ n in atTop,
    (pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1)).toReal ≤ B n
  tendsto_zero : Tendsto B atTop (𝓝 0)

/-- A stagewise real upper bound tending to zero gives inside mass decay. -/
theorem signedAxisInsideMassDecay_of_stagewise_insideMass_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hbound : SignedAxisStagewiseInsideMassBound pkg) :
    SignedAxisInsideMassDecay pkg := by
  refine ⟨?_⟩
  exact squeeze_zero'
    (Eventually.of_forall fun _n => ENNReal.toReal_nonneg)
    hbound.bound
    hbound.tendsto_zero

/-- Stagewise inside-mass bounds close the inside-vanishing gate on any signed axis. -/
theorem signedAxisInsideVanishing_of_stagewise_insideMass_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x) (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hbound : SignedAxisStagewiseInsideMassBound pkg) :
    SignedAxisInsideVanishing pkg axis :=
  signedAxisInsideVanishing_of_insideMassDecay axis hx
    (signedAxisInsideMassDecay_of_stagewise_insideMass_bound hbound)

end

end Loewner
end TraceInequality
end Quantum
