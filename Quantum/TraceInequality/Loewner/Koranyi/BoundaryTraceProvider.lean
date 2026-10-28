import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTrace
import Quantum.TraceInequality.Loewner.UnitInterval.KernelPositivity

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal

/-!
Provider-side adapter for the fixed-boundary trace bridge.

The actual Koranyi/support-elimination boundary trace limit remains a named
contract, `FixedBoundaryTraceTendsto`.  This file only discharges the
Löwner-kernel nonnegativity from `GlobalStrictPosDef` and assembles the bridge.
-/

/-- The still-open tendsto contract in `FixedBoundaryTraceBridge`.

This isolates the single remaining fixed-boundary trace limit needed after
kernel nonnegativity has been discharged from strict positivity. -/
structure FixedBoundaryTraceTendsto {f : ℝ → ℝ}
    (pkg : StrictApproxPackage f) (x : ℝ) : Prop where
  tendsto :
    Tendsto
      (fun n =>
        ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
          ∂(supportElimMeasure (pkg.μn (pkg.φ n))))
      atTop
      (𝓝 (ENNReal.ofReal (loewnerKernel f x 0)))

/-- Assemble the fixed-boundary trace bridge from the tendsto contract and
the nonnegativity consequence of strict positivity. -/
theorem fixedBoundaryTraceBridge_of_tendsto
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hT : FixedBoundaryTraceTendsto pkg x) :
    FixedBoundaryTraceBridge pkg x where
  nonneg := loewnerKernel_zero_nonneg_of_globalStrictPosDef h hx hx0
  tendsto := hT.tendsto

/-- ENNReal-valued Cayley/Koranyi boundary trace identification from the named
tendsto contract. -/
theorem cayleyKoranyi_boundaryTrace_identification_of_tendsto
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hT : FixedBoundaryTraceTendsto pkg x) :
    ENNReal.ofReal (loewnerKernel f x 0) =
      ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ENNReal) :=
  cayleyKoranyi_boundaryTrace_identification_of_bridge
    (pkg := pkg) hx
    (fixedBoundaryTraceBridge_of_tendsto h pkg hx hx0 hT)

/-- Real-valued Cayley/Koranyi boundary trace identification from the named
tendsto contract. -/
theorem cayleyKoranyi_boundaryTrace_identification_toReal_of_tendsto
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hT : FixedBoundaryTraceTendsto pkg x) :
    loewnerKernel f x 0 =
      ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ℝ) :=
  cayleyKoranyi_boundaryTrace_identification_toReal_of_bridge
    (pkg := pkg) hx
    (fixedBoundaryTraceBridge_of_tendsto h pkg hx hx0 hT)

end Quantum.TraceInequality.Loewner
