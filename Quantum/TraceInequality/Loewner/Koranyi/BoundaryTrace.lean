import Quantum.TraceInequality.Loewner.Koranyi.StrictApproxPackage
import Quantum.TraceInequality.Loewner.Koranyi.SignedPointsKernelZeroAxis
import Quantum.TraceInequality.Loewner.Statement


namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section

/-!
Bridge-assumption API for the Cayley/Koranyi boundary trace step.

This file intentionally avoids importing historical path shims.  The only
argument used here is uniqueness of limits: `pkg.hKoranyi` gives the
`ratioFunctional` limit, while `FixedBoundaryTraceBridge.tendsto` gives the
same sequence converging to the Löwner-kernel boundary value.
-/

/-- Strict approximation package enhanced with the signed-points finite evaluation identity.

This package deliberately records only the finite-dimensional signed-evaluation data needed
to split the signed-axis evaluation identity.  Support elimination, Koranyi
transport, and fixed-boundary trace control are left to later provider lemmas. -/
structure StrictApproxSignedEvalPackage (f : ℝ → ℝ) extends StrictApproxPackage f where
  hKernelIntegrableSubseq :
    ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn (φ n))
  hEvalSigned :
    ∀ n : ℕ, ∀ i : Fin (φ n + 1), i ≠ 0 →
      (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
        ∫ t, (1 / (1 - (signedPoints (φ n) i : ℂ) * (t : ℂ))) ∂(μn (φ n))


/--
Build the signed-evaluation extension from the global strict positivity
hypothesis.
-/
noncomputable def strictApproximantSignedEval_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) :
    StrictApproxSignedEvalPackage f :=
  let p :=
    Classical.choice
      (exists_supportElimStieltjesDiffSubseq_of_signedGlobalPosDef_zeroAxis_kernelIntegrable
        (f := f) h)
  { toStrictApproxPackage := p.toStrictApproxFullPackage.toStrictApproxPackage
    hKernelIntegrableSubseq := p.hKernelIntegrableSubseq
    hEvalSigned := p.hSignedZeroAxis }

/-- Hypothesis package for the still-open fixed-boundary trace bridge.

The interval hypothesis `x ∈ (-1, 1)` is kept outside this structure, because
it is only needed to consume `StrictApproxPackage.hKoranyi`. -/
structure FixedBoundaryTraceBridge {f : ℝ → ℝ}
    (pkg : StrictApproxPackage f) (x : ℝ) : Prop where
  nonneg : 0 ≤ loewnerKernel f x 0
  tendsto :
    Tendsto
      (fun n =>
        ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
          ∂(supportElimMeasure (pkg.μn (pkg.φ n))))
      atTop
      (𝓝 (ENNReal.ofReal (loewnerKernel f x 0)))

/-- The non-negativity bundled in a fixed-boundary trace bridge. -/
theorem FixedBoundaryTraceBridge.loewnerKernel_nonneg
    {f : ℝ → ℝ} {pkg : StrictApproxPackage f} {x : ℝ}
    (hbridge : FixedBoundaryTraceBridge pkg x) :
    0 ≤ loewnerKernel f x 0 :=
  hbridge.nonneg

/-- Boundary trace identification under an explicit fixed-boundary bridge hypothesis. -/
theorem cayleyKoranyi_boundaryTrace_identification_of_bridge
    {f : ℝ → ℝ} (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hbridge : FixedBoundaryTraceBridge pkg x) :
    ENNReal.ofReal (loewnerKernel f x 0) =
      ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ENNReal) := by
  exact tendsto_nhds_unique hbridge.tendsto (pkg.hKoranyi x hx)

/-- Real-valued form of the bridge-assumption boundary trace identification. -/
theorem cayleyKoranyi_boundaryTrace_identification_toReal_of_bridge
    {f : ℝ → ℝ} (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hbridge : FixedBoundaryTraceBridge pkg x) :
    loewnerKernel f x 0 =
      ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ℝ) := by
  have hEN :=
    cayleyKoranyi_boundaryTrace_identification_of_bridge
      (pkg := pkg) hx hbridge
  have h := congrArg ENNReal.toReal hEN
  simpa only [ENNReal.toReal_ofReal hbridge.nonneg, ENNReal.coe_toReal] using h

end

end Loewner
end TraceInequality
end Quantum
