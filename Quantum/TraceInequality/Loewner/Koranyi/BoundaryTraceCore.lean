import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceProvider

namespace Quantum.TraceInequality.Loewner

open scoped NNReal

noncomputable section

/-!
# Fixed-boundary trace candidate-identification consumers

This file is not the analytic producer for the fixed-boundary trace limit.
It records the consumer layer: once the Cayley/Koranyi candidate is identified
with the Löwner-kernel boundary value, the existing `StrictApproxPackage`
Koranyi convergence yields `FixedBoundaryTraceTendsto`, hence the bridge and
the boundary-trace identifications.
-/

/-- Candidate identification needed to consume `StrictApproxPackage.hKoranyi`.

The analytic frontier is to produce this equality from the support-elimination,
inside-correction, and outside-comparison arguments. -/
structure BoundaryTraceCandidateIdentification {f : ℝ → ℝ}
    (pkg : StrictApproxPackage f) (x : ℝ) : Prop where
  eq :
    ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ENNReal) =
      ENNReal.ofReal (loewnerKernel f x 0)

/-- Turn candidate identification into the fixed-boundary trace tendsto contract. -/
theorem fixedBoundaryTraceTendsto_of_candidate_identification
    {f : ℝ → ℝ} (pkg : StrictApproxPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hId : BoundaryTraceCandidateIdentification pkg x) :
    FixedBoundaryTraceTendsto pkg x where
  tendsto := by
    rw [← hId.eq]
    exact pkg.hKoranyi x hx

/-- Signed-backbone specialization of the candidate-identification consumer. -/
theorem fixedBoundaryTraceTendsto_of_globalStrictPosDef_of_candidate_identification
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hId :
      BoundaryTraceCandidateIdentification
        (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x) :
    FixedBoundaryTraceTendsto
      (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x :=
  fixedBoundaryTraceTendsto_of_candidate_identification
    (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage hx hId

/-- Assemble the fixed-boundary trace bridge on the signed backbone. -/
theorem fixedBoundaryTraceBridge_of_globalStrictPosDef_of_candidate_identification
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hId :
      BoundaryTraceCandidateIdentification
        (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x) :
    FixedBoundaryTraceBridge
      (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x :=
  fixedBoundaryTraceBridge_of_tendsto h
    (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage
    hx hx0
    (fixedBoundaryTraceTendsto_of_globalStrictPosDef_of_candidate_identification h hx hId)

/-- ENNReal-valued boundary trace identification from candidate identification. -/
theorem cayleyKoranyi_boundaryTrace_identification_of_candidate_identification
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hId :
      BoundaryTraceCandidateIdentification
        (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x) :
    ENNReal.ofReal (loewnerKernel f x 0) =
      ((ratioFunctional
          (strictApproximantSignedEval_of_globalStrictPosDef h).ν
          (Real.toNNReal (cayley x)) : ℝ≥0) : ENNReal) :=
  cayleyKoranyi_boundaryTrace_identification_of_bridge
    (pkg := (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage)
    hx
    (fixedBoundaryTraceBridge_of_globalStrictPosDef_of_candidate_identification h hx hx0 hId)

/-- Real-valued boundary trace identification from candidate identification. -/
theorem cayleyKoranyi_boundaryTrace_identification_toReal_of_candidate_identification
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hId :
      BoundaryTraceCandidateIdentification
        (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage x) :
    loewnerKernel f x 0 =
      ((ratioFunctional
          (strictApproximantSignedEval_of_globalStrictPosDef h).ν
          (Real.toNNReal (cayley x)) : ℝ≥0) : ℝ) :=
  cayleyKoranyi_boundaryTrace_identification_toReal_of_bridge
    (pkg := (strictApproximantSignedEval_of_globalStrictPosDef h).toStrictApproxPackage)
    hx
    (fixedBoundaryTraceBridge_of_globalStrictPosDef_of_candidate_identification h hx hx0 hId)

end

end Quantum.TraceInequality.Loewner
