import Quantum.TraceInequality.Loewner.Koranyi.InsideMassInput
import Quantum.TraceInequality.Loewner.Koranyi.FiniteResolventWitness

namespace Quantum.TraceInequality.Loewner

open MeasureTheory

noncomputable section

/-!
# Same-witness package contract for Chapter 27 Proposition 27.3

This file introduces only the data-carrying package layer.  It does not
construct the package from `GlobalStrictPosDef`; that producer remains a
separate frontier.
-/

/--
Same-witness package contract for feeding Chapter 27 Proposition 27.3 into the
canonical signed-evaluation backbone.

The fields keep the signed-evaluation package, finite-stage witnesses, the
canonical-measure identity, and the Prop. 27.3 input in one package.  This is
the Lean-level contract that prevents combining independently chosen witnesses.

Proposition 27.3 of [simon2019].
-/
structure StrictApproxSameWitnessSqInvDistPackage (f : ℝ → ℝ)
    extends StrictApproxSignedEvalPackage f where
  stageWitness : ∀ n : ℕ, FiniteResolventWitness f (φ n)
  hμ_eq : ∀ n : ℕ, μn (φ n) = (stageWitness n).diracMeasure
  hProp273Input :
    SignedAxisSqInvDistInput toStrictApproxSignedEvalPackage

/-- Extract the Prop. 27.3 input carried by a same-witness package.
Proposition 27.3 of [simon2019]. -/
def signedAxisSqInvDistInput_of_sameWitnessPackage
    {f : ℝ → ℝ} (pkg : StrictApproxSameWitnessSqInvDistPackage f) :
    SignedAxisSqInvDistInput pkg.toStrictApproxSignedEvalPackage :=
  pkg.hProp273Input

/--
The same-witness package supplies the existing stagewise inverse-square
condition on its signed-evaluation projection.

Proposition 27.3 of [simon2019].
-/
def signedAxisStagewiseSqInvDistBound_of_sameWitnessPackage
    {f : ℝ → ℝ} (pkg : StrictApproxSameWitnessSqInvDistPackage f) :
    SignedAxisStagewiseSqInvDistBound pkg.toStrictApproxSignedEvalPackage :=
  signedAxisStagewiseSqInvDistBound_of_signedAxisSqInvDistInput
    (signedAxisSqInvDistInput_of_sameWitnessPackage pkg)

/--
The same-witness package implies inside mass decay through the existing
Chapter 27 input consumer.

Proposition 27.3 of [simon2019].
-/
theorem signedAxisInsideMassDecay_of_sameWitnessPackage
    {f : ℝ → ℝ} (pkg : StrictApproxSameWitnessSqInvDistPackage f) :
    SignedAxisInsideMassDecay pkg.toStrictApproxSignedEvalPackage :=
  signedAxisInsideMassDecay_of_signedAxisSqInvDistInput
    (signedAxisSqInvDistInput_of_sameWitnessPackage pkg)

end

end Quantum.TraceInequality.Loewner
