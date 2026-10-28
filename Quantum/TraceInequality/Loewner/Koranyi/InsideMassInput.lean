import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceStagewiseSqInvDist

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped NNReal
open scoped Topology

noncomputable section

/-!
# Chapter 27 Proposition 27.3 input contract

This file records the theorem-58 contract layer.  It does not produce the
Chapter 27 estimate from `GlobalStrictPosDef`; it only packages a
Proposition 27.3-style stagewise inverse-square input and forwards it to the
existing signed-axis stagewise consumers.
-/

/--
Chapter 27 Proposition 27.3-type inverse-square input on the canonical
signed-evaluation backbone.

The fields are intentionally only a sufficient-condition contract: a stagewise
inverse-square bound `K n`, together with an eventual finite bound on `K`.
The actual Chapter 27 producer for this input remains a separate frontier.

Proposition 27.3 of [simon2019].
-/
structure SignedAxisSqInvDistInput {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) where
  K : ℕ → ℝ≥0
  C : ℝ≥0
  hK_bound :
    ∀ n : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount (pkg.φ n) + 1),
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
            (zeroAnchoredDyadicPointFamily (pkg.φ n) i) y ∂(pkg.μn (pkg.φ n))) ≤
        (K n : ENNReal)
  hK_le : ∀ᶠ n in atTop, K n ≤ C

/--
The Chapter 27 Proposition 27.3 input supplies the existing stagewise
inverse-square bound on the same signed-evaluation backbone.

Proposition 27.3 of [simon2019].
-/
def signedAxisStagewiseSqInvDistBound_of_signedAxisSqInvDistInput
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hinput : SignedAxisSqInvDistInput pkg) :
    SignedAxisStagewiseSqInvDistBound pkg :=
  signedAxisStagewiseSqInvDistBound_of_eventually_le_const
    hinput.hK_bound hinput.C hinput.hK_le

/--
The Chapter 27 Proposition 27.3 input implies inside mass decay through the
existing stagewise inverse-square consumer.

Proposition 27.3 of [simon2019].
-/
theorem signedAxisInsideMassDecay_of_signedAxisSqInvDistInput
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hinput : SignedAxisSqInvDistInput pkg) :
    SignedAxisInsideMassDecay pkg :=
  signedAxisInsideMassDecay_of_sqInvDist_bound
    (signedAxisStagewiseSqInvDistBound_of_signedAxisSqInvDistInput hinput)

end

end Quantum.TraceInequality.Loewner
