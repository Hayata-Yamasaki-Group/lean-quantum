import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure

namespace Quantum.TraceInequality.Loewner

open MeasureTheory

noncomputable section

/--
Neutral finite-stage witness for the Chapter 27 Proposition 27.3 route.

The witness deliberately records only a symmetric finite-dimensional operator,
its vector, and the associated Dirac/spectral measure.  It does not decide here
whether a later concrete adapter will instantiate `T` by the dyadic operator or
by a transformed operator.

Proposition 27.3 of [simon2019].
-/
structure FiniteResolventWitness (f : ℝ → ℝ) (m : ℕ) where
  H : Type
  instNormedAddCommGroup : NormedAddCommGroup H
  instInnerProductSpace : InnerProductSpace ℂ H
  instFiniteDimensional : FiniteDimensional ℂ H
  T : H →ₗ[ℂ] H
  hT : T.IsSymmetric
  φ : H

attribute [instance] FiniteResolventWitness.instNormedAddCommGroup
attribute [instance] FiniteResolventWitness.instInnerProductSpace
attribute [instance] FiniteResolventWitness.instFiniteDimensional

namespace FiniteResolventWitness

variable {f : ℝ → ℝ} {m : ℕ}

/-- The Dirac/spectral measure attached to a finite-stage Prop. 27.3 witness. -/
def diracMeasure (W : FiniteResolventWitness f m) : Measure ℝ :=
  _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
    (T := W.T) (hT := W.hT) W.φ

end FiniteResolventWitness

end

end Quantum.TraceInequality.Loewner
