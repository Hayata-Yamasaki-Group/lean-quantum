import Quantum.OperationalProbabilistic.Framework.FiniteIIDPMF.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Finite events

`w41Event P` is the finite set of points of a finite type satisfying `P`.  This module keeps the
declarations of the original module that the public development uses.
-/

open scoped BigOperators

universe u

namespace GourConditionalEntropy

/-- A predicate viewed as a finite event, using classical decidability. -/
noncomputable def w41Event {α : Type u} [Fintype α] (P : α → Prop) : Finset α := by
  classical
  exact Finset.univ.filter P

end GourConditionalEntropy
