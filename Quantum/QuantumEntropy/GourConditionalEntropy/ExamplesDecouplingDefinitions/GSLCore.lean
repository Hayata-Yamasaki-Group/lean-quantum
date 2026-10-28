import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumEntropy.GourBipartiteChoiDictionary.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.TraceInequality.HilbertSchmidtOperatorSpace

/-!
# The trace of the square

`w40Q X = Tr (X^2)` is complex bilinear, not the Hilbert--Schmidt square.  This module keeps the
declarations of the original module that the public development uses.
-/

open QuantumState QuantumChannel MeasureTheory
open scoped TensorProduct ComplexOrder
universe u

namespace GourConditionalEntropy

noncomputable def w40Q {H : Type u} [Qudit.{u} H] (X : L H) : ℂ := Tr (X ^ 2)

end GourConditionalEntropy
