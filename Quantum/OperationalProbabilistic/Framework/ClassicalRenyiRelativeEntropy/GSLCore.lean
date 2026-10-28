/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

-- The logarithm-base definitions are used only in the closed endpoint formulas.
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore

open scoped BigOperators ENNReal

/-!
# Classical Rényi relative entropy in bits

The KL divergence and the positive finite-order Rényi divergence of finite PMFs are rescaled
from the natural logarithm to bits by `log 2`.  The order-zero value is given by the closed
formula through the support overlap (`classicalMinRelativeEntropyBitsPMF`); it is infinite when
the overlap vanishes.
-/

namespace OPT

noncomputable section

/-! ## Positive finite orders and order one -/

/-- The classical Kullback--Leibler divergence in bits. -/
noncomputable def classicalKLDivergenceBitsPMF
    {ι : Type} [Fintype ι] (p q : PMF ι) : ℝ≥0∞ :=
  classicalRelEntropyPMF p q / ENNReal.ofReal (Real.log 2)

/-- The existing positive-finite classical Rényi divergence, rescaled from
natural logarithms to bits without changing any of its support branches. -/
noncomputable def classicalRenyiDivBitsFinitePMF
    (alpha : RenyiOrder) {ι : Type} [Fintype ι]
    (p q : PMF ι) : ℝ≥0∞ :=
  classicalRenyiDivPMF alpha p q / ENNReal.ofReal (Real.log 2)

/-! ## Closed endpoint formulas -/

/-- The mass that `q` assigns to the support of `p`. -/
noncomputable def classicalSupportOverlapPMF
    {ι : Type} [Fintype ι] (p q : PMF ι) : ℝ≥0∞ := by
  classical
  exact ∑ i, if i ∈ p.support then q i else 0

/-- The order-zero, or min-relative, classical Rényi entropy in bits.  Zero
support overlap is assigned `∞`. -/
noncomputable def classicalMinRelativeEntropyBitsPMF
    {ι : Type} [Fintype ι] (p q : PMF ι) : ℝ≥0∞ :=
  if classicalSupportOverlapPMF p q = 0 then
    ⊤
  else
    ENNReal.ofReal (-Real.logb 2 (classicalSupportOverlapPMF p q).toReal)

/-- Zero support overlap selects the infinite order-zero branch. -/
theorem classicalMinRelativeEntropyBitsPMF_of_overlap_eq_zero
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (hoverlap : classicalSupportOverlapPMF p q = 0) :
    classicalMinRelativeEntropyBitsPMF p q = ⊤ := by
  simp [classicalMinRelativeEntropyBitsPMF, hoverlap]

end

end OPT
