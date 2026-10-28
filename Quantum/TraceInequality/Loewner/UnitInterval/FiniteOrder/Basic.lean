import Quantum.TraceInequality.Loewner.UnitInterval.StrictHardDirection

/-!
# Chapter 20 finite-order regularity basic definitions

This file contains the lowest-level public data structures and canonical
approximant definitions used by the Chapter 20 finite-order regularity proof.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal

noncomputable section

/--
Explicit strictification input for the book-route Theorem 20.1 reduction.

The `pos` field records the original public Löwner-positivity input, while the
remaining fields record the smooth strict approximants and the weak-limit
transfer back to `f`.  The package is constructed from `pos` by
`bookStrictificationInput_of_loewnerPosOnUnitInterval_of_interiorSmooth_of_limitTransfer`,
with interior smoothness from `publicSmoothRegularity_of_finiteOrderRegularityInput` and
the limit transfer from `canonicalStrictificationApproximant_limitTransferInput_of_loewnerPos`
(all in `CanonicalStrictificationBridge.lean`).
-/
structure BookStrictificationInput (f : ℝ → ℝ) where
  pos : LoewnerPosOnUnitInterval f
  approximant : ℕ → ℝ → ℝ
  smoothStrict : ∀ n : ℕ, GlobalStrictSmoothNeighborhoodInput (approximant n)
  limitTransfer : BookRouteLimitTransferInput f approximant

/--
Canonical Chapter 20 strictification approximants
`f_{ε_n,δ_n}(x) = f((1-δ_n)x) + ε_n g₀(x)`.
-/
def bookCanonicalStrictificationApproximant
    (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  bookSmoothApprox f (bookEpsilon n) (bookDelta n)

/-- The canonical perturbation parameter is uniformly bounded by `1`. -/
theorem bookEpsilon_le_one (n : ℕ) :
    bookEpsilon n ≤ 1 := by
  unfold bookEpsilon
  have hge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    norm_num
  simpa using inv_le_one_of_one_le₀ hge

end

end Quantum.TraceInequality.Loewner
