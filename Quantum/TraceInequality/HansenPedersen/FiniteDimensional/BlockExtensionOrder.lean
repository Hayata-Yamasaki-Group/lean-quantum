/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.OrderTransport
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.BlockExtensionOrder

/-!
# Order facts for finite-dimensional block extensions

This module keeps the order-transport helpers used by the finite-dimensional
Hansen–Pedersen functional-calculus bridge outside the heavier CFC payload.

## Main results

* `le_of_quadratic_form_nonneg`: converts nonnegative quadratic forms into
  Loewner order.
* `le_of_sub_clm_tendsto_of_pointwise_le`: passes order inequalities through
  pointwise strong limits of operator differences.
* `midpoint_order_bounds`: interval bounds are preserved by operator midpoints.
* `compression_midpoint_eq`: compression commutes with taking midpoints.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Lemma 5.1.4 and
  Proposition 5.1.5.
-/

namespace HansenPedersen

universe u

open scoped Topology MatrixOrder
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Loewner order is closed under pointwise strong limits of differences: if
`Aγ i ≤ Bγ i` and `Bγ i - Aγ i` tends pointwise to `B - A`, then `A ≤ B`. -/
theorem le_of_sub_clm_tendsto_of_pointwise_le
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hself : IsSelfAdjoint (B - A))
    (hγ : ∀ i, Aγ i ≤ Bγ i)
    (hsub : ∀ x : ℋ, Tendsto (fun i : ι => ((Bγ i - Aγ i) x)) atTop (𝓝 ((B - A) x))) :
    A ≤ B := by
  refine le_of_quadratic_form_nonneg (ℋ := ℋ) hself ?_
  intro x
  have hquad :
      ∀ i, 0 ≤ RCLike.re (inner ℂ ((Bγ i - Aγ i) x) x) :=
    quadratic_form_nonneg_of_pointwise_le (ℋ := ℋ) (T := Aγ) (S := Bγ) hγ x
  have hinner_eval :
      Tendsto (fun i : ι => Complex.re (inner ℂ ((Bγ i - Aγ i) x) x))
        atTop
        (𝓝 (Complex.re (inner ℂ ((B - A) x) x))) :=
    real_inner_tendsto_of_clm_tendsto (ℋ := ℋ) (hsub x) x
  exact isClosed_Ici.mem_of_tendsto hinner_eval (Filter.Eventually.of_forall hquad)

/- Instance cache: the real scalar action on `K →L[ℂ] K` (and on submodule
endomorphism spaces `↥U →L[ℂ] ↥U`) triggers a deep `synthInstance` derivation
through the restricted real structure, exceeding the default budget.  A file-local
reducible instance
turns each search into a head-match. -/
-- One-time search for the cache itself; every later use is a head-match.
-- Direct `SMul` search times out through non-algebra candidates; naming
-- `Algebra.toSMul` leaves only the cheap `Algebra ℝ _` subgoal.
attribute [local instance] instSMulRealSubmoduleEndScopedBEO

end NormalCFC514

end HansenPedersen
