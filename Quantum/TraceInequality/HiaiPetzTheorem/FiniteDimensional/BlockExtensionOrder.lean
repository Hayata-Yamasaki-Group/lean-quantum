/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.OrderTransport
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

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
/-- For a self-adjoint difference `T - S`, nonnegativity of every quadratic
form implies the Loewner inequality `S ≤ T`. -/
theorem le_of_quadratic_form_nonneg
    {S T : L ℋ}
    (hself : IsSelfAdjoint (T - S))
    (hquad : ∀ x : ℋ, 0 ≤ RCLike.re (inner ℂ ((T - S) x) x)) :
    S ≤ T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  refine ⟨?_, hquad x⟩
  have hsymm : (T - S).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  exact Complex.conj_eq_iff_re.mp
    ((LinearMap.isSymmetric_iff_inner_map_self_real _).mp hsymm x)

/-- If two operators both satisfy the scalar lower and upper bounds
`α I ≤ · ≤ β I`, then their midpoint satisfies the same bounds. -/
theorem midpoint_order_bounds
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {A B : K →L[ℂ] K} {α β : ℝ}
    (hA : (α : ℂ) • (1 : K →L[ℂ] K) ≤ A ∧ A ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (hB : (α : ℂ) • (1 : K →L[ℂ] K) ≤ B ∧ B ≤ (β : ℂ) • (1 : K →L[ℂ] K)) :
    (α : ℂ) • (1 : K →L[ℂ] K) ≤ (1 / 2 : ℝ) • (A + B) ∧
      (1 / 2 : ℝ) • (A + B) ≤ (β : ℂ) • (1 : K →L[ℂ] K) := by
  constructor
  · have hadd :
        (α : ℂ) • (1 : K →L[ℂ] K) + (α : ℂ) • (1 : K →L[ℂ] K) ≤ A + B := by
      exact add_le_add hA.1 hB.1
    have h2 : (2 : ℝ) • ((α : ℂ) • (1 : K →L[ℂ] K)) ≤ A + B := by
      simpa [two_smul] using hadd
    have hhalf := smul_le_smul_of_nonneg_left h2 (show 0 ≤ (1 / 2 : ℝ) by positivity)
    simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hhalf
  · have hadd :
        A + B ≤ (β : ℂ) • (1 : K →L[ℂ] K) + (β : ℂ) • (1 : K →L[ℂ] K) := by
      exact add_le_add hA.2 hB.2
    have h2 : A + B ≤ (2 : ℝ) • ((β : ℂ) • (1 : K →L[ℂ] K)) := by
      simpa [two_smul] using hadd
    have hhalf := smul_le_smul_of_nonneg_left h2 (show 0 ≤ (1 / 2 : ℝ) by positivity)
    simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hhalf

/- Instance cache: the real scalar action on `K →L[ℂ] K` (and on submodule
endomorphism spaces `↥U →L[ℂ] ↥U`) triggers a deep `synthInstance` derivation
through the restricted real structure, exceeding the default budget.  A file-local
reducible instance
turns each search into a head-match. -/
-- One-time search for the cache itself; every later use is a head-match.
-- Direct `SMul` search times out through non-algebra candidates; naming
-- `Algebra.toSMul` leaves only the cheap `Algebra ℝ _` subgoal.
/-- Local reducible cache for real scalar multiplication on submodule
endomorphisms used by midpoint compression calculations. -/
@[reducible, local instance] noncomputable def instSMulRealSubmoduleEndScopedBEO
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {U : Submodule ℂ K} :
    SMul ℝ (↥U →L[ℂ] ↥U) :=
  Algebra.toSMul

/-- Compression by an orthogonal projection commutes with taking the midpoint
of two ambient operators. -/
theorem compression_midpoint_eq
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {U : Submodule ℂ K} [U.HasOrthogonalProjection] {A B : K →L[ℂ] K} :
    U.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L U.subtypeL =
      (1 / 2 : ℝ) •
        ((U.orthogonalProjection ∘L A ∘L U.subtypeL) +
          (U.orthogonalProjection ∘L B ∘L U.subtypeL)) := by
  have hscalar : ((1 / 2 : ℝ) • (A + B)) = (((1 / 2 : ℂ)) • (A + B)) := by
    change ((((1 / 2 : ℝ) : ℂ)) • (A + B)) = (((1 / 2 : ℂ)) • (A + B))
    norm_num
  calc
    U.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L U.subtypeL
        = U.orthogonalProjection ∘L (((1 / 2 : ℂ)) • (A + B)) ∘L U.subtypeL := by
            rw [hscalar]
    _ = ((1 / 2 : ℂ)) • (U.orthogonalProjection ∘L (A + B) ∘L U.subtypeL) := by
            rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    _ = ((1 / 2 : ℂ)) •
          ((U.orthogonalProjection ∘L A ∘L U.subtypeL) +
            (U.orthogonalProjection ∘L B ∘L U.subtypeL)) := by
          rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    _ = (1 / 2 : ℝ) •
          ((U.orthogonalProjection ∘L A ∘L U.subtypeL) +
            (U.orthogonalProjection ∘L B ∘L U.subtypeL)) := by
          change
            ((1 / 2 : ℂ)) •
                ((U.orthogonalProjection ∘L A ∘L U.subtypeL) +
                  (U.orthogonalProjection ∘L B ∘L U.subtypeL)) =
              ((((1 / 2 : ℝ) : ℂ)) •
                ((U.orthogonalProjection ∘L A ∘L U.subtypeL) +
                  (U.orthogonalProjection ∘L B ∘L U.subtypeL)))
          norm_num

end NormalCFC514

end HansenPedersen
