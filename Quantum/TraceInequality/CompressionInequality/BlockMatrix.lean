import Quantum.TraceInequality.Core
import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.UnitaryBlockMatrix

/-!
# Block-operator calculus for compression inequalities

This module collects the concrete two-by-two block operators on
`WithLp 2 (K × K)` used in the Hansen--Pedersen compression argument.  It
provides algebraic identities for multiplication and adjoints.

## Main results

* `blockCLM`: the concrete two-by-two block operator.
* `blockCLM_mul` and `blockCLM_star`: algebraic facts for later Julia-unitary
  and compression constructions.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section BlockHelpers

variable {K : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugating a self-adjoint operator by an arbitrary operator preserves
self-adjointness of the resulting `C* T C`. -/
lemma star_mul_selfAdjoint_mul {T C : L K}
    (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (star C * T * C) := by
  change star (star C * T * C) = star C * T * C
  simp [mul_assoc, hT.star_eq]

/-- General `2 × 2` block operator on `WithLp 2 (K × K)`. -/
noncomputable def blockCLM (a b c d : L K) :
    L (WithLp 2 (K × K)) :=
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ K K : WithLp 2 (K × K) ≃L[ℂ] K × K)
  let fst := (ContinuousLinearMap.fst ℂ K K : K × K →L[ℂ] K)
  let snd := (ContinuousLinearMap.snd ℂ K K : K × K →L[ℂ] K)
  let row₁ : K × K →L[ℂ] K := a.comp fst + b.comp snd
  let row₂ : K × K →L[ℂ] K := c.comp fst + d.comp snd
  e.symm.toContinuousLinearMap.comp ((row₁.prod row₂).comp e.toContinuousLinearMap)

omit [CompleteSpace K] in
/-- Evaluation formula for `blockCLM` on the two components of `WithLp 2`. -/
@[simp] lemma blockCLM_apply (a b c d : L K) (x : WithLp 2 (K × K)) :
    blockCLM a b c d x =
      WithLp.toLp 2 (a x.fst + b x.snd, c x.fst + d x.snd) := by
  simp [blockCLM]

omit [CompleteSpace K] in
/-- A block operator with zero off-diagonal entries is the internal diagonal
map. -/
@[simp] lemma blockCLM_zero_zero (a d : L K) :
    blockCLM a 0 0 d = HansenPedersen.Internal.diagMapCLM a d := by
  ext x
  simp [HansenPedersen.Internal.diagMapCLM_apply]

omit [CompleteSpace K] in
/-- The identity block matrix is the identity operator on `WithLp 2 (K × K)`. -/
@[simp] lemma blockCLM_one :
    blockCLM (1 : L K) 0 0 (1 : L K) = (1 : L (WithLp 2 (K × K))) := by
  ext x
  apply WithLp.ofLp_injective
  ext
  · simp
  · simp

omit [CompleteSpace K] in
/-- Multiplication of concrete two-by-two block operators follows ordinary
matrix multiplication of the entries. -/
lemma blockCLM_mul (a b c d e f g h : L K) :
    blockCLM a b c d * blockCLM e f g h =
      blockCLM (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h) := by
  ext x
  simp [blockCLM_apply, add_left_comm, add_comm]

omit [CompleteSpace K] in
/-- Addition of concrete two-by-two block operators is entrywise addition. -/
lemma blockCLM_add (a b c d e f g h : L K) :
    blockCLM a b c d + blockCLM e f g h =
      blockCLM (a + e) (b + f) (c + g) (d + h) := by
  ext x
  apply WithLp.ofLp_injective
  ext
  · simp [blockCLM_apply, add_left_comm, add_comm]
  · simp [blockCLM_apply, add_left_comm, add_comm]

/-- Real scalar multiplication of a block operator is entrywise scalar
multiplication. -/
lemma smul_blockCLM (t : ℝ) (a b c d : L K) :
    t • blockCLM a b c d = blockCLM (t • a) (t • b) (t • c) (t • d) := by
  ext x
  apply WithLp.ofLp_injective
  ext
  · change t • (a x.fst + b x.snd) = t • a x.fst + t • b x.snd
    simp
  · change t • (c x.fst + d x.snd) = t • c x.fst + t • d x.snd
    simp

/-- Adjoint of a concrete two-by-two block operator is the conjugate-transpose
block operator. -/
lemma blockCLM_star (a b c d : L K) :
    star (blockCLM a b c d) = blockCLM (star a) (star c) (star b) (star d) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [blockCLM_apply, blockCLM_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  have h11 := ContinuousLinearMap.adjoint_inner_left a (y.fst) (x.fst)
  have h12 := ContinuousLinearMap.adjoint_inner_left c (y.fst) (x.snd)
  have h21 := ContinuousLinearMap.adjoint_inner_left b (y.snd) (x.fst)
  have h22 := ContinuousLinearMap.adjoint_inner_left d (y.snd) (x.snd)
  simp only [inner_add_left, inner_add_right] at *
  simpa [ContinuousLinearMap.star_eq_adjoint, add_assoc, add_left_comm, add_comm] using
    congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd h11 h12) (congrArg₂ HAdd.hAdd h21 h22)

end BlockHelpers

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
