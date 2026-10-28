/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Core lemmas for the Hansen–Pedersen development

Shared entry-level lemmas for the Hiai–Yanagi Chapter 5.1 formalization:
adapters between the foundational `LownerHeinzTheorem.OperatorMonotoneOn`
and the book-faithful `OperatorMonotoneOnInterval`, together with the
Löwner–Heinz power monotonicity `opRpow_le_opRpow` and spectrum-based
order bounds used throughout the chapter.

## Main results

* `opRpow_le_opRpow`: `0 ≤ A ≤ B` implies `A ^ p ≤ B ^ p` for `p ∈ [0, 1]`
  (Löwner–Heinz).
* `operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici` /
  `..._Ioi`: hypothesis-order adapters from the foundational predicate.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology CStarAlgebra
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

namespace Internal

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L' : Type*} [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']

/-- The block-diagonal continuous linear endomorphism of `WithLp 2 (K × L')`
built from blocks `a : K →L[ℂ] K` and `b : L' →L[ℂ] L'`, acting as `a` on the
first component and `b` on the second. -/
noncomputable def diagMapCLM (a : K →L[ℂ] K) (b : L' →L[ℂ] L') :
    (WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L')) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ K L').symm :
      K × L' →L[ℂ] WithLp 2 (K × L')).comp <|
    (a.prodMap b).comp ((WithLp.prodContinuousLinearEquiv 2 ℂ K L') :
      WithLp 2 (K × L') →L[ℂ] K × L')

omit [CompleteSpace K] [CompleteSpace L'] in
/-- Componentwise action of the block-diagonal map: `diagMapCLM a b` sends `x`
to `(a x.fst, b x.snd)`. -/
@[simp] lemma diagMapCLM_apply (a : K →L[ℂ] K) (b : L' →L[ℂ] L')
    (x : WithLp 2 (K × L')) :
    diagMapCLM a b x = WithLp.toLp 2 (a x.fst, b x.snd) := by
  rfl

/-- The adjoint (star) of a block-diagonal map is the block-diagonal map of the
blockwise adjoints. -/
lemma diagMapCLM_star (a : K →L[ℂ] K) (b : L' →L[ℂ] L') :
    star (diagMapCLM a b) = diagMapCLM (star a) (star b) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change inner ℂ (WithLp.toLp 2 ((star a) x.fst, (star b) x.snd)) y =
      inner ℂ x (WithLp.toLp 2 (a y.fst, b y.snd))
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  have h1 := ContinuousLinearMap.adjoint_inner_left a (y.fst) (x.fst)
  have h2 := ContinuousLinearMap.adjoint_inner_left b (y.snd) (x.snd)
  simpa [ContinuousLinearMap.star_eq_adjoint] using congrArg₂ HAdd.hAdd h1 h2

/-- If both blocks are self-adjoint, the block-diagonal map is self-adjoint. -/
lemma isSelfAdjoint_diagMapCLM
    {a : K →L[ℂ] K} {b : L' →L[ℂ] L'}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (diagMapCLM a b) := by
  change star (diagMapCLM a b) = diagMapCLM a b
  calc
    star (diagMapCLM a b) = diagMapCLM (star a) (star b) := diagMapCLM_star (a := a) (b := b)
    _ = diagMapCLM a b := by
      ext x
      apply WithLp.ofLp_injective
      ext
      · simpa using congrArg (fun T : K →L[ℂ] K => T x.fst) ha
      · simpa using congrArg (fun T : L' →L[ℂ] L' => T x.snd) hb

/-- The `⋆`-algebra homomorphism from the product algebra
`(K →L[ℂ] K) × (L' →L[ℂ] L')` into endomorphisms of `WithLp 2 (K × L')`, sending
a pair `(a, b)` to the block-diagonal map `diagMapCLM a b`. -/
noncomputable def diagStarAlgHom :
    ((K →L[ℂ] K) × (L' →L[ℂ] L')) →⋆ₐ[ℂ]
      ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) where
  toFun ab := diagMapCLM ab.1 ab.2
  map_one' := by
    ext x
    cases x
    rfl
  map_mul' a b := by
    ext x
    apply WithLp.ofLp_injective
    simp [diagMapCLM_apply, WithLp.ofLp_toLp]
  map_zero' := by
    ext x
    cases x
    rfl
  map_add' := by
    intro a b
    ext x
    cases x
    rfl
  commutes' r := by
    ext x
    cases x
    rfl
  map_star' ab := by
    symm
    simpa using diagMapCLM_star ab.1 ab.2

/-- `Star` structure on endomorphisms of a complete submodule `U ⊆ ℋ`, given by
the Hilbert-space adjoint. -/
noncomputable instance instStarSubmoduleEnd {U : Submodule ℂ ℋ} [CompleteSpace U] :
    Star (U →L[ℂ] U) where
  star A :=
    (@ContinuousLinearMap.adjoint ℂ U U _ _ _ _ _ ‹CompleteSpace U› ‹CompleteSpace U›) A

/-- `InvolutiveStar` structure on endomorphisms of a complete submodule `U ⊆ ℋ`:
the adjoint is an involution. -/
noncomputable instance instInvolutiveStarSubmoduleEnd {U : Submodule ℂ ℋ} [CompleteSpace U] :
    InvolutiveStar (U →L[ℂ] U) where
  star_involutive A := by
    simpa using
      (@ContinuousLinearMap.adjoint_adjoint ℂ U U _ _ _ _ _ ‹CompleteSpace U›
        ‹CompleteSpace U› A)

/-- `StarMul` structure on endomorphisms of a complete submodule `U ⊆ ℋ`: the
adjoint of a product is the reversed product of adjoints. -/
noncomputable instance instStarMulSubmoduleEnd {U : Submodule ℂ ℋ} [CompleteSpace U] :
    StarMul (U →L[ℂ] U) where
  star_mul A B := by
    simpa using
      (@ContinuousLinearMap.adjoint_comp ℂ U U U _ _ _ _ _ _ _ ‹CompleteSpace U›
        ‹CompleteSpace U› ‹CompleteSpace U› A B)

/-- `StarRing` structure on endomorphisms of a complete submodule `U ⊆ ℋ`,
assembling the additive and multiplicative compatibility of the adjoint. -/
noncomputable instance instStarRingSubmoduleEnd {U : Submodule ℂ ℋ} [CompleteSpace U] :
    StarRing (U →L[ℂ] U) where
  star_add A B := by
    exact map_add
      (@ContinuousLinearMap.adjoint ℂ U U _ _ _ _ _ ‹CompleteSpace U›
        ‹CompleteSpace U›) A B

end Internal

end HansenPedersen
