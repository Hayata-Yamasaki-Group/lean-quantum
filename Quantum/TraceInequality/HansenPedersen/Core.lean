/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.OperatorCore
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

/-- Nontriviality of the operator algebra forces nontriviality of its Hilbert
space. -/
theorem nontrivial_of_nontrivial_L
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial (L K)] :
    Nontrivial K := by
  by_contra hK
  haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
  exact zero_ne_one (Subsingleton.elim (0 : L K) (1 : L K))

/-- Real continuous functional calculus always produces a self-adjoint
operator. -/
theorem isSelfAdjoint_cfcR
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {A : L K} :
    IsSelfAdjoint (cfcR (ℋ := K) f A) := by
  rw [cfcR]
  exact IsSelfAdjoint.cfc (R := ℝ) (A := L K) (f := f) (a := A)

namespace Internal

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L' : Type*} [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']

/-- The off-diagonal block map on `WithLp 2 (K × K)`, with `a` in the
upper-right block and `b` in the lower-left block. -/
noncomputable def offDiagCLM (a b : K →L[ℂ] K) :
    (WithLp 2 (K × K)) →L[ℂ] (WithLp 2 (K × K)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ K K).symm :
      K × K →L[ℂ] WithLp 2 (K × K)).comp <|
    (a.prodMap b).comp
      (((ContinuousLinearEquiv.prodComm ℂ K K : (K × K) ≃L[ℂ] (K × K)) :
        (K × K) →L[ℂ] (K × K)).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℂ K K) :
          WithLp 2 (K × K) →L[ℂ] K × K))

omit [CompleteSpace K] in
/-- Componentwise action of `offDiagCLM`. -/
@[simp] lemma offDiagCLM_apply (a b : K →L[ℂ] K) (x : WithLp 2 (K × K)) :
    offDiagCLM a b x = WithLp.toLp 2 (a x.snd, b x.fst) := by
  apply congrArg (WithLp.toLp 2)
  ext <;> rfl

omit [CompleteSpace K] in
/-- The product of two off-diagonal block maps is block diagonal. -/
lemma offDiagCLM_mul_offDiagCLM (a b c d : K →L[ℂ] K) :
    offDiagCLM a b * offDiagCLM c d = diagMapCLM (a * d) (b * c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

omit [CompleteSpace K] in
/-- Left multiplication of an off-diagonal map by a diagonal map. -/
lemma diagMapCLM_mul_offDiagCLM (a b c d : K →L[ℂ] K) :
    diagMapCLM a b * offDiagCLM c d = offDiagCLM (a * c) (b * d) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

omit [CompleteSpace K] in
/-- Right multiplication of an off-diagonal map by a diagonal map. -/
lemma offDiagCLM_mul_diagMapCLM (a b c d : K →L[ℂ] K) :
    offDiagCLM a b * diagMapCLM c d = offDiagCLM (a * d) (b * c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

omit [CompleteSpace K] in
/-- Equality of off-diagonal block maps is equivalent to equality of their two blocks. -/
lemma offDiagCLM_inj {a₁ b₁ a₂ b₂ : K →L[ℂ] K}
    (h : offDiagCLM a₁ b₁ = offDiagCLM a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · ext x
    have hx := congrArg
      (fun T : (WithLp 2 (K × K)) →L[ℂ] (WithLp 2 (K × K)) =>
        (T (WithLp.toLp 2 (0, x))).fst) h
    simpa using hx
  · ext x
    have hx := congrArg
      (fun T : (WithLp 2 (K × K)) →L[ℂ] (WithLp 2 (K × K)) =>
        (T (WithLp.toLp 2 (x, 0))).snd) h
    simpa using hx

omit [CompleteSpace K] [CompleteSpace L'] in
/-- The block-diagonal map of blockwise sums is the sum of the block-diagonal
maps. -/
lemma diagMapCLM_add (a₁ a₂ : K →L[ℂ] K) (b₁ b₂ : L' →L[ℂ] L') :
    diagMapCLM (a₁ + a₂) (b₁ + b₂) = diagMapCLM a₁ b₁ + diagMapCLM a₂ b₂ := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

/-- A real scalar factors through the block-diagonal map: scaling both blocks by
`r` equals scaling the block-diagonal map by `r`. -/
lemma diagMapCLM_smul_real (r : ℝ) (a : K →L[ℂ] K) (b : L' →L[ℂ] L') :
    diagMapCLM (r • a) (r • b) = r • diagMapCLM a b := by
  ext x
  apply WithLp.ofLp_injective
  ext
  · change ((r : ℂ) • a x.fst) = (((r : ℂ) • WithLp.toLp 2 (a x.fst, b x.snd)).fst)
    simp
  · change ((r : ℂ) • b x.snd) = (((r : ℂ) • WithLp.toLp 2 (a x.fst, b x.snd)).snd)
    simp

end Internal

end HansenPedersen
