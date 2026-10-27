import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.BasicTheorems

import Quantum.TraceInequality.LownerHeinzTheorem

/-!
# Core lemmas for the Hansen–Pedersen development

Shared entry-level lemmas for the Hiai–Yanagi Chapter 5.1 formalization.

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

/-- For a self-adjoint bounded endomorphism `T` of `K`, the scalar order bounds
`α • 1 ≤ T` and
`T ≤ β • 1` imply that the real spectrum of `T` is contained in
`Set.Icc α β`. The proof applies the spectral order equivalences separately to
the lower and upper bounds. -/
theorem spectrum_subset_Icc_of_order_bounds_clm
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {T : K →L[ℂ] K} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hlow : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T)
    (hupp : T ≤ (β : ℂ) • (1 : K →L[ℂ] K)) :
    spectrum ℝ T ⊆ Set.Icc α β := by
  intro x hx
  constructor
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := α) (a := T) (ha := hT)).1 hlow x hx
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := β) (a := T) (ha := hT)).1 hupp x hx

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

omit [CompleteSpace K] [CompleteSpace L'] in
/-- The block-diagonal map is additive in its blocks: the difference of two
block-diagonal maps is the block-diagonal map of the blockwise differences. -/
lemma diagMapCLM_sub (a₁ a₂ : K →L[ℂ] K) (b₁ b₂ : L' →L[ℂ] L') :
    diagMapCLM a₁ b₁ - diagMapCLM a₂ b₂ = diagMapCLM (a₁ - a₂) (b₁ - b₂) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

end Internal

end HansenPedersen
