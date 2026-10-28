/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.Conditions
import Quantum.TraceInequality.HansenPedersen.UnitaryBlockMatrix
import Quantum.TraceInequality.HansenPedersen.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Block-operator calculus for compression inequalities

This module collects the concrete two-by-two block operators on
`WithLp 2 (K × K)` used in the Hansen--Pedersen compression argument.  It
provides algebraic identities for multiplication, adjoints, diagonal CFC, and
the norm estimate for a block column.

## Main results

* `cfcR_diagMapCLM`: real CFC of a diagonal block is diagonal CFC.
* `blockCLM`: the concrete two-by-two block operator.
* `blockCLM_mul`, `blockCLM_star`, and `blockCLM_col_norm_le_one`: algebra and
  norm facts for later Julia-unitary and compression constructions.

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

/-- A pair of self-adjoint operators is self-adjoint in the product
star-algebra. -/
lemma pair_isSelfAdjoint {a b : L K}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (a, b) := by
  change star (a, b) = (a, b)
  ext <;> simp [ha.star_eq, hb.star_eq]

/-- Conjugating a self-adjoint operator by an arbitrary operator preserves
self-adjointness of the resulting `C* T C`. -/
lemma star_mul_selfAdjoint_mul {T C : L K}
    (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (star C * T * C) := by
  change star (star C * T * C) = star C * T * C
  simp [mul_assoc, hT.star_eq]

/-- The diagonal block star-algebra homomorphism is injective, so equality of
diagonal block operators is equality of both entries. -/
lemma diagStarAlgHom_injective :
    Function.Injective (HansenPedersen.Internal.diagStarAlgHom (K := K) (L' := K)) := by
  intro ab₁ ab₂ h
  rcases ab₁ with ⟨a₁, b₁⟩
  rcases ab₂ with ⟨a₂, b₂⟩
  change HansenPedersen.Internal.diagMapCLM a₁ b₁ =
      HansenPedersen.Internal.diagMapCLM a₂ b₂ at h
  have ha : a₁ = a₂ := by
    ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (x, 0))).fst) h
    simpa [HansenPedersen.Internal.diagMapCLM_apply] using hx
  have hb : b₁ = b₂ := by
    ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (0, x))).snd) h
    simpa [HansenPedersen.Internal.diagMapCLM_apply] using hx
  simp [ha, hb]

/-- Real functional calculus of a two-by-two diagonal block agrees with the
diagonal block of the real functional calculi of its entries. -/
lemma cfcR_diagMapCLM {α : WithTop ℝ} {f : ℝ → ℝ} {a b : L K}
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (hf : ContinuousOn f (halfOpenRay α))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hσa : spectrum ℝ a ⊆ halfOpenRay α)
    (hσb : spectrum ℝ b ⊆ halfOpenRay α) :
    cfcR (ℋ := WithLp 2 (K × K)) f (HansenPedersen.Internal.diagMapCLM a b) =
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := K) f a) (cfcR (ℋ := K) f b) := by
  have hfab_union : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b) := by
    refine hf.mono ?_
    intro x hx
    cases hx with
    | inl hxa => exact hσa hxa
    | inr hxb => exact hσb hxb
  simpa [cfcR] using
    (HansenPedersen.cfcR_diagMapCLM_union (ℋ := K) (f := f) (a := a) (b := b)
      hfab_union ha hb)

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

omit [CompleteSpace K] in
/-- Compressing a block operator by the first-coordinate projection keeps only
the upper-left entry. -/
lemma proj11_mul_blockCLM_mul_proj11 (a b c d : L K) :
    blockCLM (1 : L K) 0 0 0 * blockCLM a b c d * blockCLM (1 : L K) 0 0 0 =
      blockCLM a 0 0 0 := by
  rw [blockCLM_mul, blockCLM_mul]
  simp

/-- Adjoint of a block column, written as the corresponding block row. -/
lemma blockCLM_col_star (c d : L K) :
    star (blockCLM c 0 d 0) = blockCLM (star c) (star d) 0 0 := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [blockCLM_apply, blockCLM_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only
  rw [inner_add_left]
  have h1 := ContinuousLinearMap.adjoint_inner_left c (y.fst) (x.fst)
  have h2 := ContinuousLinearMap.adjoint_inner_left d (y.fst) (x.snd)
  simpa [ContinuousLinearMap.star_eq_adjoint] using congrArg₂ HAdd.hAdd h1 h2

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

/-- A block column is a contraction when the sum of its entrywise squares is
bounded by the identity. -/
lemma blockCLM_col_norm_le_one {c d : L K}
    (hcd : star c * c + star d * d ≤ (1 : L K)) :
    ‖blockCLM c 0 d 0‖ ≤ 1 := by
  have hstar_mul :
      star (blockCLM c 0 d 0) * blockCLM c 0 d 0 ≤ (1 : L (WithLp 2 (K × K))) := by
    calc
      star (blockCLM c 0 d 0) * blockCLM c 0 d 0
          = HansenPedersen.Internal.diagMapCLM (star c * c + star d * d) 0 := by
              rw [blockCLM_col_star]
              simpa using blockCLM_mul (star c) (star d) 0 0 c 0 d 0
      _ ≤ HansenPedersen.Internal.diagMapCLM (1 : L K) (1 : L K) := by
          exact HansenPedersen.Internal.diagMapCLM_mono hcd zero_le_one
      _ = (1 : L (WithLp 2 (K × K))) := by
          ext x
          cases x
          rfl
  rw [← sq_le_one_iff₀ (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).2 hstar_mul

omit [CompleteSpace K] in
/-- Equality of concrete two-by-two block operators is equivalent to equality
of their four entries. -/
lemma blockCLM_inj {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : L K}
    (h : blockCLM a₁ b₁ c₁ d₁ = blockCLM a₂ b₂ c₂ d₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  constructor
  · ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (x, 0))).fst) h
    simpa [blockCLM_apply] using hx
  constructor
  · ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (0, x))).fst) h
    simpa [blockCLM_apply] using hx
  constructor
  · ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (x, 0))).snd) h
    simpa [blockCLM_apply] using hx
  · ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (0, x))).snd) h
    simpa [blockCLM_apply] using hx

end BlockHelpers

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
