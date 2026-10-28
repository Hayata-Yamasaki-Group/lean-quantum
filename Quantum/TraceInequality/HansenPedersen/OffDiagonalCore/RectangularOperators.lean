/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore.Basic

/-!
# Rectangular off-diagonal operators

Rectangular off-diagonal and diagonal block operators, their algebraic
identities, positivity transfers through triangular conjugation, and spectral
bounds for product-space diagonal maps.

## Main results

* `offDiagCLMRect` and `diagMapCLMRectHs`: rectangular off-diagonal and
  diagonal block operators on `WithLp` product Hilbert spaces.
* `upperTriangularRect_conj_eq_directSchur`: triangular conjugation reduces a
  block operator to its direct Schur complement.
* `upperTriangularRect_directSchur_snd_nonneg_of_nonneg` and
  `upperTriangularRect_nonneg_of_directSchur_snd_nonneg`: the two directions of
  the Schur-complement positivity transfer.
* `spectrum_diagMapCLMRect_subset_halfOpenRay`: spectrum control for diagonal
  block operators.

## References

* Hiai, block-matrix Schur complement arguments used in the
  off-diagonal convexity reduction.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra

/-- Rectangular off-diagonal continuous linear map on `WithLp 2 (K × L')`;
the first component is `a` applied to the second input and the second component
is `b` applied to the first input. -/
noncomputable def offDiagCLMRect
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (b : K →L[ℂ] L') :
    (WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L')) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ K L').symm :
      K × L' →L[ℂ] WithLp 2 (K × L')).comp <|
    (a.prodMap b).comp
      (((ContinuousLinearEquiv.prodComm ℂ K L' : (K × L') ≃L[ℂ] (L' × K)) :
        (K × L') →L[ℂ] (L' × K)).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℂ K L') :
          WithLp 2 (K × L') →L[ℂ] K × L'))

@[simp] private theorem offDiagCLMRect_apply
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (b : K →L[ℂ] L') (x : WithLp 2 (K × L')) :
    offDiagCLMRect a b x = WithLp.toLp 2 (a x.snd, b x.fst) := by
  apply congrArg (WithLp.toLp 2)
  ext <;> rfl

/-- The adjoint of a rectangular off-diagonal block map swaps the two
off-diagonal entries and takes Hilbert-space adjoints. -/
theorem offDiagCLMRect_star
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (b : K →L[ℂ] L') :
    star (offDiagCLMRect a b) =
      offDiagCLMRect (ContinuousLinearMap.adjoint b) (ContinuousLinearMap.adjoint a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [offDiagCLMRect_apply, offDiagCLMRect_apply, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  have h1 := ContinuousLinearMap.adjoint_inner_left a y.snd x.fst
  have h2 := ContinuousLinearMap.adjoint_inner_left b y.fst x.snd
  simpa [add_comm, add_left_comm, add_assoc] using
    congrArg₂ HAdd.hAdd h1 h2

/-- Multiplying two rectangular off-diagonal block maps gives a diagonal block
map with componentwise compositions. -/
theorem offDiagCLMRect_mul_offDiagCLMRect
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (b : K →L[ℂ] L')
    (c : L' →L[ℂ] K) (d : K →L[ℂ] L') :
    offDiagCLMRect a b * offDiagCLMRect c d =
      HansenPedersen.Internal.diagMapCLM (a.comp d) (b.comp c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRect_apply, HansenPedersen.Internal.diagMapCLM_apply]

/-- A diagonal block map multiplied on the left of a rectangular off-diagonal
map acts by left composition on each off-diagonal component. -/
theorem diagMapCLM_mul_offDiagCLMRect
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : K →L[ℂ] K) (b : L' →L[ℂ] L')
    (c : L' →L[ℂ] K) (d : K →L[ℂ] L') :
    HansenPedersen.Internal.diagMapCLM a b * offDiagCLMRect c d =
      offDiagCLMRect (a.comp c) (b.comp d) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRect_apply, HansenPedersen.Internal.diagMapCLM_apply]

/-- A rectangular off-diagonal map multiplied on the left of a diagonal block
map acts by right composition on each off-diagonal component. -/
theorem offDiagCLMRect_mul_diagMapCLM
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (b : K →L[ℂ] L')
    (c : K →L[ℂ] K) (d : L' →L[ℂ] L') :
    offDiagCLMRect a b * HansenPedersen.Internal.diagMapCLM c d =
      offDiagCLMRect (a.comp d) (b.comp c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRect_apply, HansenPedersen.Internal.diagMapCLM_apply]

/-- Upper triangular block operator with identity diagonal and rectangular
upper-right entry `a`. -/
noncomputable def upperTriangularRect
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) :
    HansenPedersen.L (WithLp 2 (K × L')) :=
  HansenPedersen.Internal.diagMapCLM (1 : HansenPedersen.L K) (1 : HansenPedersen.L L') +
    offDiagCLMRect a 0

@[simp] private theorem upperTriangularRect_apply
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (x : WithLp 2 (K × L')) :
    upperTriangularRect a x = WithLp.toLp 2 (x.fst + a x.snd, x.snd) := by
  apply WithLp.ofLp_injective
  ext <;> simp [upperTriangularRect, offDiagCLMRect_apply,
    HansenPedersen.Internal.diagMapCLM_apply]

/-- The upper triangular block operator is a unit, with inverse obtained by
negating its off-diagonal entry. -/
theorem upperTriangularRect_isUnit
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) :
    IsUnit (upperTriangularRect a) := by
  refine ⟨⟨upperTriangularRect a, upperTriangularRect (-a), ?_, ?_⟩, rfl⟩
  · ext x
    apply WithLp.ofLp_injective
    ext <;> simp [upperTriangularRect, offDiagCLMRect_apply,
      HansenPedersen.Internal.diagMapCLM_apply, add_left_comm, add_comm]
  · ext x
    apply WithLp.ofLp_injective
    ext <;> simp [upperTriangularRect, offDiagCLMRect_apply,
      HansenPedersen.Internal.diagMapCLM_apply, add_assoc, add_comm]

/-- The adjoint of the upper triangular block operator is lower triangular with
lower-left entry `a†`. -/
theorem upperTriangularRect_star
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) :
    star (upperTriangularRect a) =
      HansenPedersen.Internal.diagMapCLM (1 : HansenPedersen.L K) (1 : HansenPedersen.L L') +
        offDiagCLMRect 0 (ContinuousLinearMap.adjoint a) := by
  have hdiag :
      star (HansenPedersen.Internal.diagMapCLM
        (1 : HansenPedersen.L K) (1 : HansenPedersen.L L')) =
        HansenPedersen.Internal.diagMapCLM
          (1 : HansenPedersen.L K) (1 : HansenPedersen.L L') := by
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [HansenPedersen.Internal.diagMapCLM_apply, HansenPedersen.Internal.diagMapCLM_apply,
      WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    simp
  calc
    star (upperTriangularRect a)
        = star (HansenPedersen.Internal.diagMapCLM
            (1 : HansenPedersen.L K) (1 : HansenPedersen.L L')) +
          star (offDiagCLMRect a 0) := by
            simp [upperTriangularRect]
    _ = HansenPedersen.Internal.diagMapCLM
          (1 : HansenPedersen.L K) (1 : HansenPedersen.L L') +
        offDiagCLMRect 0 (ContinuousLinearMap.adjoint a) := by
          simp [hdiag, offDiagCLMRect_star]

@[simp] private theorem upperTriangularRect_star_apply
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K) (x : WithLp 2 (K × L')) :
    star (upperTriangularRect a) x =
      WithLp.toLp 2 (x.fst, ContinuousLinearMap.adjoint a x.fst + x.snd) := by
  apply WithLp.ofLp_injective
  rw [upperTriangularRect_star]
  ext <;> simp [offDiagCLMRect_apply, HansenPedersen.Internal.diagMapCLM_apply, add_comm]

/-- Conjugating a block operator by `upperTriangularRect a` becomes diagonal
when the off-diagonal entries satisfy the cancellation equations `h12` and
`h21`. -/
theorem upperTriangularRect_conj_eq_diag
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K)
    (C : HansenPedersen.L K) (D : HansenPedersen.L L')
    (X : L' →L[ℂ] K) (Y : K →L[ℂ] L')
    (h12 : C.comp a + X = 0)
    (h21 : (ContinuousLinearMap.adjoint a).comp C + Y = 0) :
    star (upperTriangularRect a) *
        (HansenPedersen.Internal.diagMapCLM C D + offDiagCLMRect X Y) *
        upperTriangularRect a =
      HansenPedersen.Internal.diagMapCLM C (D + Y.comp a) := by
  have h12' : ∀ z, C (a z) + X z = 0 := by
    intro z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T z) h12
  have h21' : ∀ z, ContinuousLinearMap.adjoint a (C z) + Y z = 0 := by
    intro z
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T z) h21
  ext x
  apply WithLp.ofLp_injective
  ext
  · have h12x := h12' x.snd
    simpa [upperTriangularRect_star_apply, upperTriangularRect_apply,
      HansenPedersen.Internal.diagMapCLM_apply, offDiagCLMRect_apply, add_assoc] using
      congrArg (fun z => C x.fst + z) h12x
  · have h12x := h12' x.snd
    have h21x := h21' x.fst
    have h12a :
        ContinuousLinearMap.adjoint a (C (a x.snd) + X x.snd) = 0 := by
      simpa [ContinuousLinearMap.map_add] using congrArg (ContinuousLinearMap.adjoint a) h12x
    have h21x' : Y x.fst + ContinuousLinearMap.adjoint a (C x.fst) = 0 := by
      simpa [add_comm] using h21x
    simp only [HansenPedersen.Internal.diagMapCLM_apply]
    simpa [add_assoc, add_left_comm, add_comm, h12a] using
      congrArg (fun z => z + (Y (a x.snd) + D x.snd)) h21x'

/-- Direct Schur-complement specialization of
`upperTriangularRect_conj_eq_diag`, with off-diagonal entries chosen to cancel
against `C.comp a`. -/
theorem upperTriangularRect_conj_eq_directSchur
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    (a : L' →L[ℂ] K)
    (C : HansenPedersen.L K) (D : HansenPedersen.L L') :
    star (upperTriangularRect a) *
        (HansenPedersen.Internal.diagMapCLM C D +
          offDiagCLMRect (-(C.comp a)) (-((ContinuousLinearMap.adjoint a).comp C))) *
        upperTriangularRect a =
      HansenPedersen.Internal.diagMapCLM C
        (D - (ContinuousLinearMap.adjoint a).comp (C.comp a)) := by
  simpa [sub_eq_add_neg, ContinuousLinearMap.comp_assoc] using
    (upperTriangularRect_conj_eq_diag
      (a := a) (C := C) (D := D)
      (X := -(C.comp a))
      (Y := -((ContinuousLinearMap.adjoint a).comp C))
      (by simp)
      (by simp))

/-- Order comparison of diagonal block maps implies the corresponding order
comparison on the first diagonal component. -/
theorem diagMapCLMRect_fst_le_of_le
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a c : HansenPedersen.L K} {b d : HansenPedersen.L L'}
    (ha : IsSelfAdjoint a) (hc : IsSelfAdjoint c)
    (h : HansenPedersen.Internal.diagMapCLM a b ≤ HansenPedersen.Internal.diagMapCLM c d) :
    a ≤ c := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact hc.sub ha
  · intro x
    have hx := h.inner_nonneg_left (WithLp.toLp 2 (x, 0))
    simpa [HansenPedersen.Internal.diagMapCLM_sub,
      HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

/-- Order comparison of diagonal block maps implies the corresponding order
comparison on the second diagonal component. -/
theorem diagMapCLMRect_snd_le_of_le
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a c : HansenPedersen.L K} {b d : HansenPedersen.L L'}
    (hb : IsSelfAdjoint b) (hd : IsSelfAdjoint d)
    (h : HansenPedersen.Internal.diagMapCLM a b ≤ HansenPedersen.Internal.diagMapCLM c d) :
    b ≤ d := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact hd.sub hb
  · intro x
    have hx := h.inner_nonneg_left (WithLp.toLp 2 (0, x))
    simpa [HansenPedersen.Internal.diagMapCLM_sub,
      HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

/-- Positivity of a diagonal block map implies positivity of its first diagonal
component. -/
theorem diagMapCLMRect_fst_nonneg_of_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : HansenPedersen.L K} {b : HansenPedersen.L L'}
    (h : 0 ≤ HansenPedersen.Internal.diagMapCLM a b) :
    0 ≤ a := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  have hpos : (HansenPedersen.Internal.diagMapCLM a b).IsPositive := by
    simpa using h
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · have hsaDiag : IsSelfAdjoint (HansenPedersen.Internal.diagMapCLM a b) :=
      ContinuousLinearMap.IsPositive.isSelfAdjoint hpos
    have hdiag :
        HansenPedersen.Internal.diagMapCLM (star a) (star b) =
          HansenPedersen.Internal.diagMapCLM a b := by
      calc
        HansenPedersen.Internal.diagMapCLM (star a) (star b)
            = star (HansenPedersen.Internal.diagMapCLM a b) := by
                symm
                exact HansenPedersen.Internal.diagMapCLM_star a b
        _ = HansenPedersen.Internal.diagMapCLM a b := hsaDiag.star_eq
    ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (x, 0))).fst) hdiag
    simpa [HansenPedersen.Internal.diagMapCLM_apply] using hx
  · intro x
    have hx := hpos.inner_nonneg_left (WithLp.toLp 2 (x, 0))
    simpa [HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

/-- Positivity of a diagonal block map implies positivity of its second
diagonal component. -/
theorem diagMapCLMRect_snd_nonneg_of_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : HansenPedersen.L K} {b : HansenPedersen.L L'}
    (h : 0 ≤ HansenPedersen.Internal.diagMapCLM a b) :
    0 ≤ b := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  have hpos : (HansenPedersen.Internal.diagMapCLM a b).IsPositive := by
    simpa using h
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · have hsaDiag : IsSelfAdjoint (HansenPedersen.Internal.diagMapCLM a b) :=
      ContinuousLinearMap.IsPositive.isSelfAdjoint hpos
    have hdiag :
        HansenPedersen.Internal.diagMapCLM (star a) (star b) =
          HansenPedersen.Internal.diagMapCLM a b := by
      calc
        HansenPedersen.Internal.diagMapCLM (star a) (star b)
            = star (HansenPedersen.Internal.diagMapCLM a b) := by
                symm
                exact HansenPedersen.Internal.diagMapCLM_star a b
        _ = HansenPedersen.Internal.diagMapCLM a b := hsaDiag.star_eq
    ext x
    have hx := congrArg (fun T => (T (WithLp.toLp 2 (0, x))).snd) hdiag
    simpa [HansenPedersen.Internal.diagMapCLM_apply] using hx
  · intro x
    have hx := hpos.inner_nonneg_left (WithLp.toLp 2 (0, x))
    simpa [HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

/-- A diagonal block map is positive when both diagonal components are
positive. -/
theorem diagMapCLM_nonneg_of_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : HansenPedersen.L K} {b : HansenPedersen.L L'}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ HansenPedersen.Internal.diagMapCLM a b := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at ha hb ⊢
  rw [ContinuousLinearMap.isPositive_def'] at ha hb ⊢
  rcases ha with ⟨ha_sa, ha_pos⟩
  rcases hb with ⟨hb_sa, hb_pos⟩
  constructor
  · calc
      star (HansenPedersen.Internal.diagMapCLM a b)
          = HansenPedersen.Internal.diagMapCLM (star a) (star b) := by
              exact HansenPedersen.Internal.diagMapCLM_star a b
      _ = HansenPedersen.Internal.diagMapCLM a b := by
            rw [ha_sa.star_eq, hb_sa.star_eq]
  · intro x
    have hx1 := ha_pos x.fst
    have hx2 := hb_pos x.snd
    simpa [HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using
      add_nonneg hx1 hx2

/-- Positivity is preserved under conjugation by an arbitrary continuous linear
map: `T ≥ 0` implies `U† T U ≥ 0`. -/
theorem star_mul_mul_nonneg_of_nonneg_main
    {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {U T : HansenPedersen.L K}
    (hT : 0 ≤ T) :
    0 ≤ star U * T * U := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT ⊢
  rw [ContinuousLinearMap.isPositive_def'] at hT ⊢
  rcases hT with ⟨hTsa, hTpos⟩
  constructor
  · calc
      star (star U * T * U) = star U * star T * U := by
        simp [mul_assoc]
      _ = star U * T * U := by
        rw [hTsa.star_eq]
  · intro x
    have hx := hTpos (U x)
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    rw [show (star U * T * U) x = (star U) (T (U x)) by
      simp]
    rw [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hx

/-- From positivity of the ambient block operator, triangular conjugation gives
positivity of the second Schur complement. -/
theorem upperTriangularRect_directSchur_snd_nonneg_of_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : L' →L[ℂ] K} {C : HansenPedersen.L K} {D : HansenPedersen.L L'}
    (hambient :
      0 ≤ HansenPedersen.Internal.diagMapCLM C D +
        offDiagCLMRect (-(C.comp a)) (-((ContinuousLinearMap.adjoint a).comp C))) :
    0 ≤ D - (ContinuousLinearMap.adjoint a).comp (C.comp a) := by
  have hconj_nonneg :
      0 ≤
        star (upperTriangularRect a) *
          (HansenPedersen.Internal.diagMapCLM C D +
            offDiagCLMRect (-(C.comp a)) (-((ContinuousLinearMap.adjoint a).comp C))) *
          upperTriangularRect a := by
    exact star_mul_mul_nonneg_of_nonneg_main hambient
  rw [upperTriangularRect_conj_eq_directSchur (a := a) (C := C) (D := D)] at hconj_nonneg
  exact diagMapCLMRect_snd_nonneg_of_nonneg hconj_nonneg

/-- First-component version of the Schur-complement positivity extraction,
obtained by swapping the two rectangular sides. -/
theorem upperTriangularRect_directSchur_fst_nonneg_of_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : K →L[ℂ] L'} {C : HansenPedersen.L K} {D : HansenPedersen.L L'}
    (hambient :
      0 ≤ HansenPedersen.Internal.diagMapCLM D C +
        offDiagCLMRect (-(D.comp a)) (-((ContinuousLinearMap.adjoint a).comp D))) :
    0 ≤ C - (ContinuousLinearMap.adjoint a).comp (D.comp a) := by
  simpa using
    upperTriangularRect_directSchur_snd_nonneg_of_nonneg
      (a := a) (C := D) (D := C) hambient

/-- If the first diagonal block and the second Schur complement are positive,
then the ambient upper-triangular block operator is positive. -/
theorem upperTriangularRect_nonneg_of_directSchur_snd_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : L' →L[ℂ] K} {C : HansenPedersen.L K} {D : HansenPedersen.L L'}
    (hC : 0 ≤ C)
    (hschur : 0 ≤ D - (ContinuousLinearMap.adjoint a).comp (C.comp a)) :
    0 ≤ HansenPedersen.Internal.diagMapCLM C D +
      offDiagCLMRect (-(C.comp a)) (-((ContinuousLinearMap.adjoint a).comp C)) := by
  let ambient : HansenPedersen.L (WithLp 2 (K × L')) :=
    HansenPedersen.Internal.diagMapCLM C D +
      offDiagCLMRect (-(C.comp a)) (-((ContinuousLinearMap.adjoint a).comp C))
  let U : HansenPedersen.L (WithLp 2 (K × L')) := upperTriangularRect a
  let V : HansenPedersen.L (WithLp 2 (K × L')) := upperTriangularRect (-a)
  have hdiag :
      0 ≤ HansenPedersen.Internal.diagMapCLM C
        (D - (ContinuousLinearMap.adjoint a).comp (C.comp a)) :=
    diagMapCLM_nonneg_of_nonneg hC hschur
  have hUV : U * V = 1 := by
    ext x
    apply WithLp.ofLp_injective
    ext <;> simp [U, V, upperTriangularRect, offDiagCLMRect_apply,
      HansenPedersen.Internal.diagMapCLM_apply, add_left_comm, add_comm]
  have hstarVU : star V * star U = 1 := by
    simpa [U, V] using congrArg star hUV
  have hrepr :
      ambient =
        star V *
          HansenPedersen.Internal.diagMapCLM C
            (D - (ContinuousLinearMap.adjoint a).comp (C.comp a)) *
          V := by
    calc
      ambient = (star V * star U) * ambient * (U * V) := by
        rw [hstarVU, hUV]
        simp
      _ = star V * (star U * ambient * U) * V := by
        simp [mul_assoc]
      _ = star V *
            HansenPedersen.Internal.diagMapCLM C
              (D - (ContinuousLinearMap.adjoint a).comp (C.comp a)) *
            V := by
        rw [upperTriangularRect_conj_eq_directSchur (a := a) (C := C) (D := D)]
  have hnonneg_ambient :
      0 ≤ ambient := by
    simpa [hrepr] using star_mul_mul_nonneg_of_nonneg_main (U := V) hdiag
  simpa [ambient] using hnonneg_ambient

/-- Swapped version of `upperTriangularRect_nonneg_of_directSchur_snd_nonneg`
for positivity from the first Schur complement. -/
theorem upperTriangularRect_nonneg_of_directSchur_fst_nonneg
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {a : K →L[ℂ] L'} {C : HansenPedersen.L K} {D : HansenPedersen.L L'}
    (hD : 0 ≤ D)
    (hschur : 0 ≤ C - (ContinuousLinearMap.adjoint a).comp (D.comp a)) :
    0 ≤ HansenPedersen.Internal.diagMapCLM D C +
      offDiagCLMRect (-(D.comp a)) (-((ContinuousLinearMap.adjoint a).comp D)) := by
  simpa using
    upperTriangularRect_nonneg_of_directSchur_snd_nonneg
      (a := a) (C := D) (D := C) hD hschur

namespace RectangularOperatorInstances

/-- Opt-in real algebra structure on endomorphisms of a `WithLp` product
Hilbert space, obtained by restricting scalars from the complex normed algebra. -/
noncomputable scoped instance instWithLpEndAlgebraReal
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L'] :
    Algebra ℝ ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
  NormedAlgebra.complexToReal.toAlgebra

end RectangularOperatorInstances

/-- Hilbert-space model for a rectangular pair of matrix blocks of sizes
`Nat.succ k` and `Nat.succ l`. -/
noncomputable def hsBlockSpaceRect (k l : ℕ) : Type :=
  letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI := instMatrixNormedSpace (n := Nat.succ k)
  letI := instMatrixInnerProductSpace (n := Nat.succ k)
  letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI := instMatrixNormedSpace (n := Nat.succ l)
  letI := instMatrixInnerProductSpace (n := Nat.succ l)
  WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l))

/-- Normed additive group structure on the rectangular Hilbert-Schmidt block
space. -/
noncomputable scoped instance instHsBlockSpaceRectNormedAddCommGroup {k l : ℕ} :
    NormedAddCommGroup (hsBlockSpaceRect k l) := by
  unfold hsBlockSpaceRect
  exact WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ (Nat.succ k))
    (β := Mₙ (Nat.succ l))

/-- Complex normed-space structure on the rectangular Hilbert-Schmidt block
space. -/
noncomputable scoped instance instHsBlockSpaceRectNormedSpace {k l : ℕ} :
    NormedSpace ℂ (hsBlockSpaceRect k l) := by
  unfold hsBlockSpaceRect
  exact WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ (Nat.succ k))
    (β := Mₙ (Nat.succ l))

/-- Inner-product structure on the rectangular Hilbert-Schmidt block space,
using the product `WithLp` inner product. -/
noncomputable scoped instance instHsBlockSpaceRectInnerProductSpace {k l : ℕ} :
    InnerProductSpace ℂ (hsBlockSpaceRect k l) := by
  unfold hsBlockSpaceRect
  exact @WithLp.instProdInnerProductSpace ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
    inferInstance
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))

/-- Completeness of the rectangular Hilbert-Schmidt block space. -/
noncomputable scoped instance instHsBlockSpaceRectCompleteSpace {k l : ℕ} :
    CompleteSpace (hsBlockSpaceRect k l) := by
  unfold hsBlockSpaceRect
  exact WithLp.instProdCompleteSpace (p := 2) (α := Mₙ (Nat.succ k))
    (β := Mₙ (Nat.succ l))

/-- Matrix-specialized rectangular off-diagonal block operator on
`hsBlockSpaceRect`. -/
noncomputable def offDiagCLMRectHs {k l : ℕ}
    (a : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l)) :
    HansenPedersen.L (hsBlockSpaceRect k l) := by
  let K1 := hsBlockSpaceRect k l
  letI : NormedAddCommGroup K1 := instHsBlockSpaceRectNormedAddCommGroup (k := k) (l := l)
  letI : NormedSpace ℂ K1 := instHsBlockSpaceRectNormedSpace (k := k) (l := l)
  letI : InnerProductSpace ℂ K1 := instHsBlockSpaceRectInnerProductSpace (k := k) (l := l)
  letI : CompleteSpace K1 := instHsBlockSpaceRectCompleteSpace (k := k) (l := l)
  exact (@offDiagCLMRect (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (instMatrixCompleteSpace (n := Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))
    (instMatrixCompleteSpace (n := Nat.succ l))
    a b : HansenPedersen.L K1)

/-- Matrix-specialized diagonal block operator on `hsBlockSpaceRect`. -/
noncomputable def diagMapCLMRectHs {k l : ℕ}
    (a : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ l)) :
    HansenPedersen.L (hsBlockSpaceRect k l) := by
  exact
    ((show (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)) →L[ℂ] hsBlockSpaceRect k l from
        ((WithLp.prodContinuousLinearEquiv 2 ℂ
            (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))).symm :
          (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)) →L[ℂ]
            WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)))).comp <|
      (a.prodMap b).comp
        (show hsBlockSpaceRect k l →L[ℂ] (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)) from
          ((WithLp.prodContinuousLinearEquiv 2 ℂ
              (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))) :
            WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)) →L[ℂ]
              (Mₙ (Nat.succ k) × Mₙ (Nat.succ l)))))

/-- Applying the matrix-specialized off-diagonal operator swaps the two
components and applies the rectangular maps. -/
@[simp] theorem offDiagCLMRectHs_apply
    {k l : ℕ}
    (a : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l))
    (x : hsBlockSpaceRect k l) :
    offDiagCLMRectHs (k := k) (l := l) a b x = WithLp.toLp 2 (a x.snd, b x.fst) := by
  rfl

/-- Applying the matrix-specialized diagonal operator applies the two diagonal
endomorphisms componentwise. -/
@[simp] theorem diagMapCLMRectHs_apply
    {k l : ℕ}
    (a : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ l))
    (x : hsBlockSpaceRect k l) :
    diagMapCLMRectHs (k := k) (l := l) a b x = WithLp.toLp 2 (a x.fst, b x.snd) := by
  rfl

/-- The adjoint of the matrix-specialized rectangular off-diagonal operator
swaps the entries and applies Hilbert-Schmidt adjoints. -/
theorem offDiagCLMRectHs_star
    {k l : ℕ}
    (a : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l)) :
    star (offDiagCLMRectHs (k := k) (l := l) a b) =
      offDiagCLMRectHs (k := k) (l := l)
        (hsAdjoint b) (hsAdjoint a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l))) :=
    WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ (Nat.succ k))
      (β := Mₙ (Nat.succ l))
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l))) :=
    WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ (Nat.succ k))
      (β := Mₙ (Nat.succ l))
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ k) × Mₙ (Nat.succ l))) :=
    @WithLp.instProdInnerProductSpace ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
      inferInstance
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
  have h1 :=
    @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ k))
      a y.snd x.fst
  have h2 :=
    @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ l))
      b y.fst x.snd
  rw [show y = WithLp.toLp 2 (y.fst, y.snd) by rfl, show x = WithLp.toLp 2 (x.fst, x.snd) by rfl]
  rw [offDiagCLMRectHs_apply, offDiagCLMRectHs_apply]
  simp only [Nat.succ_eq_add_one, WithLp.toLp_snd, WithLp.toLp_fst]
  have hlhs :
      inner ℂ
          (WithLp.toLp 2 ((hsAdjoint b) x.snd, (hsAdjoint a) x.fst))
          (WithLp.toLp 2 (y.fst, y.snd)) =
        inner ℂ ((hsAdjoint b) x.snd) y.fst + inner ℂ ((hsAdjoint a) x.fst) y.snd := by
    simp
  have hrhs :
      inner ℂ (WithLp.toLp 2 (x.fst, x.snd))
          (WithLp.toLp 2 (a y.snd, b y.fst)) =
        inner ℂ x.fst (a y.snd) + inner ℂ x.snd (b y.fst) := by
    simp
  calc
    inner ℂ
        (WithLp.toLp 2 ((hsAdjoint b) x.snd, (hsAdjoint a) x.fst))
        (WithLp.toLp 2 (y.fst, y.snd))
      = inner ℂ ((hsAdjoint b) x.snd) y.fst + inner ℂ ((hsAdjoint a) x.fst) y.snd := hlhs
    _ = inner ℂ (WithLp.snd x) (b (WithLp.fst y)) +
          inner ℂ (WithLp.fst x) (a (WithLp.snd y)) := congrArg₂ HAdd.hAdd h2 h1
    _ = inner ℂ (WithLp.fst x) (a (WithLp.snd y)) +
          inner ℂ (WithLp.snd x) (b (WithLp.fst y)) := by ac_rfl
    _ = inner ℂ (WithLp.toLp 2 (x.fst, x.snd))
          (WithLp.toLp 2 (a y.snd, b y.fst)) := hrhs.symm

/-- Product of two matrix-specialized off-diagonal operators is the
matrix-specialized diagonal operator with componentwise compositions. -/
theorem offDiagCLMRectHs_mul_offDiagCLMRectHs
    {k l : ℕ}
    (a : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l))
    (c : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (d : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l)) :
    offDiagCLMRectHs (k := k) (l := l) a b *
        offDiagCLMRectHs (k := k) (l := l) c d =
      diagMapCLMRectHs (k := k) (l := l) (a.comp d) (b.comp c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRectHs_apply, diagMapCLMRectHs_apply]

/-- Multiplying a matrix-specialized off-diagonal operator by a diagonal one on
the right composes the off-diagonal entries with the diagonal entries. -/
theorem offDiagCLMRectHs_mul_diagMapCLMRectHs
    {k l : ℕ}
    (a : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l))
    (c : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ k))
    (d : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ l)) :
    offDiagCLMRectHs (k := k) (l := l) a b *
        diagMapCLMRectHs (k := k) (l := l) c d =
      offDiagCLMRectHs (k := k) (l := l) (a.comp d) (b.comp c) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRectHs_apply, diagMapCLMRectHs_apply]

/-- Multiplying a matrix-specialized diagonal operator by an off-diagonal one
on the right composes the diagonal entries with the off-diagonal entries. -/
theorem diagMapCLMRectHs_mul_offDiagCLMRectHs
    {k l : ℕ}
    (a : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ k))
    (b : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ l))
    (c : Mₙ (Nat.succ l) →L[ℂ] Mₙ (Nat.succ k))
    (d : Mₙ (Nat.succ k) →L[ℂ] Mₙ (Nat.succ l)) :
    diagMapCLMRectHs (k := k) (l := l) a b *
        offDiagCLMRectHs (k := k) (l := l) c d =
      offDiagCLMRectHs (k := k) (l := l) (a.comp c) (b.comp d) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [offDiagCLMRectHs_apply, diagMapCLMRectHs_apply]

/-- If the real spectra of both diagonal components lie in the same half-open
ray, then so does the real spectrum of their diagonal block map. -/
theorem spectrum_diagMapCLMRect_subset_halfOpenRay
    {K L' : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']
    {α : WithTop ℝ}
    {a : HansenPedersen.L K} {b : HansenPedersen.L L'}
    (_ha : IsSelfAdjoint a) (_hb : IsSelfAdjoint b)
    (hσa : spectrum ℝ a ⊆ HansenPedersen.halfOpenRay α)
    (hσb : spectrum ℝ b ⊆ HansenPedersen.halfOpenRay α) :
    spectrum ℝ (HansenPedersen.Internal.diagMapCLM a b) ⊆ HansenPedersen.halfOpenRay α := by
  letI : CompleteSpace (WithLp 2 (K × L')) :=
    WithLp.instProdCompleteSpace (p := 2) (α := K) (β := L')
  let hCstar :
      CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (WithLp 2 (K × L')) _ _
      ‹CompleteSpace (WithLp 2 (K × L'))›
  letI : CStarAlgebra ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar
  letI : Semiring ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Star ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : StarRing ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := by
    infer_instance
  letI : Algebra ℂ ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) := hCstar.toAlgebra
  letI : Algebra ℝ ((WithLp 2 (K × L')) →L[ℂ] (WithLp 2 (K × L'))) :=
    NormedAlgebra.complexToReal.toAlgebra
  let Ψ₀ :
      (HansenPedersen.L K × HansenPedersen.L L') →⋆ₐ[ℂ]
        (HansenPedersen.L (WithLp 2 (K × L'))) :=
    @HansenPedersen.Internal.diagStarAlgHom K inferInstance inferInstance inferInstance
      L' inferInstance inferInstance inferInstance
  let Ψ :
      (HansenPedersen.L K × HansenPedersen.L L') →⋆ₐ[ℝ]
        (HansenPedersen.L (WithLp 2 (K × L'))) :=
    Ψ₀.restrictScalars ℝ
  intro x hx
  have hx' : x ∈ spectrum ℝ (a, b) := by
    exact AlgHom.spectrum_apply_subset Ψ (a, b) hx
  rw [Prod.spectrum_eq] at hx'
  exact hx'.elim (fun hxa => hσa hxa) (fun hxb => hσb hxb)


end HiaiPetz
