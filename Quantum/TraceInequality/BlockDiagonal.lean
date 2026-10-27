/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorNotation
import Quantum.TraceInequality.LownerHeinzTheorem

/-!
# Operators on a two-fold Hilbert sum

This module constructs inclusions, projections and block operators on a two-fold
Hilbert sum. It proves the algebraic and order identities used in the block-operator
proof of Jensen's inequality.
-/

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- A two-fold Hilbert sum used for the block-operator proof of Jensen's inequality. -/
abbrev HSum (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  PiLp 2 (fun _ : Fin 2 => ℋ)

noncomputable def hsumEquiv (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] :
    HSum ℋ ≃L[ℂ] (Fin 2 → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin 2 => ℋ)

noncomputable def hsumProj (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : HSum ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℋ) i) ∘L
    (hsumEquiv ℋ).toContinuousLinearMap

noncomputable def hsumIncl (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : ℋ →L[ℂ] HSum ℋ :=
  (hsumEquiv ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℋ) i)

noncomputable local instance : DistribSMul ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : MulAction ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_hsumIncl_apply (i j : Fin 2) (x : ℋ) :
    hsumProj ℋ i (hsumIncl ℋ j x) = if i = j then x else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumProj, hsumIncl, hsumEquiv]

omit [Nontrivial ℋ] in
@[simp] theorem hsumIncl_adjoint (i : Fin 2) :
    (hsumIncl ℋ i).adjoint = hsumProj ℋ i := by
  fin_cases i
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]

omit [Nontrivial ℋ] in
@[simp] theorem hsumProj_adjoint (i : Fin 2) :
    (hsumProj ℋ i).adjoint = hsumIncl ℋ i := by
  calc
    (hsumProj ℋ i).adjoint = ((hsumIncl ℋ i).adjoint).adjoint := by
      rw [hsumIncl_adjoint (ℋ := ℋ) i]
    _ = hsumIncl ℋ i := ContinuousLinearMap.adjoint_adjoint _

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumIncl_proj_sum (z : HSum ℋ) :
    hsumIncl ℋ 0 (hsumProj ℋ 0 z) + hsumIncl ℋ 1 (hsumProj ℋ 1 z) = z := by
  ext i
  fin_cases i <;> simp [hsumProj, hsumIncl, hsumEquiv]

/-- The block diagonal operator `diag(A, B)` on the two-fold Hilbert sum. -/
noncomputable def blockDiagonal (A B : QuantumState.B ℋ) : QuantumState.B (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L B ∘L hsumProj ℋ 1

/-- A general `2 × 2` block operator on `HSum ℋ`. -/
noncomputable def blockOp (A00 A01 A10 A11 : QuantumState.B ℋ) : QuantumState.B (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A00 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 0 ∘L A01 ∘L hsumProj ℋ 1 +
    hsumIncl ℋ 1 ∘L A10 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 1 ∘L A11 ∘L hsumProj ℋ 1

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_ext {T S : QuantumState.B (HSum ℋ)}
    (h0 : ∀ z : HSum ℋ, hsumProj ℋ 0 (T z) = hsumProj ℋ 0 (S z))
    (h1 : ∀ z : HSum ℋ, hsumProj ℋ 1 (T z) = hsumProj ℋ 1 (S z)) :
    T = S := by
  ext z i
  fin_cases i
  · simpa using h0 z
  · simpa using h1 z

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_star (A B : QuantumState.B ℋ) :
    star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) (star A) (star B) := by
  ext z i
  fin_cases i
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]

noncomputable def blockDiagonalHom : (QuantumState.B ℋ × QuantumState.B ℋ) →⋆ₐ[ℝ]
    QuantumState.B (HSum ℋ) where
  toFun p := blockDiagonal (ℋ := ℋ) p.1 p.2
  map_one' := by
    ext z
    simp [blockDiagonal]
  map_mul' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, ContinuousLinearMap.mul_def]
  map_zero' := by
    ext z i
    fin_cases i <;> simp [blockDiagonal]
  map_add' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, ContinuousLinearMap.add_apply]
  commutes' := by
    intro r
    ext z i
    fin_cases i <;> {
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, Algebra.algebraMap_eq_smul_one]
      rfl
    }
  map_star' := by
    intro p
    simp

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonalHom_apply (p : QuantumState.B ℋ × QuantumState.B ℋ) :
    blockDiagonalHom (ℋ := ℋ) p = blockDiagonal (ℋ := ℋ) p.1 p.2 :=
  rfl

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_zero (A B : QuantumState.B ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockDiagonal A B z) = A (hsumProj ℋ 0 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_one (A B : QuantumState.B ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockDiagonal A B z) = B (hsumProj ℋ 1 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_one :
    blockDiagonal (ℋ := ℋ) (1 : QuantumState.B ℋ) (1 : QuantumState.B ℋ) =
      (1 : QuantumState.B (HSum ℋ)) := by
  ext z i
  fin_cases i <;> simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockDiagonal_nonneg {A B : QuantumState.B ℋ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ blockDiagonal A B := by
  have hApos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hBpos : B.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hB
  refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hAz := (ContinuousLinearMap.isPositive_iff_complex A).mp hApos (hsumProj ℋ 0 z)
  have hBz := (ContinuousLinearMap.isPositive_iff_complex B).mp hBpos (hsumProj ℋ 1 z)
  have hz0 :
      inner ℂ ((hsumIncl ℋ 0) (A (hsumProj ℋ 0 z))) z =
        inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  have hz1 :
      inner ℂ ((hsumIncl ℋ 1) (B (hsumProj ℋ 1 z))) z =
        inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  constructor
  · dsimp [blockDiagonal]
    rw [inner_add_left, hz0, hz1]
    calc
      ↑(RCLike.re
          (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
            inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) =
          ↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
            RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) := by
            simp
      _ = inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
          inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
            have hsumre :
                (↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
                    RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) : ℂ) =
                  ((RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) : ℂ) +
                    (RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z)) : ℂ)) := by
                  simp
            rw [hsumre, hAz.1, hBz.1]
  · dsimp [blockDiagonal]
    rw [inner_add_left, hz0, hz1]
    exact add_nonneg hAz.2 hBz.2

omit [Nontrivial ℋ] in
/-- The block diagonal construction is monotone in both diagonal blocks. -/
@[gcongr]
theorem blockDiagonal_le_blockDiagonal {A C B D : QuantumState.B ℋ} (hAC : A ≤ C) (hBD : B ≤ D) :
    blockDiagonal (ℋ := ℋ) A B ≤ blockDiagonal (ℋ := ℋ) C D := by
  have hpos : 0 ≤ blockDiagonal (ℋ := ℋ) (C - A) (D - B) :=
    blockDiagonal_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAC) (sub_nonneg.mpr hBD)
  have hsub :
      blockDiagonal (ℋ := ℋ) (C - A) (D - B) =
        blockDiagonal (ℋ := ℋ) C D - blockDiagonal (ℋ := ℋ) A B := by
    ext z i
    fin_cases i <;> simp [blockDiagonal] <;> abel
  rw [hsub] at hpos
  exact sub_nonneg.mp hpos

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_zero (A00 A01 A10 A11 : QuantumState.B ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A00 (hsumProj ℋ 0 z) + A01 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_one (A00 A01 A10 A11 : QuantumState.B ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A10 (hsumProj ℋ 0 z) + A11 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [Nontrivial ℋ] in
@[simp] theorem blockOp_star (A00 A01 A10 A11 : QuantumState.B ℋ) :
    star (blockOp (ℋ := ℋ) A00 A01 A10 A11) =
      blockOp (ℋ := ℋ) (star A00) (star A10) (star A01) (star A11) := by
  ext z i
  fin_cases i
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockDiagonal_eq_blockOp (A B : QuantumState.B ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_mul (A00 A01 A10 A11 B00 B01 B10 B11 : QuantumState.B ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      hsumProj_blockOp_zero, hsumProj_blockOp_one, ContinuousLinearMap.add_apply, map_add]
    abel
  · intro z
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      hsumProj_blockOp_zero, hsumProj_blockOp_one, ContinuousLinearMap.add_apply, map_add]
    abel

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_add
    (A00 A01 A10 A11 B00 B01 B10 B11 : QuantumState.B ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 + blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ) (A00 + B00) (A01 + B01) (A10 + B10) (A11 + B11) := by
  ext z i
  fin_cases i <;> simp [blockOp] <;> abel

-- Scalar action on `blockOp` triggers expensive instance search for nested operator expressions.
omit [Nontrivial ℋ] in
theorem blockOp_smulR
    (r : ℝ) (A00 A01 A10 A11 : QuantumState.B ℋ) :
    r • blockOp (ℋ := ℋ) A00 A01 A10 A11 =
      blockOp (ℋ := ℋ) (r • A00) (r • A01) (r • A10) (r • A11) := by
  have coe_smul_hsum : ∀ (f : (HSum ℋ →L[ℂ] HSum ℋ)) (x : HSum ℋ), (r • f) x = r • (f x) := by
    intros
    rfl
  have coe_smul_h : ∀ (f : (ℋ →L[ℂ] ℋ)) (x : ℋ), (r • f) x = r • (f x) := by
    intros
    rfl
  ext z i
  fin_cases i <;> {
    simp only [blockOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      smul_add, coe_smul_hsum, coe_smul_h]
    simp [hsumProj, hsumIncl, hsumEquiv]
  }

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_mul_blockDiagonal_zero_right
    (P00 P01 P10 P11 A Q00 Q01 Q10 Q11 : QuantumState.B ℋ) :
    blockOp (ℋ := ℋ) P00 P01 P10 P11 * blockDiagonal (ℋ := ℋ) 0 A *
        blockOp (ℋ := ℋ) Q00 Q01 Q10 Q11 =
      blockOp (ℋ := ℋ)
        (P01 * A * Q10)
        (P01 * A * Q11)
        (P11 * A * Q10)
        (P11 * A * Q11) := by
  rw [blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul]
  simp [mul_assoc, add_comm]

-- IsSelfAdjoint CFC for the product type.
noncomputable local instance : ContinuousFunctionalCalculus ℝ ((ℋ →L[ℂ] ℋ) ×
    (ℋ →L[ℂ] ℋ)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- `StarAlgHom.map_cfc` needs `MulAction ℝ (HSum ℋ →L[ℂ] HSum ℋ)`; search is deep here.
omit [Nontrivial ℋ] in
theorem cfcR_blockDiagonal (f : ℝ → ℝ)
    (A B : QuantumState.B ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcont : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B)) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
  let φ : ((ℋ →L[ℂ] ℋ) × (ℋ →L[ℂ] ℋ)) →⋆ₐ[ℝ] (HSum ℋ →L[ℂ] HSum ℋ) :=
      blockDiagonalHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    change Continuous (fun p : (ℋ →L[ℂ] ℋ) × (ℋ →L[ℂ] ℋ) => blockDiagonal (ℋ
        := ℋ) p.1 p.2)
    change Continuous (fun p : (ℋ →L[ℂ] ℋ) × (ℋ →L[ℂ] ℋ) =>
      hsumIncl ℋ 0 ∘L p.1 ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L p.2 ∘L hsumProj ℋ 1)
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := by
    change star (A, B) = (A, B)
    ext <;> simp [hA.star_eq, hB.star_eq]
  have hpair' : IsSelfAdjoint (φ (A, B)) := hpair.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hcont)
    (hφ := hφ) (ha := hpair) (hφa := hpair')
  have hprod :
      cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ) × (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f (A, B) =
        (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
    simpa [cfcR] using
      (cfc_map_prod (R := ℝ) (S := ℝ)
        (A := (ℋ →L[ℂ] ℋ)) (B := (ℋ →L[ℂ] ℋ))
        (pab := IsSelfAdjoint) (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
        f A B
        (hf := hcont)
        (hab := hpair) (ha := hA) (hb := hB))
  calc
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B)
        = cfc (R := ℝ) (A := (HSum ℋ →L[ℂ] HSum ℋ)) (p := IsSelfAdjoint) f (φ (A, B)) := by
          simp [cfcR, φ]
    _ = φ (cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ) × (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f
        (A, B)) := by
          simpa using hmap.symm
    _ = φ (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
          rw [hprod]
    _ = blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
          simp [φ, blockDiagonalHom]

omit [Nontrivial ℋ] in
theorem blockDiagonal_le_left {A0 A1 B0 B1 : QuantumState.B ℋ}
    (h : blockDiagonal (ℋ := ℋ) A0 A1 ≤ blockDiagonal (ℋ := ℋ) B0 B1) :
    A0 ≤ B0 := by
  have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
    have hsub :
        blockDiagonal (ℋ := ℋ) B0 B1 - blockDiagonal (ℋ := ℋ) A0 A1 =
          blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg]
      · intro z
        simp [sub_eq_add_neg]
    exact hsub ▸ sub_nonneg.mpr h
  have hpos :
      (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 hnonneg
  have hleftPos : (B0 - A0).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    have hx :=
      (ContinuousLinearMap.isPositive_iff_complex
        (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1))).1 hpos (hsumIncl ℋ 0 x)
    simpa [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply] using hx
  exact sub_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hleftPos)

omit [Nontrivial ℋ] in
theorem blockDiagonal_selfAdjoint {A B : QuantumState.B ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  change star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) A B
  simp [blockDiagonal_star, hA.star_eq, hB.star_eq]

omit [CompleteSpace ℋ] in
theorem nontrivial_hsumL : Nontrivial (QuantumState.B (HSum ℋ)) := by
  infer_instance

theorem continuousOn_union_of_subset_Ici {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) := by
  refine hcont.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact hs hx
  · exact ht hx

omit [Nontrivial ℋ] in
theorem spectrum_Ici_of_nonneg {A : QuantumState.B ℋ} (hA0 : (0 : QuantumState.B ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
  exact
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A
      (ha := IsSelfAdjoint.of_nonneg hA0)).1 hA0

theorem spectrum_zero_subset_Ici :
    spectrum ℝ (0 : QuantumState.B ℋ) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  have hx0 : x = 0 := by
    simpa using hx
  simp [Set.Ici, hx0]

end JensenOperatorInequality
