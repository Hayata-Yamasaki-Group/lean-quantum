/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.CoreRetained

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
-- Direct matrix CFC identifies the explicit powers in Example 5.1.2.
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Concrete Hansen--Pedersen examples

This file formalizes the finite-dimensional counterexample from
Hiai--Yanagi Example 5.1.2. The matrices `A` and `B` satisfy `0 ≤ A ≤ B`, but
for every exponent `p > 1` the CFC power comparison `A^p ≤ B^p` fails.

## Main results

* `RpowCounterexample.spec`: the bundled Lean-facing statement of
  Example 5.1.2.
* `RpowCounterexample.spec_cfc`: the genuine CFC-power version of the example.
* `RpowCounterexample.matrixBpowComplex_eq_matrixCfcR`: the bridge from the
  explicit diagonal formula to matrix CFC.
* `RpowCounterexample.det_matrixBpow_sub_matrixA_neg_of_one_lt`: the
  determinant obstruction proving failure of positivity.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Example 5.1.2.
-/

namespace HansenPedersen

open scoped CStarAlgebra ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section Example_5_1_2

/-- The real `2 × 2` matrix algebra used for the explicit counterexample. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

namespace RpowCounterexample

/-- The matrix `A` in Example 5.1.2.
Source: Hiai–Yanagi, Example 5.1.2. -/
def matrixA : M2 :=
  !![(1 / 2 : ℝ), 1 / 2;
     1 / 2,       1 / 2]

/-- The matrix `B` in Example 5.1.2.
Source: Hiai–Yanagi, Example 5.1.2. -/
def matrixB : M2 :=
  !![(3 / 2 : ℝ), 0;
     0,           3 / 4]

/-- Lean-facing explicit formula for `B^p` in this diagonal example.
Source: Hiai–Yanagi, Example 5.1.2. -/
def matrixBpow (p : ℝ) : M2 :=
  !![((3 / 2 : ℝ) ^ p), 0;
     0,                 ((3 / 4 : ℝ) ^ p)]

/-- The matrix `A`, regarded in the complex matrix algebra used by `matrixCfcR`. -/
def matrixAComplex : Mₙ 2 :=
  !![Complex.ofReal (1 / 2 : ℝ), Complex.ofReal (1 / 2 : ℝ);
     Complex.ofReal (1 / 2 : ℝ), Complex.ofReal (1 / 2 : ℝ)]

/-- The matrix `B`, regarded in the complex matrix algebra used by `matrixCfcR`. -/
def matrixBComplex : Mₙ 2 :=
  Matrix.diagonal ![Complex.ofReal (3 / 2 : ℝ), Complex.ofReal (3 / 4 : ℝ)]

/-- The explicit complex diagonal formula corresponding to `matrixBpow`. -/
def matrixBpowComplex (p : ℝ) : Mₙ 2 :=
  Matrix.diagonal
    ![Complex.ofReal ((3 / 2 : ℝ) ^ p), Complex.ofReal ((3 / 4 : ℝ) ^ p)]

/-- The generic CFC signature fixes a semiring projection chain from `[Ring A]`.
For complex matrices that chain is definitionally, but not instance-transparently,
equal to the one carried by `Matrix.instStarRing`; supply the exact local instance. -/
private noncomputable local instance matrixStarRingOfRing
    {n : Type*} [Fintype n] [DecidableEq n] :
    @StarRing (Matrix n n ℂ)
      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring _
        (@NonAssocRing.toNonUnitalNonAssocRing _
          (@Ring.toNonAssocRing _ Matrix.instRing))) :=
  Matrix.instStarRing

/-- Positivity of the matrix `A`.
Source: Hiai–Yanagi, Example 5.1.2. -/
theorem matrixA_nonneg : 0 ≤ matrixA := by
  classical
  have hsqrt2inv_sq : (Real.sqrt (2 : ℝ))⁻¹ ^ (2 : ℕ) = (1 / 2 : ℝ) := by
    calc
      (Real.sqrt (2 : ℝ))⁻¹ ^ (2 : ℕ) = ((Real.sqrt (2 : ℝ)) ^ (2 : ℕ))⁻¹ := by
        simp
      _ = (2 : ℝ)⁻¹ := by
        simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ))]
      _ = (1 / 2 : ℝ) := by
        ring_nf
  have hsqrt2inv_mul :
      (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹ = (2 : ℝ)⁻¹ := by
    have : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹ = (1 / 2 : ℝ) := by
      simpa [pow_two] using hsqrt2inv_sq
    simpa [one_div] using this
  let C : M2 :=
    !![Real.sqrt (1 / 2 : ℝ), Real.sqrt (1 / 2 : ℝ);
       0,                    0]
  have hC : Cᵀ * C = matrixA := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [C, matrixA, Matrix.mul_apply, Fin.sum_univ_two]
      simpa using hsqrt2inv_mul
    · simp [C, matrixA, Matrix.mul_apply, Fin.sum_univ_two]
      simpa using hsqrt2inv_mul
    · simp [C, matrixA, Matrix.mul_apply, Fin.sum_univ_two]
      simpa using hsqrt2inv_mul
    · simp [C, matrixA, Matrix.mul_apply, Fin.sum_univ_two]
      simpa using hsqrt2inv_mul
  have hpsd : matrixA.PosSemidef := by
    simpa [hC] using (Matrix.posSemidef_conjTranspose_mul_self C)
  exact (Matrix.nonneg_iff_posSemidef (A := matrixA)).2 hpsd

/-- The order comparison `A ≤ B`.
Source: Hiai–Yanagi, Example 5.1.2. -/
theorem matrixA_le_matrixB : matrixA ≤ matrixB := by
  classical
  let C : M2 :=
    !![(1 : ℝ), -(1 / 2 : ℝ);
       0,       0]
  have hC : Cᵀ * C = matrixB - matrixA := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [C, matrixA, matrixB, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
    · simp [C, matrixA, matrixB, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [C, matrixA, matrixB, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [C, matrixA, matrixB, Matrix.mul_apply, Fin.sum_univ_two]
      ring_nf
  have hpsd : (matrixB - matrixA).PosSemidef := by
    simpa [hC] using (Matrix.posSemidef_conjTranspose_mul_self C)
  exact (Matrix.le_iff (A := matrixA) (B := matrixB)).2 hpsd

/-- Determinant formula for `B^p - A`.
Source: Hiai–Yanagi, Example 5.1.2. -/
theorem det_matrixBpow_sub_matrixA (p : ℝ) :
    (matrixBpow p - matrixA).det =
      ((9 / 8 : ℝ) ^ p) - (((3 / 2 : ℝ) ^ p + (3 / 4 : ℝ) ^ p) / 2) := by
  classical
  have hmul :
      ((3 / 2 : ℝ) ^ p) * ((3 / 4 : ℝ) ^ p) = ((9 / 8 : ℝ) ^ p) := by
    simpa [show (3 / 2 : ℝ) * (3 / 4 : ℝ) = (9 / 8 : ℝ) by ring_nf] using
      (Real.mul_rpow (x := (3 / 2 : ℝ)) (y := (3 / 4 : ℝ)) (z := p)
          (by positivity) (by positivity)).symm
  simp [Matrix.det_fin_two, matrixBpow, matrixA]
  ring_nf
  simp [hmul]
  ring_nf

/-- Negativity of the determinant for powers `p > 1`.
Source: Hiai–Yanagi, Example 5.1.2. -/
theorem det_matrixBpow_sub_matrixA_neg_of_one_lt {p : ℝ} (hp : 1 < p) :
    (matrixBpow p - matrixA).det < 0 := by
  have hx : (3 / 2 : ℝ) ∈ Set.Ici (0 : ℝ) := by
    have : (0 : ℝ) ≤ (3 / 2 : ℝ) := by positivity
    simpa [Set.mem_Ici] using this
  have hy : (3 / 4 : ℝ) ∈ Set.Ici (0 : ℝ) := by
    have : (0 : ℝ) ≤ (3 / 4 : ℝ) := by positivity
    simpa [Set.mem_Ici] using this
  have hne : (3 / 2 : ℝ) ≠ (3 / 4 : ℝ) := by nlinarith
  have hab : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring_nf
  have hstrict :
      ((9 / 8 : ℝ) ^ p) < (((3 / 2 : ℝ) ^ p + (3 / 4 : ℝ) ^ p) / 2) := by
    have hfun := (strictConvexOn_rpow (p := p) hp).2
    have h :=
      hfun hx hy hne (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by positivity) (by positivity) hab
    have h1 : (2⁻¹ : ℝ) * (3 / 2 : ℝ) + (2⁻¹ : ℝ) * (3 / 4 : ℝ) = (9 / 8 : ℝ) := by
      ring_nf
    have h2 :
        (2⁻¹ : ℝ) * ((3 / 2 : ℝ) ^ p) + (2⁻¹ : ℝ) * ((3 / 4 : ℝ) ^ p) =
          (((3 / 2 : ℝ) ^ p + (3 / 4 : ℝ) ^ p) / 2) := by
      ring_nf
    have h' :
        ((2⁻¹ : ℝ) * (3 / 2 : ℝ) + (2⁻¹ : ℝ) * (3 / 4 : ℝ)) ^ p <
          (2⁻¹ : ℝ) * ((3 / 2 : ℝ) ^ p) + (2⁻¹ : ℝ) * ((3 / 4 : ℝ) ^ p) := by
      simpa [smul_eq_mul] using h
    simpa [h1, h2] using h'
  have hdet :
      (matrixBpow p - matrixA).det =
        ((9 / 8 : ℝ) ^ p) - (((3 / 2 : ℝ) ^ p + (3 / 4 : ℝ) ^ p) / 2) :=
    det_matrixBpow_sub_matrixA p
  have : ((9 / 8 : ℝ) ^ p) - (((3 / 2 : ℝ) ^ p + (3 / 4 : ℝ) ^ p) / 2) < 0 :=
    sub_lt_zero.2 hstrict
  simpa [hdet] using this

/-- Failure of the order comparison `A ≤ B^p` for `p > 1`.
Source: Hiai–Yanagi, Example 5.1.2. -/
theorem not_matrixA_le_matrixBpow_of_one_lt {p : ℝ} (hp : 1 < p) :
    ¬ matrixA ≤ matrixBpow p := by
  classical
  intro hle
  have hpsd : (matrixBpow p - matrixA).PosSemidef :=
    (Matrix.le_iff (A := matrixA) (B := matrixBpow p)).1 hle
  have hdet0 : 0 ≤ (matrixBpow p - matrixA).det :=
    Matrix.PosSemidef.det_nonneg (A := matrixBpow p - matrixA) hpsd
  have hdetlt : (matrixBpow p - matrixA).det < 0 :=
    det_matrixBpow_sub_matrixA_neg_of_one_lt hp
  exact (not_lt_of_ge hdet0) hdetlt

/-- The complex copy of `A` is idempotent. -/
theorem matrixAComplex_mul_matrixAComplex :
    matrixAComplex * matrixAComplex = matrixAComplex := by
  classical
  ext i j
  fin_cases i <;> fin_cases j
  · simp [matrixAComplex, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [matrixAComplex, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [matrixAComplex, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [matrixAComplex, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Positivity of `A` in the complex matrix algebra used by `matrixCfcR`. -/
theorem matrixAComplex_nonneg : 0 ≤ matrixAComplex := by
  classical
  have hC : matrixAComplexᴴ * matrixAComplex = matrixAComplex := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [matrixAComplex, Matrix.mul_apply, Fin.sum_univ_two,
        RCLike.star_def, Complex.ext_iff]
  have hpsd : matrixAComplex.PosSemidef := by
    simpa [hC] using
      (Matrix.posSemidef_conjTranspose_mul_self matrixAComplex)
  exact (Matrix.nonneg_iff_posSemidef (A := matrixAComplex)).2 hpsd

/-- The order comparison `A ≤ B` in the complex matrix algebra. -/
theorem matrixAComplex_le_matrixBComplex : matrixAComplex ≤ matrixBComplex := by
  classical
  let C : Mₙ 2 :=
    !![Complex.ofReal (1 : ℝ), Complex.ofReal (-(1 / 2 : ℝ));
       0,                       0]
  have hC : Cᴴ * C = matrixBComplex - matrixAComplex := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [C, matrixAComplex, matrixBComplex, Matrix.mul_apply,
        Fin.sum_univ_two, RCLike.star_def, Complex.ext_iff]
  have hpsd : (matrixBComplex - matrixAComplex).PosSemidef := by
    simpa [hC] using (Matrix.posSemidef_conjTranspose_mul_self C)
  exact (Matrix.le_iff (A := matrixAComplex) (B := matrixBComplex)).2 hpsd

/-- The determinant obstruction also rules out the complex matrix order. -/
theorem not_matrixAComplex_le_matrixBpowComplex_of_one_lt
    {p : ℝ} (hp : 1 < p) :
    ¬ matrixAComplex ≤ matrixBpowComplex p := by
  classical
  intro hle
  have hpsd : (matrixBpowComplex p - matrixAComplex).PosSemidef :=
    (Matrix.le_iff (A := matrixAComplex) (B := matrixBpowComplex p)).1 hle
  have hdet0 : 0 ≤ (matrixBpowComplex p - matrixAComplex).det :=
    Matrix.PosSemidef.det_nonneg hpsd
  have hdetRe0 : 0 ≤ (matrixBpowComplex p - matrixAComplex).det.re :=
    (Complex.nonneg_iff.mp hdet0).1
  have hdetRe :
      (matrixBpowComplex p - matrixAComplex).det.re =
        (matrixBpow p - matrixA).det := by
    simp [matrixBpowComplex, matrixAComplex, matrixBpow, matrixA,
      Matrix.det_fin_two]
  rw [hdetRe] at hdetRe0
  exact (not_lt_of_ge hdetRe0)
    (det_matrixBpow_sub_matrixA_neg_of_one_lt hp)

/-- The real spectrum of the diagonal matrix `B` consists of its two entries. -/
private theorem spectrum_matrixBComplex_subset :
    spectrum ℝ matrixBComplex ⊆ ({3 / 2, 3 / 4} : Set ℝ) := by
  intro x hx
  have hxComplex : (x : ℂ) ∈ spectrum ℂ matrixBComplex :=
    spectrum.algebraMap_mem ℂ hx
  rw [matrixBComplex, spectrum_diagonal] at hxComplex
  rcases hxComplex with ⟨i, hi⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases i
  · left
    have h : (x : ℂ) = Complex.ofReal (3 / 2 : ℝ) := by
      simpa using hi.symm
    exact_mod_cast h
  · right
    have h : (x : ℂ) = Complex.ofReal (3 / 4 : ℝ) := by
      simpa using hi.symm
    exact_mod_cast h

/-- On a self-adjoint complex matrix, the transported operator CFC agrees with
the direct matrix CFC. -/
private theorem matrixCfcR_eq_matrixCfc
    (f : ℝ → ℝ) (A : Mₙ 2) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    matrixCfcR f A = cfc f A := by
  let φ := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hφisom : Isometry φ := by
    rw [isometry_iff_dist_eq]
    intro X Y
    calc
      dist (φ X) (φ Y) = ‖φ (X - Y)‖ := by
        rw [dist_eq_norm, map_sub]
      _ = ‖X - Y‖ := (Matrix.cstar_norm_def (X - Y)).symm
      _ = dist X Y := by rw [dist_eq_norm]
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ f A
    (hf := hf) (hφ := hφisom.continuous) (ha := hA) (hφa := hφA)
  change φ.symm (cfc f (φ A)) = cfc f A
  rw [← hmap, φ.symm_apply_apply]

/-- For `p > 1`, CFC sends the idempotent matrix `A` to `A` under `t ↦ t^p`. -/
theorem matrixCfcR_rpow_matrixAComplex {p : ℝ} (hp : 1 < p) :
    matrixCfcR (fun t : ℝ => t ^ p) matrixAComplex = matrixAComplex := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  have hpne : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hA : IsSelfAdjoint matrixAComplex :=
    IsSelfAdjoint.of_nonneg matrixAComplex_nonneg
  have hf : ContinuousOn (fun t : ℝ => t ^ p) (spectrum ℝ matrixAComplex) :=
    (Real.continuous_rpow_const hp0).continuousOn
  rw [matrixCfcR_eq_matrixCfc (fun t : ℝ => t ^ p) matrixAComplex hA hf]
  have hspec : spectrum ℝ matrixAComplex ⊆ ({0, 1} : Set ℝ) :=
    (isIdempotentElem_iff_spectrum_subset ℝ matrixAComplex hA).mp
      matrixAComplex_mul_matrixAComplex
  have hfun : Set.EqOn (fun t : ℝ => t ^ p) id (spectrum ℝ matrixAComplex) := by
    intro t ht
    rcases hspec ht with (rfl | rfl)
    · simp [Real.zero_rpow hpne]
    · simp
  calc
    cfc (fun t : ℝ => t ^ p) matrixAComplex = cfc id matrixAComplex :=
      cfc_congr hfun
    _ = matrixAComplex := cfc_id ℝ matrixAComplex hA

/-- The explicit diagonal power of `B` is exactly its matrix CFC power. -/
theorem matrixBpowComplex_eq_matrixCfcR {p : ℝ} (hp : 1 < p) :
    matrixBpowComplex p =
      matrixCfcR (fun t : ℝ => t ^ p) matrixBComplex := by
  let u : ℝ := (3 / 2 : ℝ) ^ p
  let v : ℝ := (3 / 4 : ℝ) ^ p
  let a : ℝ := (4 / 3 : ℝ) * (u - v)
  let b : ℝ := 2 * v - u
  let g : ℝ → ℝ := fun t => a * t + b
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  have hBnonneg : 0 ≤ matrixBComplex :=
    le_trans matrixAComplex_nonneg matrixAComplex_le_matrixBComplex
  have hB : IsSelfAdjoint matrixBComplex :=
    IsSelfAdjoint.of_nonneg hBnonneg
  have hf : ContinuousOn (fun t : ℝ => t ^ p) (spectrum ℝ matrixBComplex) :=
    (Real.continuous_rpow_const hp0).continuousOn
  rw [matrixCfcR_eq_matrixCfc (fun t : ℝ => t ^ p) matrixBComplex hB hf]
  have hfun : Set.EqOn (fun t : ℝ => t ^ p) g (spectrum ℝ matrixBComplex) := by
    intro t ht
    rcases spectrum_matrixBComplex_subset ht with (rfl | rfl)
    · dsimp [g, a, b, u, v]
      ring
    · dsimp [g, a, b, u, v]
      ring
  have hcfc :
      cfc g matrixBComplex =
        a • matrixBComplex + algebraMap ℝ (Mₙ 2) b := by
    change cfc (fun t : ℝ => a * t + b) matrixBComplex = _
    rw [cfc_add_const (R := ℝ) b (fun t : ℝ => a * t) matrixBComplex
      (by fun_prop) hB]
    rw [cfc_const_mul_id (R := ℝ) a matrixBComplex hB]
  have hexplicit :
      a • matrixBComplex + algebraMap ℝ (Mₙ 2) b =
        matrixBpowComplex p := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.add_apply, Matrix.algebraMap_matrix_apply]
      simp [matrixBpowComplex, matrixBComplex, a, b, u, v]
      ring
    · simp only [Matrix.add_apply, Matrix.algebraMap_matrix_apply]
      simp [matrixBpowComplex, matrixBComplex, a, u, v]
    · simp only [Matrix.add_apply, Matrix.algebraMap_matrix_apply]
      simp [matrixBpowComplex, matrixBComplex, a, u, v]
    · simp only [Matrix.add_apply, Matrix.algebraMap_matrix_apply]
      simp [matrixBpowComplex, matrixBComplex, a, b, u, v]
      ring
  calc
    matrixBpowComplex p = a • matrixBComplex + algebraMap ℝ (Mₙ 2) b :=
      hexplicit.symm
    _ = cfc g matrixBComplex := hcfc.symm
    _ = cfc (fun t : ℝ => t ^ p) matrixBComplex := (cfc_congr hfun).symm

/-- The CFC powers in Example 5.1.2 fail to preserve the matrix order. -/
theorem not_matrixCfcR_rpow_le_of_one_lt {p : ℝ} (hp : 1 < p) :
    ¬ matrixCfcR (fun t : ℝ => t ^ p) matrixAComplex ≤
      matrixCfcR (fun t : ℝ => t ^ p) matrixBComplex := by
  rw [matrixCfcR_rpow_matrixAComplex hp,
    ← matrixBpowComplex_eq_matrixCfcR hp]
  exact not_matrixAComplex_le_matrixBpowComplex_of_one_lt hp

/-- The original explicit-form statement of Example 5.1.2. -/
theorem spec {p : ℝ} (hp : 1 < p) :
    0 ≤ matrixA ∧
    matrixA ≤ matrixB ∧
    ¬ matrixA ≤ matrixBpow p := by
  exact ⟨matrixA_nonneg, matrixA_le_matrixB, not_matrixA_le_matrixBpow_of_one_lt hp⟩


/-- CFC-connected Lean-facing form of Example 5.1.2. -/
theorem spec_cfc {p : ℝ} (hp : 1 < p) :
    0 ≤ matrixAComplex ∧
    matrixAComplex ≤ matrixBComplex ∧
    ¬ matrixCfcR (fun t : ℝ => t ^ p) matrixAComplex ≤
      matrixCfcR (fun t : ℝ => t ^ p) matrixBComplex := by
  exact ⟨matrixAComplex_nonneg, matrixAComplex_le_matrixBComplex,
    not_matrixCfcR_rpow_le_of_one_lt hp⟩

end RpowCounterexample

end Example_5_1_2

end

end HansenPedersen
