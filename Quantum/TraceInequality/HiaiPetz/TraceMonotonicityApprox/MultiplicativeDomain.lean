/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.TracePowerPos
import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore.SchwarzAdjoint
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Adjoint multiplicative domain and negative exponent ranges

The Schwarz-defect argument showing `hsAdjoint Φ` is multiplicative on the
adjoint multiplicative domain, and the transport of Theorem 6.3(3) to the
negative ranges `-1 < p < 0` and `-1 ≤ p ≤ 0`, combining into the full range
`-1 ≤ p ≤ 2` (`liebTracePower_map_le_outputSupport_fullRange`).
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology Interval
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private theorem hsAdjoint_map_conjTranspose_of_schwarz_all {n m : ℕ} {Φ : HSMap n m}
    (hSch : HSAdjointSchwarz Φ) (X : Mₙ m) :
    (hsAdjoint Φ) (Matrix.conjTranspose X) =
      Matrix.conjTranspose ((hsAdjoint Φ) X) := by
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      cases m with
      | zero =>
          have hXzero : X = 0 := by
            ext i
            exact Fin.elim0 i
          subst hXzero
          have hz : (hsAdjoint Φ) (0 : Mₙ 0) = 0 := (hsAdjoint Φ).map_zero
          have hct0 : Matrix.conjTranspose (0 : Mₙ 0) = 0 := by
            ext i
            exact Fin.elim0 i
          rw [hct0]
          ext i j
          calc
            (hsAdjoint Φ) 0 i j = (0 : Mₙ (Nat.succ n)) i j :=
              congrFun (congrFun hz i) j
            _ = Matrix.conjTranspose (0 : Mₙ (Nat.succ n)) i j := by simp
            _ = Matrix.conjTranspose ((hsAdjoint Φ) 0) i j :=
              congrArg (fun Y : Mₙ (Nat.succ n) => Matrix.conjTranspose Y i j) hz.symm
      | succ m =>
          exact hsAdjoint_map_conjTranspose_of_schwarz (Φ := Φ) hSch X

private theorem inAdjointMultiplicativeDomain_conjTranspose {n m : ℕ} {Φ : HSMap n m}
    {X : Mₙ m} (hSch : HSAdjointSchwarz Φ)
    (hmd : InAdjointMultiplicativeDomain Φ X) :
    InAdjointMultiplicativeDomain Φ (Matrix.conjTranspose X) := by
  have hmap := hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch X
  constructor
  · have h :
        (hsAdjoint Φ) (Matrix.conjTranspose X * X) =
          (hsAdjoint Φ) (Matrix.conjTranspose X) *
            Matrix.conjTranspose ((hsAdjoint Φ) (Matrix.conjTranspose X)) := by
      rw [hmd.2, hmap]
      simp [Matrix.conjTranspose_conjTranspose]
    simpa [Matrix.conjTranspose_conjTranspose] using h
  · have h :
        (hsAdjoint Φ) (X * Matrix.conjTranspose X) =
          Matrix.conjTranspose ((hsAdjoint Φ) (Matrix.conjTranspose X)) *
            (hsAdjoint Φ) (Matrix.conjTranspose X) := by
      rw [hmd.1, hmap]
      simp [Matrix.conjTranspose_conjTranspose]
    simpa [Matrix.conjTranspose_conjTranspose] using h

private def schwarzDefect {n m : ℕ} (Φ : HSMap n m) (U V : Mₙ m) : Mₙ n :=
  (hsAdjoint Φ) (U * Matrix.conjTranspose V) -
    ((hsAdjoint Φ) U) * Matrix.conjTranspose ((hsAdjoint Φ) V)

private def scalarSchwarzDefect {n m : ℕ} (Φ : HSMap n m)
    (U V : Mₙ m) (v : Fin n → ℂ) : ℂ :=
  star v ⬝ᵥ ((schwarzDefect Φ U V).mulVec v)

private theorem hsAdjointSchwarz_mul_conjTranspose_all {n m : ℕ} {Φ : HSMap n m}
    (hSch : HSAdjointSchwarz Φ) (U : Mₙ m) :
    ((hsAdjoint Φ) U) * Matrix.conjTranspose ((hsAdjoint Φ) U) ≤
      (hsAdjoint Φ) (U * Matrix.conjTranspose U) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      cases m with
      | zero =>
          have hUzero : U = 0 := by
            ext i
            exact Fin.elim0 i
          subst hUzero
          have hz : (hsAdjoint Φ) (0 : Mₙ 0) = 0 := (hsAdjoint Φ).map_zero
          have hz' : (hsAdjoint Φ) 0 = 0 := by
            ext i j
            exact congrFun (congrFun hz i) j
          rw [hz']
          have hprod : (0 : Mₙ 0) * Matrix.conjTranspose 0 = 0 := by
            ext i
            exact Fin.elim0 i
          rw [hprod, hz']
          rw [zero_mul]
      | succ m =>
          exact hsAdjointSchwarz_mul_conjTranspose (Φ := Φ) hSch U

private theorem scalarSchwarzDefect_diag_nonneg {n m : ℕ} {Φ : HSMap n m}
    (hSch : HSAdjointSchwarz Φ) (U : Mₙ m) (v : Fin n → ℂ) :
    0 ≤ Complex.re (scalarSchwarzDefect Φ U U v) := by
  have hle := hsAdjointSchwarz_mul_conjTranspose_all (Φ := Φ) hSch U
  have hnonneg : 0 ≤ schwarzDefect Φ U U := by
    dsimp [schwarzDefect]
    exact sub_nonneg.mpr hle
  have hpsd : (schwarzDefect Φ U U).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnonneg
  have hv := hpsd.dotProduct_mulVec_nonneg v
  exact Complex.nonneg_iff.mp hv |>.1

private theorem scalarSchwarzDefect_diag_zero {n m : ℕ} {Φ : HSMap n m}
    {X : Mₙ m} (hmd : InAdjointMultiplicativeDomain Φ X) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ X X v = 0 := by
  dsimp [scalarSchwarzDefect, schwarzDefect]
  rw [hmd.1]
  simp

private theorem schwarzDefect_add_left {n m : ℕ} (Φ : HSMap n m)
    (U₁ U₂ V : Mₙ m) :
    schwarzDefect Φ (U₁ + U₂) V =
      schwarzDefect Φ U₁ V + schwarzDefect Φ U₂ V := by
  simp only [schwarzDefect, Matrix.add_mul, map_add]
  abel

private theorem schwarzDefect_smul_left {n m : ℕ} (Φ : HSMap n m)
    (z : ℂ) (U V : Mₙ m) :
    schwarzDefect Φ (z • U) V = z • schwarzDefect Φ U V := by
  ext i j
  simp [schwarzDefect, sub_eq_add_neg]
  ring

private theorem schwarzDefect_add_right {n m : ℕ} (Φ : HSMap n m)
    (U V₁ V₂ : Mₙ m) :
    schwarzDefect Φ U (V₁ + V₂) =
      schwarzDefect Φ U V₁ + schwarzDefect Φ U V₂ := by
  simp only [schwarzDefect, Matrix.conjTranspose_add, Matrix.mul_add, map_add]
  abel

private theorem schwarzDefect_smul_right {n m : ℕ} (Φ : HSMap n m)
    (z : ℂ) (U V : Mₙ m) :
    schwarzDefect Φ U (z • V) = star z • schwarzDefect Φ U V := by
  ext i j
  simp [schwarzDefect, Matrix.conjTranspose_smul, sub_eq_add_neg]
  ring

private theorem scalarSchwarzDefect_add_left {n m : ℕ} (Φ : HSMap n m)
    (U₁ U₂ V : Mₙ m) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ (U₁ + U₂) V v =
      scalarSchwarzDefect Φ U₁ V v + scalarSchwarzDefect Φ U₂ V v := by
  rw [scalarSchwarzDefect, schwarzDefect_add_left]
  simp [scalarSchwarzDefect, Matrix.add_mulVec]

private theorem scalarSchwarzDefect_smul_left {n m : ℕ} (Φ : HSMap n m)
    (z : ℂ) (U V : Mₙ m) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ (z • U) V v = z * scalarSchwarzDefect Φ U V v := by
  rw [scalarSchwarzDefect, schwarzDefect_smul_left]
  simp [scalarSchwarzDefect, Matrix.smul_mulVec, dotProduct_smul]

private theorem scalarSchwarzDefect_add_right {n m : ℕ} (Φ : HSMap n m)
    (U V₁ V₂ : Mₙ m) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ U (V₁ + V₂) v =
      scalarSchwarzDefect Φ U V₁ v + scalarSchwarzDefect Φ U V₂ v := by
  rw [scalarSchwarzDefect, schwarzDefect_add_right]
  simp [scalarSchwarzDefect, Matrix.add_mulVec]

private theorem scalarSchwarzDefect_smul_right {n m : ℕ} (Φ : HSMap n m)
    (z : ℂ) (U V : Mₙ m) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ U (z • V) v = star z * scalarSchwarzDefect Φ U V v := by
  rw [scalarSchwarzDefect, schwarzDefect_smul_right]
  simp [scalarSchwarzDefect, Matrix.smul_mulVec, dotProduct_smul]

private theorem scalarSchwarzDefect_add_smul_self {n m : ℕ} (Φ : HSMap n m)
    (X Y : Mₙ m) (v : Fin n → ℂ) (z : ℂ) :
    scalarSchwarzDefect Φ (X + z • Y) (X + z • Y) v =
      scalarSchwarzDefect Φ X X v + star z * scalarSchwarzDefect Φ X Y v +
        z * scalarSchwarzDefect Φ Y X v +
          (z * star z) * scalarSchwarzDefect Φ Y Y v := by
  rw [scalarSchwarzDefect_add_left, scalarSchwarzDefect_add_right,
    scalarSchwarzDefect_smul_right, scalarSchwarzDefect_add_right,
    scalarSchwarzDefect_smul_right, scalarSchwarzDefect_smul_left,
    scalarSchwarzDefect_smul_left]
  ring

private theorem schwarzDefect_conjTranspose {n m : ℕ} {Φ : HSMap n m}
    (hSch : HSAdjointSchwarz Φ) (U V : Mₙ m) :
    schwarzDefect Φ V U = Matrix.conjTranspose (schwarzDefect Φ U V) := by
  have hUV :
      (hsAdjoint Φ) (V * Matrix.conjTranspose U) =
        Matrix.conjTranspose ((hsAdjoint Φ) (U * Matrix.conjTranspose V)) := by
    have h :=
      hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch
        (U * Matrix.conjTranspose V)
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h
  rw [schwarzDefect, schwarzDefect, hUV]
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, sub_eq_add_neg]

private theorem scalarSchwarzDefect_conj {n m : ℕ} {Φ : HSMap n m}
    (hSch : HSAdjointSchwarz Φ) (U V : Mₙ m) (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ V U v = star (scalarSchwarzDefect Φ U V v) := by
  rw [scalarSchwarzDefect, schwarzDefect_conjTranspose (Φ := Φ) hSch U V]
  simp only [scalarSchwarzDefect, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
    Finset.mul_sum, star_sum, star_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

private theorem real_linear_coeff_zero_of_quad_nonneg {a b : ℝ}
    (h : ∀ r : ℝ, 0 ≤ r * r * a + r * b) : b = 0 := by
  by_contra hb
  let R : ℝ := |a| + 1
  have hRpos : 0 < R := by
    have hnonneg : 0 ≤ |a| := abs_nonneg a
    dsimp [R]
    linarith
  have hAlt : a - 2 * R < 0 := by
    have hle : a ≤ |a| := le_abs_self a
    dsimp [R]
    linarith
  have hb2pos : 0 < b * b := mul_self_pos.mpr hb
  let r : ℝ := -b / (2 * R)
  have hnonneg := h r
  have hcalc : r * r * a + r * b = (b * b / (4 * R * R)) * (a - 2 * R) := by
    dsimp [r]
    field_simp [hRpos.ne']
    ring
  rw [hcalc] at hnonneg
  have hcoefpos : 0 < b * b / (4 * R * R) := by
    positivity
  have hneg : (b * b / (4 * R * R)) * (a - 2 * R) < 0 := by
    nlinarith
  linarith

private theorem scalarSchwarzDefect_add_real_smul_self_re {n m : ℕ} {Φ : HSMap n m}
    {X Y : Mₙ m} (v : Fin n → ℂ) (r : ℝ)
    (hXX : scalarSchwarzDefect Φ X X v = 0)
    (hYX : scalarSchwarzDefect Φ Y X v = star (scalarSchwarzDefect Φ X Y v)) :
    Complex.re (scalarSchwarzDefect Φ (X + (r : ℂ) • Y) (X + (r : ℂ) • Y) v) =
      r * r * Complex.re (scalarSchwarzDefect Φ Y Y v) +
        r * (2 * Complex.re (scalarSchwarzDefect Φ X Y v)) := by
  rw [scalarSchwarzDefect_add_smul_self, hXX, hYX]
  simp
  ring

private theorem scalarSchwarzDefect_add_im_smul_self_re {n m : ℕ} {Φ : HSMap n m}
    {X Y : Mₙ m} (v : Fin n → ℂ) (r : ℝ)
    (hXX : scalarSchwarzDefect Φ X X v = 0)
    (hYX : scalarSchwarzDefect Φ Y X v = star (scalarSchwarzDefect Φ X Y v)) :
    Complex.re (scalarSchwarzDefect Φ (X + ((r : ℂ) * Complex.I) • Y)
        (X + ((r : ℂ) * Complex.I) • Y) v) =
      r * r * Complex.re (scalarSchwarzDefect Φ Y Y v) +
        r * (2 * Complex.im (scalarSchwarzDefect Φ X Y v)) := by
  rw [scalarSchwarzDefect_add_smul_self, hXX, hYX]
  simp
  ring

private theorem scalarSchwarzDefect_left_zero_of_inAdjointMultiplicativeDomain
    {n m : ℕ} {Φ : HSMap n m} {X Y : Mₙ m}
    (hSch : HSAdjointSchwarz Φ) (hmd : InAdjointMultiplicativeDomain Φ X)
    (v : Fin n → ℂ) :
    scalarSchwarzDefect Φ X Y v = 0 := by
  have hXX : scalarSchwarzDefect Φ X X v = 0 := scalarSchwarzDefect_diag_zero hmd v
  have hYX : scalarSchwarzDefect Φ Y X v = star (scalarSchwarzDefect Φ X Y v) :=
    scalarSchwarzDefect_conj (Φ := Φ) hSch X Y v
  have hre : Complex.re (scalarSchwarzDefect Φ X Y v) = 0 := by
    have h2 : 2 * Complex.re (scalarSchwarzDefect Φ X Y v) = 0 := by
      apply (real_linear_coeff_zero_of_quad_nonneg
        (a := Complex.re (scalarSchwarzDefect Φ Y Y v))
        (b := 2 * Complex.re (scalarSchwarzDefect Φ X Y v)))
      intro r
      have hnonneg := scalarSchwarzDefect_diag_nonneg (Φ := Φ) hSch
        (X + (r : ℂ) • Y) v
      rw [scalarSchwarzDefect_add_real_smul_self_re (Φ := Φ) (X := X) (Y := Y)
        v r hXX hYX] at hnonneg
      simpa [mul_assoc] using hnonneg
    linarith
  have him : Complex.im (scalarSchwarzDefect Φ X Y v) = 0 := by
    have h2 : 2 * Complex.im (scalarSchwarzDefect Φ X Y v) = 0 := by
      apply (real_linear_coeff_zero_of_quad_nonneg
        (a := Complex.re (scalarSchwarzDefect Φ Y Y v))
        (b := 2 * Complex.im (scalarSchwarzDefect Φ X Y v)))
      intro r
      have hnonneg := scalarSchwarzDefect_diag_nonneg (Φ := Φ) hSch
        (X + ((r : ℂ) * Complex.I) • Y) v
      rw [scalarSchwarzDefect_add_im_smul_self_re (Φ := Φ) (X := X) (Y := Y)
        v r hXX hYX] at hnonneg
      simpa [mul_assoc] using hnonneg
    linarith
  exact Complex.ext hre him

private def matrixSesq {n : ℕ} (M : Mₙ n) (u v : Fin n → ℂ) : ℂ :=
  star u ⬝ᵥ (M.mulVec v)

private theorem matrixSesq_add_smul_self {n : ℕ} (M : Mₙ n)
    (u v : Fin n → ℂ) (z : ℂ) :
    matrixSesq M (u + z • v) (u + z • v) =
      matrixSesq M u u + z * matrixSesq M u v +
        star z * matrixSesq M v u + (star z * z) * matrixSesq M v v := by
  simp [matrixSesq, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, dotProduct_smul, smul_dotProduct, add_assoc]
  ring

private theorem matrixSesq_zero_of_quad_zero {n : ℕ} (M : Mₙ n)
    (h : ∀ v : Fin n → ℂ, matrixSesq M v v = 0) (u v : Fin n → ℂ) :
    matrixSesq M u v = 0 := by
  have huu := h u
  have hvv := h v
  have hplus := h (u + (1 : ℂ) • v)
  have him := h (u + Complex.I • v)
  have hsum : matrixSesq M u v + matrixSesq M v u = 0 := by
    rw [matrixSesq_add_smul_self, huu, hvv] at hplus
    simpa using hplus
  have himsum : Complex.I * matrixSesq M u v - Complex.I * matrixSesq M v u = 0 := by
    rw [matrixSesq_add_smul_self, huu, hvv] at him
    simpa [sub_eq_add_neg, Complex.star_def] using him
  have hdiff : matrixSesq M u v - matrixSesq M v u = 0 := by
    have hmul : Complex.I * (matrixSesq M u v - matrixSesq M v u) = 0 := by
      simpa [mul_sub] using himsum
    exact mul_eq_zero.mp hmul |>.resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * hsum + (1 / 2 : ℂ) * hdiff

private theorem matrixSesq_single_single {n : ℕ} (M : Mₙ n) (i j : Fin n) :
    matrixSesq M (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) = M i j := by
  simp [matrixSesq]

private theorem matrix_eq_zero_of_quadratic_form_zero {n : ℕ} (M : Mₙ n)
    (h : ∀ v : Fin n → ℂ, star v ⬝ᵥ (M.mulVec v) = 0) : M = 0 := by
  ext i j
  have hsesq := matrixSesq_zero_of_quad_zero M (by
    intro v
    exact h v) (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ))
  simpa [matrixSesq_single_single] using hsesq

private theorem schwarzDefect_left_zero_of_inAdjointMultiplicativeDomain
    {n m : ℕ} {Φ : HSMap n m} {X Y : Mₙ m}
    (hSch : HSAdjointSchwarz Φ) (hmd : InAdjointMultiplicativeDomain Φ X) :
    schwarzDefect Φ X Y = 0 := by
  apply matrix_eq_zero_of_quadratic_form_zero
  intro v
  simpa [scalarSchwarzDefect] using
    scalarSchwarzDefect_left_zero_of_inAdjointMultiplicativeDomain
      (Φ := Φ) (X := X) (Y := Y) hSch hmd v

/-- On the adjoint multiplicative domain of `X`, the Hilbert–Schmidt adjoint is
multiplicative for the product `X * Yᴴ`:
`Φ*(X Yᴴ) = Φ*(X) Φ*(Y)ᴴ`. -/
theorem hsAdjoint_mul_conjTranspose_of_inAdjointMultiplicativeDomain
    {n m : ℕ} {Φ : HSMap n m} {X Y : Mₙ m}
    (hSch : HSAdjointSchwarz Φ) (hmd : InAdjointMultiplicativeDomain Φ X) :
    (hsAdjoint Φ) (X * Matrix.conjTranspose Y) =
      ((hsAdjoint Φ) X) * Matrix.conjTranspose ((hsAdjoint Φ) Y) := by
  have hzero :=
    schwarzDefect_left_zero_of_inAdjointMultiplicativeDomain
      (Φ := Φ) (X := X) (Y := Y) hSch hmd
  simpa [schwarzDefect, sub_eq_zero] using hzero

/-- On the adjoint multiplicative domain of `X`, the Hilbert–Schmidt adjoint is
multiplicative for the product `Xᴴ * Y`:
`Φ*(Xᴴ Y) = Φ*(X)ᴴ Φ*(Y)`. -/
theorem hsAdjoint_conjTranspose_mul_of_inAdjointMultiplicativeDomain
    {n m : ℕ} {Φ : HSMap n m} {X Y : Mₙ m}
    (hSch : HSAdjointSchwarz Φ) (hmd : InAdjointMultiplicativeDomain Φ X) :
    (hsAdjoint Φ) (Matrix.conjTranspose X * Y) =
      Matrix.conjTranspose ((hsAdjoint Φ) X) * ((hsAdjoint Φ) Y) := by
  have hmdStar : InAdjointMultiplicativeDomain Φ (Matrix.conjTranspose X) :=
    inAdjointMultiplicativeDomain_conjTranspose hSch hmd
  have hmain :=
    hsAdjoint_mul_conjTranspose_of_inAdjointMultiplicativeDomain
      (Φ := Φ) (X := Matrix.conjTranspose X) (Y := Matrix.conjTranspose Y) hSch hmdStar
  have hXmap := hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch X
  have hYmap := hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch Y
  simpa [Matrix.conjTranspose_conjTranspose, hXmap, hYmap] using hmain

private theorem liebTracePower_conjTranspose_swap {n : ℕ} (p : ℝ) (A B X : Mₙ n) :
    liebTracePower p A B X =
      liebTracePower (1 - p) B A (Matrix.conjTranspose X) := by
  rw [liebTracePower, liebTracePower, powerTrace, powerTrace]
  simp only [Matrix.conjTranspose_conjTranspose]
  congr 1
  ring_nf
  calc
    Matrix.trace (Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B)
        = Matrix.trace (matrixPower p A * X * matrixPower (1 - p) B *
            Matrix.conjTranspose X) := by
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_comm (Matrix.conjTranspose X)
              (matrixPower p A * X * matrixPower (1 - p) B)
    _ = Matrix.trace (X * matrixPower (1 - p) B * Matrix.conjTranspose X *
          matrixPower p A) := by
        simpa [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (matrixPower p A)
            (X * matrixPower (1 - p) B * Matrix.conjTranspose X)

/-- Strict-output positive-definite trace-power form of Theorem 6.3(3) on
the negative open range `-1 < p < 0`.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeStrictlyPositiveNegIoo : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Ioo (-1 : ℝ) 0 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    InAdjointMultiplicativeDomain Φ X →
    liebTracePower p (Φ A) (Φ B) X ≤
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- Reduce the negative open range of Theorem 6.3(3) to the already formalized
positive open range by swapping `A` and `B` and replacing `X` by `X*`.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_strictlyPositive_negIoo :
    LiebTracePowerMapLeStrictlyPositiveNegIoo := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hmd
  let q : ℝ := 1 - p
  have hq : q ∈ Set.Ioo (1 : ℝ) 2 := by
    dsimp [q]
    constructor <;> linarith [hp.1, hp.2]
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hmdStar : InAdjointMultiplicativeDomain Φ (Matrix.conjTranspose X) :=
    inAdjointMultiplicativeDomain_conjTranspose hSch hmd
  have hpos :=
    liebTracePower_map_le_strictlyPositive_Ioo Φ (p := q) (A := B) (B := A)
      (X := Matrix.conjTranspose X) hq hPos hTrace hSch hB hA hΦ1 hΦA hmdStar
  have hleft :
      liebTracePower p (Φ A) (Φ B) X =
        liebTracePower q (Φ B) (Φ A) (Matrix.conjTranspose X) := by
    simpa [q] using
      liebTracePower_conjTranspose_swap (p := p) (A := Φ A) (B := Φ B) (X := X)
  have hmap := hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch X
  have hright :
      liebTracePower p A B ((hsAdjoint Φ) X) =
        liebTracePower q B A ((hsAdjoint Φ) (Matrix.conjTranspose X)) := by
    have hswap :=
      liebTracePower_conjTranspose_swap (p := p) (A := A) (B := B)
        (X := (hsAdjoint Φ) X)
    simpa [q, hmap] using hswap
  rwa [← hleft, ← hright] at hpos

/-- Output-support trace-power form of the negative open range of Theorem 6.3(3).
As in the positive open range, this is stated on a fixed orthonormal matrix realization of
the support corner.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeOutputSupportNegIoo : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Ioo (-1 : ℝ) 0 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      InAdjointMultiplicativeDomain Ψ X →
      liebTracePower p (Ψ A) (Ψ B) X ≤
        liebTracePower p A B ((hsAdjoint Ψ) X)

/-- Transport the negative open range of Theorem 6.3(3) to the fixed orthonormal matrix
realization of the output-support corner.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_outputSupport_negIoo :
    LiebTracePowerMapLeOutputSupportNegIoo := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X hmd
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (liebTracePower_map_le_strictlyPositive_negIoo Ψ (p := p) (A := A) (B := B)
      (X := X) hp hΨpos hΨtrace hΨsch hA hB hΨ1 hmd)

/-- Strict-output positive-definite trace-power form of Theorem 6.3(3) on
the negative closed range `-1 ≤ p ≤ 0`.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeStrictlyPositiveNegIcc : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Icc (-1 : ℝ) 0 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    InAdjointMultiplicativeDomain Φ X →
    liebTracePower p (Φ A) (Φ B) X ≤
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- Reduce the negative closed range to the positive closed range by swapping `A` and
`B` and replacing `X` by `X*`.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_strictlyPositive_negIcc :
    LiebTracePowerMapLeStrictlyPositiveNegIcc := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hmd
  let q : ℝ := 1 - p
  have hq : q ∈ Set.Icc (1 : ℝ) 2 := by
    dsimp [q]
    constructor <;> linarith [hp.1, hp.2]
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hmdStar : InAdjointMultiplicativeDomain Φ (Matrix.conjTranspose X) :=
    inAdjointMultiplicativeDomain_conjTranspose hSch hmd
  have hpos :=
    liebTracePower_map_le_strictlyPositive_posIcc Φ (p := q) (A := B) (B := A)
      (X := Matrix.conjTranspose X) hq hPos hTrace hSch hB hA hΦ1 hΦA hmdStar
  have hleft :
      liebTracePower p (Φ A) (Φ B) X =
        liebTracePower q (Φ B) (Φ A) (Matrix.conjTranspose X) := by
    simpa [q] using
      liebTracePower_conjTranspose_swap (p := p) (A := Φ A) (B := Φ B) (X := X)
  have hmap := hsAdjoint_map_conjTranspose_of_schwarz_all (Φ := Φ) hSch X
  have hright :
      liebTracePower p A B ((hsAdjoint Φ) X) =
        liebTracePower q B A ((hsAdjoint Φ) (Matrix.conjTranspose X)) := by
    have hswap :=
      liebTracePower_conjTranspose_swap (p := p) (A := A) (B := B)
        (X := (hsAdjoint Φ) X)
    simpa [q, hmap] using hswap
  rwa [← hleft, ← hright] at hpos

/-- Output-support trace-power form of the negative closed range of Theorem 6.3(3).
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeOutputSupportNegIcc : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Icc (-1 : ℝ) 0 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      InAdjointMultiplicativeDomain Ψ X →
      liebTracePower p (Ψ A) (Ψ B) X ≤
        liebTracePower p A B ((hsAdjoint Ψ) X)

/-- Transport the negative closed range of Theorem 6.3(3) to the fixed orthonormal matrix
realization of the output-support corner.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_outputSupport_negIcc :
    LiebTracePowerMapLeOutputSupportNegIcc := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X hmd
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (liebTracePower_map_le_strictlyPositive_negIcc Ψ (p := p) (A := A) (B := B)
      (X := X) hp hΨpos hΨtrace hΨsch hA hB hΨ1 hmd)

/-- Output-support trace-power form of Theorem 6.3(3) on the full book range
`[-1,0] ∪ [1,2]`, stated on a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeOutputSupportFullRange : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Icc (-1 : ℝ) 0 ∪ Set.Icc (1 : ℝ) 2 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      InAdjointMultiplicativeDomain Ψ X →
      liebTracePower p (Ψ A) (Ψ B) X ≤
        liebTracePower p A B ((hsAdjoint Ψ) X)

/-- Assemble the positive and negative closed output-support ranges for
Theorem 6.3(3).
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_outputSupport_fullRange :
    LiebTracePowerMapLeOutputSupportFullRange := by
  intro n m Φ p A B hp
  rcases hp with hpneg | hppos
  · exact liebTracePower_map_le_outputSupport_negIcc Φ hpneg
  · exact liebTracePower_map_le_outputSupport_posIcc Φ hppos

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
