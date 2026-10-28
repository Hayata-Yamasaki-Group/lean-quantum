/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.BlockDecomposition
import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerAlgebras

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 implementers

Carlen 2022 Theorem 1.45 (AH1): finite-dimensional C*-algebra
classification infrastructure stage for normalized inner implementers,
quadratic signs, and trace tests for matrix-block stars.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra
open scoped Topology
open Filter
open Matrix

section PositiveRayEndpointQuotientCFC

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    ContinuousFunctionalCalculus ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative bounded operators on `EuclideanSpace ℂ (Fin n)` have nonnegative real spectrum. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    NonnegSpectrumClass ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := inferInstance

/-! ### Phase normalization of inner implementers -/
/--
Scaling the matrix implementer by a nonzero scalar does not change the
transported involution represented by `M ↦ star (P * M * ⅟P)`.
-/
theorem matrixBlock_star_conj_unit_smul_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (P M : Matrix n n ℂ) [Invertible P] (c : ℂˣ) :
    letI : Invertible ((c : ℂ) • P) :=
      Classical.choice ((nonempty_invertible_iff_isUnit ((c : ℂ) • P)).mpr
        ((isUnit_smul_iff c P).mpr (isUnit_of_invertible P)))
    star (((c : ℂ) • P) * M * ⅟((c : ℂ) • P)) =
      star (P * M * ⅟P) := by
  classical
  letI : Invertible ((c : ℂ) • P) :=
    Classical.choice ((nonempty_invertible_iff_isUnit ((c : ℂ) • P)).mpr
      ((isUnit_smul_iff c P).mpr (isUnit_of_invertible P)))
  have hdet : IsUnit (star P).det := by
    exact (isUnit_of_invertible (star P)).map Matrix.detMonoidHom
  letI : Invertible (star (c : ℂ)) := invertibleOfNonzero (star_ne_zero.mpr c.ne_zero)
  have hinv :
      (star ((c : ℂ) • P))⁻¹ = ((star (c : ℂ))⁻¹ : ℂ) • (star P)⁻¹ := by
    simpa using (Matrix.inv_smul (A := star P) (star (c : ℂ)) hdet :
      ((star (c : ℂ)) • star P)⁻¹ = ((star (c : ℂ))⁻¹ : ℂ) • (star P)⁻¹)
  have hstar_inv :
      star (((c : ℂ) • P)⁻¹) =
        ((star (c : ℂ))⁻¹ : ℂ) • (star P)⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
      ← Matrix.star_eq_conjTranspose]
    exact hinv
  have hPstar_inv : star (P⁻¹) = (star P)⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
      ← Matrix.star_eq_conjTranspose]
  simp [hstar_inv, hPstar_inv]

/--
Existence packaging for scalar renormalization of the implementer.  If `P`
implements the transported involution, then every nonzero scalar multiple of
`P` implements the same transported involution.
-/
theorem matrixBlockTransportedStar_eq_star_conj_of_unit_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (c : ℂˣ) :
    ∃ _hPc : Invertible ((c : ℂ) • P),
      ∀ M : Matrix n n ℂ, τ M = star (((c : ℂ) • P) * M * ⅟((c : ℂ) • P)) := by
  classical
  let hPc : Invertible ((c : ℂ) • P) :=
    Classical.choice ((nonempty_invertible_iff_isUnit ((c : ℂ) • P)).mpr
      ((isUnit_smul_iff c P).mpr (isUnit_of_invertible P)))
  refine ⟨hPc, ?_⟩
  intro M
  letI : Invertible ((c : ℂ) • P) := hPc
  rw [hτ M]
  exact (matrixBlock_star_conj_unit_smul_eq P M c).symm

/--
If `(star P)⁻¹ P` is the scalar matrix `zI`, then `P = z • star P`.
This is the scalar-residue form used to choose a phase of the implementer.
-/
theorem matrixBlock_eq_smul_star_of_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) [Invertible P] {z : ℂ}
    (hz : ⅟(star P) * P = Matrix.scalar n z) :
    P = z • star P := by
  calc
    P = star P * (⅟(star P) * P) := by
      symm
      simp
    _ = star P * Matrix.scalar n z := by rw [hz]
    _ = z • star P := by
      rw [show Matrix.scalar n z = Matrix.diagonal (fun _ : n => z) by rfl]
      rw [← Matrix.smul_eq_mul_diagonal]

/--
In a nonzero matrix block, the scalar residue in
`(star P)⁻¹ P = zI` is nonzero.  This supplies the unit scalar needed before
choosing the phase that makes the implementer self-adjoint.
-/
theorem matrixBlock_scalar_ne_zero_of_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℂ) [Invertible P] {z : ℂ}
    (hz : ⅟(star P) * P = Matrix.scalar n z) :
    z ≠ 0 := by
  have hdet_ne : (Matrix.scalar n z).det ≠ 0 := by
    rw [← hz, Matrix.det_mul]
    exact mul_ne_zero
      (Matrix.det_ne_zero_of_right_inverse
        (A := ⅟(star P)) (B := star P) (invOf_mul_self (star P)))
      (Matrix.isUnit_det_of_invertible (A := P)).ne_zero
  have hdet_eq : (Matrix.scalar n z).det = z ^ Fintype.card n := by
    rw [show Matrix.scalar n z = Matrix.diagonal (fun _ : n => z) by rfl]
    simp [Matrix.det_diagonal]
  have hpow : z ^ Fintype.card n ≠ 0 := by
    simpa [hdet_eq] using hdet_ne
  exact (pow_ne_zero_iff Fintype.card_ne_zero).mp hpow

/--
The scalar residue in `(star P)⁻¹ P = zI` lies on the unit circle.  This is the
algebraic input for the later choice of a half-phase scalar.
-/
theorem matrixBlock_star_mul_scalar_eq_one_of_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℂ) [Invertible P] {z : ℂ}
    (hz : ⅟(star P) * P = Matrix.scalar n z) :
    star z * z = 1 := by
  classical
  have hP : P = z • star P :=
    matrixBlock_eq_smul_star_of_star_inv_mul_eq_scalar P hz
  have hstarP : star P = star z • P := by
    calc
      star P = star (z • star P) := by rw [← hP]
      _ = star z • P := by simp
  have hscaleP : (z * star z) • P = P := by
    calc
      (z * star z) • P = z • (star z • P) := by
        rw [smul_smul]
      _ = z • star P := by rw [hstarP]
      _ = P := hP.symm
  have hmat : Matrix.scalar n (z * star z) = 1 := by
    calc
      Matrix.scalar n (z * star z) = (z * star z) • (1 : Matrix n n ℂ) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.scalar, Matrix.diagonal]
        · simp [Matrix.scalar, Matrix.diagonal, hij]
      _ = (z * star z) • (P * ⅟P) := by simp
      _ = ((z * star z) • P) * ⅟P := by simp
      _ = P * ⅟P := by rw [hscaleP]
      _ = 1 := by simp
  let i : n := Classical.choice inferInstance
  have hentry := congr_fun (congr_fun hmat i) i
  have hzstar : z * star z = 1 := by
    simpa [Matrix.scalar, Matrix.diagonal, i] using hentry
  simpa [mul_comm] using hzstar

/--
Every unit-circle scalar admits a half-phase scalar in the form needed for
renormalizing the matrix implementer: from `star z * z = 1` one can choose a
nonzero `c` with `star c = c * z`.
-/
theorem exists_unit_phase_of_star_mul_scalar_eq_one
    {z : ℂ} (hz : star z * z = 1) :
    ∃ c : ℂˣ, star (c : ℂ) = (c : ℂ) * z := by
  classical
  have hz_ne : z ≠ 0 := by
    intro h
    simp [h] at hz
  rcases IsAlgClosed.exists_pow_nat_eq (k := ℂ) z (by norm_num : 0 < 2) with ⟨d, hd⟩
  have hd_ne : d ≠ 0 := by
    intro h
    apply hz_ne
    rw [← hd, h]
    simp
  have hnorm_d_sq : Complex.normSq d ^ 2 = 1 := by
    have hz_norm : Complex.normSq z = 1 := by
      have hcast : (Complex.normSq z : ℂ) = 1 := by
        simpa [Complex.normSq_eq_conj_mul_self] using hz
      exact_mod_cast hcast
    calc
      Complex.normSq d ^ 2 = Complex.normSq (d ^ 2) := by
        rw [pow_two, show d ^ 2 = d * d by rw [pow_two], Complex.normSq_mul]
      _ = Complex.normSq z := by rw [hd]
      _ = 1 := hz_norm
  have hnorm_d : Complex.normSq d = 1 := by
    have hnonneg : 0 ≤ Complex.normSq d := Complex.normSq_nonneg d
    nlinarith
  have hstar_mul_d : star d * d = 1 := by
    have hcast : (Complex.normSq d : ℂ) = 1 := by
      exact_mod_cast hnorm_d
    simpa [Complex.normSq_eq_conj_mul_self] using hcast
  let c : ℂˣ := Units.mk0 (star d) (star_ne_zero.mpr hd_ne)
  refine ⟨c, ?_⟩
  change star (star d) = star d * z
  rw [star_star, ← hd]
  calc
    d = (star d * d) * d := by rw [hstar_mul_d, one_mul]
    _ = star d * (d * d) := by ring
    _ = star d * d ^ 2 := by rw [pow_two]

/--
If the scalar residue is `zI` and a nonzero scalar `c` satisfies
`star c = c * z`, then the scalar-renormalized implementer `c • P` is
self-adjoint.
-/
theorem matrixBlock_unit_smul_isSelfAdjoint_of_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) [Invertible P] {z : ℂ}
    (hz : ⅟(star P) * P = Matrix.scalar n z)
    (c : ℂˣ) (hc : star (c : ℂ) = (c : ℂ) * z) :
    IsSelfAdjoint ((c : ℂ) • P) := by
  have hP : P = z • star P :=
    matrixBlock_eq_smul_star_of_star_inv_mul_eq_scalar P hz
  change star ((c : ℂ) • P) = (c : ℂ) • P
  calc
    star ((c : ℂ) • P) = star (c : ℂ) • star P := by
      simp
    _ = ((c : ℂ) * z) • star P := by rw [hc]
    _ = (c : ℂ) • (z • star P) := by
      simp [smul_smul]
    _ = (c : ℂ) • P := by rw [← hP]

/--
Existence packaging for phase-normalizing an implementer.  Under the scalar
residue equation and a scalar phase equation, the same transported involution
has a self-adjoint implementer.
-/
theorem matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_scalar_phase
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    {z : ℂ} (hz : ⅟(star P) * P = Matrix.scalar n z)
    (c : ℂˣ) (hc : star (c : ℂ) = (c : ℂ) * z) :
    ∃ P' : Matrix n n ℂ, ∃ _hP' : Invertible P',
      IsSelfAdjoint P' ∧
        ∀ M : Matrix n n ℂ, τ M = star (P' * M * ⅟P') := by
  rcases matrixBlockTransportedStar_eq_star_conj_of_unit_smul τ P hτ c with
    ⟨hPc, hτc⟩
  refine ⟨(c : ℂ) • P, hPc, ?_, hτc⟩
  exact matrixBlock_unit_smul_isSelfAdjoint_of_star_inv_mul_eq_scalar P hz c hc

/--
The scalar residue equation already supplies the phase-normalized
self-adjoint implementer in a nonzero matrix block.
-/
theorem matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    {z : ℂ} (hz : ⅟(star P) * P = Matrix.scalar n z) :
    ∃ P' : Matrix n n ℂ, ∃ _hP' : Invertible P',
      IsSelfAdjoint P' ∧
        ∀ M : Matrix n n ℂ, τ M = star (P' * M * ⅟P') := by
  have hunit :
      star z * z = 1 :=
    matrixBlock_star_mul_scalar_eq_one_of_star_inv_mul_eq_scalar P hz
  rcases exists_unit_phase_of_star_mul_scalar_eq_one hunit with ⟨c, hc⟩
  exact matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_scalar_phase
    τ P hτ hz c hc

/--
If a transported involution has the form `τ M = star (P * M * ⅟P)` and is
involutive, then the implementer satisfies the corresponding centrality
constraint: `(star P)⁻¹ P` commutes with every matrix.  This is the purely
algebraic residue of the condition `τ^2 = id`, and is one of the inputs for the
C*-positive/polar normalization (completed in `cornerCStarMatrixStarAlgEquiv`,
`CornerNormalization.lean`).
-/
theorem matrixBlockTransportedStar_involutive_star_inv_mul_central
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M)
    (M : Matrix n n ℂ) :
    (⅟(star P) * P) * M = M * (⅟(star P) * P) := by
  have hcalc :
      τ (τ M) = ⅟(star P) * P * M * ⅟P * star P := by
    rw [hτ (τ M), hτ M]
    rw [StarMul.star_mul, StarMul.star_mul, star_invOf, star_star]
    noncomm_ring
  have hmain :
      ⅟(star P) * P * M * ⅟P * star P = M := by
    exact hcalc.symm.trans (hinv M)
  calc
    (⅟(star P) * P) * M =
        (⅟(star P) * P) * M * ((⅟P * star P) * (⅟(star P) * P)) := by
      simp [mul_assoc]
    _ = (⅟(star P) * P * M * ⅟P * star P) * (⅟(star P) * P) := by
      noncomm_ring
    _ = M * (⅟(star P) * P) := by
      rw [hmain]

/--
A matrix that commutes with every matrix in the same full matrix block is a
scalar matrix.  This packages the Mathlib transvection criterion in the form
needed after the transported-involution centrality hook.
-/
theorem matrixBlock_mem_range_scalar_of_commutes_all
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ)
    (hC : ∀ M : Matrix n n ℂ, C * M = M * C) :
    C ∈ Set.range (Matrix.scalar n) := by
  exact Matrix.mem_range_scalar_of_commute_transvectionStruct (M := C) (by
    intro t
    change t.toMatrix * C = C * t.toMatrix
    exact (hC t.toMatrix).symm)

/--
If a transported involution has the form `τ M = star (P * M * ⅟P)` and is
involutive, then `(star P)⁻¹ P` is a scalar matrix.  This is the center-scalar
form of the pure algebraic residue of `τ^2 = id`.
-/
theorem matrixBlockTransportedStar_involutive_star_inv_mul_mem_range_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M) :
    ⅟(star P) * P ∈ Set.range (Matrix.scalar n) := by
  exact matrixBlock_mem_range_scalar_of_commutes_all
    (⅟(star P) * P)
    (matrixBlockTransportedStar_involutive_star_inv_mul_central τ P hτ hinv)

/--
Existential form of
`matrixBlockTransportedStar_involutive_star_inv_mul_mem_range_scalar`, with the
equality oriented as the matrix normalizer calculation uses it.
-/
theorem matrixBlockTransportedStar_involutive_star_inv_mul_eq_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M) :
    ∃ z : ℂ, ⅟(star P) * P = Matrix.scalar n z := by
  rcases matrixBlockTransportedStar_involutive_star_inv_mul_mem_range_scalar
      τ P hτ hinv with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

/--
For a nonzero full matrix block, an involutive transported star represented by
`M ↦ star (P M P⁻¹)` admits a self-adjoint implementer representing the same
transported star.
-/
theorem matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_involutive
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hinv : ∀ M : Matrix n n ℂ, τ (τ M) = M) :
    ∃ P' : Matrix n n ℂ, ∃ _hP' : Invertible P',
      IsSelfAdjoint P' ∧
        ∀ M : Matrix n n ℂ, τ M = star (P' * M * ⅟P') := by
  rcases matrixBlockTransportedStar_involutive_star_inv_mul_eq_scalar
      τ P hτ hinv with ⟨z, hz⟩
  exact matrixBlockTransportedStar_exists_selfAdjoint_implementer_of_star_inv_mul_eq_scalar
    τ P hτ hz

/--
Positive definite matrices admit an invertible square factor in the exact form
needed by the normalizer calculation: `A = star Q * Q`.
-/
theorem matrixBlock_exists_invertible_star_mul_self_of_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q, star Q * Q = A := by
  -- Take `Q = √D * Uᴴ` from the spectral decomposition `A = U * D * Uᴴ`; the eigenvalues are
  -- positive, so `√D` and hence `Q` are invertible.
  let Q : Matrix n n ℂ := Matrix.diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) *
    star (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  have hQunit : IsUnit Q := by
    refine IsUnit.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => ?_)) ?_
    · exact (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne').isUnit
    · rw [← Unitary.coe_star]
      exact Unitary.isUnit_coe
  have hQeq : star Q * Q = A := by
    conv_rhs => rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [Q, Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
      ← Matrix.star_eq_conjTranspose]
    congr 3
    funext i
    simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_pos i).le]
    rfl
  let hQ : Invertible Q :=
    Classical.choice ((nonempty_invertible_iff_isUnit Q).mpr hQunit)
  exact ⟨Q, hQ, hQeq⟩

/--
If a transported involution is represented as the standard adjoint after
conjugation by an invertible matrix `P`, and an invertible matrix `Q` supplies
the two factor identities expected from the positive-normalization step, then
conjugation by `Q` intertwines that transported involution with the standard
matrix adjoint.  This is the algebraic calculation needed after the
C*-positive/polar normalization supplies the factors (see
`cornerCStarMatrixStarAlgEquiv` in `CornerNormalization.lean`).
-/
theorem matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_factors
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P Q : Matrix n n ℂ) [Invertible P] [Invertible Q]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hleft : Q * star (⅟P) = star (⅟Q))
    (hright : star P * ⅟Q = star Q)
    (M : Matrix n n ℂ) :
    matrixBlockConjAlgEquivOfInvertible Q (τ M) =
      star (matrixBlockConjAlgEquivOfInvertible Q M) := by
  dsimp [matrixBlockConjAlgEquivOfInvertible]
  rw [hτ]
  calc
    Q * star (P * M * ⅟P) * ⅟Q =
        Q * (star (⅟P) * star M * star P) * ⅟Q := by
      rw [StarMul.star_mul, StarMul.star_mul]
      noncomm_ring
    _ = (Q * star (⅟P)) * star M * (star P * ⅟Q) := by noncomm_ring
    _ = star (⅟Q) * star M * star Q := by rw [hleft, hright]
    _ = star (Q * M * ⅟Q) := by
      rw [StarMul.star_mul, StarMul.star_mul]
      noncomm_ring

/--
The right factor identity required by
`matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_factors` follows
from the single square-root type normalization equation `star Q * Q = star P`.
-/
theorem matrixBlockConjAlgEquivOfInvertible_star_conj_right_factor_of_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) [Invertible P] [Invertible Q]
    (hQ : star Q * Q = star P) :
    star P * ⅟Q = star Q := by
  calc
    star P * ⅟Q = (star Q * Q) * ⅟Q := by rw [← hQ]
    _ = star Q := by simp [mul_assoc]

/--
The left factor identity required by
`matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_factors` follows
from the same square-root type normalization equation `star Q * Q = star P`.
-/
theorem matrixBlockConjAlgEquivOfInvertible_star_conj_left_factor_of_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) [Invertible P] [Invertible Q]
    (hQ : star Q * Q = star P) :
    Q * star (⅟P) = star (⅟Q) := by
  have hInvP : ⅟(star P) = ⅟Q * ⅟(star Q) := by
    apply invOf_eq_right_inv
    rw [← hQ]
    simp [mul_assoc]
  calc
    Q * star (⅟P) = Q * ⅟(star P) := by rw [star_invOf]
    _ = Q * (⅟Q * ⅟(star Q)) := by rw [hInvP]
    _ = ⅟(star Q) := by simp
    _ = star (⅟Q) := by rw [star_invOf]

/--
If the transported involution has the form `τ M = star (P * M * ⅟P)` and the
C*-normalization step has produced an invertible `Q` with
`star Q * Q = star P`, then conjugation by `Q` already gives the desired
normalizer.  Such a `Q` is obtained from a positive-definite `star P` by
`matrixBlock_exists_invertible_star_mul_self_of_posDef`; for the transported corner
involutions of a C*-algebra, `P` and `Q` are constructed in
`cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`).
-/
theorem matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P Q : Matrix n n ℂ) [Invertible P] [Invertible Q]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hQ : star Q * Q = star P)
    (M : Matrix n n ℂ) :
    matrixBlockConjAlgEquivOfInvertible Q (τ M) =
      star (matrixBlockConjAlgEquivOfInvertible Q M) := by
  exact matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_factors
    τ P Q hτ
    (matrixBlockConjAlgEquivOfInvertible_star_conj_left_factor_of_square P Q hQ)
    (matrixBlockConjAlgEquivOfInvertible_star_conj_right_factor_of_square P Q hQ)
    M

/--
Existence packaging for the matrix-block normalizer.  Once a
C*-positive/polar normalization supplies a square-root implementer `Q` with
`star Q * Q = star P`, conjugation by that `Q` is the desired algebra
automorphism intertwining the transported involution with the standard matrix
adjoint.
-/
theorem matrixBlockConjAlgEquivOfInvertible_exists_intertwiner_of_star_conj_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (P : Matrix n n ℂ) [Invertible P]
    (hτ : ∀ M : Matrix n n ℂ, τ M = star (P * M * ⅟P))
    (hQ : ∃ Q : Matrix n n ℂ, ∃ _hQ : Invertible Q, star Q * Q = star P) :
    ∃ β : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ,
      ∀ M : Matrix n n ℂ, β (τ M) = star (β M) := by
  rcases hQ with ⟨Q, hQinv, hQsq⟩
  letI : Invertible Q := hQinv
  refine ⟨matrixBlockConjAlgEquivOfInvertible Q, ?_⟩
  intro M
  exact matrixBlockConjAlgEquivOfInvertible_intertwines_of_star_conj_square
    τ P Q hτ hQsq M


/-! ### Quadratic sign and trace tests for implementers -/
/--
A self-adjoint matrix is semidefinite up to sign once its standard quadratic
forms all have one sign.  This is the pure matrix-order endpoint of a
C*-positive-cone argument: after that argument gives a consistent sign
for the quadratic forms of the self-adjoint implementer, the required
sign-semidefinite alternative follows immediately.
-/
theorem matrixBlock_selfAdjoint_signSemidef_of_quadratic_sign
    {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) (hself : IsSelfAdjoint P)
    (hquad :
      (∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (P *ᵥ v)) ∨
        (∀ v : n → ℂ, star v ⬝ᵥ (P *ᵥ v) ≤ 0)) :
    P.PosSemidef ∨ (-P).PosSemidef := by
  have hHerm : P.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact hself
  rcases hquad with hnonneg | hnonpos
  · exact Or.inl (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm hnonneg)
  · have hNegHerm : (-P).IsHermitian := by
      rw [Matrix.isHermitian_iff_isSelfAdjoint]
      change star (-P) = -P
      rw [star_neg, hself.star_eq]
    refine Or.inr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hNegHerm ?_)
    intro v
    have hv := hnonpos v
    have hrewrite : star v ⬝ᵥ ((-P) *ᵥ v) = -(star v ⬝ᵥ (P *ᵥ v)) := by
      rw [Matrix.neg_mulVec, dotProduct_neg]
    rw [hrewrite]
    exact neg_nonneg.mpr hv

private theorem complex_nonneg_of_mul_pos_nonneg {z c : ℂ}
    (hc : 0 < c) (h : 0 ≤ z * c) : 0 ≤ z := by
  rw [Complex.pos_iff] at hc
  have hcim : c.im = 0 := hc.2.symm
  rw [Complex.nonneg_iff] at h ⊢
  constructor
  · have hre : 0 ≤ z.re * c.re := by
      simpa [Complex.mul_re, hcim] using h.1
    exact nonneg_of_mul_nonneg_left hre hc.1
  · have him : z.im * c.re = 0 := by
      have hzero : (z * c).im = 0 := h.2.symm
      simpa [Complex.mul_im, hcim] using hzero
    exact ((mul_eq_zero.mp him).resolve_right (ne_of_gt hc.1)).symm

private theorem complex_nonpos_of_mul_pos_nonpos {z c : ℂ}
    (hc : 0 < c) (h : z * c ≤ 0) : z ≤ 0 := by
  rw [Complex.pos_iff] at hc
  have hcim : c.im = 0 := hc.2.symm
  rw [Complex.nonpos_iff] at h ⊢
  constructor
  · have hre : z.re * c.re ≤ 0 := by
      simpa [Complex.mul_re, hcim] using h.1
    exact nonpos_of_mul_nonpos_left hre hc.1
  · have him : z.im * c.re = 0 := by
      have hzero : (z * c).im = 0 := h.2
      simpa [Complex.mul_im, hcim] using hzero
    exact (mul_eq_zero.mp him).resolve_right (ne_of_gt hc.1)

private theorem complex_nonpos_of_mul_neg_nonneg {z c : ℂ}
    (hc : c < 0) (h : 0 ≤ z * c) : z ≤ 0 := by
  have hcpos : 0 < -c := neg_pos.mpr hc
  have hnonpos : z * (-c) ≤ 0 := by
    have hrewrite : z * (-c) = -(z * c) := by ring
    rw [hrewrite]
    exact neg_nonpos.mpr h
  exact complex_nonpos_of_mul_pos_nonpos hcpos hnonpos

private theorem complex_mul_nonneg_of_nonneg_of_pos {z c : ℂ}
    (hz : 0 ≤ z) (hc : 0 < c) : 0 ≤ z * c := by
  rw [Complex.nonneg_iff] at hz ⊢
  rw [Complex.pos_iff] at hc
  have hzim : z.im = 0 := hz.2.symm
  have hcim : c.im = 0 := hc.2.symm
  constructor
  · simpa [Complex.mul_re, hzim, hcim] using mul_nonneg hz.1 (le_of_lt hc.1)
  · simp [Complex.mul_im, hzim, hcim]

/--
If every quadratic form of a matrix has nonnegative product with one fixed
nonzero ordered complex scalar, then the quadratic forms all have one sign.
This is the rank-one scalar endpoint expected from the transported
C*-positive-cone computation.
-/
theorem matrixBlock_quadratic_sign_of_scalar_product_nonneg
    {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) {c : ℂ}
    (hc : 0 < c ∨ c < 0)
    (hprod : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (P *ᵥ v)) * c) :
    (∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (P *ᵥ v)) ∨
      (∀ v : n → ℂ, star v ⬝ᵥ (P *ᵥ v) ≤ 0) := by
  rcases hc with hcpos | hcneg
  · exact Or.inl fun v =>
      complex_nonneg_of_mul_pos_nonneg hcpos (hprod v)
  · exact Or.inr fun v =>
      complex_nonpos_of_mul_neg_nonneg hcneg (hprod v)

/--
Normalized rank-one scalar-product control is enough to recover the
unnormalized scalar-product provider.  This is the pure scaling bridge needed
after the unnormalized fixed-scalar linear-functional route is ruled out:
a C*-positive-cone argument may work on projective rank-one matrices, provided
the denominator `v^*v` is kept explicitly.  The normalization
`cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`) uses spectrum
nonnegativity of transported squares instead.
-/
theorem matrixBlock_scalarProductProvider_of_normalized_quadratic
    {n : Type*} [Fintype n]
    (Q : Matrix n n ℂ) {c : ℂ}
    (hc : 0 < c ∨ c < 0)
    (hnorm :
      ∀ v : n → ℂ, v ≠ 0 →
        0 ≤ ((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) :
    ∃ c : ℂ, (0 < c ∨ c < 0) ∧
      ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * c := by
  refine ⟨c, hc, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hdpos : 0 < star v ⬝ᵥ v :=
      (Matrix.dotProduct_star_self_pos_iff).mpr hv
    have hdne : star v ⬝ᵥ v ≠ 0 := ne_of_gt hdpos
    have hmul :
        0 ≤ (((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) *
            (star v ⬝ᵥ v) :=
      complex_mul_nonneg_of_nonneg_of_pos (hnorm v hv) hdpos
    have hrewrite :
        (((star v ⬝ᵥ (Q *ᵥ v)) / (star v ⬝ᵥ v)) * c) *
            (star v ⬝ᵥ v) =
          (star v ⬝ᵥ (Q *ᵥ v)) * c := by
      field_simp [hdne]
    simpa [hrewrite] using hmul

/--
Self-adjoint implementers are semidefinite up to sign once the transported
positive-cone calculation supplies a fixed nonzero scalar whose product with
every standard quadratic form is nonnegative.
-/
theorem matrixBlock_selfAdjoint_signSemidef_of_scalar_product_nonneg
    {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) (hself : IsSelfAdjoint P) {c : ℂ}
    (hc : 0 < c ∨ c < 0)
    (hprod : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (P *ᵥ v)) * c) :
    P.PosSemidef ∨ (-P).PosSemidef :=
  matrixBlock_selfAdjoint_signSemidef_of_quadratic_sign P hself
    (matrixBlock_quadratic_sign_of_scalar_product_nonneg P hc hprod)

/--
The scalar-product provider follows from a rank-one positive-functional
calculation.  On this route the C*-specific task is to construct such a
functional from the transported positive cone and prove the rank-one evaluation
formula; the normalization `cornerCStarMatrixStarAlgEquiv` (`CornerNormalization.lean`)
uses spectrum nonnegativity of transported squares instead.
-/
theorem matrixBlock_scalarProductProvider_of_rankOne_positiveFunctional
    {n : Type*} [Fintype n] [DecidableEq n]
    (τ : Matrix n n ℂ → Matrix n n ℂ)
    (Q : Matrix n n ℂ) [Invertible Q]
    (c : ℂ) (hc : 0 < c ∨ c < 0)
    (Λ : Matrix n n ℂ → ℂ)
    (hpos : ∀ R : Matrix n n ℂ, 0 ≤ Λ (τ R * R))
    (hrank :
      ∀ v : n → ℂ,
        Λ (τ (Matrix.vecMulVec v (star v)) * Matrix.vecMulVec v (star v)) =
          (star v ⬝ᵥ (Q *ᵥ v)) * c) :
    ∃ c : ℂ, (0 < c ∨ c < 0) ∧
      ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (Q *ᵥ v)) * c := by
  refine ⟨c, hc, ?_⟩
  intro v
  rw [← hrank v]
  exact hpos (Matrix.vecMulVec v (star v))


end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
