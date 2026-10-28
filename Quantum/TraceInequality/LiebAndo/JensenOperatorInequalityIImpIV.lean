/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.BlockDiagonal
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Quantum.TraceInequality.LownerHeinz.Reciprocal

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

-- Cached here once: repeating this search in every statement that mentions `CFC.sqrt`
-- on `(HSum ℋ →L[ℂ] HSum ℋ)` exceeds the default instance-search budget.
noncomputable local instance : Algebra ℝ (HSum ℋ →L[ℂ] HSum ℋ) := by infer_instance
noncomputable local instance : NormedSpace ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : Module ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance

-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
noncomputable local instance : NonnegSpectrumClass ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance

/-- Condition (iv) in Theorem 2.5.2.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2. -/
def JensenContractionCondition (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A X : (ℋ →L[ℂ] ℋ)⦄, IsSelfAdjoint A → spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → ‖X‖ ≤ 1 →
    cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X

/-- Condition (i) in Theorem 2.5.2 on the fixed Hilbert space `ℋ`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConvexNonposAtZero (f : ℝ → ℝ) : Prop :=
  OperatorConvex (ℋ := ℋ) f ∧ f 0 ≤ 0

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/--
Uniform version of Condition (i), packaged as `OperatorConvexAll` together with `f 0 ≤ 0`.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConvexAllNonposAtZero (f : ℝ → ℝ) : Prop :=
  OperatorConvexAll.{u} f ∧
    f 0 ≤ 0

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/--
Uniform localized version of Condition (i), packaged as
`OperatorConvexOnAll (Set.Ici 0)` together with continuity and `f 0 ≤ 0`.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.

This localized version requires standard operator convexity on the nonnegative half-line
(self-adjoint inputs with spectrum ⊆ [0,∞)) on all Hilbert spaces, together with continuity on the
same domain and f(0) ≤ 0. -/
def OperatorConvexIciAllContNonposAtZero (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f ∧
    ContinuousOn f (Set.Ici (0 : ℝ)) ∧
    f 0 ≤ 0

/-- Condition (v) in Theorem 2.5.2.

Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2. -/
def JensenContractiveColumnCondition (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B X Y : (ℋ →L[ℂ] ℋ)⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B ⊆ Set.Ici (0 : ℝ) →
    star X * X + star Y * Y ≤ (1 : (ℋ →L[ℂ] ℋ)) →
    cfcR (ℋ := ℋ) f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y

/-- Selfadjoint `2 × 2` block built from a contraction candidate `X`. -/
private noncomputable def blockSwap (X : (ℋ →L[ℂ] ℋ)) : (HSum ℋ →L[ℂ] HSum ℋ) :=
  blockOp (ℋ := ℋ) 0 (star X) X 0

omit [Nontrivial ℋ] in
private lemma blockSwap_star (X : (ℋ →L[ℂ] ℋ)) :
    star (blockSwap (ℋ := ℋ) X) = blockSwap (ℋ := ℋ) X := by
  simp [blockSwap, blockOp_star]

omit [Nontrivial ℋ] in
private lemma blockSwap_sq (X : (ℋ →L[ℂ] ℋ)) :
    blockSwap (ℋ := ℋ) X * blockSwap (ℋ := ℋ) X =
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
  ext z i
  fin_cases i <;>
    simp [blockSwap, blockOp, blockDiagonal, ContinuousLinearMap.mul_def] <;> abel

omit [Nontrivial ℋ] in
private lemma blockSwap_add_I_smul_blockDiagonal (X R0 R1 : (ℋ →L[ℂ] ℋ)) :
    blockSwap (ℋ := ℋ) X + Complex.I • blockDiagonal (ℋ := ℋ) R0 R1 =
      blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
  rw [blockDiagonal_eq_blockOp]
  ext z i
  fin_cases i <;> simp [blockSwap, blockOp] <;> abel

omit [Nontrivial ℋ] in
private lemma cfcR_zero (f : ℝ → ℝ) :
    cfcR (ℋ := ℋ) f (0 : (ℋ →L[ℂ] ℋ)) = algebraMap ℝ (ℋ →L[ℂ] ℋ) (f 0) := by
  change cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f (0 : (ℋ →L[ℂ] ℋ)) =
    algebraMap ℝ (ℋ →L[ℂ] ℋ) (f 0)
  simp

omit [Nontrivial ℋ] in
private lemma cfcR_conj_unitary_on (s : Set ℝ) (f : ℝ → ℝ) (hcont : ContinuousOn f s)
    {A : (ℋ →L[ℂ] ℋ)} (hAs : spectrum ℝ A ⊆ s)
    (u : unitary (ℋ →L[ℂ] ℋ)) (hA : IsSelfAdjoint A) :
    cfcR (ℋ := ℋ) f (star u * A * u) = star u * cfcR (ℋ := ℋ) f A * u := by
  let φ : (ℋ →L[ℂ] ℋ) →⋆ₐ[ℝ] (ℋ →L[ℂ] ℋ) := Unitary.conjStarAlgAut ℝ
      (ℋ →L[ℂ] ℋ) (star u)
  have hφ : Continuous φ := by
    have h1 : Continuous (fun x : (ℋ →L[ℂ] ℋ) => (star u : (ℋ →L[ℂ] ℋ)) * x *
        (u : (ℋ →L[ℂ] ℋ))) := by
      fun_prop
    have hEq : (fun x : (ℋ →L[ℂ] ℋ) => φ x) = (fun x : (ℋ →L[ℂ] ℋ) => (star u
        : (ℋ →L[ℂ] ℋ)) * x * (u : (ℋ →L[ℂ] ℋ))) := by
      funext x
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa [hEq] using h1
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hcont.mono hAs)
    (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hmap.symm

omit [Nontrivial ℋ] in
private lemma cfcR_real_sqrt_eq_sqrt {A : (ℋ →L[ℂ] ℋ)} (hA : (0 : (ℋ →L[ℂ] ℋ)) ≤ A) :
    cfcR (ℋ := ℋ) Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc (f := Real.sqrt) (a := A) (hf0 := by simp), cfcR]

-- `CFC.sqrt` on block-diagonal operators triggers expensive instance search through the product
-- map.
omit [Nontrivial ℋ] in
private lemma sqrt_blockDiagonal_of_nonneg
    {A B : (ℋ →L[ℂ] ℋ)} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hA_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ A) (hB_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ B) :
    CFC.sqrt (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (CFC.sqrt A) (CFC.sqrt B) := by
  letI : Algebra ℝ (HSum ℋ →L[ℂ] HSum ℋ) := by infer_instance
  have hdiag_nonneg : (0 : (HSum ℋ →L[ℂ] HSum ℋ)) ≤ blockDiagonal (ℋ := ℋ) A B :=
    blockDiagonal_nonneg (ℋ := ℋ) hA_nonneg hB_nonneg
  rw [← cfcR_real_sqrt_eq_sqrt (ℋ := HSum ℋ) hdiag_nonneg]
  rw [cfcR_blockDiagonal (ℋ := ℋ) (f := Real.sqrt) (A := A) (B := B) hA hB]
  · rw [← cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hA_nonneg, ← cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hB_nonneg]
  · simpa using
      (by cfc_cont_tac : ContinuousOn Real.sqrt (spectrum ℝ A ∪ spectrum ℝ B))

omit [Nontrivial ℋ] in
private lemma complex_I_smul_real_I_smul_invTwo (r : ℝ) (T : (ℋ →L[ℂ] ℋ)) :
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T =
      -((2⁻¹ : ℝ) * r) • T := by
  ext x
  have hcomm : r • (Complex.I • ((2⁻¹ : ℝ) • T x)) = Complex.I • (r • ((2⁻¹ : ℝ) • T x)) := by
    simpa using (smul_comm r (Complex.I : ℂ) ((2⁻¹ : ℝ) • T x))
  calc
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T x
        = Complex.I • (r • (Complex.I • ((2⁻¹ : ℝ) • T x))) := by
            rfl
    _ = Complex.I • (Complex.I • (r • ((2⁻¹ : ℝ) • T x))) := by
            rw [hcomm]
    _ = ((Complex.I : ℂ) * Complex.I) • (r • ((2⁻¹ : ℝ) • T x)) := by
            rw [smul_smul]
    _ = (-1 : ℂ) • (r • ((2⁻¹ : ℝ) • T x)) := by
            norm_num
    _ = (-1 : ℂ) • (((r * 2⁻¹ : ℝ)) • T x) := by
            rw [smul_smul]
    _ = -((2⁻¹ : ℝ) * r) • T x := by
            simp [neg_smul, mul_comm]

omit [Nontrivial ℋ] in
private lemma real_smul_complex_I_real_smul_complex_I_comm (s r : ℝ) (T : (ℋ →L[ℂ] ℋ)) :
    (s : ℝ) • Complex.I • r • Complex.I • T =
      Complex.I • r • Complex.I • (s : ℝ) • T := by
  calc
    (s : ℝ) • Complex.I • r • Complex.I • T
        = Complex.I • ((s : ℝ) • (r • (Complex.I • T))) := by
            simpa [smul_smul] using (smul_comm (s : ℝ) (Complex.I : ℂ) (r • (Complex.I • T)))
    _ = Complex.I • (r • ((s : ℝ) • (Complex.I • T))) := by
            rw [smul_comm (s : ℝ) r (Complex.I • T)]
    _ = Complex.I • (r • (Complex.I • ((s : ℝ) • T))) := by
            rw [smul_comm (s : ℝ) (Complex.I : ℂ) T]
    _ = Complex.I • r • Complex.I • (s : ℝ) • T := by
            rfl

omit [Nontrivial ℋ] in
private lemma half_add_half_eq (T : (ℋ →L[ℂ] ℋ)) :
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = T := by
  calc
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = (2⁻¹ + 2⁻¹ : ℝ) • T := by
      simp [add_smul]
    _ = (1 : ℝ) • T := by norm_num
    _ = T := by simp

omit [Nontrivial ℋ] in
private lemma half_mul_real_add_half_mul_real_eq (r : ℝ) (T : (ℋ →L[ℂ] ℋ)) :
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T = r • T := by
  calc
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T =
        (((2⁻¹ : ℝ) * r) + ((2⁻¹ : ℝ) * r)) • T := by
          simp [add_smul]
    _ = r • T := by ring_nf

omit [Nontrivial ℋ] in
private lemma rightEval_topLeft_scalar
    (r : ℝ) (R0 X T : (ℋ →L[ℂ] ℋ)) :
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)))) =
      star X * (T * X) + r • (R0 * R0) := by
  have hP :
      (2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X)) =
        star X * (T * X) := by
    simpa using half_add_half_eq (ℋ := ℋ) (star X * (T * X))
  have hQhalf :
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        r • (R0 * R0) := by
    have hterm :
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
          ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
      calc
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))
            = -(Complex.I • r • Complex.I • (2⁻¹ : ℝ) • (R0 * R0)) := by
                rw [real_smul_complex_I_real_smul_complex_I_comm
                  (ℋ := ℋ) (s := (2⁻¹ : ℝ)) (r := r) (T := R0 * R0)]
        _ = ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
            rw [complex_I_smul_real_I_smul_invTwo (ℋ := ℋ) (r := r) (T := R0 * R0)]
            simp
    calc
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        ((2⁻¹ : ℝ) * r) • (R0 * R0) + ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
          simp [hterm]
      _ = r • (R0 * R0) := half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (R0 * R0)
  calc
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))))
        =
      ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X))) +
        (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))) := by
            abel
    _ = star X * (T * X) + r • (R0 * R0) := by rw [hP, hQhalf]

omit [Nontrivial ℋ] in
private lemma rightEval_bottomRight_scalar
    (r : ℝ) (R1 X T : (ℋ →L[ℂ] ℋ)) :
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1)))) =
      (R1 * T * R1) + r • (X * star X) := by
  have hS :
      (2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X) = r • (X * star X) := by
    simpa using half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (X * star X)
  have hT :
      (2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1)) =
        R1 * (T * R1) := by
    simpa using half_add_half_eq (ℋ := ℋ) (R1 * (T * R1))
  calc
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1))))
        =
      ((2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X)) +
        ((2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1))) := by
            abel
    _ = r • (X * star X) + R1 * (T * R1) := by rw [hS, hT]
    _ = (R1 * T * R1) + r • (X * star X) := by simp [mul_assoc, add_comm]

private lemma star_mul_le_one (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    (star X * X : (ℋ →L[ℂ] ℋ)) ≤ 1 := by
  have h1 : star X * X ≤ algebraMap ℝ (ℋ →L[ℂ] ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

private lemma mul_star_le_one (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    (X * star X : (ℋ →L[ℂ] ℋ)) ≤ 1 := by
  have h1 : X * star X ≤ algebraMap ℝ (ℋ →L[ℂ] ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := star X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

-- `simp` and normalization over block expressions are expensive here.
private lemma blockSwap_norm_le_one (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    ‖blockSwap (ℋ := ℋ) X‖ ≤ 1 := by
  have hSstar : star (blockSwap (ℋ := ℋ) X) = blockSwap (ℋ := ℋ) X :=
    blockSwap_star (ℋ := ℋ) X
  have hSstarS :
      star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X =
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa only [hSstar] using blockSwap_sq (ℋ := ℋ) X
  have hDiagLe :
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤ (1 : (HSum ℋ →L[ℂ] HSum ℋ)) := by
    have hle := blockDiagonal_le_blockDiagonal (ℋ := ℋ)
      (star_mul_le_one (ℋ := ℋ) X hX) (mul_star_le_one (ℋ := ℋ) X hX)
    simpa only [blockDiagonal_one] using hle
  have hSstarSle :
      star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X ≤ (1 : (HSum ℋ →L[ℂ] HSum ℋ)) := by
    simpa only [hSstarS] using hDiagLe
  have hSstarSnonneg : 0 ≤ star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X :=
    star_mul_self_nonneg _
  have hnormSq : ‖star (blockSwap (ℋ := ℋ) X) * blockSwap (ℋ := ℋ) X‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hSstarSnonneg).2 hSstarSle
  have hnormSq' : ‖blockSwap (ℋ := ℋ) X‖ * ‖blockSwap (ℋ := ℋ) X‖ ≤ 1 :=
    (CStarRing.norm_star_mul_self (x := blockSwap (ℋ := ℋ) X)).symm.trans_le hnormSq
  have hsq : ‖blockSwap (ℋ := ℋ) X‖ ^ 2 ≤ 1 := by simpa [pow_two] using hnormSq'
  nlinarith [norm_nonneg (blockSwap (ℋ := ℋ) X)]

-- ### Auxiliary identities for Theorem 2.5.2 `(i) → (iv)`

-- Both implications rely on the same dilation argument: the contraction `X` is dilated
-- to the unitary `U = S + i√(1 - S²)` on `HSum ℋ` built from the selfadjoint swap block
-- `S = blockSwap X`, and the compression `X*AX` is recovered from the midpoint
-- `½ U*ÃU + ½ V*ÃV` with `V = U*` and `Ã = diag(0, A)`.  The heavy block-matrix
-- normalizations are isolated in the private lemmas below (over atomic operator
-- variables), so that each declaration stays within the default heartbeat budget.

omit [Nontrivial ℋ] in
/-- Conjugation by a selfadjoint operator preserves nonnegativity. -/
private lemma conj_selfAdjoint_nonneg {A R : (ℋ →L[ℂ] ℋ)} (hA0 : (0 : (ℋ →L[ℂ] ℋ)) ≤ A)
    (hR : IsSelfAdjoint R) : (0 : (ℋ →L[ℂ] ℋ)) ≤ R * A * R := by
  simpa [hR.star_eq, mul_assoc] using star_right_conjugate_nonneg hA0 R

omit [Nontrivial ℋ] in
/-- Perturbing by `r • R²` with `r ≤ 0` and `R` selfadjoint can only decrease an operator. -/
private lemma add_smul_sq_le_self {r : ℝ} (hr : r ≤ 0) {R : (ℋ →L[ℂ] ℋ)} (hR
    : IsSelfAdjoint R)
    (T : (ℋ →L[ℂ] ℋ)) : T + r • (R * R) ≤ T := by
  have hsq : (0 : (ℋ →L[ℂ] ℋ)) ≤ R * R := by
    simpa [hR.star_eq] using star_mul_self_nonneg R
  have hneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ (-r) • (R * R) := smul_nonneg (by linarith) hsq
  have hterm : r • (R * R) ≤ (0 : (ℋ →L[ℂ] ℋ)) := neg_nonneg.mp (by simpa
      [neg_smul] using hneg)
  calc T + r • (R * R) = r • (R * R) + T := by rw [add_comm]
    _ ≤ 0 + T := add_le_add_left hterm T
    _ = T := by rw [zero_add]

omit [Nontrivial ℋ] in
/-- `cfcR` of a block diagonal of nonnegative operators splits componentwise,
assuming continuity of `f` on `[0, ∞)`. -/
private lemma cfcR_blockDiagonal_of_nonneg {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    {A B : (ℋ →L[ℂ] ℋ)} (hA0 : (0 : (ℋ →L[ℂ] ℋ)) ≤ A) (hB0 : (0
        : (ℋ →L[ℂ] ℋ)) ≤ B) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) :=
  cfcR_blockDiagonal (ℋ := ℋ) f A B (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0)
    (continuousOn_union_of_subset_Ici hcont
      (spectrum_Ici_of_nonneg (ℋ := ℋ) hA0) (spectrum_Ici_of_nonneg (ℋ := ℋ) hB0))

/-- Defect operator `√(1 - X*X)` of a contraction candidate `X`. -/
private noncomputable def defectL (X : (ℋ →L[ℂ] ℋ)) : (ℋ →L[ℂ] ℋ) :=
  CFC.sqrt (1 - star X * X)

/-- Defect operator `√(1 - XX*)` of a contraction candidate `X`. -/
private noncomputable def defectR (X : (ℋ →L[ℂ] ℋ)) : (ℋ →L[ℂ] ℋ) :=
  CFC.sqrt (1 - X * star X)

omit [Nontrivial ℋ] in
/-- The left defect operator is selfadjoint. -/
private lemma defectL_isSelfAdjoint (X : (ℋ →L[ℂ] ℋ)) : IsSelfAdjoint (defectL (ℋ := ℋ) X) :=
  (CFC.sqrt_nonneg (1 - star X * X)).isSelfAdjoint

omit [Nontrivial ℋ] in
/-- The right defect operator is selfadjoint. -/
private lemma defectR_isSelfAdjoint (X : (ℋ →L[ℂ] ℋ)) : IsSelfAdjoint (defectR (ℋ := ℋ) X) :=
  (CFC.sqrt_nonneg (1 - X * star X)).isSelfAdjoint

omit [Nontrivial ℋ] in
/-- `1 - S²` for the swap block is the block diagonal of the defect squares. -/
private lemma one_sub_blockSwap_sq (X : (ℋ →L[ℂ] ℋ)) :
    1 - blockSwap (ℋ := ℋ) X ^ 2 =
      blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) := by
  have hSsq : blockSwap (ℋ := ℋ) X ^ 2 =
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [pow_two] using blockSwap_sq (ℋ := ℋ) X
  rw [hSsq]
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp [sub_eq_add_neg, add_comm]
  · intro z
    simp [sub_eq_add_neg, add_comm]

/-- `√(1 - S²)` for the swap block is the block diagonal of the defect operators. -/
private lemma sqrt_one_sub_blockSwap_sq (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    CFC.sqrt (1 - blockSwap (ℋ := ℋ) X ^ 2) =
      blockDiagonal (ℋ := ℋ) (defectL (ℋ := ℋ) X) (defectR (ℋ := ℋ) X) := by
  have hR0nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ 1 - star X * X :=
    sub_nonneg.mpr (star_mul_le_one (ℋ := ℋ) X hX)
  have hR1nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ 1 - X * star X :=
    sub_nonneg.mpr (mul_star_le_one (ℋ := ℋ) X hX)
  have hR0sa : IsSelfAdjoint (1 - star X * X) := by
    change star (1 - star X * X) = 1 - star X * X
    simp
  have hR1sa : IsSelfAdjoint (1 - X * star X) := by
    change star (1 - X * star X) = 1 - X * star X
    simp
  rw [one_sub_blockSwap_sq (ℋ := ℋ) X]
  exact sqrt_blockDiagonal_of_nonneg (ℋ := ℋ) hR0sa hR1sa hR0nonneg hR1nonneg

/-- The swap-block dilation `S + i√(1 - S²)` of a contraction is unitary. -/
private lemma blockSwap_dilation_mem_unitary (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    blockSwap (ℋ := ℋ) X + Complex.I • CFC.sqrt (1 - blockSwap (ℋ := ℋ) X ^ 2) ∈
      unitary (HSum ℋ →L[ℂ] HSum ℋ) := by
  have hSsa : IsSelfAdjoint (blockSwap (ℋ := ℋ) X) := by
    change star (blockSwap (ℋ := ℋ) X) = blockSwap (ℋ := ℋ) X
    exact blockSwap_star (ℋ := ℋ) X
  exact IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ hSsa
    (blockSwap_norm_le_one (ℋ := ℋ) X hX)

/-- The dilation unitary associated with a contraction candidate `X`. -/
private noncomputable def dilationUnitary (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) : unitary
    (HSum ℋ →L[ℂ] HSum ℋ) :=
  ⟨blockSwap (ℋ := ℋ) X + Complex.I • CFC.sqrt (1 - blockSwap (ℋ := ℋ) X ^ 2),
    blockSwap_dilation_mem_unitary (ℋ := ℋ) X hX⟩

/-- The dilation unitary as an explicit corner block operator. -/
private lemma dilationUnitary_coe (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    (dilationUnitary (ℋ := ℋ) X hX : (HSum ℋ →L[ℂ] HSum ℋ)) =
      blockOp (ℋ := ℋ) (Complex.I • defectL (ℋ := ℋ) X) (star X) X
        (Complex.I • defectR (ℋ := ℋ) X) := by
  change blockSwap (ℋ := ℋ) X + Complex.I • CFC.sqrt (1 - blockSwap (ℋ := ℋ) X ^ 2) = _
  rw [sqrt_one_sub_blockSwap_sq (ℋ := ℋ) X hX]
  exact blockSwap_add_I_smul_blockDiagonal (ℋ := ℋ) X (defectL (ℋ := ℋ) X)
    (defectR (ℋ := ℋ) X)

omit [Nontrivial ℋ] in
/-- Star of the corner block operator with `i`-scaled selfadjoint diagonal corners. -/
private lemma star_corner_blockOp (X : (ℋ →L[ℂ] ℋ)) {R0 R1 : (ℋ →L[ℂ] ℋ)} (hR0
    : IsSelfAdjoint R0)
    (hR1 : IsSelfAdjoint R1) :
    star (blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1)) =
      blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1) := by
  ext z i
  fin_cases i <;>
    simp [blockOp_star, hR0.star_eq, hR1.star_eq]

/-- The star of the dilation unitary as a corner block operator. -/
private lemma dilationUnitary_star_coe (X : (ℋ →L[ℂ] ℋ)) (hX : ‖X‖ ≤ 1) :
    (star (dilationUnitary (ℋ := ℋ) X hX) : (HSum ℋ →L[ℂ] HSum ℋ)) =
      blockOp (ℋ := ℋ) (-Complex.I • defectL (ℋ := ℋ) X) (star X) X
        (-Complex.I • defectR (ℋ := ℋ) X) := by
  rw [dilationUnitary_coe (ℋ := ℋ) X hX]
  exact star_corner_blockOp (ℋ := ℋ) X (defectL_isSelfAdjoint (ℋ := ℋ) X)
    (defectR_isSelfAdjoint (ℋ := ℋ) X)

omit [Nontrivial ℋ] in
/-- Averaging the two sign-conjugations of `diag(0, A)` by the corner blocks compresses to
the block diagonal of `X*AX` and `R₁AR₁`. -/
private lemma half_conj_add_half_conj_blockDiagonal_zero (X A R0 R1 : (ℋ →L[ℂ] ℋ)) :
    (1 / 2 : ℝ) • (blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1) *
          blockDiagonal (ℋ := ℋ) 0 A *
          blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1)) +
        (1 / 2 : ℝ) • (blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) *
          blockDiagonal (ℋ := ℋ) 0 A *
          blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1)) =
      blockDiagonal (ℋ := ℋ) (star X * A * X) (R1 * A * R1) := by
  rw [blockOp_mul_blockDiagonal_zero_right, blockOp_mul_blockDiagonal_zero_right]
  rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
  congr 1
  · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
    calc
      (1 / 2 : ℝ) • (star X * A * X) + (1 / 2 : ℝ) • (star X * A * X)
          = (2⁻¹ + 2⁻¹ : ℝ) • (star X * (A * X)) := by
              simp [add_smul, mul_assoc]
      _ = (1 : ℝ) • (star X * (A * X)) := by rw [hhalf]
      _ = star X * (A * X) := by simp
      _ = star X * A * X := by simp [mul_assoc]
  · simp [mul_assoc]
  · simp [mul_assoc]
  · have hhalf : (2⁻¹ + 2⁻¹ : ℝ) = (1 : ℝ) := by norm_num
    calc
      (1 / 2 : ℝ) • (-Complex.I • R1 * A * (Complex.I • R1)) +
          (1 / 2 : ℝ) • (Complex.I • R1 * A * (-Complex.I • R1))
          = (2⁻¹ + 2⁻¹ : ℝ) • (R1 * (A * R1)) := by
              simp [Complex.I_mul_I, smul_smul, add_smul, mul_assoc]
      _ = (1 : ℝ) • (R1 * (A * R1)) := by rw [hhalf]
      _ = R1 * A * R1 := by simp [mul_assoc]

omit [Nontrivial ℋ] in
/-- Top-left entry of the averaged sign-conjugation of `diag(r·1, T)`. -/
private lemma half_conj_scalar_topLeft (r : ℝ) (X T : (ℋ →L[ℂ] ℋ)) {R0 : (ℋ →L[ℂ] ℋ)}
    (hR0 : IsSelfAdjoint R0) :
    (1 / 2 : ℝ) • (star (Complex.I • R0) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r *
        (Complex.I • R0) + 0 * X) +
          star X * (0 * (Complex.I • R0) + T * X)) +
      (1 / 2 : ℝ) • (star (-Complex.I • R0) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r *
          (-Complex.I • R0) + 0 * X) +
          star X * (0 * (-Complex.I • R0) + T * X)) =
      star X * (T * X) + r • (R0 * R0) := by
  have hTopLeft :
      (2⁻¹ : ℝ) • (star X * (T * X)) +
          ((2⁻¹ : ℝ) • (star X * (T * X)) +
            (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
              -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)))) =
        star X * (T * X) + r • (R0 * R0) := by
    simpa using
      rightEval_topLeft_scalar (ℋ := ℋ) (r := r) (R0 := R0) (X := X) (T := T)
  simpa [hR0.star_eq, Algebra.algebraMap_eq_smul_one, mul_assoc,
    add_assoc, add_left_comm, add_comm] using hTopLeft

omit [Nontrivial ℋ] in
/-- Top-right entry of the averaged sign-conjugation of `diag(r·1, T)` vanishes. -/
private lemma half_conj_scalar_topRight (r : ℝ) (X T R0 R1 : (ℋ →L[ℂ] ℋ)) :
    (1 / 2 : ℝ) • (star (Complex.I • R0) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * star X +
            0 * (Complex.I • R1)) +
          star X * (0 * star X + T * (Complex.I • R1))) +
      (1 / 2 : ℝ) • (star (-Complex.I • R0) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * star X +
            0 * (-Complex.I • R1)) +
          star X * (0 * star X + T * (-Complex.I • R1))) = 0 := by
  simp [Algebra.algebraMap_eq_smul_one]
  abel

omit [Nontrivial ℋ] in
/-- Bottom-left entry of the averaged sign-conjugation of `diag(r·1, T)` vanishes. -/
private lemma half_conj_scalar_bottomLeft (r : ℝ) (X T R0 R1 : (ℋ →L[ℂ] ℋ)) :
    (1 / 2 : ℝ) • (star (star X) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * (Complex.I • R0) + 0 * X) +
          star (Complex.I • R1) * (0 * (Complex.I • R0) + T * X)) +
      (1 / 2 : ℝ) • (star (star X) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * (-Complex.I • R0)
          + 0 * X) +
          star (-Complex.I • R1) * (0 * (-Complex.I • R0) + T * X)) = 0 := by
  simp [Algebra.algebraMap_eq_smul_one]
  abel

omit [Nontrivial ℋ] in
/-- Bottom-right entry of the averaged sign-conjugation of `diag(r·1, T)`. -/
private lemma half_conj_scalar_bottomRight (r : ℝ) (X T : (ℋ →L[ℂ] ℋ)) {R1
    : (ℋ →L[ℂ] ℋ)}
    (hR1 : IsSelfAdjoint R1) :
    (1 / 2 : ℝ) • (star (star X) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * star X + 0 *
        (Complex.I • R1)) +
          star (Complex.I • R1) * (0 * star X + T * (Complex.I • R1))) +
      (1 / 2 : ℝ) • (star (star X) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r * star X + 0 *
          (-Complex.I • R1)) +
          star (-Complex.I • R1) * (0 * star X + T * (-Complex.I • R1))) =
      R1 * (T * R1) + r • (X * star X) := by
  have hBottomRight :
      (2⁻¹ * r) • (X * star X) +
          ((2⁻¹ * r) • (X * star X) +
            ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
              (2⁻¹ : ℝ) • (R1 * (T * R1)))) =
        (R1 * T * R1) + r • (X * star X) := by
    simpa [mul_assoc] using
      rightEval_bottomRight_scalar (ℋ := ℋ) (r := r) (R1 := R1) (X := X) (T := T)
  simpa [hR1.star_eq, Algebra.algebraMap_eq_smul_one, Complex.I_mul_I, smul_smul,
    mul_assoc, add_assoc, add_left_comm, add_comm] using hBottomRight

omit [Nontrivial ℋ] in
/-- Averaging the two sign-conjugations of `diag(r·1, T)` by the corner blocks compresses to
the block diagonal of `X*TX + r·R₀²` and `R₁TR₁ + r·XX*`. -/
private lemma half_conj_add_half_conj_blockDiagonal_scalar
    (r : ℝ) (X T : (ℋ →L[ℂ] ℋ)) {R0 R1 : (ℋ →L[ℂ] ℋ)} (hR0 : IsSelfAdjoint
        R0) (hR1 : IsSelfAdjoint R1) :
    (1 / 2 : ℝ) • (star (blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1)) *
          blockDiagonal (ℋ := ℋ) (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) T *
          blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1)) +
        (1 / 2 : ℝ) • (star (blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1)) *
          blockDiagonal (ℋ := ℋ) (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) T *
          blockOp (ℋ := ℋ) (-Complex.I • R0) (star X) X (-Complex.I • R1)) =
      blockDiagonal (ℋ := ℋ) (star X * T * X + r • (R0 * R0)) (R1 * T * R1 + r • (X * star X)) := by
  rw [blockDiagonal_eq_blockOp (ℋ := ℋ) (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) T]
  rw [blockOp_star, blockOp_star]
  simp_rw [mul_assoc]
  rw [blockOp_mul, blockOp_mul, blockOp_mul, blockOp_mul]
  rw [blockOp_smulR, blockOp_smulR, blockOp_add, blockDiagonal_eq_blockOp]
  congr 1
  · exact half_conj_scalar_topLeft (ℋ := ℋ) r X T hR0
  · exact half_conj_scalar_topRight (ℋ := ℋ) r X T R0 R1
  · exact half_conj_scalar_bottomLeft (ℋ := ℋ) r X T R0 R1
  · exact half_conj_scalar_bottomRight (ℋ := ℋ) r X T hR1

/-- Core dilation argument for Theorem 2.5.2 `(i) → (iv)`: compression by a contraction is
controlled by the midpoint operator convexity inequality on the doubled space `HSum ℋ`. -/
lemma cfcR_compression_le_of_midpoint {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) (hf0 : f 0 ≤ 0)
    (hmid : ∀ B₁ B₂ : (HSum ℋ →L[ℂ] HSum ℋ), IsSelfAdjoint B₁ → IsSelfAdjoint B₂ →
      spectrum ℝ B₁ ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B₂ ⊆ Set.Ici (0 : ℝ) →
      cfcR (ℋ := HSum ℋ) f ((1 / 2 : ℝ) • B₁ + (1 / 2 : ℝ) • B₂) ≤
        (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f B₁ + (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f B₂)
    {A X : (ℋ →L[ℂ] ℋ)} (hA : IsSelfAdjoint A) (hAs : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hX : ‖X‖ ≤ 1) :
    cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X := by
  have hA0 : (0 : (ℋ →L[ℂ] ℋ)) ≤ A :=
    LownerHeinzCore.nonneg_of_spectrum_subset_Ici (𝓐 := (ℋ →L[ℂ] ℋ)) hA hAs
  letI : Nontrivial (HSum ℋ →L[ℂ] HSum ℋ) := nontrivial_hsumL (ℋ := ℋ)
  let U : unitary (HSum ℋ →L[ℂ] HSum ℋ) := dilationUnitary (ℋ := ℋ) X hX
  let V : unitary (HSum ℋ →L[ℂ] HSum ℋ) := star U
  let Atilde : (HSum ℋ →L[ℂ] HSum ℋ) := blockDiagonal (ℋ := ℋ) 0 A
  have hR0self : IsSelfAdjoint (defectL (ℋ := ℋ) X) := defectL_isSelfAdjoint (ℋ := ℋ) X
  have hR1self : IsSelfAdjoint (defectR (ℋ := ℋ) X) := defectR_isSelfAdjoint (ℋ := ℋ) X
  have hU_block : (U : (HSum ℋ →L[ℂ] HSum ℋ)) =
      blockOp (ℋ := ℋ) (Complex.I • defectL (ℋ := ℋ) X) (star X) X
        (Complex.I • defectR (ℋ := ℋ) X) := dilationUnitary_coe (ℋ := ℋ) X hX
  have hV_block : (V : (HSum ℋ →L[ℂ] HSum ℋ)) =
      blockOp (ℋ := ℋ) (-Complex.I • defectL (ℋ := ℋ) X) (star X) X
        (-Complex.I • defectR (ℋ := ℋ) X) := dilationUnitary_star_coe (ℋ := ℋ) X hX
  have hAtilde0 : (0 : (HSum ℋ →L[ℂ] HSum ℋ)) ≤ Atilde := blockDiagonal_nonneg (ℋ :=
      ℋ) le_rfl hA0
  have hAtilde_sa : IsSelfAdjoint Atilde := IsSelfAdjoint.of_nonneg hAtilde0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hAtilde0
  have hB1_nonneg : (0 : (HSum ℋ →L[ℂ] HSum ℋ)) ≤ (star U : (HSum ℋ →L[ℂ] HSum ℋ))
      * Atilde * (U : (HSum ℋ →L[ℂ] HSum ℋ)) :=
    star_left_conjugate_nonneg hAtilde0 (U : (HSum ℋ →L[ℂ] HSum ℋ))
  have hB2_nonneg : (0 : (HSum ℋ →L[ℂ] HSum ℋ)) ≤ (star V : (HSum ℋ →L[ℂ] HSum ℋ))
      * Atilde * (V : (HSum ℋ →L[ℂ] HSum ℋ)) :=
    star_left_conjugate_nonneg hAtilde0 (V : (HSum ℋ →L[ℂ] HSum ℋ))
  have hmid_conv := hmid _ _ (IsSelfAdjoint.of_nonneg hB1_nonneg)
    (IsSelfAdjoint.of_nonneg hB2_nonneg)
    (spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB1_nonneg)
    (spectrum_Ici_of_nonneg (ℋ := HSum ℋ) hB2_nonneg)
  have hmid_block :
      (1 / 2 : ℝ) • ((star U : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (U : (HSum ℋ →L[ℂ] HSum ℋ))) +
          (1 / 2 : ℝ) • ((star V : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (V : (HSum ℋ →L[ℂ] HSum ℋ))) =
        blockDiagonal (ℋ := ℋ) (star X * A * X)
          (defectR (ℋ := ℋ) X * A * defectR (ℋ := ℋ) X) := by
    rw [show (star U : (HSum ℋ →L[ℂ] HSum ℋ)) = (V : (HSum ℋ →L[ℂ] HSum ℋ)) from rfl,
      show (star V : (HSum ℋ →L[ℂ] HSum ℋ)) = (U : (HSum ℋ →L[ℂ] HSum ℋ)) by simp [V],
      hU_block, hV_block,
      show Atilde = blockDiagonal (ℋ := ℋ) 0 A from rfl]
    exact half_conj_add_half_conj_blockDiagonal_zero (ℋ := ℋ) X A
      (defectL (ℋ := ℋ) X) (defectR (ℋ := ℋ) X)
  have hUcfc :
      cfcR (ℋ := HSum ℋ) f
          ((star U : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (U : (HSum ℋ →L[ℂ] HSum ℋ))) =
        (star U : (HSum ℋ →L[ℂ] HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde *
          (U : (HSum ℋ →L[ℂ] HSum ℋ)) := by
    simpa [mul_assoc] using
      cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcont
        hAtilde_spec U hAtilde_sa
  have hVcfc :
      cfcR (ℋ := HSum ℋ) f
          ((star V : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (V : (HSum ℋ →L[ℂ] HSum ℋ))) =
        (star V : (HSum ℋ →L[ℂ] HSum ℋ)) * cfcR (ℋ := HSum ℋ) f Atilde *
          (V : (HSum ℋ →L[ℂ] HSum ℋ)) := by
    simpa [mul_assoc] using
      cfcR_conj_unitary_on (ℋ := HSum ℋ) (s := Set.Ici (0 : ℝ)) (f := f) hcont
        hAtilde_spec V hAtilde_sa
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f 0) (cfcR (ℋ := ℋ) f A) :=
    cfcR_blockDiagonal_of_nonneg (ℋ := ℋ) hcont le_rfl hA0
  have hXAX_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ star X * A * X := star_left_conjugate_nonneg hA0 X
  have hR1AR1_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ defectR (ℋ := ℋ) X * A * defectR (ℋ := ℋ) X :=
    conj_selfAdjoint_nonneg (ℋ := ℋ) hA0 hR1self
  have hLeftEval :
      cfcR (ℋ := HSum ℋ) f
          ((1 / 2 : ℝ) •
              ((star U : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (U : (HSum ℋ →L[ℂ] HSum ℋ))) +
            (1 / 2 : ℝ) •
              ((star V : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde * (V : (HSum ℋ →L[ℂ] HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f (star X * A * X))
          (cfcR (ℋ := ℋ) f (defectR (ℋ := ℋ) X * A * defectR (ℋ := ℋ) X)) := by
    rw [hmid_block]
    exact cfcR_blockDiagonal_of_nonneg (ℋ := ℋ) hcont hXAX_nonneg hR1AR1_nonneg
  have hRightEval :
      ((1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star U : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde *
          (U : (HSum ℋ →L[ℂ] HSum ℋ))) +
        (1 / 2 : ℝ) • cfcR (ℋ := HSum ℋ) f ((star V : (HSum ℋ →L[ℂ] HSum ℋ)) * Atilde *
            (V : (HSum ℋ →L[ℂ] HSum ℋ)))) =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X +
            (f 0) • (defectL (ℋ := ℋ) X * defectL (ℋ := ℋ) X))
          ((defectR (ℋ := ℋ) X * cfcR (ℋ := ℋ) f A * defectR (ℋ := ℋ) X) +
            (f 0) • (X * star X)) := by
    rw [hUcfc, hVcfc, hAtilde_cfc, cfcR_zero, hU_block, hV_block]
    exact half_conj_add_half_conj_blockDiagonal_scalar (ℋ := ℋ) (f 0) X (cfcR (ℋ := ℋ) f A)
      hR0self hR1self
  rw [hLeftEval, hRightEval] at hmid_conv
  have htop :
      cfcR (ℋ := ℋ) f (star X * A * X) ≤
        star X * cfcR (ℋ := ℋ) f A * X +
          (f 0) • (defectL (ℋ := ℋ) X * defectL (ℋ := ℋ) X) :=
    blockDiagonal_le_left (ℋ := ℋ) hmid_conv
  exact htop.trans (add_smul_sq_le_self (ℋ := ℋ) hf0 hR0self _)

--Theorem 2.5.2 `(i) → (iv)`.

/--
Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.
-/
theorem jensenContraction_of_opConvexIciAll {f : ℝ → ℝ}
    (hf : OperatorConvexIciAllContNonposAtZero.{u} f) :
    JensenContractionCondition (ℋ := ℋ) f := by
  rcases hf with ⟨hconvAll, hcontIci, hf0⟩
  intro A X hA hAs hX
  letI : Nontrivial (HSum ℋ →L[ℂ] HSum ℋ) := nontrivial_hsumL (ℋ := ℋ)
  have hconv₂ : OperatorConvexOn (ℋ := HSum ℋ) (Set.Ici (0 : ℝ)) f :=
    hconvAll (K := HSum ℋ)
  refine cfcR_compression_le_of_midpoint (ℋ := ℋ) hcontIci hf0 ?_ hA hAs hX
  intro B₁ B₂ hB₁ hB₂ hs₁ hs₂
  have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
  simpa [hhalf] using
    (hconv₂ (A := B₁) (B := B₂) (t := (1 / 2 : ℝ)) hB₁ hB₂ (by positivity) (by norm_num)
      hs₁ hs₂)

end Theorem252

end JensenOperatorInequality
