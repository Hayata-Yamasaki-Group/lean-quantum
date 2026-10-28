/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Positive and invertible J-operator core

This file proves the basic positivity and strict-invertibility properties of
the Hiai-Petz operator `J_f(A,B)`. The proofs reduce `J_f(A,B)` to functional
calculus of the positive Hilbert-Schmidt operator `L_A R_{B^{-1}}` and use
commutation with right multiplication to build the explicit inverse model.

## Main results

* `jArg_isSelfAdjoint` and `jArg_nonneg`: self-adjointness and positivity of
  `L_A R_{B^{-1}}`.
* `jOperator_mul_jOperatorInv_of_posDef` and
  `jOperatorInv_mul_jOperator_of_posDef`: the strict positive-definite inverse
  identities for `J_f(A,B)`.
* `jOperator_nonneg`, `jOperatorInv_nonneg`, `jOperator_strict_pos`, and
  `jOperatorInv_strict_pos`: positivity and strict positivity of `J_f(A,B)` and
  its inverse model.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, Definition 6.1 and Theorem 6.2 setup.
-/

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section MatrixScopedInstances

variable {n m : ℕ}

private theorem jArg_isUnit {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jArg A B) := by
  have hLeft : IsUnit (leftMul A) :=
    leftMul_isUnit_of_isUnit (n := n) (Matrix.PosDef.isUnit hA)
  have hRight : IsUnit (rightMul (B⁻¹)) := by
    rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
    simpa using rightMul_isUnit_of_isUnit (n := n) ((u⁻¹).isUnit)
  simpa [jArg] using hRight.mul hLeft

private theorem jArg_isStrictlyPositive {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsStrictlyPositive (jArg A B) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact (jArg_isUnit hA hB).isStrictlyPositive
    (jArg_nonneg (A := A) (B := B) (Matrix.PosDef.nonneg hA) hB)

private theorem spectrum_jArg_subset_Ioi {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact jArg_isStrictlyPositive hA hB |>.spectrum_pos hx

@[fun_prop] private theorem continuousOn_inv_of_pos_jArg
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (jArg A B)) := by
  have hInvIoi : ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.inv₀ hf ?_
    intro x hx
    exact (hpos x hx).ne'
  exact hInvIoi.mono (spectrum_jArg_subset_Ioi hA hB)

private theorem cfc_jArg_mul_cfc_inv_of_posDef
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    hsCfcR f (jArg A B) *
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) =
      (1 : HSOp n) := by
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa using jArg_isSelfAdjoint hA.1 hB
  have hcont_f : ContinuousOn f (spectrum ℝ (jArg A B)) := by
    exact hf.mono (spectrum_jArg_subset_Ioi hA hB)
  have hcont_inv : ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (jArg A B)) :=
    continuousOn_inv_of_pos_jArg hf hpos hA hB
  calc
    hsCfcR f (jArg A B) *
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)
      = hsCfcR (fun x : ℝ ↦ f x * (f x)⁻¹) (jArg A B) := by
          dsimp [hsCfcR, HansenPedersen.cfcR]
          rw [← cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (f := f) (g := fun x : ℝ ↦ (f x)⁻¹) (a := jArg A B) hcont_f hcont_inv]
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) (jArg A B) := by
          apply cfc_congr
          intro x hx
          have hxne : f x ≠ 0 := (hpos x (spectrum_jArg_subset_Ioi hA hB hx)).ne'
          simp [hxne]
    _ = (1 : HSOp n) := by
          dsimp [hsCfcR, HansenPedersen.cfcR]
          simpa using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B)
              (ha := hjArg_sa))

private theorem cfc_inv_jArg_mul_cfc_of_posDef
    {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
        hsCfcR f (jArg A B) =
      (1 : HSOp n) := by
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa using jArg_isSelfAdjoint hA.1 hB
  have hcont_f : ContinuousOn f (spectrum ℝ (jArg A B)) := by
    exact hf.mono (spectrum_jArg_subset_Ioi hA hB)
  have hcont_inv : ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (jArg A B)) :=
    continuousOn_inv_of_pos_jArg hf hpos hA hB
  calc
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
        hsCfcR f (jArg A B)
      = hsCfcR (fun x : ℝ ↦ (f x)⁻¹ * f x) (jArg A B) := by
          dsimp [hsCfcR, HansenPedersen.cfcR]
          rw [← cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (f := fun x : ℝ ↦ (f x)⁻¹) (g := f) (a := jArg A B) hcont_inv hcont_f]
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) (jArg A B) := by
          apply cfc_congr
          intro x hx
          have hxne : f x ≠ 0 := (hpos x (spectrum_jArg_subset_Ioi hA hB hx)).ne'
          simp [hxne]
    _ = (1 : HSOp n) := by
          dsimp [hsCfcR, HansenPedersen.cfcR]
          simpa using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B)
              (ha := hjArg_sa))

private theorem jArg_mul_rightMul {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    jArg A B * rightMul B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

private theorem rightMul_mul_jArg {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * jArg A B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

private theorem commute_jArg_rightMul {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (jArg A B) (rightMul B) := by
  change jArg A B * rightMul B = rightMul B * jArg A B
  rw [jArg_mul_rightMul hB, rightMul_mul_jArg hB]

private theorem commute_jArg_rightMul_posInv {A B : Mₙ n}
    (_hB : Matrix.PosDef B) :
    Commute (jArg A B) (rightMul (B⁻¹)) := by
  ext X
  simp [jArg, rightMul_apply, leftMul_apply, mul_assoc]

private theorem commute_cfc_jArg_rightMul {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (hsCfcR f (jArg A B)) (rightMul B) := by
  exact (commute_jArg_rightMul (A := A) hB).cfc_real f

private theorem commute_cfc_jArg_rightMul_posInv {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (hsCfcR f (jArg A B)) (rightMul (B⁻¹)) := by
  exact (commute_jArg_rightMul_posInv (A := A) hB).cfc_real f

/-- For positive-definite `B`, the reciprocal-CFC `J`-operator used in the
inverse inequality is self-adjoint. -/
theorem jOperatorInv_isSelfAdjoint {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    IsSelfAdjoint (jOperatorInv f A B) := by
  have hcfc : IsSelfAdjoint (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) := by
    simp [hsCfcR]
  have hright : IsSelfAdjoint (rightMul (B⁻¹)) :=
    rightMul_isSelfAdjoint (posInv_posDef hB).isSelfAdjoint
  have hcomm := commute_cfc_jArg_rightMul_posInv
    (f := fun x : ℝ ↦ (f x)⁻¹) (A := A) hB
  rw [jOperatorInv]
  calc
    star (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) * rightMul (B⁻¹)) =
        star (rightMul (B⁻¹)) *
          star (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) := star_mul _ _
    _ = rightMul (B⁻¹) * hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
      rw [hright.star_eq, hcfc.star_eq]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) * rightMul (B⁻¹) := hcomm.eq.symm

private theorem rightMul_posInv_mul_rightMul {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul (B⁻¹) * rightMul B = 1 := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [rightMul_apply, mul_assoc]

private theorem rightMul_mul_rightMul_posInv {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * rightMul (B⁻¹) = 1 := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [rightMul_apply, mul_assoc]

/-- Multiplying `J_f(A,B)` on the right by `R_{B^{-1}}` cancels the trailing
right multiplication.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem jOperator_mul_rightMul_posInv_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    jOperator f A B * rightMul (B⁻¹) =
      hsCfcR f (jArg A B) := by
  calc
    jOperator f A B * rightMul (B⁻¹)
        = (hsCfcR f (jArg A B) * rightMul B) *
            rightMul (B⁻¹) := by
              rfl
    _ = hsCfcR f (jArg A B) *
          (rightMul B * rightMul (B⁻¹)) := by
            simp [mul_assoc]
    _ = hsCfcR f (jArg A B) := by
          rw [rightMul_mul_rightMul_posInv hB]
          simp

/-- Multiplying `J_f(A,B)⁻¹` on the right by `R_B` cancels the trailing
`R_{B^{-1}}`.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem jOperatorInv_mul_rightMul_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    jOperatorInv f A B * rightMul B =
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
  calc
    jOperatorInv f A B * rightMul B
        = (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
            rightMul (B⁻¹)) * rightMul B := by
              rfl
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
          (rightMul (B⁻¹) * rightMul B) := by
            simp [mul_assoc]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
          rw [rightMul_posInv_mul_rightMul hB]
          simp

/-- Multiplying `J_f(A,B)` on the left by `R_{B^{-1}}` cancels the right
multiplication, using commutation with the functional calculus of `jArg`.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem rightMul_posInv_mul_jOperator_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul (B⁻¹) * jOperator f A B =
      hsCfcR f (jArg A B) := by
  have hcomm := commute_cfc_jArg_rightMul_posInv (f := f) (A := A) hB
  calc
    rightMul (B⁻¹) * jOperator f A B
        = rightMul (B⁻¹) *
          (hsCfcR f (jArg A B) * rightMul B) := by
            rfl
    _ = (rightMul (B⁻¹) *
          hsCfcR f (jArg A B)) * rightMul B := by
            simp [mul_assoc]
    _ = (hsCfcR f (jArg A B) *
          rightMul (B⁻¹)) * rightMul B := by
            rw [(Commute.eq hcomm).symm]
    _ = hsCfcR f (jArg A B) *
          (rightMul (B⁻¹) * rightMul B) := by
            simp [mul_assoc]
    _ = hsCfcR f (jArg A B) := by
          rw [rightMul_posInv_mul_rightMul hB]
          simp

/-- Multiplying `J_f(A,B)⁻¹` on the left by `R_B` cancels the right
`R_{B^{-1}}`, using commutation with the functional calculus of `jArg`.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem rightMul_mul_jOperatorInv_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * jOperatorInv f A B =
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
  have hcomm := commute_cfc_jArg_rightMul (f := fun x : ℝ ↦ (f x)⁻¹) (A := A) hB
  calc
    rightMul B * jOperatorInv f A B
        = rightMul B *
          (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
            rightMul (B⁻¹)) := by
              rfl
    _ = (rightMul B *
          hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) *
          rightMul (B⁻¹) := by
            simp [mul_assoc]
    _ = (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
          rightMul B) * rightMul (B⁻¹) := by
            rw [(Commute.eq hcomm).symm]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
          (rightMul B * rightMul (B⁻¹)) := by
            simp [mul_assoc]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
          rw [rightMul_mul_rightMul_posInv hB]
          simp

/-- `J_f(A,B)` is a left inverse of its strict positive-definite inverse model.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem jOperator_mul_jOperatorInv_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    jOperator f A B * jOperatorInv f A B = 1 := by
  have hcomm :
      Commute
        (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B))
        (rightMul B) :=
    commute_cfc_jArg_rightMul (f := fun x : ℝ ↦ (f x)⁻¹) (A := A) hB
  calc
    jOperator f A B * jOperatorInv f A B
        = (hsCfcR f (jArg A B) * rightMul B) *
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
              rightMul (B⁻¹)) := by
              rfl
    _ = hsCfcR f (jArg A B) *
          (rightMul B *
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
              rightMul (B⁻¹))) := by
            simp [mul_assoc]
    _ = hsCfcR f (jArg A B) *
          ((hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) * rightMul B) *
              rightMul (B⁻¹)) := by
            rw [hcomm.eq]
            simp [mul_assoc]
    _ = (hsCfcR f (jArg A B) *
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) *
          (rightMul B * rightMul (B⁻¹)) := by
            simp [mul_assoc]
    _ = (1 : HSOp n) * (rightMul B * rightMul (B⁻¹)) := by
          rw [cfc_jArg_mul_cfc_inv_of_posDef hf hpos hA hB]
    _ = 1 := by
          rw [rightMul_mul_rightMul_posInv hB]
          simp

/-- The strict positive-definite inverse model is a left inverse of `J_f(A,B)`.
Source: Hiai, Definition 6.1 algebra of `J_f(A,B)`. -/
theorem jOperatorInv_mul_jOperator_of_posDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    jOperatorInv f A B * jOperator f A B = 1 := by
  have hcomm :
      Commute
        (hsCfcR f (jArg A B))
        (rightMul (B⁻¹)) :=
    commute_cfc_jArg_rightMul_posInv (f := f) (A := A) hB
  calc
    jOperatorInv f A B * jOperator f A B
        = (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
            rightMul (B⁻¹)) *
          (hsCfcR f (jArg A B) * rightMul B) := by
            rfl
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
          (rightMul (B⁻¹) *
            (hsCfcR f (jArg A B) * rightMul B)) := by
            simp [mul_assoc]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
          ((hsCfcR f (jArg A B) * rightMul (B⁻¹)) *
            rightMul B) := by
            rw [hcomm.eq]
            simp [mul_assoc]
    _ = (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) *
            hsCfcR f (jArg A B)) *
          (rightMul (B⁻¹) * rightMul B) := by
            simp [mul_assoc]
    _ = (1 : HSOp n) * (rightMul (B⁻¹) * rightMul B) := by
          rw [cfc_inv_jArg_mul_cfc_of_posDef hf hpos hA hB]
    _ = 1 := by
          rw [rightMul_posInv_mul_rightMul hB]
          simp

private noncomputable def jOperatorUnitOfPosDef {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) : Units (HSOp n) where
  val := jOperator f A B
  inv := jOperatorInv f A B
  val_inv := jOperator_mul_jOperatorInv_of_posDef hf hpos hA hB
  inv_val := jOperatorInv_mul_jOperator_of_posDef hf hpos hA hB

private theorem jOperator_isUnit_of_posDef_core {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jOperator f A B) := by
  refine ⟨jOperatorUnitOfPosDef hf hpos hA hB, rfl⟩

private theorem ringInverse_jOperator_eq_jOperatorInv_of_posDef_core {f : ℝ → ℝ}
    {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (jOperator f A B) = jOperatorInv f A B := by
  let u := jOperatorUnitOfPosDef hf hpos hA hB
  simpa [u, jOperatorUnitOfPosDef] using Ring.inverse_unit u

private theorem jOperatorInv_isUnit_of_posDef_core {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jOperatorInv f A B) := by
  rw [← ringInverse_jOperator_eq_jOperatorInv_of_posDef_core
    (f := f) (A := A) (B := B) hf hpos hA hB]
  exact (jOperator_isUnit_of_posDef_core hf hpos hA hB).ringInverse

private theorem ringInverse_jOperatorInv_eq_jOperator_of_posDef_core {f : ℝ → ℝ}
    {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (jOperatorInv f A B) = jOperator f A B := by
  let u := (jOperator_isUnit_of_posDef_core hf hpos hA hB).unit
  rw [← ringInverse_jOperator_eq_jOperatorInv_of_posDef_core
    (f := f) (A := A) (B := B) hf hpos hA hB]
  rw [show Ring.inverse (jOperator f A B) =
      (((u : Units (HSOp n))⁻¹ : Units (HSOp n)) : HSOp n) by
    simpa [u] using Ring.inverse_unit u]
  simp [u]

/-- File-local weak quadratic-form view used only to evaluate quasi-entropy.
The public positivity theorems below use Mathlib's operator order. -/
private def HSQuadraticNonneg (T : HSOp n) : Prop :=
  ∀ X : Mₙ n, 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * T X))

private theorem hsQuadraticNonneg_of_nonneg {T : HSOp n}
    (hT : 0 ≤ T) : HSQuadraticNonneg T := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  have hT' : 0 ≤ (T : Mₙ n →L[ℂ] Mₙ n) := by simpa using hT
  have hTpos :
      @ContinuousLinearMap.IsPositive ℂ (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        ((T : Mₙ n →L[ℂ] Mₙ n)) :=
    ((@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ n)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      ((T : Mₙ n →L[ℂ] Mₙ n))).1 hT')
  intro X
  have hsymm : T.IsSymmetric := by
    exact hTpos.1
  have hinner : 0 ≤ Complex.re (Matrix.trace (X * Matrix.conjTranspose (T X))) := by
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply, inner] using hTpos.2 X
  have hswap : inner ℂ (T X) X = inner ℂ X (T X) := by
    exact hsymm X X
  have hswap' :
      Complex.re (Matrix.trace (X * Matrix.conjTranspose (T X))) =
        Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
    simpa [inner] using congrArg Complex.re hswap
  have hinner' : 0 ≤ Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
    rw [← hswap']
    exact hinner
  rwa [Matrix.trace_mul_comm] at hinner'

private theorem rightMul_nonneg_le_of_posDef {B : Mₙ n} (hB : Matrix.PosDef B) :
    0 ≤ rightMul B := by
  exact rightMul_nonneg (Matrix.PosDef.nonneg hB)

private theorem rightMul_posInv_nonneg_le_of_posDef {B : Mₙ n} (hB : Matrix.PosDef B) :
    0 ≤ rightMul (B⁻¹) := by
  exact rightMul_nonneg (Matrix.PosDef.nonneg (posInv_posDef hB))

/-- `J_f(A,B)` is nonnegative when `A` and `B` are positive definite and `f` is
continuous and strictly positive on `(0, ∞)`. -/
theorem jOperator_nonneg {f : ℝ → ℝ} {A B : Mₙ n} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    Matrix.PosDef A →
    Matrix.PosDef B →
    0 ≤ jOperator f A B := by
  intro hf hpos hA hB
  have hcfc_nonneg :
      0 ≤ hsCfcR f (jArg A B) := by
    refine cfc_nonneg (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B) ?_
    intro x hx
    exact le_of_lt (hpos x (spectrum_jArg_subset_Ioi hA hB hx))
  have hright_nonneg : 0 ≤ rightMul B := rightMul_nonneg_le_of_posDef hB
  have hcomm : Commute (hsCfcR f (jArg A B)) (rightMul B) :=
    commute_cfc_jArg_rightMul (f := f) (A := A) hB
  rw [jOperator]
  exact (commute_iff_mul_nonneg hcfc_nonneg hright_nonneg).mp hcomm

/-- Quasi-entropy is nonnegative when the representing function is positive on `(0, ∞)`.
Sanity lemma: positivity of `J_f(A,B)` gives nonnegativity of the associated
quadratic form; terminology from Hiai, Definition 6.1. -/
theorem quasiEntropy_nonneg {f : ℝ → ℝ} {A B X : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    0 ≤ quasiEntropy f A B X := by
  have hJ : 0 ≤ jOperator f A B := by
    exact jOperator_nonneg (f := f) (A := A) (B := B) hf hpos hA hB
  simpa [quasiEntropy] using hsQuadraticNonneg_of_nonneg hJ X

/-- The explicit inverse model of `J_f(A,B)` is nonnegative under the same
positive-definite input and positive-function hypotheses as `jOperator_nonneg`. -/
theorem jOperatorInv_nonneg {f : ℝ → ℝ} {A B : Mₙ n} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    Matrix.PosDef A →
    Matrix.PosDef B →
    0 ≤ jOperatorInv f A B := by
  intro hf hpos hA hB
  have hcfc_nonneg :
      0 ≤ hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
    refine cfc_nonneg (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B) ?_
    intro x hx
    exact le_of_lt (inv_pos.mpr (hpos x (spectrum_jArg_subset_Ioi hA hB hx)))
  have hright_nonneg : 0 ≤ rightMul (B⁻¹) := rightMul_posInv_nonneg_le_of_posDef hB
  have hcomm :
      Commute (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B))
        (rightMul (B⁻¹)) :=
    commute_cfc_jArg_rightMul_posInv (f := fun x : ℝ ↦ (f x)⁻¹) (A := A) hB
  rw [jOperatorInv]
  exact (commute_iff_mul_nonneg hcfc_nonneg hright_nonneg).mp hcomm

/-- `J_f(A,B)` is strictly positive in Mathlib's standard sense: it is
nonnegative and a unit, using the inverse constructed for positive-definite
inputs. -/
theorem jOperator_strict_pos {f : ℝ → ℝ} {A B : Mₙ n} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    Matrix.PosDef A →
    Matrix.PosDef B →
    IsStrictlyPositive (jOperator f A B) := by
  intro hf hpos hA hB
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact (jOperator_isUnit_of_posDef_core hf hpos hA hB).isStrictlyPositive <|
    jOperator_nonneg (f := f) hf hpos hA hB

/-- The strict positive-definite inverse model of `J_f(A,B)` is also strictly
positive in Mathlib's standard sense. -/
theorem jOperatorInv_strict_pos {f : ℝ → ℝ} {A B : Mₙ n} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    Matrix.PosDef A →
    Matrix.PosDef B →
    IsStrictlyPositive (jOperatorInv f A B) := by
  intro hf hpos hA hB
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact (jOperatorInv_isUnit_of_posDef_core hf hpos hA hB).isStrictlyPositive <|
    jOperatorInv_nonneg (f := f) hf hpos hA hB

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.Core

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- With zero-dimensional codomain, the direct `J`-operator inequality for `Φ`
holds trivially: both compared operators are the zero operator. -/
theorem direct_zeroCodomain (f : ℝ → ℝ)
    {n : ℕ} (Φ : HSMap n 0) {A B : Mₙ n} :
    (show HSOp 0 from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  apply le_of_eq
  ext X i j
  exact Fin.elim0 i

end

end HiaiPetz.Core
