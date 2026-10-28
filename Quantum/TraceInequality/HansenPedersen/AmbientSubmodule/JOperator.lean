/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HansenPedersen.Core.JOperatorPositivity
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Positive-definite `J`-operator algebra

Private support lemmas and public consequences for positive-definite
`jArg`, `jOperator`, and their inverses.

## Main results

* `spectrum_jArg_subset_Ioi`: the real spectrum of a positive-definite
  `jArg` lies in the positive half-line.
* `jOperator_isUnit_of_posDef` and
  `ringInverse_jOperator_eq_jOperatorInv_of_posDef`: invertibility of
  `jOperator` when the scalar function is positive on `(0, ∞)`.
* `jOperator_nonneg_of_posDef`: positivity of `jOperator` for positive scalar
  functions.

## References

* Hiai, `J`-operator calculus for positive definite matrices in the
  operator convexity/monotonicity framework.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

@[fun_prop] private theorem continuousOn_inv_of_pos_jArg
    {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
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
    {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
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
          simpa [hsCfcR] using
            (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (f := f) (g := fun x : ℝ ↦ (f x)⁻¹) (a := jArg A B) hcont_f hcont_inv).symm
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) (jArg A B) := by
          apply cfc_congr
          intro x hx
          have hxne : f x ≠ 0 := (hpos x (spectrum_jArg_subset_Ioi hA hB hx)).ne'
          simp [hxne]
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B)
              (ha := hjArg_sa))

private theorem cfc_inv_jArg_mul_cfc_of_posDef
    {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
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
          simpa [hsCfcR] using
            (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (f := fun x : ℝ ↦ (f x)⁻¹) (g := f) (a := jArg A B) hcont_inv hcont_f).symm
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) (jArg A B) := by
          apply cfc_congr
          intro x hx
          have hxne : f x ≠ 0 := (hpos x (spectrum_jArg_subset_Ioi hA hB hx)).ne'
          simp [hxne]
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B)
              (ha := hjArg_sa))

private theorem hsTrace_jOperatorInv_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (_hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Matrix.trace (Matrix.conjTranspose X * (jOperatorInv f A B Y)) =
      Matrix.trace
        ((Matrix.conjTranspose X *
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) Y)) *
          B⁻¹) := by
  have hcomm :
      Commute
        (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B))
        (rightMul (B⁻¹)) :=
    by
      have hcomm0 : Commute (jArg A B) (rightMul (B⁻¹)) := by
        ext X
        simp [jArg, rightMul_apply, leftMul_apply, mul_assoc]
      exact hcomm0.cfc_real (fun x : ℝ ↦ (f x)⁻¹)
  rw [jOperatorInv, (Commute.eq hcomm)]
  simpa using
    hsTrace_rightMul_shift X
      (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) Y)
      (B⁻¹)

/-- Trace-pairing formula for `jOperatorInv`, using the inverse scalar
functional calculus and right multiplication by `B⁻¹`. -/
theorem hsQForm_jOperatorInv_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperatorInv f A B Y))) =
      Complex.re
        (Matrix.trace
          ((Matrix.conjTranspose X *
              (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) Y)) *
            B⁻¹)) := by
  rw [hsTrace_jOperatorInv_of_posDef hB X Y]

private theorem commute_jArg_rightMul {n : ℕ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (jArg A B) (rightMul B) := by
  change jArg A B * rightMul B = rightMul B * jArg A B
  rw [jArg_mul_rightMul hB, rightMul_mul_jArg hB]

private theorem commute_jArg_rightMul_posInv {n : ℕ} {A B : Mₙ n}
    (_hB : Matrix.PosDef B) :
    Commute (jArg A B) (rightMul (B⁻¹)) := by
  ext X
  simp [jArg, rightMul_apply, leftMul_apply, mul_assoc]

private theorem rightMul_posInv_mul_rightMul {n : ℕ} {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul (B⁻¹) * rightMul B = 1 := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [rightMul_apply, mul_assoc]

private theorem rightMul_mul_rightMul_posInv {n : ℕ} {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * rightMul (B⁻¹) = 1 := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [rightMul_apply, mul_assoc]

private theorem commute_cfc_jArg_rightMul {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (hsCfcR f (jArg A B)) (rightMul B) := by
  exact (commute_jArg_rightMul (A := A) hB).cfc_real f

private theorem commute_cfc_jArg_rightMul_posInv {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute (hsCfcR f (jArg A B)) (rightMul (B⁻¹)) := by
  exact (commute_jArg_rightMul_posInv (A := A) hB).cfc_real f

private noncomputable def jOperatorUnitOfPosDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) : Units (HSOp n) where
  val := jOperator f A B
  inv := jOperatorInv f A B
  val_inv := jOperator_mul_jOperatorInv_of_posDef hf hpos hA hB
  inv_val := jOperatorInv_mul_jOperator_of_posDef hf hpos hA hB

/-- If `f` is positive on `(0, ∞)` and `A`, `B` are positive definite, then
`jOperator f A B` is a unit with inverse `jOperatorInv f A B`. -/
theorem jOperator_isUnit_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jOperator f A B) := by
  refine ⟨jOperatorUnitOfPosDef hf hpos hA hB, rfl⟩

/-- Under the positive-definite and positivity hypotheses, the ring inverse of
`jOperator f A B` is the explicitly defined `jOperatorInv f A B`. -/
theorem ringInverse_jOperator_eq_jOperatorInv_of_posDef {n : ℕ} {f : ℝ → ℝ}
    {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (jOperator f A B) = jOperatorInv f A B := by
  let u := jOperatorUnitOfPosDef hf hpos hA hB
  simpa [u, jOperatorUnitOfPosDef] using Ring.inverse_unit u

-- Transporting positivity through `cfcR` and the commuting product with `rightMul B`
-- causes expensive elaboration; keep it local to this theorem.

/-- If `f` is positive on `(0, ∞)`, then `jOperator f A B` is nonnegative for
positive definite `A` and `B`. -/
theorem jOperator_nonneg_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    0 ≤ jOperator f A B := by
  have hcfc_nonneg :
      0 ≤ hsCfcR f (jArg A B) := by
    refine cfc_nonneg (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B) ?_
    intro x hx
    exact le_of_lt (hpos x (spectrum_jArg_subset_Ioi hA hB hx))
  have hright_nonneg : 0 ≤ rightMul B := by
    exact rightMul_nonneg (Matrix.PosDef.nonneg hB)
  have hcomm : Commute (hsCfcR f (jArg A B)) (rightMul B) :=
    commute_cfc_jArg_rightMul (f := f) (A := A) hB
  rw [jOperator]
  exact (commute_iff_mul_nonneg hcfc_nonneg hright_nonneg).mp hcomm

end MatrixScopedInstances

end HiaiPetz
