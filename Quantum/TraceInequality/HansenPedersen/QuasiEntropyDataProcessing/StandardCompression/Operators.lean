/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardCompression.Basic
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities

/-!
# Standard compression operators

Compression and core operators used to restate the strict-output direct and
inverse standard conditions as operator nonnegativity statements.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

namespace StrictlyPositive

/-- Compression reformulation of the strict-output direct standard condition
`DirectStandard f Φ A B`: for every test matrix `X : Mₙ (l+1)` the compression
quadratic form `directCompressionQForm f Φ A B hPos hB hΦ1 X` is nonnegative. -/
def DirectCompression (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ l), 0 ≤ StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X

/-- Compression reformulation of the strict-output inverse standard condition
`InverseStandard f Φ A B`: for every test matrix `X : Mₙ (k+1)` the compression
quadratic form `inverseCompressionQForm f Φ A B hPos hB hΦ1 X` is nonnegative. -/
def InverseCompression (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ k), 0 ≤ StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X

end StrictlyPositive

/-- The strict-output direct standard condition `DirectStandard f Φ A B` is
equivalent to its compression reformulation `DirectCompression f Φ A B hPos hB hΦ1`,
obtained by rewriting each standard quadratic form as the compression one. -/
theorem StrictlyPositive.directStandard_iff_compression
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectStandard f Φ A B ↔
      StrictlyPositive.DirectCompression f Φ A B hPos hB hΦ1 := by
  constructor
  · intro hdir X
    simpa [StrictlyPositive.DirectCompression,
      StrictlyPositive.directStandardQForm_eq_directCompressionQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using
      (show 0 ≤ StrictlyPositive.directStandardQForm f Φ A B X from hdir X)
  · intro hcomp X
    simpa [StrictlyPositive.DirectCompression,
      StrictlyPositive.directStandardQForm_eq_directCompressionQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using
      (show 0 ≤ StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X from hcomp X)

/-- The strict-output inverse standard condition `InverseStandard f Φ A B` is
equivalent to its compression reformulation `InverseCompression f Φ A B hPos hB hΦ1`,
obtained by rewriting each standard quadratic form as the compression one. -/
theorem StrictlyPositive.inverseStandard_iff_compression
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseStandard f Φ A B ↔
      StrictlyPositive.InverseCompression f Φ A B hPos hB hΦ1 := by
  constructor
  · intro hinv X
    simpa [StrictlyPositive.InverseCompression,
      StrictlyPositive.inverseStandardQForm_eq_inverseCompressionQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using
      (show 0 ≤ StrictlyPositive.inverseStandardQForm f Φ A B X from hinv X)
  · intro hcomp X
    simpa [StrictlyPositive.InverseCompression,
      StrictlyPositive.inverseStandardQForm_eq_inverseCompressionQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using
      (show 0 ≤ StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X from hcomp X)

/-- The direct compression operator on `Mₙ (l+1)`, namely `S ∘ (TΦ − V* ∘ TA ∘ V) ∘ S`
where `TΦ = hsCfcR f (jArg (Φ A) (Φ B))`, `TA = hsCfcR f (jArg A B)`, `V` is the contraction
`contraction Φ hPos hB hΦ1`, and `S = rightMul (matrixSqrtPos (Φ B))`. Its trace
quadratic form realises the direct compression quadratic form. -/
noncomputable def StrictlyPositive.directCompressionOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ l) :=
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let TV : HSOp (Nat.succ l) := (hsAdjoint V).comp (TA.comp V)
  let C : HSOp (Nat.succ l) := TΦ - TV
  let S : HSOp (Nat.succ l) := rightMul (matrixSqrtPos (Φ B))
  S.comp (C.comp S)

/-- The direct core operator on `Mₙ (l+1)`, namely `TΦ − V* ∘ TA ∘ V`, the compressed
difference of J-operators before the outer conjugation by `S = rightMul (matrixSqrtPos (Φ B))`;
here `TΦ = hsCfcR f (jArg (Φ A) (Φ B))`, `TA = hsCfcR f (jArg A B)`, and
`V = contraction Φ hPos hB hΦ1`. -/
noncomputable def StrictlyPositive.directCoreOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ l) :=
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let TV : HSOp (Nat.succ l) := (hsAdjoint V).comp (TA.comp V)
  let C : HSOp (Nat.succ l) := TΦ - TV
  C

/-- The inverse compression operator on `Mₙ (k+1)`, namely `S ∘ (TA − W* ∘ TΦ ∘ W) ∘ S`
where `TA = hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)` and
`TΦ = hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))`,
`W = hsAdjoint (contraction Φ hPos hB hΦ1)`, and `S = rightMul (matrixInvSqrtPos B)`. -/
noncomputable def StrictlyPositive.inverseCompressionOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ k) :=
  let TA : HSOp (Nat.succ k) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := TA - TW
  let S : HSOp (Nat.succ k) := rightMul (matrixInvSqrtPos B)
  S.comp (C.comp S)

/-- The inverse core operator on `Mₙ (k+1)`, namely `TA − W* ∘ TΦ ∘ W` with the reciprocal
function: `TA = hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)` and
`TΦ = hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))`,
and `W = hsAdjoint (contraction Φ hPos hB hΦ1)`, before the outer conjugation by
`matrixInvSqrtPos B`. -/
noncomputable def StrictlyPositive.inverseCoreOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ k) :=
  let TA : HSOp (Nat.succ k) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := TA - TW
  C

/-- Image-side counterpart of `cfcR_inv_eq_ringInverse_of_jArg_posDef`: for a positive
map `Φ`, the real CFC of `x ↦ (f x)⁻¹` at `jArg (Φ A) (Φ B)` equals the ring inverse of
`hsCfcR f (jArg (Φ A) (Φ B))`, using that `Φ` preserves positive definiteness. -/
theorem cfcR_inv_eq_ringInverse_of_image_jArg_posDef
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B)) =
      Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  exact HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef
    (f := f) hf hpos hΦA hΦB

/-- For positive-definite `A`, `B` and `f` continuous and strictly positive on `(0, ∞)`,
the ring inverse is a left inverse of `hsCfcR f (jArg A B)`:
`Ring.inverse (hsCfcR f (jArg A B)) * hsCfcR f (jArg A B) = 1`. -/
theorem ringInverse_cfcR_mul_cfcR_eq_one_of_jArg_posDef
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (hsCfcR f (jArg A B)) * hsCfcR f (jArg A B) =
      (1 : HSOp n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hσ : spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_jArg_subset_Ioi_of_posDef hA hB
  have hcont_f : ContinuousOn f (spectrum ℝ (jArg A B)) := hf.mono hσ
  have hcont_invf : ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (jArg A B)) := by
    refine hcont_f.inv₀ ?_
    intro x hx
    exact (hpos x (hσ hx)).ne'
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
  rw [← HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef (f := f) hf hpos hA hB]
  have hmul :
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) * hsCfcR f (jArg A B) =
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹ * f x) (jArg A B) := by
    simpa [HansenPedersen.cfcR] using
      (cfc_mul (fun x : ℝ ↦ (f x)⁻¹) f (jArg A B) hcont_invf hcont_f).symm
  rw [hmul]
  rw [← cfc_const_one ℝ (jArg A B) (ha := hjArg_sa)]
  apply cfc_congr
  intro x hx
  have hxne : f x ≠ 0 := (hpos x (hσ hx)).ne'
  simp [hxne]

/-- For positive-definite `A`, `B` and `f` continuous and strictly positive on `(0, ∞)`,
the ring inverse is a right inverse of `hsCfcR f (jArg A B)`:
`hsCfcR f (jArg A B) * Ring.inverse (hsCfcR f (jArg A B)) = 1`. -/
theorem cfcR_mul_ringInverse_cfcR_eq_one_of_jArg_posDef
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    hsCfcR f (jArg A B) * Ring.inverse (hsCfcR f (jArg A B)) =
      (1 : HSOp n) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hσ : spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_jArg_subset_Ioi_of_posDef hA hB
  have hcont_f : ContinuousOn f (spectrum ℝ (jArg A B)) := hf.mono hσ
  have hcont_invf : ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (jArg A B)) := by
    refine hcont_f.inv₀ ?_
    intro x hx
    exact (hpos x (hσ hx)).ne'
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
  rw [← HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef (f := f) hf hpos hA hB]
  have hmul :
      hsCfcR f (jArg A B) * hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) =
        hsCfcR (fun x : ℝ ↦ f x * (f x)⁻¹) (jArg A B) := by
    simpa [HansenPedersen.cfcR] using
      (cfc_mul f (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) hcont_f hcont_invf).symm
  rw [hmul]
  rw [← cfc_const_one ℝ (jArg A B) (ha := hjArg_sa)]
  apply cfc_congr
  intro x hx
  have hxne : f x ≠ 0 := (hpos x (hσ hx)).ne'
  simp [hxne]

/-- Image-side left-inverse identity: for a positive map `Φ`, `Ring.inverse` is a left
inverse of `hsCfcR f (jArg (Φ A) (Φ B))`, i.e.
`Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) * hsCfcR f (jArg (Φ A) (Φ B)) = 1`. -/
theorem ringInverse_cfcR_mul_cfcR_eq_one_of_image_jArg_posDef
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) * hsCfcR f (jArg (Φ A) (Φ B)) =
      (1 : HSOp (Nat.succ l)) := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  exact ringInverse_cfcR_mul_cfcR_eq_one_of_jArg_posDef
    (f := f) hf hpos hΦA hΦB

/-- Image-side right-inverse identity: for a positive map `Φ`, `Ring.inverse` is a right
inverse of `hsCfcR f (jArg (Φ A) (Φ B))`, i.e.
`hsCfcR f (jArg (Φ A) (Φ B)) * Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) = 1`. -/
theorem cfcR_mul_ringInverse_cfcR_eq_one_of_image_jArg_posDef
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsCfcR f (jArg (Φ A) (Φ B)) * Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) =
      (1 : HSOp (Nat.succ l)) := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  exact cfcR_mul_ringInverse_cfcR_eq_one_of_jArg_posDef
    (f := f) hf hpos hΦA hΦB

/-- Variant of `inverseCoreOperator` using the ring inverses `Ring.inverse (hsCfcR f (jArg A B))`
and `Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B)))` in place of the reciprocal-function CFC
  operators;
it agrees with `inverseCoreOperator` when `f` is continuous and positive on `(0, ∞)`
(see `inverseCoreOperator_eq_inverseRingCoreOperator`). -/
noncomputable def StrictlyPositive.inverseRingCoreOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ k) :=
  let TA : HSOp (Nat.succ k) :=
    Ring.inverse (hsCfcR f (jArg A B))
  let TΦ : HSOp (Nat.succ l) :=
    Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B)))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := TA - TW
  C

/-- For `f` continuous and strictly positive on `(0, ∞)` with `A`, `B` positive definite,
`inverseCoreOperator` and `inverseRingCoreOperator` coincide: the reciprocal-function CFC
operators equal the ring inverses of the corresponding J-operators. -/
theorem StrictlyPositive.inverseCoreOperator_eq_inverseRingCoreOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1 =
      StrictlyPositive.inverseRingCoreOperator f Φ A B hPos hB hΦ1 := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  rw [StrictlyPositive.inverseCoreOperator, StrictlyPositive.inverseRingCoreOperator]
  rw [HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef (f := f) hf hpos hA hB,
    cfcR_inv_eq_ringInverse_of_image_jArg_posDef
      (f := f) (Φ := Φ) hf hpos hPos hA hB hΦ1]

/-- The source-side J-operator `hsCfcR f (jArg A B)` on `Mₙ (k+1)`, i.e. the real CFC of `f`
at `jArg A B`; the map `Φ` is a phantom parameter kept for uniform signatures. -/
noncomputable def StrictlyPositive.sourceJOp
    (f : ℝ → ℝ)
    {k l : ℕ} (_Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k)) : HSOp (Nat.succ k) :=
  hsCfcR f (jArg A B)

/-- The image-side J-operator `hsCfcR f (jArg (Φ A) (Φ B))` on `Mₙ (l+1)`, i.e. the real CFC
of `f` at `jArg (Φ A) (Φ B)`, evaluated at the pushed-forward pair `(Φ A, Φ B)`. -/
noncomputable def StrictlyPositive.imageJOp
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k)) : HSOp (Nat.succ l) :=
  hsCfcR f (jArg (Φ A) (Φ B))

/-- Loewner-order form of the direct compressed condition:
`V* ∘ (hsCfcR f (jArg A B)) ∘ V ≤ hsCfcR f (jArg (Φ A) (Φ B))`,
where `V = contraction Φ hPos hB hΦ1`. -/
def StrictlyPositive.DirectCompressedLE
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  (show HSOp (Nat.succ l) from
    (hsAdjoint (StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1)).comp
      ((StrictlyPositive.sourceJOp f Φ A B).comp
        (StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1))) ≤
    (StrictlyPositive.imageJOp f Φ A B)

/-- Loewner-order form of the inverse compressed condition:
`V ∘ Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) ∘ V* ≤ Ring.inverse (hsCfcR f (jArg A B))`,
where `V = contraction Φ hPos hB hΦ1`. -/
def StrictlyPositive.InverseCompressedLE
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  (show HSOp (Nat.succ k) from
    (StrictlyPositive.contraction
      (Φ := Φ) hPos hB hΦ1).comp
      ((Ring.inverse (StrictlyPositive.imageJOp f Φ A B)).comp
        (hsAdjoint (StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1)))) ≤
    (Ring.inverse (StrictlyPositive.sourceJOp f Φ A B))

/-- The direct compression quadratic form equals the trace quadratic form of the direct
compression operator:
`directCompressionQForm ... X = Re tr(Xᴴ · directCompressionOperator ... X)`. -/
theorem StrictlyPositive.directCompressionQForm_eq_operatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hsqrtΦ_sa : IsSelfAdjoint (matrixSqrtPos (Φ B)) :=
    (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).1
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let S : HSOp (Nat.succ l) := rightMul (matrixSqrtPos (Φ B))
  let C : HSOp (Nat.succ l) := StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1
  have hshift :=
    hsQForm_shift_rightMul_testMatrix
      (B := matrixSqrtPos (Φ B))
      (X := X)
      (Y := C (S X))
      hsqrtΦ_sa
  calc
    StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (S X) * (C (S X)))) := by
            simp [StrictlyPositive.directCompressionQForm,
              StrictlyPositive.directCoreOperator, S, C]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((C (S X)) *
                matrixSqrtPos (Φ B)))) := by
            simpa [S, ContinuousLinearMap.comp_apply, Matrix.mul_assoc] using hshift.symm
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
            simp [StrictlyPositive.directCompressionOperator,
              StrictlyPositive.directCoreOperator, S, C, sub_mul]

/-- The direct compression quadratic form equals the trace quadratic form of the direct
core operator on the shifted test matrix `rightMul (matrixSqrtPos (Φ B)) X`. -/
theorem StrictlyPositive.directCompressionQForm_eq_coreOperatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) X) *
            ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1)
              (rightMul (matrixSqrtPos (Φ B)) X)))) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hsqrtΦ_sa : IsSelfAdjoint (matrixSqrtPos (Φ B)) :=
    (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).1
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let S : HSOp (Nat.succ l) := rightMul (matrixSqrtPos (Φ B))
  let C : HSOp (Nat.succ l) := StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1
  calc
    StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (S X) * (C (S X)))) := by
            simp [StrictlyPositive.directCompressionQForm,
              StrictlyPositive.directCoreOperator, S, C]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) X) *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixSqrtPos (Φ B)) X)))) := by
            simp [S, C]

/-- The trace quadratic form of the direct compression operator on `X` equals that of the
direct core operator on the shifted matrix `rightMul (matrixSqrtPos (Φ B)) X`. -/
theorem StrictlyPositive.directCompressionOperator_qform_eq_coreOperatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) X) *
            ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1)
              (rightMul (matrixSqrtPos (Φ B)) X)))) := by
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X)))
      = StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X := by
          simpa using
            (StrictlyPositive.directCompressionQForm_eq_operatorQForm
              (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X).symm
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) X) *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixSqrtPos (Φ B)) X)))) := by
          exact StrictlyPositive.directCompressionQForm_eq_coreOperatorQForm
            (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X

/-- The inverse compression quadratic form equals the trace quadratic form of the inverse
compression operator:
`inverseCompressionQForm ... X = Re tr(Xᴴ · inverseCompressionOperator ... X)`. -/
theorem StrictlyPositive.inverseCompressionQForm_eq_operatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
  have hInvSqrtB_sa : IsSelfAdjoint (matrixInvSqrtPos B) := (matrixInvSqrtPos_posDef hB).1
  let S : HSOp (Nat.succ k) := rightMul (matrixInvSqrtPos B)
  let C : HSOp (Nat.succ k) := StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1
  have hshift :=
    hsQForm_shift_rightMul_testMatrix
      (B := matrixInvSqrtPos B)
      (X := X)
      (Y := C (S X))
      hInvSqrtB_sa
  calc
    StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (S X) * (C (S X)))) := by
            simp [StrictlyPositive.inverseCompressionQForm,
              StrictlyPositive.inverseCoreOperator, S, C]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((C (S X)) *
                matrixInvSqrtPos B))) := by
            simpa [S, ContinuousLinearMap.comp_apply, Matrix.mul_assoc] using hshift.symm
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
            simp [StrictlyPositive.inverseCompressionOperator,
              StrictlyPositive.inverseCoreOperator, S, C, sub_mul]

/-- The inverse compression quadratic form equals the trace quadratic form of the inverse
core operator on the shifted test matrix `rightMul (matrixInvSqrtPos B) X`. -/
theorem StrictlyPositive.inverseCompressionQForm_eq_coreOperatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) X) *
            ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1)
              (rightMul (matrixInvSqrtPos B) X)))) := by
  have hInvSqrtB_sa : IsSelfAdjoint (matrixInvSqrtPos B) := (matrixInvSqrtPos_posDef hB).1
  let TA : HSOp (Nat.succ k) :=
    hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1
  let S : HSOp (Nat.succ k) := rightMul (matrixInvSqrtPos B)
  calc
    StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (S X) * (C (S X)))) := by
            simp [StrictlyPositive.inverseCompressionQForm,
              StrictlyPositive.inverseCoreOperator, C, S]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) X) *
              ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixInvSqrtPos B) X)))) := by
            simp [S, C]

/-- The trace quadratic form of the inverse compression operator on `X` equals that of the
inverse core operator on the shifted matrix `rightMul (matrixInvSqrtPos B) X`. -/
theorem StrictlyPositive.inverseCompressionOperator_qform_eq_coreOperatorQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) X) *
            ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1)
              (rightMul (matrixInvSqrtPos B) X)))) := by
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X)))
      = StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X := by
          simpa using
            (StrictlyPositive.inverseCompressionQForm_eq_operatorQForm
              (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X).symm
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) X) *
              ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixInvSqrtPos B) X)))) := by
          exact StrictlyPositive.inverseCompressionQForm_eq_coreOperatorQForm
            (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X

/-- The direct compression condition `DirectCompression f Φ A B hPos hB hΦ1` holds iff the
direct compression operator has nonnegative trace quadratic form on every `X`, i.e.
`0 ≤ Re tr(Xᴴ · directCompressionOperator ... X)`. -/
theorem StrictlyPositive.directCompression_iff_operatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectCompression f Φ A B hPos hB hΦ1 ↔
      ∀ X : Mₙ (Nat.succ l), 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
  constructor
  · intro hcomp X
    simpa [StrictlyPositive.directCompressionQForm_eq_operatorQForm
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using hcomp X
  · intro hcomp X
    simpa [StrictlyPositive.directCompressionQForm_eq_operatorQForm
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using hcomp X

/-- The inverse compression condition `InverseCompression f Φ A B hPos hB hΦ1` holds iff the
inverse compression operator has nonnegative trace quadratic form on every `X`, i.e.
`0 ≤ Re tr(Xᴴ · inverseCompressionOperator ... X)`. -/
theorem StrictlyPositive.inverseCompression_iff_operatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseCompression f Φ A B hPos hB hΦ1 ↔
      ∀ X : Mₙ (Nat.succ k), 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X))) := by
  constructor
  · intro hcomp X
    simpa [StrictlyPositive.inverseCompressionQForm_eq_operatorQForm
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using hcomp X
  · intro hcomp X
    simpa [StrictlyPositive.inverseCompressionQForm_eq_operatorQForm
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X] using hcomp X

namespace StrictlyPositive

/-- Nonnegativity of the trace quadratic form of the direct compression operator:
`0 ≤ Re tr(Xᴴ · directCompressionOperator f Φ A B hPos hB hΦ1 X)` for all `X : Mₙ
  (l+1)`. -/
def DirectCompressionOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ l), 0 ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X)))

/-- Nonnegativity of the trace quadratic form of the inverse compression operator:
`0 ≤ Re tr(Xᴴ · inverseCompressionOperator f Φ A B hPos hB hΦ1 X)` for all `X : Mₙ
  (k+1)`. -/
def InverseCompressionOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ k), 0 ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X)))

/-- Nonnegativity of the trace quadratic form of the direct core operator:
`0 ≤ Re tr(Xᴴ · directCoreOperator f Φ A B hPos hB hΦ1 X)` for all `X : Mₙ (l+1)`. -/
def DirectCoreOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ l), 0 ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1) X)))

/-- Nonnegativity of the trace quadratic form of the inverse core operator:
`0 ≤ Re tr(Xᴴ · inverseCoreOperator f Φ A B hPos hB hΦ1 X)` for all `X : Mₙ (k+1)`. -/
def InverseCoreOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ k), 0 ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1) X)))

/-- Nonnegativity of the trace quadratic form of the inverse ring-core operator:
`0 ≤ Re tr(Xᴴ · inverseRingCoreOperator f Φ A B hPos hB hΦ1 X)` for all `X : Mₙ (k+1)`. -/
def InverseRingCoreOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  ∀ X : Mₙ (Nat.succ k), 0 ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.inverseRingCoreOperator f Φ A B hPos hB hΦ1) X)))

end StrictlyPositive


end MatrixScopedInstances

end HiaiPetz
