/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.Internal.ShiftedCompressionInstances
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Conditions
import
Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonal

/-!
Shifted strict-output compression inequalities for the inverse/direct equivalence.

This file contains the residual comparison layer; the shifted ambient diagonal front is
isolated in the `AmbientDiagonal` modules of this directory (entry point `AmbientDiagonal.lean`).
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
open scoped HiaiPetz.RectangularOperatorInstances
open ProofNetInternal.ShiftedCompressionInstances

noncomputable section MatrixScopedInstances

private noncomputable abbrev strictEquivShiftedCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

private noncomputable abbrev strictEquivShiftedComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

private noncomputable abbrev strictEquivShiftedRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/- Instance caches: inside the proofs below the cross-space pair instances are only
available as `letI`-bound local definitions, and let-bound fvars bypass the
discrimination tree, so every `StarMul`/`Monoid`/`Algebra ℝ`/CFC search on
`HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))` re-runs the full global derivation.
Registering the content-named canonical abbrevs as section-level local instances
(they are `abbrev`s, hence reducible) plus a few extra reducible caches turns each
search into a head-match without changing the instance values. -/

attribute [local instance] strictEquivShiftedPairCStarAlgebra
  strictEquivShiftedPairComplexCFC strictEquivShiftedPairRealCFC
  strictEquivShiftedCStarAlgebra strictEquivShiftedComplexCFC strictEquivShiftedRealCFC

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the real-algebra structure on `HSOp n`
(value `inferInstance`), registered so that repeated `Algebra ℝ (HSOp n)`
synthesis reduces to a head-match; see the section comment above for the
performance rationale. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpShiftedScoped {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the real-algebra structure on the product
`HSOp l × HSOp k` (value `inferInstance`), so that its synthesis reduces to a
head-match. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpPairShiftedScoped {k l : ℕ} :
    Algebra ℝ (HSOp l × HSOp k) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the complex continuous functional calculus
(on star-normal elements) of the product `HSOp l × HSOp k`, so that its synthesis
reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instComplexCFCHSOpPairShiftedScoped {k l : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp l × HSOp k) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the real continuous functional calculus
(on self-adjoint elements) of the product `HSOp l × HSOp k`, so that its
synthesis reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instRealCFCHSOpPairShiftedScoped {k l : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp l × HSOp k) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the `ContinuousMapClass` instance of the
diagonal star-algebra homomorphism from `HSOp l × HSOp k` into the paired
operator space `HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))`, so that its synthesis
reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instContinuousMapClassDiagStarAlgHomShiftedScoped
    {k l : ℕ} :
    ContinuousMapClass
      ((HSOp l × HSOp k) →⋆ₐ[ℂ]
        (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
          (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
          (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))))
      (HSOp l × HSOp k)
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the `StarMul` structure on the paired
operator space `HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))`, so that its synthesis
reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instStarMulLPairShiftedScoped {k l : ℕ} :
    StarMul
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the `Monoid` structure on the paired
operator space `HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))`, so that its synthesis
reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instMonoidLPairShiftedScoped {k l : ℕ} :
    Monoid
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache for the `ContinuousMap.UniqueHom ℝ` structure on
the paired operator space `HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))`, so that its
synthesis reduces to a head-match. -/
@[reducible, local instance]
private noncomputable def instUniqueHomRealLPairShiftedScoped {k l : ℕ} :
    ContinuousMap.UniqueHom ℝ
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  inferInstance

-- The codomain-side shifted ambient alias still triggers heavy definitional
-- reduction at the header.
/-- The negated shifted functional calculus `fun t ↦ -(f (t + p))` applied to the
second ambient operator `StrictlyPositive.ambientSecondOperator Φ A B`; the
second-component CFC entering the strict-output residual comparison. -/
noncomputable def StrictlyPositive.ambientShiftedSecondCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ k) :=
  hsCfcR (StrictlyPositive.shiftedNegFn f p)
    (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1)

/-- The un-negated shifted functional calculus `fun t ↦ f (t + p)` applied to the
first ambient operator `StrictlyPositive.ambientFirstOperator Φ A B`, valued in
`HSOp (l + 1)`. -/
noncomputable def StrictlyPositive.ambientShiftedFirstPosCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ l) :=
  hsCfcR (fun t : ℝ ↦ f (t + p))
    (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)

/-- The un-negated shifted functional calculus `fun t ↦ f (t + p)` applied to the
second ambient operator `StrictlyPositive.ambientSecondOperator Φ A B`, valued in
`HSOp (k + 1)`. -/
noncomputable def StrictlyPositive.ambientShiftedSecondPosCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ k) :=
  hsCfcR (fun t : ℝ ↦ f (t + p))
    (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1)

/-- Componentwise real CFC of a pair of self-adjoint Hilbert-Schmidt operators. -/
private theorem cfc_prod_hsOp_of_isSelfAdjoint {k l : ℕ} {g : ℝ → ℝ}
    {a : HSOp (Nat.succ l)} {b : HSOp (Nat.succ k)}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hg_union : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b)) :
    cfc (R := ℝ) g (a, b) = (cfc (R := ℝ) g a, cfc (R := ℝ) g b) := by
  have hab : IsSelfAdjoint (a, b) := by
    change star (a, b) = (a, b)
    ext <;> simp [ha.star_eq, hb.star_eq]
  simpa using cfc_map_prod (R := ℝ) (S := ℝ) g a b
    (hf := hg_union) (hab := hab) (ha := ha) (hb := hb)

/-- CFC transport through the rectangular diagonal star-algebra homomorphism on
atom operators: `cfc g` of the block-diagonal operator `diagMapCLMRectHs a b`
is the block diagonal of the componentwise `cfc g`.  This is the heavy
`map_cfc`/product-CFC step of `StrictlyPositive.ambientJArgCFC_eq_diagMapCLM`,
factored out so that it elaborates once over atom variables instead of over the
large `StrictlyPositive.ambient*Operator` terms. -/
private theorem cfc_diagMapCLMRectHs_of_isSelfAdjoint {k l : ℕ} {g : ℝ → ℝ}
    {a : HSOp (Nat.succ l)} {b : HSOp (Nat.succ k)}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hg_union : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b)) :
    cfc (R := ℝ) g (diagMapCLMRectHs (k := l) (l := k) a b) =
      diagMapCLMRectHs (k := l) (l := k) (hsCfcR g a) (hsCfcR g b) := by
  let Ψ :
      (HSOp (Nat.succ l) × HSOp (Nat.succ k)) →⋆ₐ[ℂ]
        (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) :=
    @HansenPedersen.Internal.diagStarAlgHom (Mₙ (Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      (Mₙ (Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ k))
  have hab : IsSelfAdjoint (a, b) := by
    change star (a, b) = (a, b)
    ext <;> simp [ha.star_eq, hb.star_eq]
  have hΨab : IsSelfAdjoint (Ψ (a, b)) := by
    simpa [Ψ] using
      (@HansenPedersen.Internal.isSelfAdjoint_diagMapCLM (Mₙ (Nat.succ l))
        (instMatrixNormedAddCommGroup (n := Nat.succ l))
        (instMatrixInnerProductSpace (n := Nat.succ l))
        (instMatrixCompleteSpace (n := Nat.succ l))
        (Mₙ (Nat.succ k))
        (instMatrixNormedAddCommGroup (n := Nat.succ k))
        (instMatrixInnerProductSpace (n := Nat.succ k))
        (instMatrixCompleteSpace (n := Nat.succ k))
        a b ha hb)
  have hg : ContinuousOn g (spectrum ℝ (a, b)) := by
    rwa [Prod.spectrum_eq]
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) Ψ g (a, b)
    (hf := hg)
    (hφ := map_continuous Ψ)
    (ha := hab)
    (hφa := hΨab)
  have hprod : cfc (R := ℝ) g (a, b) = (cfc (R := ℝ) g a, cfc (R := ℝ) g b) :=
    cfc_prod_hsOp_of_isSelfAdjoint ha hb hg_union
  -- `Ψ (x, y) ≡ diagMapCLMRectHs x y` is definitional; rewriting it first aligns
  -- the heads on both sides, so the final `exact` only unifies arguments pointwise
  -- instead of `whnf`-ing through the CFC instance stack.
  have hΨeq : ∀ (x : HSOp (Nat.succ l)) (y : HSOp (Nat.succ k)),
      Ψ (x, y) = diagMapCLMRectHs (k := l) (l := k) x y := fun _ _ => rfl
  have h := hmap.symm.trans (congrArg Ψ hprod)
  simp only [hΨeq] at h
  exact h

/-- Functional-calculus transport across the compressed J-argument operator: the
negated shifted CFC `fun t ↦ -(f (t + p))` of
`StrictlyPositive.ambientJArgOperator Φ A B` equals the rectangular block diagonal
`diagMapCLMRectHs` of the two componentwise CFCs
`StrictlyPositive.ambientShiftedFirstCFC` and
`StrictlyPositive.ambientShiftedSecondCFC`. -/
theorem StrictlyPositive.ambientJArgCFC_eq_diagMapCLM
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
    letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : ContinuousFunctionalCalculus ℝ
        (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
      strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
    HansenPedersen.cfcR
        (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) =
      diagMapCLMRectHs (k := l) (l := k)
        (StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p)
        (StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ (Nat.succ l))
      (β := Mₙ (Nat.succ k))
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ (Nat.succ l))
      (β := Mₙ (Nat.succ k))
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    @WithLp.instProdInnerProductSpace ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
      inferInstance
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    inferInstance
  let g : ℝ → ℝ := StrictlyPositive.shiftedNegFn f p
  let a : HSOp (Nat.succ l) := StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1
  let b : HSOp (Nat.succ k) := StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1
  have ha : IsSelfAdjoint a := by
    simpa [a, hsAdjoint] using
      StrictlyPositive.ambientFirstOperator_isSelfAdjoint
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hb : IsSelfAdjoint b := by
    simpa [b, hsAdjoint] using
      StrictlyPositive.ambientSecondOperator_isSelfAdjoint
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hσa : spectrum ℝ a ⊆ HansenPedersen.halfOpenRay ⊤ := by
    simpa [a] using
      StrictlyPositive.spectrum_ambientFirstOperator_subset_halfOpenRay
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hσb : spectrum ℝ b ⊆ HansenPedersen.halfOpenRay ⊤ := by
    simpa [b] using
      StrictlyPositive.spectrum_ambientSecondOperator_subset_halfOpenRay
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hg_union : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b) := by
    refine (HansenPedersen.continuousOn_shift_Ici (f := f) hf hp).neg.mono ?_
    intro x hx
    cases hx with
    | inl hxa => exact hσa hxa
    | inr hxb => exact hσb hxb
  -- Only the `JArgOperator = diagMapCLMRectHs ...` step is propositional; the
  -- `map_cfc`/product-CFC transport is the atom-level private lemma above, and the
  -- remaining gaps (`cfcR ≡ cfc`, `hsCfcR ≡ cfc`, the local `let`s) are definitional.
  rw [StrictlyPositive.ambientJArgOperator_eq_diagMapCLM
    (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1]
  exact cfc_diagMapCLMRectHs_of_isSelfAdjoint ha hb hg_union

/-- The compressed right-hand side of the shifted inverse inequality: the
codomain-first off-diagonal contraction `C` conjugating the negated shifted CFC
`fun t ↦ -(f (t + p))` of `StrictlyPositive.ambientDiagOperator Φ A B`, i.e.
`star C * cfcR (…) (ambientDiagOperator …) * C` on the paired `L²` space. -/
noncomputable def StrictlyPositive.shiftedAmbientRhs
    (f : ℝ → ℝ) {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) (p : ℝ) :
    @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) :=
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : ContinuousFunctionalCalculus ℝ
      (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
    strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
  star (StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1) *
    HansenPedersen.cfcR
      (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (StrictlyPositive.shiftedNegFn f p)
      (StrictlyPositive.ambientDiagOperator Φ A B) *
    StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1

-- This specialized cross-space `diagMapCLM` statement is expensive to unfold at the theorem header.
/-- Rewrites `StrictlyPositive.shiftedAmbientRhs` as a rectangular block diagonal
`diagMapCLMRectHs`, whose two blocks are the contraction-conjugated negated shifted
domain and codomain CFCs. -/
theorem StrictlyPositive.shiftedAmbientRhs_eq_diagMapCLM
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    StrictlyPositive.shiftedAmbientRhs f Φ A B hPos hB hΦ1 p =
      diagMapCLMRectHs (k := l) (l := k)
        ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
          (((-StrictlyPositive.shiftedDomainCFC f Φ A B p)).comp
            (StrictlyPositive.contraction Φ hPos hB hΦ1)))
        ((StrictlyPositive.contraction Φ hPos hB hΦ1).comp
          (((-StrictlyPositive.shiftedCodomainCFC f Φ A B p)).comp
            (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))) := by
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : ContinuousFunctionalCalculus ℝ
      (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
    strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
  have hdiag :
      HansenPedersen.cfcR
          (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
          (StrictlyPositive.shiftedNegFn f p)
          (StrictlyPositive.ambientDiagOperator Φ A B) =
        diagMapCLMRectHs (k := l) (l := k)
          (-StrictlyPositive.shiftedCodomainCFC f Φ A B p)
          (-StrictlyPositive.shiftedDomainCFC f Φ A B p) :=
    StrictlyPositive.shiftedAmbientCFC_eq_diagMapCLM
      (f := f) hf (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 hp
  rw [StrictlyPositive.shiftedAmbientRhs]
  rw [hdiag]
  exact
    StrictlyPositive.offDiagContractionCodomainFirst_star_mul_diagMapCLM_generic
      (Φ := Φ) (hPos := hPos) (hB := hB) (hΦ1 := hΦ1)
      (TΦ := -StrictlyPositive.shiftedCodomainCFC f Φ A B p)
      (TA := -StrictlyPositive.shiftedDomainCFC f Φ A B p)

/-- The ambient block-diagonal operator `StrictlyPositive.ambientDiagOperator Φ A B`
is self-adjoint, being the rectangular block diagonal of the self-adjoint
J-arguments `jArg (Φ A) (Φ B)` and `jArg A B`. -/
theorem StrictlyPositive.ambientDiagOperator_isSelfAdjoint
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    IsSelfAdjoint (StrictlyPositive.ambientDiagOperator Φ A B) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  simpa [StrictlyPositive.ambientDiagOperator] using
    (@HansenPedersen.Internal.isSelfAdjoint_diagMapCLM (Mₙ (Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      (Mₙ (Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ k))
      (jArg (Φ A) (Φ B)) (jArg A B)
      (jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB)
      (jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB))

/-- The spectrum of `StrictlyPositive.ambientDiagOperator Φ A B` lies in the
half-open ray `HansenPedersen.halfOpenRay ⊤`, since each block J-argument has
spectrum bounded below by a positive number. -/
theorem StrictlyPositive.spectrum_ambientDiagOperator_subset_halfOpenRay
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    spectrum ℝ (StrictlyPositive.ambientDiagOperator Φ A B) ⊆
      HansenPedersen.halfOpenRay ⊤ := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  simpa [StrictlyPositive.ambientDiagOperator] using
    (@spectrum_diagMapCLMRect_subset_halfOpenRay
      (Mₙ (Nat.succ l))
      (Mₙ (Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ k))
      ⊤
      (jArg (Φ A) (Φ B))
      (jArg A B)
      (jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB)
      (jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB)
      (spectrum_jArg_subset_halfOpenRay_top hΦA hΦB)
      (spectrum_jArg_subset_halfOpenRay_top hA hB))

/-- Shifted inverse inequality on the ambient paired space: the negated shifted CFC
`fun t ↦ -(f (t + p))` of the compressed J-argument operator is dominated by the
compressed right-hand side `StrictlyPositive.shiftedAmbientRhs`, obtained by
applying the `ShiftedInverseInequalityNeg f` hypothesis to the contraction. -/
theorem StrictlyPositive.shiftedAmbient_inverseInequality
    (f : ℝ → ℝ)
    (_hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hshiftII : ShiftedInverseInequalityNeg f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
    letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : ContinuousFunctionalCalculus ℝ
        (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
      strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
    HansenPedersen.cfcR
        (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) ≤
      StrictlyPositive.shiftedAmbientRhs f Φ A B hPos hB hΦ1 p := by
  letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
  letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
    strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
  letI : ContinuousFunctionalCalculus ℝ
      (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
    strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
  have hIIp := hshiftII hp
  have hAself :
      IsSelfAdjoint (StrictlyPositive.ambientDiagOperator Φ A B) :=
    StrictlyPositive.ambientDiagOperator_isSelfAdjoint
      (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hσA :
      spectrum ℝ (StrictlyPositive.ambientDiagOperator Φ A B) ⊆
        HansenPedersen.halfOpenRay ⊤ :=
    StrictlyPositive.spectrum_ambientDiagOperator_subset_halfOpenRay
      (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hCnorm :
      ‖StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1‖ ≤ 1 :=
    by
      letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
      letI := instMatrixNormedSpace (n := Nat.succ l)
      letI := instMatrixInnerProductSpace (n := Nat.succ l)
      letI := instMatrixCompleteSpace (n := Nat.succ l)
      letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
      letI := instMatrixNormedSpace (n := Nat.succ k)
      letI := instMatrixInnerProductSpace (n := Nat.succ k)
      letI := instMatrixCompleteSpace (n := Nat.succ k)
      let C :
          WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)) →L[ℂ]
            WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)) :=
        StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1
      change ‖C‖ ≤ 1
      rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
      intro x
      simpa [C, StrictlyPositive.offDiagContractionCodomainFirstPair] using
        StrictlyPositive.offDiagContractionCodomainFirst_contractive
          (Φ := Φ) (hPos := hPos) (hSch := hSch) (hB := hB) (hΦ1 := hΦ1) x
  -- Both sides are definitional unfoldings (`JArgOperator` is literally
  -- `star C * DiagOperator * C` and `ShiftedAmbientRhs` is
  -- `star C * cfcR ... DiagOperator * C`), so the specialized `ConditionII`
  -- instance closes the goal by `exact`, without re-normalizing the large cross-space
  -- expression by `simpa`.
  have h :=
    hIIp
      (K := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (A := StrictlyPositive.ambientDiagOperator Φ A B)
      (C := StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1)
      hAself hσA hCnorm
  assumption

/-- First-component compressed residual: the contraction `V` conjugating the negated
shifted domain CFC, i.e. `V* ∘ (-shiftedDomainCFC f Φ A B p) ∘ V`, as an operator
on `HSOp (l + 1)`. -/
noncomputable def StrictlyPositive.shiftedAmbientFirstRhs
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ l) :=
  (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
    (((-StrictlyPositive.shiftedDomainCFC f Φ A B p)).comp
      (StrictlyPositive.contraction Φ hPos hB hΦ1))

/-- Un-negated core of `StrictlyPositive.shiftedAmbientFirstRhs`: the contraction `V`
conjugating the shifted domain CFC, `V* ∘ (shiftedDomainCFC f Φ A B p) ∘ V`. -/
noncomputable def StrictlyPositive.shiftedAmbientFirstRhsCore
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ l) :=
  (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
    ((StrictlyPositive.shiftedDomainCFC f Φ A B p).comp
      (StrictlyPositive.contraction Φ hPos hB hΦ1))

/-- Second-component compressed residual: the adjoint contraction conjugating the
negated shifted codomain CFC, i.e. `V ∘ (-shiftedCodomainCFC f Φ A B p) ∘ V*`, as
an operator on `HSOp (k + 1)`. -/
noncomputable def StrictlyPositive.shiftedAmbientSecondRhs
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ k) :=
  (StrictlyPositive.contraction Φ hPos hB hΦ1).comp
    (((-StrictlyPositive.shiftedCodomainCFC f Φ A B p)).comp
      (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))

/-- Un-negated core of `StrictlyPositive.shiftedAmbientSecondRhs`: the adjoint
contraction conjugating the shifted codomain CFC,
`V ∘ (shiftedCodomainCFC f Φ A B p) ∘ V*`. -/
noncomputable def StrictlyPositive.shiftedAmbientSecondRhsCore
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ k) :=
  (StrictlyPositive.contraction Φ hPos hB hΦ1).comp
    ((StrictlyPositive.shiftedCodomainCFC f Φ A B p).comp
      (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))

/-- First-component left-hand side of the residual comparison, definitionally equal
to `StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p`. -/
noncomputable def StrictlyPositive.shiftedAmbientFirstLhs
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ l) :=
  StrictlyPositive.ambientShiftedFirstCFC f Φ A B hPos hB hΦ1 p

/-- Second-component left-hand side of the residual comparison, definitionally equal
to `StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p`. -/
noncomputable def StrictlyPositive.shiftedAmbientSecondLhs
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ k) :=
  StrictlyPositive.ambientShiftedSecondCFC f Φ A B hPos hB hΦ1 p

namespace StrictlyPositive

/-- The first-component residual inequality packaged as a proposition:
`shiftedAmbientFirstLhs f Φ A B … p ≤ shiftedAmbientFirstRhs f Φ A B … p`. -/
def ShiftedAmbientFirstLE
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : Prop :=
  StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p ≤
    StrictlyPositive.shiftedAmbientFirstRhs f Φ A B hPos hB hΦ1 p

end StrictlyPositive

/-- `StrictlyPositive.shiftedAmbientFirstLhs` is self-adjoint, being a real
functional calculus of the self-adjoint first ambient operator. -/
theorem StrictlyPositive.shiftedAmbientFirstLhs_isSelfAdjoint
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} :
    IsSelfAdjoint (StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) := by
  have hself :
      IsSelfAdjoint (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) := by
    simpa [hsAdjoint] using
      StrictlyPositive.ambientFirstOperator_isSelfAdjoint
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  simp [StrictlyPositive.shiftedAmbientFirstLhs,
    StrictlyPositive.ambientShiftedFirstCFC, hsCfcR]

/-- `StrictlyPositive.shiftedAmbientFirstRhsCore` is self-adjoint, being the
contraction-conjugation `V* ∘ J ∘ V` of the self-adjoint shifted domain CFC `J`. -/
theorem StrictlyPositive.shiftedAmbientFirstRhsCore_isSelfAdjoint
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} :
    IsSelfAdjoint (StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) := by
  let J : HSOp (Nat.succ k) := StrictlyPositive.shiftedDomainCFC f Φ A B p
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hJself : IsSelfAdjoint J := by
    have hArg : IsSelfAdjoint (jArg A B) := by
      simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
    simp [J, StrictlyPositive.shiftedDomainCFC]
  have hJ : hsAdjoint J = J := by
    simpa [hsAdjoint] using hJself
  have hAdj :
      hsAdjoint (StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) =
        StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p := by
    simpa [J, V, StrictlyPositive.shiftedAmbientFirstRhsCore] using
      hsAdjoint_directRectOp (V := V) (TA := J) hJself
  simpa [hsAdjoint] using hAdj

/-- The quadratic form of `StrictlyPositive.shiftedAmbientFirstRhsCore` at `X` equals
the quadratic form of the shifted domain CFC evaluated at the contracted argument
`StrictlyPositive.contraction Φ hPos hB hΦ1 X`. -/
theorem StrictlyPositive.shiftedAmbientFirstRhsCore_qform_eq_shiftedDomain_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ}
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
              (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
  simpa [StrictlyPositive.shiftedAmbientFirstRhsCore] using
    hsQForm_hsAdjoint_comp
      (StrictlyPositive.contraction Φ hPos hB hΦ1)
      (StrictlyPositive.shiftedDomainCFC f Φ A B p)
      X

/-- The quadratic form of `StrictlyPositive.shiftedAmbientSecondRhsCore` at `X` equals
the quadratic form of the shifted codomain CFC evaluated at the adjoint-contracted
argument `(hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X`. -/
theorem StrictlyPositive.shiftedAmbientSecondRhsCore_qform_eq_shiftedCodomain_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ}
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X) *
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p)
              ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X)))) := by
  simpa [StrictlyPositive.shiftedAmbientSecondRhsCore] using
    hsQForm_comp_hsAdjoint
      (StrictlyPositive.contraction Φ hPos hB hΦ1)
      (StrictlyPositive.shiftedCodomainCFC f Φ A B p)
      X

/-- The shifted inverse inequality with its right-hand side rewritten as a
rectangular block diagonal `diagMapCLMRectHs` of `shiftedAmbientFirstRhs` and
`shiftedAmbientSecondRhs`. -/
theorem StrictlyPositive.shiftedAmbient_inverseInequality_diag
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hshiftII : ShiftedInverseInequalityNeg f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
    letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : ContinuousFunctionalCalculus ℝ
        (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
      strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
    HansenPedersen.cfcR
        (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) ≤
      diagMapCLMRectHs (k := l) (l := k)
        (StrictlyPositive.shiftedAmbientFirstRhs f Φ A B hPos hB hΦ1 p)
        (StrictlyPositive.shiftedAmbientSecondRhs f Φ A B hPos hB hΦ1 p) := by
  have hmain := StrictlyPositive.shiftedAmbient_inverseInequality
    (f := f) hf (Φ := Φ) (A := A) (B := B) hshiftII hPos hSch hA hB hΦ1 hp
  rw [StrictlyPositive.shiftedAmbientRhs_eq_diagMapCLM
    (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 hp] at hmain
  exact hmain

/-- `StrictlyPositive.shiftedAmbientFirstRhs` is the negation of its core
`StrictlyPositive.shiftedAmbientFirstRhsCore`. -/
theorem StrictlyPositive.shiftedAmbientFirstRhs_eq_neg_core
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} :
    StrictlyPositive.shiftedAmbientFirstRhs f Φ A B hPos hB hΦ1 p =
      -StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p := by
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let T : HSOp (Nat.succ k) := StrictlyPositive.shiftedDomainCFC f Φ A B p
  ext X i j
  have happly :
      (hsAdjoint V) (((-T).comp V) X) = -((hsAdjoint V) ((T.comp V) X)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, (hsAdjoint V).map_neg]
  exact congrArg (fun Y => Y i j) happly

/-- `StrictlyPositive.shiftedAmbientSecondRhs` is the negation of its core
`StrictlyPositive.shiftedAmbientSecondRhsCore`. -/
theorem StrictlyPositive.shiftedAmbientSecondRhs_eq_neg_core
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} :
    StrictlyPositive.shiftedAmbientSecondRhs f Φ A B hPos hB hΦ1 p =
      -StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p := by
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let T : HSOp (Nat.succ l) := StrictlyPositive.shiftedCodomainCFC f Φ A B p
  ext X i j
  have happly :
      V (((-T).comp (hsAdjoint V)) X) = -(V ((T.comp (hsAdjoint V)) X)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, V.map_neg]
  exact congrArg (fun Y => Y i j) happly

/-- The shifted inverse inequality with right-hand side written as the block diagonal
of the negated cores `-shiftedAmbientFirstRhsCore` and
`-shiftedAmbientSecondRhsCore`. -/
theorem StrictlyPositive.shiftedAmbient_inverseInequality_diag_core
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hshiftII : ShiftedInverseInequalityNeg f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    letI : NormedAddCommGroup (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l)
    letI : NormedSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairNormedSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : InnerProductSpace ℂ (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : CompleteSpace (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k))) :=
      strictEquivShiftedPairCompleteSpace (k := Nat.succ k) (l := Nat.succ l)
    letI : ContinuousFunctionalCalculus ℝ
        (HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))) IsSelfAdjoint :=
      strictEquivShiftedPairRealCFC (k := Nat.succ k) (l := Nat.succ l)
    HansenPedersen.cfcR
        (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
        (StrictlyPositive.shiftedNegFn f p)
        (StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1) ≤
      diagMapCLMRectHs (k := l) (l := k)
        (-StrictlyPositive.shiftedAmbientFirstRhsCore f Φ A B hPos hB hΦ1 p)
        (-StrictlyPositive.shiftedAmbientSecondRhsCore f Φ A B hPos hB hΦ1 p) := by
  simpa [StrictlyPositive.shiftedAmbientFirstRhs_eq_neg_core
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1,
    StrictlyPositive.shiftedAmbientSecondRhs_eq_neg_core
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1] using
    StrictlyPositive.shiftedAmbient_inverseInequality_diag
      (f := f) hf (Φ := Φ) (A := A) (B := B) hshiftII hPos hSch hA hB hΦ1 hp

end MatrixScopedInstances
end HiaiPetz
