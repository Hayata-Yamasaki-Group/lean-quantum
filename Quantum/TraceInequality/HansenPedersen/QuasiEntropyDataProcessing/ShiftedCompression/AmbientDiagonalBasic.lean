/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.Internal.ShiftedCompressionInstances
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardCompression

/-!
Shifted strict-output compression inequalities for the inverse/direct equivalence.

This file contains the shifted ambient compression operators and the quadratic-form
comparison layer used by the residual equivalence theorem.
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

/-- Section-local alias for the Hilbert–Schmidt normed additive group structure on `Mₙ n`; the
single source of truth is `instMatrixNormedAddCommGroup`. -/
private noncomputable abbrev strictEquivShiftedMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (Mₙ n) :=
  instMatrixNormedAddCommGroup (n := n)

/-- Section-local alias for the complex normed-space structure on `Mₙ n`; the single source of
truth is `instMatrixNormedSpace`. -/
private noncomputable abbrev strictEquivShiftedMatrixNormedSpace {n : ℕ} : NormedSpace ℂ
  (Mₙ n) :=
  instMatrixNormedSpace (n := n)

/-- Section-local alias for the complex inner-product-space structure on `Mₙ n`; the single source
of truth is `instMatrixInnerProductSpace`. -/
private noncomputable abbrev strictEquivShiftedMatrixInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ (Mₙ n) :=
  instMatrixInnerProductSpace (n := n)

/-- Section-local alias for completeness of `Mₙ n`; the single source of truth is
`instMatrixCompleteSpace`. -/
private noncomputable abbrev strictEquivShiftedMatrixCompleteSpace {n : ℕ} : CompleteSpace
  (Mₙ n) :=
  instMatrixCompleteSpace (n := n)

/-- Section-local alias for the C⋆-algebra structure on the Hilbert–Schmidt operator algebra
`HSOp n` (bounded operators on `Mₙ n`). -/
private noncomputable abbrev strictEquivShiftedCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Section-local alias for the complex continuous functional calculus on star-normal elements of
`HSOp n`. -/
private noncomputable abbrev strictEquivShiftedComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- Section-local alias for the real continuous functional calculus on self-adjoint elements of
`HSOp n`. -/
private noncomputable abbrev strictEquivShiftedRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- Shifted codomain CFC keeps the specialized matrix CFC head from timing out.
/-- The `p`-shifted codomain functional calculus:
`hsCfcR (fun t ↦ f (t + p)) (jArg (Φ A) (Φ B))`, an operator in `HSOp (l+1)`. -/
noncomputable def StrictlyPositive.shiftedCodomainCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (p : ℝ) : HSOp (Nat.succ l) :=
  hsCfcR (fun t : ℝ ↦ f (t + p)) (jArg (Φ A) (Φ B))

-- Shifted domain CFC keeps the specialized matrix CFC head from timing out.
/-- The `p`-shifted domain functional calculus:
`hsCfcR (fun t ↦ f (t + p)) (jArg A B)`, an operator in `HSOp (k+1)`. -/
noncomputable def StrictlyPositive.shiftedDomainCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (_Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (p : ℝ) : HSOp (Nat.succ k) :=
  hsCfcR (fun t : ℝ ↦ f (t + p)) (jArg A B)

/-- The block-diagonal ambient operator on the `L²` pair space
`WithLp 2 (Mₙ (l+1) × Mₙ (k+1))` with codomain block `jArg (Φ A) (Φ B)` and domain block
`jArg A B`, assembled through `diagMapCLM`. -/
noncomputable def StrictlyPositive.ambientDiagOperator
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k)) :
    @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) :=
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  @HansenPedersen.Internal.diagMapCLM
    (Mₙ (Nat.succ l))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))
    (Mₙ (Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (jArg (Φ A) (Φ B)) (jArg A B)

/-- Repackages `StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1` as an operator on
the ambient `L²` pair space `WithLp 2 (Mₙ (l+1) × Mₙ (k+1))`, so it shares the
  section-local pair
instances used by the shifted operators. -/
private noncomputable abbrev offDiagABINormedAddCommGroup {k l : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ l × Mₙ k)) :=
  WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ l) (β := Mₙ k)

private noncomputable abbrev offDiagABIInnerProductSpace {k l : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ l × Mₙ k)) :=
  @WithLp.instProdInnerProductSpace ℂ (Mₙ l) (Mₙ k)
    inferInstance
    (instMatrixNormedAddCommGroup (n := l))
    (instMatrixInnerProductSpace (n := l))
    (instMatrixNormedAddCommGroup (n := k))
    (instMatrixInnerProductSpace (n := k))

noncomputable def StrictlyPositive.offDiagContractionCodomainFirstPair
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (offDiagABINormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (offDiagABIInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) :=
  show @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (offDiagABINormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (offDiagABIInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) from
    StrictlyPositive.offDiagContractionCodomainFirst Φ hPos hB hΦ1

-- The shifted ambient CFC crosses the codomain/domain product Hilbert space.
/-- The shifted ambient functional calculus: the real CFC of `fun t ↦ -(f (t + p))` applied to the
block-diagonal ambient operator `ambientDiagOperator Φ A B`, an operator on the `L²` pair
  space. -/
noncomputable def StrictlyPositive.shiftedAmbientCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (p : ℝ) :
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
  HansenPedersen.cfcR
    (ℋ := WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
    (fun t : ℝ ↦ -(f (t + p)))
    (StrictlyPositive.ambientDiagOperator Φ A B)

/-- The block-diagonal ambient operator assembled directly from the negated shifted codomain and
domain functional calculi `-shiftedCodomainCFC f Φ A B p` and `-shiftedDomainCFC f Φ A B p`; the
blockwise companion of `shiftedAmbientCFC`. -/
noncomputable def StrictlyPositive.shiftedAmbientDiagMap
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (p : ℝ) :
    @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (strictEquivShiftedPairNormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (strictEquivShiftedPairInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) :=
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  @HansenPedersen.Internal.diagMapCLM
    (Mₙ (Nat.succ l))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))
    (Mₙ (Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (-StrictlyPositive.shiftedCodomainCFC f Φ A B p)
    (-StrictlyPositive.shiftedDomainCFC f Φ A B p)

/- Instance caches: inside the proofs below the cross-space pair instances are only
available as `letI`-bound local definitions, and let-bound fvars bypass the
discrimination tree, so the CFC / `ContinuousMapClass` / `Algebra ℝ` searches on
`HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))` and on `HSOp l × HSOp k` re-run the
full global derivation at every use site.
Registering the content-named canonical abbrevs as section-level local instances
(they are `abbrev`s, hence reducible) plus a few extra reducible caches turns
each search into a head-match without changing the instance values (same
pattern as `ResidualOperators.lean` in this directory). -/

attribute [local instance] strictEquivShiftedPairCStarAlgebra
  strictEquivShiftedPairComplexCFC strictEquivShiftedPairRealCFC
  strictEquivShiftedCStarAlgebra strictEquivShiftedComplexCFC strictEquivShiftedRealCFC

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache of the real-algebra structure `Algebra ℝ (HSOp n)`,
  registered so
later CFC searches resolve it by a head match instead of re-deriving it. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpShiftedScopedAD {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache of the real-algebra structure `Algebra ℝ (HSOp l × HSOp k)` on
the operator pair, registered for head-match resolution. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpPairShiftedScopedAD {k l : ℕ} :
    Algebra ℝ (HSOp l × HSOp k) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache of the complex continuous functional calculus on star-normal
elements of the operator pair `HSOp l × HSOp k`. -/
@[reducible, local instance]
private noncomputable def instComplexCFCHSOpPairShiftedScopedAD {k l : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp l × HSOp k) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache of the real continuous functional calculus on self-adjoint
elements of the operator pair `HSOp l × HSOp k`. -/
@[reducible, local instance]
private noncomputable def instRealCFCHSOpPairShiftedScopedAD {k l : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp l × HSOp k) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- One-time search for the cache itself; every later use is a head-match.
/-- Reducible section-local cache of the `ContinuousMapClass` instance for the diagonal
star-algebra homomorphism from `HSOp l × HSOp k` into the ambient pair operator algebra. -/
@[reducible, local instance]
private noncomputable def instContinuousMapClassDiagStarAlgHomShiftedScopedAD
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
/-- Reducible section-local cache of the `ContinuousMap.UniqueHom ℝ` instance on the ambient pair
operator algebra `HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))`. -/
@[reducible, local instance]
private noncomputable def instUniqueHomRealLPairShiftedScopedAD {k l : ℕ} :
    ContinuousMap.UniqueHom ℝ
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  inferInstance

/-- CFC transport through the diagonal star-algebra homomorphism on atom
operators: `cfc g` of the block-diagonal operator `diagMapCLM a b` is the block
diagonal of the componentwise `cfc g`.  This is the heavy `map_cfc`/product-CFC
step of `StrictlyPositive.shiftedAmbientCFC_eq_diagMapCLM`, factored out
so that it elaborates once over atom variables instead of over the large
`jArg`/compression terms. -/
private theorem cfc_diagMapCLM_pair_of_isSelfAdjoint {k l : ℕ} {g : ℝ → ℝ}
    {a : HSOp (Nat.succ l)} {b : HSOp (Nat.succ k)}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hg_union : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b)) :
    cfc (R := ℝ) g
        (@HansenPedersen.Internal.diagMapCLM
          (Mₙ (Nat.succ l))
          (instMatrixNormedAddCommGroup (n := Nat.succ l))
          (instMatrixInnerProductSpace (n := Nat.succ l))
          (Mₙ (Nat.succ k))
          (instMatrixNormedAddCommGroup (n := Nat.succ k))
          (instMatrixInnerProductSpace (n := Nat.succ k))
          a b) =
      @HansenPedersen.Internal.diagMapCLM
        (Mₙ (Nat.succ l))
        (instMatrixNormedAddCommGroup (n := Nat.succ l))
        (instMatrixInnerProductSpace (n := Nat.succ l))
        (Mₙ (Nat.succ k))
        (instMatrixNormedAddCommGroup (n := Nat.succ k))
        (instMatrixInnerProductSpace (n := Nat.succ k))
        (hsCfcR g a) (hsCfcR g b) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
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
  have hPsiab : IsSelfAdjoint (Ψ (a, b)) := by
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
    (hφa := hPsiab)
  have hprod : cfc (R := ℝ) g (a, b) = (cfc (R := ℝ) g a, cfc (R := ℝ) g b) := by
    simpa using cfc_map_prod (R := ℝ) (S := ℝ) g a b
      (hf := hg_union) (hab := hab) (ha := ha) (hb := hb)
  -- `Ψ (x, y) ≡ diagMapCLM x y` is definitional; rewriting it first aligns the
  -- heads on both sides, so the final `exact` only unifies arguments pointwise
  -- instead of `whnf`-ing through the CFC instance stack.
  have hPsieq : ∀ (x : HSOp (Nat.succ l)) (y : HSOp (Nat.succ k)),
      Ψ (x, y) =
        @HansenPedersen.Internal.diagMapCLM
          (Mₙ (Nat.succ l))
          (instMatrixNormedAddCommGroup (n := Nat.succ l))
          (instMatrixInnerProductSpace (n := Nat.succ l))
          (Mₙ (Nat.succ k))
          (instMatrixNormedAddCommGroup (n := Nat.succ k))
          (instMatrixInnerProductSpace (n := Nat.succ k))
          x y := fun _ _ => rfl
  have h := hmap.symm.trans (congrArg Ψ hprod)
  simp only [hPsieq] at h
  exact h

/-- The shifted ambient CFC equals its blockwise companion:
`shiftedAmbientCFC f Φ A B p = shiftedAmbientDiagMap f Φ A B p`. The real CFC of the
  block-diagonal
ambient operator is computed block by block, since the diagonal star-algebra homomorphism
intertwines the functional calculus. -/
theorem StrictlyPositive.shiftedAmbientCFC_eq_diagMapCLM
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    {p : ℝ} (hp : 0 < p) :
    StrictlyPositive.shiftedAmbientCFC f Φ A B p =
      StrictlyPositive.shiftedAmbientDiagMap f Φ A B p := by
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
  letI : ContinuousFunctionalCalculus ℂ (HSOp (Nat.succ l) × HSOp (Nat.succ k)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (HSOp (Nat.succ l) × HSOp (Nat.succ k)) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let g : ℝ → ℝ := fun t : ℝ ↦ -(f (t + p))
  let a : HSOp (Nat.succ l) := jArg (Φ A) (Φ B)
  let b : HSOp (Nat.succ k) := jArg A B
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have ha : IsSelfAdjoint a := by
    simpa [a] using jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB
  have hb : IsSelfAdjoint b := by
    simpa [b] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
  have hσa : spectrum ℝ a ⊆ HansenPedersen.halfOpenRay ⊤ := by
    simpa [a] using spectrum_jArg_subset_halfOpenRay_top hΦA hΦB
  have hσb : spectrum ℝ b ⊆ HansenPedersen.halfOpenRay ⊤ := by
    simpa [b] using spectrum_jArg_subset_halfOpenRay_top hA hB
  have hg_union : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b) := by
    refine (HansenPedersen.continuousOn_shift_Ici (f := f) hf hp).neg.mono ?_
    intro x hx
    cases hx with
    | inl hxa => exact hσa hxa
    | inr hxb => exact hσb hxb
  -- The `map_cfc`/product-CFC transport is the atom-level private lemma above;
  -- pulling the negation out of the componentwise CFC (`cfc_neg`) is the only
  -- remaining propositional step, and all other gaps (`cfcR ≡ cfc`,
  -- the direct `hsCfcR` application at `jArg`, the local `let`s and the definitional
  -- unfoldings of the two sides) close by `exact`.
  have hkey := cfc_diagMapCLM_pair_of_isSelfAdjoint (g := g) (a := a) (b := b) ha hb hg_union
  have hnegA : hsCfcR g a = -(hsCfcR (fun t : ℝ ↦ f (t + p)) a) :=
    cfc_neg (f := fun t : ℝ ↦ f (t + p)) (a := a)
  have hnegB : hsCfcR g b = -(hsCfcR (fun t : ℝ ↦ f (t + p)) b) :=
    cfc_neg (f := fun t : ℝ ↦ f (t + p)) (a := b)
  rw [hnegA, hnegB] at hkey
  exact hkey

end MatrixScopedInstances

end HiaiPetz
