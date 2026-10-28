/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagHilbertSpace
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.CompleteCodomain

/-!
# Functional calculus through Hilbert-Schmidt diagonal transport

This module proves that real continuous functional calculus commutes with the
diagonal star-algebra homomorphism on the Hilbert-Schmidt pair space.  The
result is the CFC transport step used by the two-block diagonal `J`-operator
bridges.

## Main results

* `cfcR_diagMapCLM_union`: applying `cfcR g` to a diagonal map with entries
  `a` and `b` is the diagonal map with entries `hsCfcR g a` and
  `hsCfcR g b`, under continuity on the union of the two spectra.

## References

* Internal CFC transport for the finite-dimensional Hiai-Petz construction.
-/

namespace HiaiPetz

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

open scoped Matrix.Norms.Frobenius

noncomputable section MatrixScopedInstances

noncomputable local instance instHsBlockSpaceNormedAddCommGroupCFC {n : ℕ} :
    NormedAddCommGroup (hsBlockSpace n) :=
  HiaiPetz.instHsBlockSpaceNormedAddCommGroup (n := n)

noncomputable local instance instHsBlockSpaceNormedSpaceCFC {n : ℕ} :
    NormedSpace ℂ (hsBlockSpace n) :=
  HiaiPetz.instHsBlockSpaceNormedSpace (n := n)

noncomputable local instance instHsBlockSpaceInnerProductSpaceCFC {n : ℕ} :
    InnerProductSpace ℂ (hsBlockSpace n) :=
  HiaiPetz.instHsBlockSpaceInnerProductSpace (n := n)

noncomputable local instance instHsBlockSpaceCompleteSpaceCFC {n : ℕ} :
    CompleteSpace (hsBlockSpace n) :=
  HiaiPetz.instHsBlockSpaceCompleteSpace (n := n)

private theorem pair_isSelfAdjoint_hsOp {n : ℕ} {a b : HSOp n}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (a, b) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  change star (a, b) = (a, b)
  ext <;> simp [ha.star_eq, hb.star_eq]

/-- Continuity of the diagonal star-algebra homomorphism on the
Hilbert-Schmidt pair space, factored out of `cfcR_diagMapCLM_union` so that the
heavy `WithLp`/`PiLp` coercion unfolding elaborates in its own
declaration. -/
@[fun_prop] private lemma diagStarAlgHom_continuous_hs {n : ℕ} :
    Continuous
      (@HansenPedersen.Internal.diagStarAlgHom (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))) := by
  let e : WithLp 2 (Mₙ n × Mₙ n) ≃L[ℂ] Mₙ n × Mₙ n :=
    WithLp.prodContinuousLinearEquiv 2 ℂ (Mₙ n) (Mₙ n)
  let pre :
      ((Mₙ n × Mₙ n →L[ℂ] Mₙ n × Mₙ n) →L[ℂ]
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] Mₙ n × Mₙ n)) :=
    ((ContinuousLinearMap.compL ℂ (WithLp 2 (Mₙ n × Mₙ n))
      (Mₙ n × Mₙ n) (Mₙ n × Mₙ n)).flip
        (e : (WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] Mₙ n × Mₙ n))
  let post :
      (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] Mₙ n × Mₙ n) →L[ℂ]
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) :=
    ContinuousLinearMap.compL ℂ (WithLp 2 (Mₙ n × Mₙ n)) (Mₙ n × Mₙ n)
      (WithLp 2 (Mₙ n × Mₙ n))
      (e.symm : (Mₙ n × Mₙ n) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))
  simpa [HansenPedersen.Internal.diagStarAlgHom, HansenPedersen.Internal.diagMapCLM,
    e, pre, post, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.prodMapL_apply] using
    post.continuous.comp
      (pre.continuous.comp
        (ContinuousLinearMap.prodMapL ℂ (Mₙ n) (Mₙ n) (Mₙ n) (Mₙ n)).continuous)

/-- Real continuous functional calculus commutes with a continuous star-algebra
homomorphism out of a product of C⋆-algebras (stated over abstract C⋆-algebras so that
the instance search stays cheap). -/
private theorem cfc_map_prod_starAlgHom_hs
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (φ : (A × B) →⋆ₐ[ℂ] C) (hφ : Continuous φ) {f : ℝ → ℝ} {a : A} {b : B}
    (hf : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc (R := ℝ) f (φ (a, b)) = φ (cfc (R := ℝ) f a, cfc (R := ℝ) f b) := by
  letI : IsScalarTower ℝ ℂ A := RestrictScalars.isScalarTower ℝ ℂ A
  letI : IsScalarTower ℝ ℂ B := RestrictScalars.isScalarTower ℝ ℂ B
  letI : IsScalarTower ℝ ℂ C := RestrictScalars.isScalarTower ℝ ℂ C
  letI : IsScalarTower ℝ ℂ (A × B) := Prod.isScalarTower
  letI : ContinuousFunctionalCalculus ℂ (A × B) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let Φ : (A × B) →⋆ₐ[ℝ] C := φ.restrictScalars ℝ
  have hab : IsSelfAdjoint (a, b) := Prod.ext ha hb
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) Φ f (a, b)
    (hf := by rwa [Prod.spectrum_eq]) (hφ := (show Continuous Φ from hφ)) (ha := hab)
    (hφa := hab.map Φ)
  have hprod : cfc (R := ℝ) f (a, b) = (cfc (R := ℝ) f a, cfc (R := ℝ) f b) :=
    cfc_map_prod (R := ℝ) (S := ℝ) (A := A) (B := B) f a b (hf := hf) (hab := hab)
      (ha := ha) (hb := hb)
  rw [hprod] at hmap
  exact hmap.symm

/-- Real continuous functional calculus commutes with the diagonal transport on
the Hilbert-Schmidt pair space, provided the function is continuous on the
union of the two component spectra. -/
theorem cfcR_diagMapCLM_union {n : ℕ} {g : ℝ → ℝ} {a b : HSOp n}
    (hg : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    HansenPedersen.cfcR (ℋ := hsBlockSpace n) g (hsDiagMapCLM a b) =
      hsDiagMapCLM (hsCfcR g a) (hsCfcR g b) := by
  let Φ :
      (HSOp n × HSOp n) →⋆ₐ[ℂ]
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
    @HansenPedersen.Internal.diagStarAlgHom (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
  have hmap := cfc_map_prod_starAlgHom_hs Φ diagStarAlgHom_continuous_hs hg ha hb
  simpa [HansenPedersen.cfcR, Φ] using hmap

end MatrixScopedInstances

end HiaiPetz
