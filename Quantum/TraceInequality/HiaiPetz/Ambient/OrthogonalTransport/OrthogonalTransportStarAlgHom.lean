/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.OrthogonalTransport.OrthogonalTransportAlgebra
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagHilbertSpace
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagRestrictedFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagPositivity
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.RestrictedContinuity
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagEquiv
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Star-algebra homs for orthogonal two-block transport

This module isolates the star-algebra homomorphisms and transported CFC image
used by the final orthogonal-transport bridge.  It packages the pair of
component `jArg` operators on `WithLp 2 (Mₙ n × Mₙ n)`, transports them through
the diagonal and orthogonal decompositions, and produces the ambient
Hilbert-Schmidt operator used downstream.

## Main results

* `twoBlockDiagOrthogonalConjStarAlgHom`,
  `twoBlockDiagOrthogonalDiagStarAlgHom`, and
  `twoBlockDiagOrthogonalTransportStarAlgHom`: the star-algebra homomorphisms
  composing the orthogonal transport.
* `cfcJArgWithLpMatrixPair`: the pair of diagonal/crossed `jArg` operators on
  the `WithLp` matrix pair space.
* `orthogonalTransportCfcImage`: the ambient image of applying CFC componentwise
  and transporting it through the orthogonal two-block construction.

## References

* Internal CFC transport layer for the finite-dimensional Hiai-Petz
  two-block construction.
-/

namespace HiaiPetz

open HiaiPetz.AmbientInstances

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroupBase
  instTwoBlockDiagOrthogonalPairSpaceNormedSpaceBase
  instTwoBlockDiagOrthogonalPairSpaceInnerProductSpaceBase
  instTwoBlockDiagOrthogonalPairSpaceCompleteSpaceBase
  instWithLpMatrixPairNormedAddCommGroup
  instWithLpMatrixPairNormedSpace'
  instWithLpMatrixPairInnerProductSpace'
  instWithLpMatrixPairCompleteSpace'

noncomputable section MatrixScopedInstances
-- Building this star hom requires the full orthogonal-decomposition instance stack.
/-- Star-algebra homomorphism that conjugates endomorphisms of the orthogonal
two-block pair space back to ambient Hilbert-Schmidt operators on `M_{2n}`. -/
noncomputable def twoBlockDiagOrthogonalConjStarAlgHom (n : ℕ) :
    cfcJArgTwoBlockDiagOrthogonalPairEnd n →⋆ₐ[ℂ]
      HSOp (2 * n) :=
  by
    letI : NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroup
    letI : NormedSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceNormedSpace
    letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceInnerProductSpace
    letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
    letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
    letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
    letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
    letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
    let e : twoBlockDiagOrthogonalPairSpace n ≃ₗᵢ[ℂ] Mₙ (2 * n) := by
      simpa [twoBlockDiagOrthogonalPairSpace] using
        (twoBlockDiagOrthogonalDecomposition n).symm
    let Φ := @LinearIsometryEquiv.conjStarAlgEquiv ℂ
        (inferInstance : RCLike ℂ)
        (twoBlockDiagOrthogonalPairSpace n)
        (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n))
        (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n))
        (instTwoBlockDiagOrthogonalPairSpaceCompleteSpace (n := n))
        (Mₙ (2 * n))
        (instMatrixNormedAddCommGroup (n := 2 * n))
        (instMatrixInnerProductSpace (n := 2 * n))
        (instMatrixCompleteSpace (n := 2 * n))
        e
    exact show
        cfcJArgTwoBlockDiagOrthogonalPairEnd n →⋆ₐ[ℂ]
          HSOp (2 * n)
      by
        simpa [cfcJArgTwoBlockDiagOrthogonalPairEnd, twoBlockDiagOrthogonalPairSpace, HSOp] using
          (StarAlgHomClass.toStarAlgHom Φ)

-- The equality unfolds the induced conjugation equivalence and its CLM maps.
/-- The star-algebra homomorphism `twoBlockDiagOrthogonalConjStarAlgHom` agrees
pointwise with the previously defined orthogonal conjugation equivalence. -/
theorem twoBlockDiagOrthogonalConjStarAlgHom_apply
    {n : ℕ} (T : cfcJArgTwoBlockDiagOrthogonalPairEnd n) :
    twoBlockDiagOrthogonalConjStarAlgHom n T = twoBlockDiagOrthogonalConjStarAlgEquiv n T := by
  letI : NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n) :=
    instTwoBlockDiagOrthogonalPairSpaceNormedAddCommGroup
  letI : NormedSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
    instTwoBlockDiagOrthogonalPairSpaceNormedSpace
  letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n) :=
    instTwoBlockDiagOrthogonalPairSpaceInnerProductSpace
  letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
    instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
  letI : NormedAddCommGroup (Mₙ (2 * n)) := instMatrixNormedAddCommGroup (n := 2 * n)
  letI : NormedSpace ℂ (Mₙ (2 * n)) := instMatrixNormedSpace (n := 2 * n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  let e : twoBlockDiagOrthogonalPairSpace n ≃ₗᵢ[ℂ] Mₙ (2 * n) := by
    simpa [twoBlockDiagOrthogonalPairSpace] using
      (twoBlockDiagOrthogonalDecomposition n).symm
  let Φ := @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (twoBlockDiagOrthogonalPairSpace n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalPairSpace n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalPairSpace n))
      (instTwoBlockDiagOrthogonalPairSpaceCompleteSpace (n := n))
      (Mₙ (2 * n))
      (instMatrixNormedAddCommGroup (n := 2 * n))
      (instMatrixInnerProductSpace (n := 2 * n))
      (instMatrixCompleteSpace (n := 2 * n))
      e
  let prodCLM :
      WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) →L[ℂ]
        (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      (twoBlockDiagSubmodule n) (twoBlockDiagOrthogonalSubmodule n)).toContinuousLinearMap
  let prodSymmCLM :
      (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) →L[ℂ]
        WithLp 2 (twoBlockDiagSubmodule n × twoBlockDiagOrthogonalSubmodule n) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      (twoBlockDiagSubmodule n) (twoBlockDiagOrthogonalSubmodule n)).symm.toContinuousLinearMap
  have he :
      e.toContinuousLinearEquiv.toContinuousLinearMap =
        twoBlockDiagOrthogonalDecompositionSymmCLM n := by
    change
      (twoBlockDiagOrthogonalDecomposition n).symm.toContinuousLinearEquiv.toContinuousLinearMap =
        ((twoBlockDiagSubmodule n).subtypeL.coprod
          (twoBlockDiagOrthogonalSubmodule n).subtypeL).comp
          prodCLM
    rfl
  have he_symm :
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        twoBlockDiagOrthogonalDecompositionCLM n := by
    ext X
    apply WithLp.ofLp_injective
    change
      ((twoBlockDiagOrthogonalDecomposition n) X).ofLp =
        ((twoBlockDiagOrthogonalDecompositionCLM n) X).ofLp
    rw [show ((twoBlockDiagOrthogonalDecomposition n) X).ofLp =
      (((twoBlockDiagOrthogonalDecomposition n) X).fst,
        ((twoBlockDiagOrthogonalDecomposition n) X).snd) by rfl]
    simp [twoBlockDiagOrthogonalDecompositionCLM_ofLp,
      twoBlockDiagOrthogonalDecomposition_fst,
      twoBlockDiagOrthogonalDecomposition_snd]
  have happly :
      Φ T =
        e.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  rw [he, he_symm] at happly
  have hconj :
      twoBlockDiagOrthogonalConjStarAlgHom n T = Φ T := by
    change Φ T = Φ T
    rfl
  calc
    twoBlockDiagOrthogonalConjStarAlgHom n T
        = Φ T := hconj
    _ = twoBlockDiagOrthogonalConjStarAlgEquiv n T := by
            simpa [twoBlockDiagOrthogonalConjStarAlgEquiv] using happly

-- Building this diagonal star hom requires the full pair-space instance stack.
/-- Diagonal star-algebra homomorphism from the product of restricted block
endomorphism algebras to endomorphisms of the orthogonal pair space. -/
noncomputable def twoBlockDiagOrthogonalDiagStarAlgHom (n : ℕ) :
    cfcJArgTwoBlockDiagOrthogonalBlockEndProd n →⋆ₐ[ℂ]
      cfcJArgTwoBlockDiagOrthogonalPairEnd n :=
  by
    letI : CompleteSpace (twoBlockDiagSubmodule n) :=
      instTwoBlockDiagSubmoduleCompleteSpace (n := n)
    letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
      instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
    letI : CompleteSpace ↥(twoBlockDiagSubmodule n) :=
      instTwoBlockDiagSubtypeCompleteSpace (n := n)
    letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
      instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
    let Φ := @HansenPedersen.Internal.diagStarAlgHom
        ↥(twoBlockDiagSubmodule n)
        (inferInstance : NormedAddCommGroup ↥(twoBlockDiagSubmodule n))
        (inferInstance : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n))
        (instTwoBlockDiagSubtypeCompleteSpace (n := n))
        ↥(twoBlockDiagOrthogonalSubmodule n)
        (inferInstance : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n))
        (inferInstance : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n))
        (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
    simpa [cfcJArgTwoBlockDiagOrthogonalBlockEndProd,
      cfcJArgTwoBlockDiagOrthogonalPairEnd, twoBlockDiagOrthogonalPairSpace] using
      Φ

/-- Star-algebra equivalence transporting operators on the explicit
off-diagonal submodule to operators on the orthogonal complement model. -/
noncomputable def twoBlockDiagOrthogonalOffDiagConjStarAlgEquiv (n : ℕ) :
    (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) := by
  letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n) :=
    inferInstance
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  let od : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
    offDiagOrthogonalEquiv n
  exact @LinearIsometryEquiv.conjStarAlgEquiv ℂ
    (inferInstance : RCLike ℂ)
    (offDiagSubmodule n)
    (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
    (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
    (instOffDiagSubtypeCompleteSpace (n := n))
    (twoBlockDiagOrthogonalSubmodule n)
    (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n))
    (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n))
    (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
    od

/-- Product algebra of two endomorphism algebras on the `WithLp` matrix pair
space, used to hold the diagonal and crossed `jArg` CFC components together. -/
noncomputable def cfcJArgWithLpMatrixPairEndProd (n : ℕ) :=
  ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
    ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))

/-- Normed additive group structure on the product of two pair-space
endomorphism algebras, inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      NormedAddCommGroup
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Complex normed-space structure on the product of two pair-space endomorphism
algebras, inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdNormedSpace (n : ℕ) :
    NormedSpace ℂ (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      NormedSpace ℂ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Semiring structure on the product of two pair-space endomorphism algebras,
inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdSemiring (n : ℕ) :
    Semiring (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      Semiring
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Ring structure on the product of two pair-space endomorphism algebras,
inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdRing (n : ℕ) :
    Ring (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      Ring
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Star structure on the product of two pair-space endomorphism algebras,
inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdStar (n : ℕ) :
    Star (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      Star
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Star-ring structure on the product of two pair-space endomorphism algebras,
inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdStarRing (n : ℕ) :
    StarRing (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      StarRing
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Complex algebra structure on the product of two pair-space endomorphism
algebras, inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdAlgebra (n : ℕ) :
    Algebra ℂ (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      Algebra ℂ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Real scalar multiplication on the product of two pair-space endomorphism
algebras, inherited through the complex operator algebra. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdSMulReal (n : ℕ) :
    SMul ℝ (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      SMul ℝ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Real algebra structure on the product of two pair-space endomorphism
algebras, inherited componentwise. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdAlgebraReal (n : ℕ) :
    Algebra ℝ (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      Algebra ℝ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- Scalar-tower compatibility between real and complex scalars for the product
of pair-space endomorphism algebras. -/
noncomputable instance instCfcJArgWithLpMatrixPairEndProdIsScalarTower (n : ℕ) :
    IsScalarTower ℝ ℂ (cfcJArgWithLpMatrixPairEndProd n) := by
  simpa [cfcJArgWithLpMatrixPairEndProd] using
    (inferInstance :
      IsScalarTower ℝ ℂ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
          ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))))

/-- The diagonal component of the pair-space `jArg` data, with entries
`jArg A₁ B₁` and `jArg A₂ B₂`. -/
noncomputable def cfcJArgWithLpMatrixPairFst {n : ℕ}
    (A₁ A₂ B₁ B₂ : Mₙ n) :
    (WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)) :=
  matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)

/-- The crossed component of the pair-space `jArg` data, with entries
`jArg A₁ B₂` and `jArg A₂ B₁`. -/
noncomputable def cfcJArgWithLpMatrixPairSnd {n : ℕ}
    (A₁ A₂ B₁ B₂ : Mₙ n) :
    (WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)) :=
  matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)

/-- The pair of diagonal and crossed pair-space `jArg` operators used as the
input to the orthogonal transport star-algebra homomorphism. -/
noncomputable def cfcJArgWithLpMatrixPair {n : ℕ}
    (A₁ A₂ B₁ B₂ : Mₙ n) : cfcJArgWithLpMatrixPairEndProd n :=
  (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂,
    cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂)

/-- The diagonal pair-space `jArg` operator is self-adjoint when the two `B`
blocks are positive definite and the two `A` blocks are self-adjoint. -/
theorem cfcJArgWithLpMatrixPairFst_isSelfAdjoint {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    IsSelfAdjoint (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂) := by
  have hJ₁₁ : IsSelfAdjoint (jArg A₁ B₁) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint hA₁ hB₁
  have hJ₂₂ : IsSelfAdjoint (jArg A₂ B₂) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint hA₂ hB₂
  simpa [cfcJArgWithLpMatrixPairFst] using
    (isSelfAdjoint_matrixDiagMapCLM (n := n) hJ₁₁ hJ₂₂)

/-- The crossed pair-space `jArg` operator is self-adjoint under the same
positive-definiteness and self-adjointness hypotheses. -/
theorem cfcJArgWithLpMatrixPairSnd_isSelfAdjoint {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    IsSelfAdjoint (cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂) := by
  have hJ₁₂ : IsSelfAdjoint (jArg A₁ B₂) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint hA₁ hB₂
  have hJ₂₁ : IsSelfAdjoint (jArg A₂ B₁) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint hA₂ hB₁
  simpa [cfcJArgWithLpMatrixPairSnd] using
    (isSelfAdjoint_matrixDiagMapCLM (n := n) hJ₁₂ hJ₂₁)

/-- The product-valued pair of diagonal and crossed `jArg` operators is
self-adjoint componentwise. -/
theorem cfcJArgWithLpMatrixPair_isSelfAdjoint {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    let K := WithLp 2 (Mₙ n × Mₙ n)
    IsSelfAdjoint
      ((cfcJArgWithLpMatrixPair (n := n) A₁ A₂ B₁ B₂ :
        (K →L[ℂ] K) × (K →L[ℂ] K))) := by
  let K := WithLp 2 (Mₙ n × Mₙ n)
  have hJ₁ :
      IsSelfAdjoint (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂ : K →L[ℂ] K) := by
    simpa using
      cfcJArgWithLpMatrixPairFst_isSelfAdjoint
        (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂
  have hJ₂ :
      IsSelfAdjoint (cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂ : K →L[ℂ] K) := by
    simpa using
      cfcJArgWithLpMatrixPairSnd_isSelfAdjoint
        (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂
  change
    star ((cfcJArgWithLpMatrixPair (n := n) A₁ A₂ B₁ B₂ :
      (K →L[ℂ] K) × (K →L[ℂ] K))) =
      (cfcJArgWithLpMatrixPair (n := n) A₁ A₂ B₁ B₂ :
        (K →L[ℂ] K) × (K →L[ℂ] K))
  change
    star
        (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂,
          cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂) =
      (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂,
        cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂)
  exact Prod.ext hJ₁.star_eq hJ₂.star_eq

/-- Unit field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_map_one {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)) :
    ((E₁ (1 :
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))).1,
      E₂ (1 :
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      1 :=
  Prod.ext E₁.map_one E₂.map_one

/-- Multiplicativity field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_map_mul {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n))
    (x y : (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))) :
    ((E₁ (x * y).1, E₂ (x * y).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      ((E₁ x.1, E₂ x.2) : cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) *
        ((E₁ y.1, E₂ y.2) : cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) :=
  Prod.ext (E₁.map_mul x.1 y.1) (E₂.map_mul x.2 y.2)

/-- Zero field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_map_zero {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)) :
    ((E₁ (0 :
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))).1,
      E₂ (0 :
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      0 :=
  Prod.ext E₁.map_zero E₂.map_zero

/-- Additivity field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_map_add {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n))
    (x y : (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))) :
    ((E₁ (x + y).1, E₂ (x + y).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      ((E₁ x.1, E₂ x.2) : cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) +
        ((E₁ y.1, E₂ y.2) : cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) :=
  Prod.ext (E₁.map_add x.1 y.1) (E₂.map_add x.2 y.2)

/-- Scalar field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_commutes {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)) (r : ℂ) :
    ((E₁ (algebraMap ℂ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) r).1,
      E₂ (algebraMap ℂ
        (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) r).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      algebraMap ℂ (cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) r :=
  Prod.ext (E₁.toAlgEquiv.commutes r) (E₂.toAlgEquiv.commutes r)

/-- Star field of `twoBlockDiagOrthogonalBlockProdStarAlgHom`. -/
private theorem blockProdStarAlgHom_map_star {n : ℕ}
    (E₁ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n))
    (E₂ : ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
      (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n))
    (x : (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))))) :
    ((E₁ (star x).1, E₂ (star x).2) :
        cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) =
      star ((E₁ x.1, E₂ x.2) : cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) :=
  Prod.ext (E₁.map_star' x.1) (E₂.map_star' x.2)

/-- Star-algebra homomorphism transporting the product of two pair-space
endomorphism algebras into the product of restricted orthogonal block algebras. -/
noncomputable def twoBlockDiagOrthogonalBlockProdStarAlgHom (n : ℕ) :
    (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) →⋆ₐ[ℂ]
      cfcJArgTwoBlockDiagOrthogonalBlockEndProd n := by
  let E₁ :
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
        (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) :=
    (twoBlockDiagSubmoduleConjStarAlgEquiv n).symm
  let E₂ :
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ≃⋆ₐ[ℂ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    ((offDiagSubmoduleConjStarAlgEquiv n).symm).trans
      (twoBlockDiagOrthogonalOffDiagConjStarAlgEquiv n)
  exact
    { toFun := fun p => (E₁ p.1, E₂ p.2)
      map_one' := blockProdStarAlgHom_map_one E₁ E₂
      map_mul' := blockProdStarAlgHom_map_mul E₁ E₂
      map_zero' := blockProdStarAlgHom_map_zero E₁ E₂
      map_add' := blockProdStarAlgHom_map_add E₁ E₂
      commutes' := blockProdStarAlgHom_commutes E₁ E₂
      map_star' := blockProdStarAlgHom_map_star E₁ E₂ }

/-- Composite star-algebra homomorphism from the pair of pair-space CFC
operators all the way to an ambient Hilbert-Schmidt operator on `M_{2n}`. -/
noncomputable def twoBlockDiagOrthogonalTransportStarAlgHom (n : ℕ) :
    (((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) ×
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n)))) →⋆ₐ[ℂ]
      HSOp (2 * n) :=
  ((twoBlockDiagOrthogonalConjStarAlgHom n).comp
      (twoBlockDiagOrthogonalDiagStarAlgHom n)).comp
    (twoBlockDiagOrthogonalBlockProdStarAlgHom n)

/-- Ambient CFC image obtained by applying `HansenPedersen.cfcR f` to the
diagonal and crossed pair-space `jArg` operators and transporting the pair
through the orthogonal two-block star-algebra homomorphism. -/
noncomputable def orthogonalTransportCfcImage {n : ℕ} (f : ℝ → ℝ)
    {A₁ A₂ B₁ B₂ : Mₙ n} :
    HSOp (2 * n) := by
  let K := WithLp 2 (Mₙ n × Mₙ n)
  letI : CStarAlgebra (K →L[ℂ] K) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace K inferInstance inferInstance
      inferInstance
  letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  exact
    twoBlockDiagOrthogonalTransportStarAlgHom n
      (HansenPedersen.cfcR (ℋ := K) f
          (cfcJArgWithLpMatrixPairFst (n := n) A₁ A₂ B₁ B₂),
        HansenPedersen.cfcR (ℋ := K) f
          (cfcJArgWithLpMatrixPairSnd (n := n) A₁ A₂ B₁ B₂))

end MatrixScopedInstances

end HiaiPetz
