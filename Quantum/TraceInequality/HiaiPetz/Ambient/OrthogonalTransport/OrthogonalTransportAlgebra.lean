/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
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

/-!
# Algebra structures for orthogonal transport

This module isolates the endomorphism algebra and star-algebra instance stack
used by the two-block diagonal orthogonal-transport CFC bridge.  The
constructions here keep the transported CFC argument in the same algebraic
language as the ambient block-diagonal model.

## Main results

* `cfcJArgTwoBlockDiagOrthogonalPairEnd` packages the transported CFC argument
  as a continuous endomorphism algebra on the orthogonal pair space.
* The surrounding instance aliases and transport lemmas supply the algebra,
  star, module, and CFC structure required by downstream comparison theorems.

## References

This is an infrastructure layer for the Hiai--Petz comparison formalization.
-/

namespace HiaiPetz

open HiaiPetz.AmbientInstances

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-!
The following four names are kept as non-instance abbreviations for downstream
files that refer to them explicitly.  Instance search is provided by the scoped
`HiaiPetz.AmbientInstances` namespace opened above.
-/

/-- Non-instance alias for the normed additive group structure on the `WithLp`
matrix-pair model used by downstream transport files. -/
noncomputable abbrev instWithLpMatrixPairNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) :=
  AmbientInstances.instWithLpMatrixPairNormedAddCommGroup

/-- Non-instance alias for the complex normed-space structure on the `WithLp`
matrix-pair model. -/
noncomputable abbrev instWithLpMatrixPairNormedSpace' {n : ℕ} :
    NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
  AmbientInstances.instWithLpMatrixPairNormedSpace'

/-- Non-instance alias for the Hilbert-space structure on the `WithLp` matrix
pair model, used when constructing transported CFC arguments. -/
noncomputable abbrev instWithLpMatrixPairInnerProductSpace' {n : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) :=
  AmbientInstances.instWithLpMatrixPairInnerProductSpace'

/-- Non-instance alias for completeness of the `WithLp` matrix-pair model. -/
noncomputable abbrev instWithLpMatrixPairCompleteSpace' {n : ℕ} :
    CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) :=
  AmbientInstances.instWithLpMatrixPairCompleteSpace'

/-- Endomorphism algebra on the orthogonal pair space that packages the
two-block diagonal and orthogonal components for CFC transport. -/
noncomputable def cfcJArgTwoBlockDiagOrthogonalPairEnd (n : ℕ) :=
  twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n

/-- Product algebra of endomorphisms on the diagonal submodule and its
orthogonal complement. -/
noncomputable def cfcJArgTwoBlockDiagOrthogonalBlockEndProd (n : ℕ) :=
  (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) ×
    (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)

/-- Star operation on endomorphisms of the orthogonal pair space, implemented
as Hilbert-space adjoint. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceEndStar (n : ℕ) :
    Star (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n) where
  star A :=
    letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
    (@ContinuousLinearMap.adjoint ℂ
      (twoBlockDiagOrthogonalPairSpace n) (twoBlockDiagOrthogonalPairSpace n) _ _ _ _ _
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›) A

/-- Involutivity of the adjoint star on endomorphisms of the orthogonal pair
space. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceEndInvolutiveStar (n : ℕ) :
    InvolutiveStar
      (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n) where
  star_involutive A := by
    letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
    change ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) = A
    exact @ContinuousLinearMap.adjoint_adjoint ℂ
      (twoBlockDiagOrthogonalPairSpace n) (twoBlockDiagOrthogonalPairSpace n) _ _ _ _ _
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)› A

/-- Compatibility of the adjoint star with composition on the orthogonal pair
endomorphism algebra. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceEndStarMul (n : ℕ) :
    StarMul (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n) where
  star_mul A B := by
    letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
    change ContinuousLinearMap.adjoint (ContinuousLinearMap.comp A B) =
        ContinuousLinearMap.comp (ContinuousLinearMap.adjoint B) (ContinuousLinearMap.adjoint A)
    exact @ContinuousLinearMap.adjoint_comp ℂ
      (twoBlockDiagOrthogonalPairSpace n) (twoBlockDiagOrthogonalPairSpace n)
      (twoBlockDiagOrthogonalPairSpace n) _ _ _ _ _ _ _
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›
      ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)› A B

/-- Star-ring structure on endomorphisms of the orthogonal pair space. -/
noncomputable scoped instance instTwoBlockDiagOrthogonalPairSpaceEndStarRing (n : ℕ) :
    StarRing (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n) where
  star_add A B := by
    letI : CompleteSpace (twoBlockDiagOrthogonalPairSpace n) :=
      instTwoBlockDiagOrthogonalPairSpaceCompleteSpace
    exact map_add
      (@ContinuousLinearMap.adjoint ℂ
        (twoBlockDiagOrthogonalPairSpace n) (twoBlockDiagOrthogonalPairSpace n) _ _ _ _ _
        ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›
        ‹CompleteSpace (twoBlockDiagOrthogonalPairSpace n)›) A B

/-- Normed-ring structure on endomorphisms of the two-block diagonal submodule. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagSubmoduleEndNormedRing (n : ℕ) :
    NormedRing (twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) :=
  ContinuousLinearMap.toNormedRing

/-- Normed-ring structure on endomorphisms of the off-diagonal submodule. -/
noncomputable scoped instance instOffDiagSubmoduleEndNormedRing (n : ℕ) :
    NormedRing (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) :=
  ContinuousLinearMap.toNormedRing

/-- Normed-ring structure on endomorphisms of the orthogonal complement of the
two-block diagonal submodule. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalSubmoduleEndNormedRing (n : ℕ) :
    NormedRing (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
  ContinuousLinearMap.toNormedRing

/-- Normed-ring structure on the bundled orthogonal-pair endomorphism type. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalPairEndNormedRing (n : ℕ) :
    NormedRing (cfcJArgTwoBlockDiagOrthogonalPairEnd n) :=
  ContinuousLinearMap.toNormedRing

/-- Complex algebra structure transported to the bundled orthogonal-pair
endomorphism type. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalPairEndAlgebra (n : ℕ) :
    Algebra ℂ (cfcJArgTwoBlockDiagOrthogonalPairEnd n) := by
  simpa [cfcJArgTwoBlockDiagOrthogonalPairEnd] using
    (inferInstance :
      Algebra ℂ
        (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n))

/-- Star operation transported to the bundled orthogonal-pair endomorphism type. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalPairEndStar (n : ℕ) :
    Star (cfcJArgTwoBlockDiagOrthogonalPairEnd n) := by
  simpa [cfcJArgTwoBlockDiagOrthogonalPairEnd] using
    (inferInstance :
      Star
        (twoBlockDiagOrthogonalPairSpace n →L[ℂ] twoBlockDiagOrthogonalPairSpace n))

/-- Real algebra structure on `WithLp` matrix-pair endomorphisms, needed for
the real/complex scalar tower. -/
noncomputable scoped instance instCfcJArgWithLpMatrixPairEndAlgebraReal (n : ℕ) :
    Algebra ℝ ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
  NormedAlgebra.complexToReal.toAlgebra

/-- Cached star-ring structure on endomorphisms of the `WithLp` matrix-pair
model; retaining this avoids expensive reconstruction in downstream CFC elaboration. -/
noncomputable scoped instance instCfcJArgWithLpMatrixPairEndStarRing (n : ℕ) :
    StarRing ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
  infer_instance

/-- Cached complex algebra structure on `WithLp` matrix-pair endomorphisms;
retaining it avoids expensive reconstruction in downstream CFC elaboration. -/
noncomputable scoped instance instCfcJArgWithLpMatrixPairEndAlgebra (n : ℕ) :
    Algebra ℂ ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
  infer_instance

/-- Cached real/complex scalar-tower compatibility on `WithLp` matrix-pair
endomorphisms; without it this module's elaboration becomes substantially slower. -/
noncomputable scoped instance instCfcJArgWithLpMatrixPairEndIsScalarTower (n : ℕ) :
    IsScalarTower ℝ ℂ
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) := by
  infer_instance

/-- Semiring structure on the product of diagonal and orthogonal block
endomorphism algebras. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalBlockEndProdSemiring (n : ℕ) :
    Semiring (cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) := by
  simpa [cfcJArgTwoBlockDiagOrthogonalBlockEndProd] using
    (inferInstance :
      Semiring
        ((twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) ×
          (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)))

/-- Complex algebra structure transported to the product of diagonal and
orthogonal block endomorphism algebras. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalBlockEndProdAlgebra (n : ℕ) :
    Algebra ℂ (cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) := by
  simpa [cfcJArgTwoBlockDiagOrthogonalBlockEndProd] using
    (inferInstance :
      Algebra ℂ
        ((twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) ×
          (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)))

/-- Star operation transported to the product of diagonal and orthogonal block
endomorphism algebras. -/
noncomputable scoped instance instCfcJArgTwoBlockDiagOrthogonalBlockEndProdStar (n : ℕ) :
    Star (cfcJArgTwoBlockDiagOrthogonalBlockEndProd n) := by
  simpa [cfcJArgTwoBlockDiagOrthogonalBlockEndProd] using
    (inferInstance :
      Star
        ((twoBlockDiagSubmodule n →L[ℂ] twoBlockDiagSubmodule n) ×
          (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n)))

end MatrixScopedInstances

end HiaiPetz
