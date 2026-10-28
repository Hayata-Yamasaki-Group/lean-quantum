/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore.RectangularOperators

/-!
Opt-in instance cache for the shifted-compression proof implementation.

These instances are internal proof infrastructure.  They are scoped so importing this module does
not change instance synthesis unless a consumer explicitly opens the scope or locally registers a
named cache.
-/

namespace ProofNetInternal.ShiftedCompressionInstances

open HiaiPetz Matrix
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.RectangularOperatorInstances

noncomputable section

/-- Internal scoped normed additive group cache for the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairNormedAddCommGroup {k l : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ l × Mₙ k)) :=
  WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ l) (β := Mₙ k)

/-- Internal scoped inner-product-space cache for the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairInnerProductSpace {k l : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ l × Mₙ k)) :=
  @WithLp.instProdInnerProductSpace ℂ (Mₙ l) (Mₙ k)
    inferInstance
    (HiaiPetz.instMatrixNormedAddCommGroup (n := l))
    (HiaiPetz.instMatrixInnerProductSpace (n := l))
    (HiaiPetz.instMatrixNormedAddCommGroup (n := k))
    (HiaiPetz.instMatrixInnerProductSpace (n := k))

/-- Internal scoped complex normed-space cache for the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairNormedSpace {k l : ℕ} :
    NormedSpace ℂ (WithLp 2 (Mₙ l × Mₙ k)) :=
  WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := Mₙ l) (β := Mₙ k)

/-- Internal scoped completeness cache for the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairCompleteSpace {k l : ℕ} :
    CompleteSpace (WithLp 2 (Mₙ l × Mₙ k)) :=
  inferInstance

/-- Internal scoped C⋆-algebra cache for operators on the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairCStarAlgebra {k l : ℕ} :
    CStarAlgebra
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
    (WithLp 2 (Mₙ l × Mₙ k))
    (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
    (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))
    (strictEquivShiftedPairCompleteSpace (k := k) (l := l))

/-- Internal scoped complex CFC cache for star-normal operators on the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairComplexCFC {k l : ℕ} :
    ContinuousFunctionalCalculus ℂ
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- Internal scoped real CFC cache for self-adjoint operators on the `L²` matrix pair. -/
noncomputable abbrev strictEquivShiftedPairRealCFC {k l : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (@HansenPedersen.L (WithLp 2 (Mₙ l × Mₙ k))
        (strictEquivShiftedPairNormedAddCommGroup (k := k) (l := l))
        (strictEquivShiftedPairInnerProductSpace (k := k) (l := l))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

attribute [scoped instance]
  strictEquivShiftedPairNormedAddCommGroup
  strictEquivShiftedPairInnerProductSpace
  strictEquivShiftedPairNormedSpace
  strictEquivShiftedPairCompleteSpace
  strictEquivShiftedPairCStarAlgebra
  strictEquivShiftedPairComplexCFC
  strictEquivShiftedPairRealCFC

end

end ProofNetInternal.ShiftedCompressionInstances
