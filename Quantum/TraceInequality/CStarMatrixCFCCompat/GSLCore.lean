import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
Restore the self-adjoint real CFC instance for matrix API consumers.
The full import environment selects the C⋆-algebra's `StarRing` and the associative
Lie algebra's real `Module`. Match those projections explicitly: they are
definitionally equal to the direct matrix instances, but instance search does
not unfold them far enough to find the original CFC instance.
-/
namespace Quantum

open scoped ComplexOrder

@[reducible, local instance]
noncomputable def cstarMatrixStarRingCompat {n : Type*} [Fintype n] :
    StarRing (CStarMatrix n n ℂ) :=
  (inferInstance : NonUnitalCStarAlgebra (CStarMatrix n n ℂ)).toStarRing

@[reducible, local instance]
noncomputable def cstarMatrixRealModuleCompat {n : Type*} [Fintype n] [DecidableEq n] :
    Module ℝ (CStarMatrix n n ℂ) :=
  (inferInstance : LieAlgebra ℝ (CStarMatrix n n ℂ)).toModule

/-- Mathlib's self-adjoint real continuous functional calculus on `CStarMatrix n n ℂ`,
registered again for the instance path selected in the full import environment (see the module
docstring). This is a global instance, visible in every module that imports this file. -/
noncomputable instance cstarMatrixRealNonUnitalCFC {n : Type*} [Fintype n]
    [DecidableEq n] :
    @NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint _ _ _ _ _ _ _
      cstarMatrixStarRingCompat _ cstarMatrixRealModuleCompat _ _ :=
  haveI : NonUnitalContinuousFunctionalCalculus ℂ (CStarMatrix n n ℂ) IsStarNormal :=
    IsStarNormal.instNonUnitalContinuousFunctionalCalculus.toNonUnitalContinuousFunctionalCalculus
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

end Quantum
