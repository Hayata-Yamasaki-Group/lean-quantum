import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.HiaiPetz.FinMatrixCStar

/-!
# Finite-dimensional condition-(i) CFC compatibility core
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

noncomputable section

private theorem conditionICompat_spectrum_lmul_eq {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (a : A) : spectrum K ((Algebra.lmul K A) a : Module.End K A) = spectrum K a := by
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hmap :
      algebraMap K (Module.End K A) r - (Algebra.lmul K A) a =
        (Algebra.lmul K A) (algebraMap K A r - a) := by
    ext x
    simp [Algebra.coe_lmul_eq_mul, Algebra.smul_def]
  rw [hmap, Algebra.lmul_isUnit_iff]

private theorem conditionICompat_spectrum_finite_of_finiteDimensional
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] (a : A) :
    (spectrum K a).Finite := by
  rw [← conditionICompat_spectrum_lmul_eq (K := K) (A := A) a]
  exact Module.End.finite_spectrum ((Algebra.lmul K A) a : Module.End K A)

private theorem conditionICompat_spectrum_real_finite_of_finiteDimensional_complex
    {B : Type*} [Ring B] [Algebra ℂ B] [IsScalarTower ℝ ℂ B]
    [FiniteDimensional ℂ B] (b : B) :
    (spectrum ℝ b).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (conditionICompat_spectrum_finite_of_finiteDimensional (K := ℂ) (A := B) b).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- The algebra of continuous `ℂ`-linear endomorphisms of `EuclideanSpace ℂ (Fin n)` is a
C⋆-algebra. -/
noncomputable local instance instConditionICompatCLMCStar {n : ℕ} :
    CStarAlgebra (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
    (EuclideanSpace ℂ (Fin n)) inferInstance inferInstance inferInstance

/-- The endomorphism algebra of `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
local instance instConditionICompatCLMRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

-- Keep the complex-to-real algebras local to matrix/C⋆-matrix spectrum transport.
noncomputable local instance instConditionICompatMatrixRealAlgebra {n : ℕ} :
    Algebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Algebra.complexToReal

-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
theorem conditionICompat_matrixCfcR_eq_cfc {f : ℝ → ℝ} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsSelfAdjoint A) :
    HansenPedersen.matrixCfcR f A = cfc f A := by
  have hHerm : A.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hA
  let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  let φ : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →⋆ₐ[ℂ]
      Matrix (Fin n) (Fin n) ℂ := e.symm
  have hAe : IsSelfAdjoint (e A) := by
    exact hA.map e
  have hφeA : IsSelfAdjoint (φ (e A)) := by
    simpa [e, φ] using hA
  haveI : FiniteDimensional ℂ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    ContinuousLinearMap.finiteDimensional
  have hfin : (spectrum ℝ (e A)).Finite :=
    conditionICompat_spectrum_real_finite_of_finiteDimensional_complex
      (B := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (e A)
  have hmap :
      φ (cfc f (e A)) = cfc f (φ (e A)) := by
    exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ f (e A)
      (hf := hfin.continuousOn f) (ha := hAe) (hφa := hφeA)
  dsimp [HansenPedersen.matrixCfcR]
  change φ (cfc f (e A)) = cfc f A
  rw [hmap]
  simp [e, φ]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
