/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Transport for matrix functional calculus on eigenvectors

This file proves that real functional calculus acts by scalar evaluation on
eigenspaces after transporting between matrices and Euclidean continuous linear
maps. The finite-spectrum argument uses polynomial interpolation, so no global
diagonalization API is needed in the downstream matrix statements.

## Main results

* `aeval_apply_of_mem_eigenspace_realpoly_transport`: polynomial evaluation on
  an eigenvector after mapping real polynomials to complex scalars.
* `cfcR_apply_of_mem_eigenspace_real_transport`: real CFC acts as `f r` on the
  eigenspace for eigenvalue `r`.
* `matrixCfcR_mulVec_toLp_eq_euclidCfc_apply_transport` and
  `matrixCfcR_mulVec_eigenvectorBasis_transport`: matrix CFC transport to
  Euclidean vectors and Hermitian eigenvector bases.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 matrix functional calculus.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/-- Polynomial evaluation of a real polynomial mapped to complex coefficients
acts by scalar evaluation on a vector in the corresponding eigenspace. -/
theorem aeval_apply_of_mem_eigenspace_realpoly_transport
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} {r : ℝ} {x : 𝓚}
    (hx : x ∈ Module.End.eigenspace T.toLinearMap (r : ℂ)) (p : Polynomial ℝ) :
    Polynomial.aeval T (Polynomial.map (algebraMap ℝ ℂ) p) x =
      ((Polynomial.map (algebraMap ℝ ℂ) p).eval (r : ℂ)) • x := by
  haveI : IsScalarTower ℝ ℂ (𝓚 →L[ℂ] 𝓚) :=
    RestrictScalars.isScalarTower ℝ ℂ (𝓚 →L[ℂ] 𝓚)
  haveI : IsScalarTower ℝ ℂ (𝓚 →ₗ[ℂ] 𝓚) :=
    RestrictScalars.isScalarTower ℝ ℂ (𝓚 →ₗ[ℂ] 𝓚)
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (Polynomial.map (algebraMap ℝ ℂ) p) x =
        Polynomial.aeval T.toLinearMap (Polynomial.map (algebraMap ℝ ℂ) p) x := by
    simpa using
      congrArg (fun F : 𝓚 →ₗ[ℂ] 𝓚 => F x)
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℂ) (S := 𝓚 →L[ℂ] 𝓚) (T := ℂ) (U := 𝓚 →ₗ[ℂ] 𝓚)
          (φ := RingHom.id ℂ) (ψ := ContinuousLinearMap.toLinearMapRingHom)
          (h := by ext z; rfl) (p := Polynomial.map (algebraMap ℝ ℂ) p) (a := T))
  rw [hmap]
  simpa using
    (Module.End.aeval_apply_of_hasEigenvector
      (f := T.toLinearMap) (p := Polynomial.map (algebraMap ℝ ℂ) p)
      (μ := (r : ℂ)) (x := x) ⟨hx, hx0⟩)

-- Finite-spectrum CFC interpolation over eigenspaces is elaboration-heavy.
/-- In finite dimension, real continuous functional calculus of a self-adjoint
operator acts on an eigenspace for real eigenvalue `r` by the scalar `f r`. -/
theorem cfcR_apply_of_mem_eigenspace_real_transport
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : HansenPedersen.L 𝓚} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : x ∈ Module.End.eigenspace T.toLinearMap (r : ℂ)) :
    HansenPedersen.cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  haveI : IsScalarTower ℝ ℂ (HansenPedersen.L 𝓚) :=
    RestrictScalars.isScalarTower ℝ ℂ (HansenPedersen.L 𝓚)
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite (spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := 𝓚) T.toLinearMap
  have hspecRfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  let s : Finset ℝ := hspecRfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate s id fun y ↦ f y
  have hq_spec : (spectrum ℝ T).EqOn f q.eval := by
    intro y hy
    have hy' : y ∈ s := by simpa [s] using hy
    symm
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun z ↦ f z) (i := y)
        (hvs := fun _ _ _ _ h => h) hy')
  have hcfc : HansenPedersen.cfcR (ℋ := 𝓚) f T =
      HansenPedersen.cfcR (ℋ := 𝓚) q.eval T := by
    simpa [HansenPedersen.cfcR] using (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)
  have hpoly : HansenPedersen.cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q := by
    simpa [HansenPedersen.cfcR] using (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
  have hxv : Module.End.HasEigenvector T.toLinearMap (r : ℂ) x := ⟨hx, hx0⟩
  have hr_specC : (r : ℂ) ∈ spectrum ℂ T := by
    change (r : ℂ) ∈ spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap)
    simpa using (Module.End.hasEigenvalue_of_hasEigenvector hxv).mem_spectrum
  have hr_spec : r ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hr_specC
  calc
    HansenPedersen.cfcR (ℋ := 𝓚) f T x =
        HansenPedersen.cfcR (ℋ := 𝓚) q.eval T x := by rw [hcfc]
    _ = Polynomial.aeval T q x := by rw [hpoly]
    _ = Polynomial.aeval T (Polynomial.map (algebraMap ℝ ℂ) q) x := by
          symm
          simp
    _ = ((Polynomial.map (algebraMap ℝ ℂ) q).eval (r : ℂ)) • x := by
          simpa using aeval_apply_of_mem_eigenspace_realpoly_transport hx q
    _ = (f r : ℂ) • x := by
          congr 1
          rw [Polynomial.eval_map_algebraMap]
          calc
            Polynomial.aeval (algebraMap ℝ ℂ r) q = ((Polynomial.eval r q : ℝ) : ℂ) := by
              simpa using
                (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := r)
                  (p := q))
            _ = (f r : ℂ) := by
              simpa using congrArg (fun t : ℝ => (t : ℂ)) (hq_spec hr_spec).symm

/-- Matrix real CFC applied to a vector agrees, after `WithLp.toLp`, with the
Euclidean CLM real CFC of the transported matrix. -/
theorem matrixCfcR_mulVec_toLp_eq_euclidCfc_apply_transport
    {n : ℕ} (f : ℝ → ℝ) (A : Mₙ n) (x : Fin n → ℂ) :
    WithLp.toLp 2 ((HansenPedersen.matrixCfcR f A).mulVec x) =
      HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A) (WithLp.toLp 2 x) := by
  change ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (HansenPedersen.matrixCfcR f A))
      (WithLp.toLp 2 x) =
    HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A) (WithLp.toLp 2 x)
  simp [HansenPedersen.matrixCfcR]

/-- For a self-adjoint matrix, matrix real CFC acts diagonally on the Hermitian
eigenvector basis with eigenvalue `f (eigenvalues i)`. -/
theorem matrixCfcR_mulVec_eigenvectorBasis_transport
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i : Fin n) :
    (HansenPedersen.matrixCfcR f A).mulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) =
      (f (hA.isHermitian.eigenvalues i) : ℂ) •
        (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ) := by
  have hx :
      (hA.isHermitian.eigenvectorBasis i : EuclideanSpace ℂ (Fin n)) ∈
        Module.End.eigenspace
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A).toLinearMap
          (hA.isHermitian.eigenvalues i : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    ext k
    simpa using congrArg (fun v : Fin n → ℂ => v k) (hA.isHermitian.mulVec_eigenvectorBasis i)
  have hcalc :=
    @cfcR_apply_of_mem_eigenspace_real_transport (EuclideanSpace ℂ (Fin n))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      f ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
      (hA.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)))
      (hA.isHermitian.eigenvalues i)
      (hA.isHermitian.eigenvectorBasis i)
      hx
  ext k
  calc
    ((HansenPedersen.matrixCfcR f A).mulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))) k
        = (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
            (hA.isHermitian.eigenvectorBasis i)) k := by
              simpa using
                congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k)
                  (matrixCfcR_mulVec_toLp_eq_euclidCfc_apply_transport (f := f) A
                    (hA.isHermitian.eigenvectorBasis i))
    _ = ((f (hA.isHermitian.eigenvalues i) : ℂ) • (hA.isHermitian.eigenvectorBasis i)) k := by
          simpa using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k) hcalc
    _ = ((f (hA.isHermitian.eigenvalues i) : ℂ) •
          (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) k := by
          rfl

end MatrixScopedInstances

end HiaiPetz
