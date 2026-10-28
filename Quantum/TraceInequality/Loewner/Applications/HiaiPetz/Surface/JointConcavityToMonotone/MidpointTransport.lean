/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyBlockSum
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.LinearAlgebra.Lagrange
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.HiaiPetz.FinMatrixCStar
import Quantum.TraceInequality.HiaiPetzTheorem.Core.Basic
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions

/-!
# HP62 Condition IV to I: midpoint transport

This module contains the midpoint/unit-J setup, matrix CFC transport,
trace midpoint inequality, and positive-spectrum transport for the
Hiai--Petz 6.2 condition IV to condition I stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace

noncomputable section

/-! ### HP62 Midpoint and Unit J Setup -/
/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance quasiEntropyDpiConditionIVToIHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance quasiEntropyDpiConditionIVToIHSOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance quasiEntropyDpiConditionIVToIHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The algebra of bounded operators on `EuclideanSpace ℂ (Fin n)` is a C⋆-algebra. -/
noncomputable local instance quasiEntropyDpiConditionIVToIEuclideanOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HansenPedersen.L (EuclideanSpace ℂ (Fin n))) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (EuclideanSpace ℂ (Fin n))
    inferInstance inferInstance inferInstance

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a complex continuous
functional calculus for star-normal elements. -/
noncomputable local instance quasiEntropyDpiConditionIVToIEuclideanOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HansenPedersen.L (EuclideanSpace ℂ (Fin n))) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
local instance quasiEntropyDpiConditionIVToIEuclideanOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HansenPedersen.L (EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The theorem-facing identity matrix is positive definite.
Theorem 6.2 of [hiai2025]. -/
theorem one_is_matrixPosDef (n : ℕ) :
    MatrixPosDef (1 : Mₙ n) :=
  matrixPosDef_of_posDef Matrix.PosDef.one

/--
Positive real spectrum for a self-adjoint finite matrix gives the
theorem-facing positive-definite predicate used by `ConditionIV`.
-/
theorem matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi
    {n : ℕ} {A : Mₙ n}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    MatrixPosDef A := by
  let hAh : A.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hA
  have hA_posDef : A.PosDef := by
    rw [hAh.posDef_iff_eigenvalues_pos]
    intro i
    have hi_spec : hAh.eigenvalues i ∈ spectrum ℝ A :=
      hAh.eigenvalues_mem_spectrum_real i
    simpa [Set.mem_Ioi] using hσA hi_spec
  exact matrixPosDef_of_posDef hA_posDef

/-- Specializing HP62 quasi-entropy joint concavity to the midpoint. -/
theorem conditionIV_midpoint
    (f : ℝ → ℝ) (hIV : QuasiEntropyDPI.quasiEntropyJointConcavityCondition f)
    {n : ℕ} {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂)
    (hB₁ : MatrixPosDef B₁) (hB₂ : MatrixPosDef B₂) :
    (1 / 2 : ℝ) * QuasiEntropyDPI.quasiEntropy f A₁ B₁ X +
      (1 - (1 / 2 : ℝ)) * QuasiEntropyDPI.quasiEntropy f A₂ B₂ X ≤
        QuasiEntropyDPI.quasiEntropy f
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)
          ((1 / 2 : ℝ) • B₁ + (1 - (1 / 2 : ℝ)) • B₂) X := by
  refine hIV (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    (X := X) (t := 1 / 2) ?_ ?_ hA₁ hA₂ hB₁ hB₂
  · norm_num
  · norm_num

/-- Midpoint concavity of quasi-entropy with the second variable fixed at `1`. -/
theorem conditionIV_midpoint_unit
    (f : ℝ → ℝ) (hIV : QuasiEntropyDPI.quasiEntropyJointConcavityCondition f)
    {n : ℕ} {A₁ A₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂) :
    (1 / 2 : ℝ) * QuasiEntropyDPI.quasiEntropy f A₁ (1 : Mₙ n) X +
      (1 - (1 / 2 : ℝ)) * QuasiEntropyDPI.quasiEntropy f A₂ (1 : Mₙ n) X ≤
        QuasiEntropyDPI.quasiEntropy f
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) (1 : Mₙ n) X := by
  have hone :
      ((1 / 2 : ℝ) • (1 : Mₙ n) + (1 - (1 / 2 : ℝ)) • (1 : Mₙ n)) =
        (1 : Mₙ n) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      norm_num [Matrix.one_apply]
    · simp [hij]
  have h :=
    conditionIV_midpoint f hIV (n := n) (A₁ := A₁) (A₂ := A₂)
      (B₁ := (1 : Mₙ n)) (B₂ := (1 : Mₙ n)) (X := X)
      hA₁ hA₂ (one_is_matrixPosDef n) (one_is_matrixPosDef n)
  rw [hone] at h
  simpa using h

/-- With second argument `1`, the `J_f` argument is just left multiplication. -/
theorem jArg_one_eq_leftMul {n : ℕ} (A : Mₙ n) :
    jArg A (1 : Mₙ n) = leftMul A := by
  ext X
  simp [_root_.HiaiPetz.jArg]

/-- Right multiplication by the identity is the identity Hilbert--Schmidt operator. -/
theorem rightMul_one_eq_id {n : ℕ} :
    rightMul (1 : Mₙ n) = 1 := by
  ext X i j
  change (X * 1) i j = X i j
  simp

/-- Before identifying matrix CFCs, `J_f(A,1)` is the CFC of left multiplication. -/
theorem jOperator_one_eq_hsCfcR_leftMul {n : ℕ} (f : ℝ → ℝ) (A : Mₙ n) :
    jOperator f A (1 : Mₙ n) = hsCfcR f (leftMul A) := by
  calc
    jOperator f A (1 : Mₙ n)
        = hsCfcR f (leftMul A) * rightMul (1 : Mₙ n) := by
            change hsCfcR f (jArg A 1) * rightMul 1 = _
            rw [jArg_one_eq_leftMul]
    _ = hsCfcR f (leftMul A) * 1 := by rw [rightMul_one_eq_id]
    _ = hsCfcR f (leftMul A) := by simp

/--
The unit-second-variable midpoint inequality, expressed before transporting
`hsCfcR (leftMul A)` back to matrix CFC.
-/
theorem conditionIV_midpoint_unit_hsCfcR
    (f : ℝ → ℝ) (hIV : QuasiEntropyDPI.quasiEntropyJointConcavityCondition f)
    {n : ℕ} {A₁ A₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂) :
    (1 / 2 : ℝ) * hsQF (hsCfcR f (leftMul A₁)) X +
      (1 - (1 / 2 : ℝ)) * hsQF (hsCfcR f (leftMul A₂)) X ≤
        hsQF
          (hsCfcR f (leftMul
            ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂))) X := by
  have hmid :=
    conditionIV_midpoint_unit f hIV (n := n) (A₁ := A₁) (A₂ := A₂) (X := X)
      hA₁ hA₂
  simpa only [_root_.HiaiPetz.quasiEntropy, hsQF,
    jOperator_one_eq_hsCfcR_leftMul] using hmid

/-! ### Matrix CFC Transport Through Eigenbases -/
/-- A singleton column turns the matrix trace expression into a vector quadratic form. -/
theorem trace_conjTranspose_mul_matrix_mul_singletonCol
    {n : ℕ} (M : Mₙ n) (x : Fin n → ℂ) (j : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) *
          (M * Matrix.vecMulVec x (Pi.single j (1 : ℂ)))) =
      dotProduct (star x) (M.mulVec x) := by
  rw [Matrix.mul_vecMulVec, Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  simp

/-- Matrix CFC of a self-adjoint matrix is self-adjoint. -/
theorem matrixCfcR_isSelfAdjoint
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (HansenPedersen.matrixCfcR f A) := by
  let φ : Mₙ n ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hφA : IsSelfAdjoint (φ A) := by
    have h1 : φ (star A) = φ A := congrArg φ hA
    simpa [map_star] using h1
  have hSelfEuclid :
      IsSelfAdjoint
        (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A)) := by
    simp [HansenPedersen.cfcR]
  have hBack :
      φ.symm (star (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A))) =
        φ.symm (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A)) := by
    exact congrArg φ.symm hSelfEuclid.star_eq
  change
    star ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A))) =
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A))
  simpa [φ, HansenPedersen.matrixCfcR, map_star] using hBack

/--
Polynomial functional calculus on an eigenvector, stated for the real
polynomial transported to the complex Hilbert-space endomorphism.
-/
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

/--
Real CFC on a finite-dimensional self-adjoint Hilbert-space operator acts on
each eigenspace by evaluating the scalar function at the corresponding real
eigenvalue.
-/
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
    simpa [HansenPedersen.cfcR] using
      (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)
  have hpoly : HansenPedersen.cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q := by
    simpa [HansenPedersen.cfcR] using
      (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
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

/-- Matrix CFC transported to Euclidean-space operator CFC, applied to a vector. -/
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

/-- Matrix CFC acts diagonally on the Hermitian eigenbasis. -/
theorem matrixCfcR_mulVec_eigenvectorBasis_transport
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i : Fin n) :
    (HansenPedersen.matrixCfcR f A).mulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) =
      (f (hA.isHermitian.eigenvalues i) : ℂ) •
        (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ) := by
  have hx :
      (hA.isHermitian.eigenvectorBasis i : EuclideanSpace ℂ (Fin n)) ∈
        Module.End.eigenspace
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A).toLinearMap
          (hA.isHermitian.eigenvalues i : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    ext k
    simpa using congrArg (fun v : Fin n → ℂ => v k)
      (hA.isHermitian.mulVec_eigenvectorBasis i)
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
    ((HansenPedersen.matrixCfcR f A).mulVec
        ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))) k
        =
          (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
            ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
            (hA.isHermitian.eigenvectorBasis i)) k := by
              simpa using
                congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k)
                  (matrixCfcR_mulVec_toLp_eq_euclidCfc_apply_transport (f := f) A
                    (hA.isHermitian.eigenvectorBasis i))
    _ = ((f (hA.isHermitian.eigenvalues i) : ℂ) •
          (hA.isHermitian.eigenvectorBasis i)) k := by
          simpa using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k) hcalc
    _ = ((f (hA.isHermitian.eigenvalues i) : ℂ) •
          (hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) k := by
          rfl

/-- The rank-one eigenmatrix is an eigenvector for left multiplication. -/
theorem leftMul_eigenmatrix_mem_eigenspace
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ)) ∈
      Module.End.eigenspace (leftMul A).toLinearMap
        (hA.isHermitian.eigenvalues i : ℂ) := by
  rw [Module.End.mem_eigenspace_iff]
  ext a b
  change (A * Matrix.vecMulVec
      ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ))) a b = _
  rw [Matrix.mul_vecMulVec]
  have hmul := hA.isHermitian.mulVec_eigenvectorBasis i
  simp [hmul, Matrix.vecMulVec_apply, mul_assoc]

/-- Real CFC of left multiplication acts diagonally on rank-one eigenmatrices. -/
theorem leftMul_cfcR_apply_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    hsCfcR f (leftMul A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ))) =
    (f (hA.isHermitian.eigenvalues i) : ℂ) •
      Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ)) := by
  simpa [hsCfcR, HansenPedersen.cfcR] using
    (@cfcR_apply_of_mem_eigenspace_real_transport (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Matrix.finiteDimensional)
      (inferInstance : ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint)
      f (leftMul A) (leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hA)
      (hA.isHermitian.eigenvalues i)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ)))
      (leftMul_eigenmatrix_mem_eigenspace (hA := hA) i j))

/-- Left multiplication by the matrix CFC has the same eigenmatrix action. -/
theorem leftMul_matrixCfcR_apply_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    leftMul (HansenPedersen.matrixCfcR f A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ))) =
    (f (hA.isHermitian.eigenvalues i) : ℂ) •
      Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ)) := by
  rw [leftMul_apply, Matrix.mul_vecMulVec,
    matrixCfcR_mulVec_eigenvectorBasis_transport (hA := hA),
    Matrix.smul_vecMulVec]

/-- Continuous linear maps commute with finite sums of scalar multiples. -/
theorem clm_map_sum_smul
    {ι : Type*} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (s : Finset ι) (c : ι → ℂ) (x : ι → E) :
    T (Finset.sum s fun i => c i • x i) = Finset.sum s fun i => c i • T (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, map_add, map_smul]

/-- Rank-one columns distribute over finite sums. -/
theorem vecMulVec_sum_smul
    {n : ℕ} (s : Finset (Fin n)) (c : Fin n → ℂ)
    (v : Fin n → Fin n → ℂ) (j : Fin n) :
    Matrix.vecMulVec (Finset.sum s fun i => c i • v i) (Pi.single j (1 : ℂ)) =
      Finset.sum s fun i => c i • Matrix.vecMulVec (v i) (Pi.single j (1 : ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]

/-- A singleton column expands in the Hermitian eigenbasis. -/
theorem singleCol_eq_sum_eigenbasis
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (x : Fin n → ℂ) (j : Fin n) :
    Matrix.vecMulVec x (Pi.single j (1 : ℂ)) =
      ∑ i : Fin n,
        (((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)) •
          Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (Pi.single j (1 : ℂ)) := by
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  have hsum :=
    congrArg (fun v : EuclideanSpace ℂ (Fin n) => Matrix.vecMulVec v (Pi.single j (1 : ℂ)))
      ((hA.isHermitian.eigenvectorBasis.toBasis).sum_repr (WithLp.toLp 2 x)).symm
  simpa [c, vecMulVec_sum_smul] using hsum

/-- CFC of left multiplication agrees with left multiplication by matrix CFC on one column. -/
theorem cfc_leftMul_eq_leftMul_matrixCfcR_on_singleCol
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n}
    (hA : IsSelfAdjoint A) (x : Fin n → ℂ) (j : Fin n) :
    hsCfcR f (leftMul A) (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) =
      leftMul (HansenPedersen.matrixCfcR f A)
        (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) := by
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  let Y : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
      (Pi.single j (1 : ℂ))
  have hdecomp : Matrix.vecMulVec x (Pi.single j (1 : ℂ)) = ∑ i : Fin n, c i • Y i := by
    simpa [c, Y] using singleCol_eq_sum_eigenbasis (hA := hA) x j
  rw [hdecomp]
  calc
    hsCfcR f (leftMul A) (∑ i : Fin n, c i • Y i) =
      ∑ i : Fin n, c i • hsCfcR f (leftMul A) (Y i) := by
        calc
          hsCfcR f (leftMul A) (∑ i : Fin n, c i • Y i) =
              ∑ i : Fin n, hsCfcR f (leftMul A) (c i • Y i) :=
            map_sum (hsCfcR f (leftMul A)).toLinearMap.toAddMonoidHom
              (fun i : Fin n => c i • Y i) Finset.univ
          _ = ∑ i : Fin n, c i • hsCfcR f (leftMul A) (Y i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hsCfcR f (leftMul A)).map_smul (c i) (Y i)
    _ =
      ∑ i : Fin n, c i • leftMul (HansenPedersen.matrixCfcR f A) (Y i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun M : Mₙ n => c i • M)
          ((leftMul_cfcR_apply_eigenmatrix (f := f) (hA := hA) i j).trans
            (leftMul_matrixCfcR_apply_eigenmatrix (f := f) (hA := hA) i j).symm)
    _ = leftMul (HansenPedersen.matrixCfcR f A) (∑ i : Fin n, c i • Y i) := by
      symm
      simp only [leftMul_apply, Matrix.mul_sum, Matrix.mul_smul]

/-- Every matrix is the sum of its singleton columns. -/
theorem matrix_eq_sum_singleCols {n : ℕ} (X : Mₙ n) :
    X = ∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)) := by
  ext a b
  rw [Matrix.sum_apply]
  simp [Matrix.vecMulVec_apply, Matrix.col, Pi.single_apply]

/-- CFC of left multiplication is left multiplication by the matrix CFC. -/
theorem cfc_leftMul_eq_leftMul_matrixCfcR
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n}
    (hA : IsSelfAdjoint A) :
    hsCfcR f (leftMul A) =
      leftMul (HansenPedersen.matrixCfcR f A) := by
  ext X a b
  rw [matrix_eq_sum_singleCols X]
  calc
    (hsCfcR f (leftMul A)
        (∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b =
      (∑ j : Fin n,
        hsCfcR f (leftMul A) (Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
        exact congrArg (fun M : Mₙ n => M a b)
          (map_sum (hsCfcR f (leftMul A)).toLinearMap.toAddMonoidHom
            (fun j : Fin n => Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ))) Finset.univ)
    _ =
      (∑ j : Fin n,
        leftMul (HansenPedersen.matrixCfcR f A)
          (Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
          exact congrArg (fun M : Mₙ n => M a b) <|
            Finset.sum_congr rfl (fun j _ =>
              cfc_leftMul_eq_leftMul_matrixCfcR_on_singleCol
                (f := f) (hA := hA) (X.col j) j)
    _ =
      (leftMul (HansenPedersen.matrixCfcR f A)
        (∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
          symm
          simp only [leftMul_apply, Matrix.mul_sum, Matrix.sum_apply]

/-- With second argument `1`, `J_f` is left multiplication by the matrix CFC. -/
theorem jOperator_one_eq_leftMul_matrixCfcR
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) :
    jOperator f A (1 : Mₙ n) = leftMul (HansenPedersen.matrixCfcR f A) := by
  rw [jOperator_one_eq_hsCfcR_leftMul, cfc_leftMul_eq_leftMul_matrixCfcR f hA]

/-- The quasi-entropy with second argument `1` is the matrix-CFC quadratic form. -/
theorem quasiEntropy_unit_eq
    {n : ℕ} (f : ℝ → ℝ) {A X : Mₙ n} (hA : IsSelfAdjoint A) :
    QuasiEntropyDPI.quasiEntropy f A (1 : Mₙ n) X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A * X))) := by
  change hsQF (jOperator f A 1) X = _
  rw [jOperator_one_eq_leftMul_matrixCfcR f hA]
  rfl

/-! ### Trace Midpoint Inequality for Matrix CFC -/
/-- `ConditionIV` gives midpoint concavity in trace form when the second argument is `1`. -/
theorem conditionIV_midpoint_unit_matrixCfcR
    (f : ℝ → ℝ) (hIV : QuasiEntropyDPI.quasiEntropyJointConcavityCondition f)
    {n : ℕ} {A₁ A₂ X : Mₙ n}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂) :
    (1 / 2 : ℝ) *
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A₁ * X))) +
      (1 - (1 / 2 : ℝ)) *
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A₂ * X))) ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            (HansenPedersen.matrixCfcR f
              ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) * X))) := by
  have hmid :=
    conditionIV_midpoint_unit f hIV (n := n) (A₁ := A₁) (A₂ := A₂) (X := X) hA₁ hA₂
  have hA_mid_sa :
      IsSelfAdjoint ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hA₁.1).add
        ((IsSelfAdjoint.all (1 - (1 / 2 : ℝ))).smul hA₂.1)
  rw [quasiEntropy_unit_eq f hA₁.1, quasiEntropy_unit_eq f hA₂.1,
    quasiEntropy_unit_eq f hA_mid_sa] at hmid
  exact hmid

/-- Vector quadratic-form version of the unit midpoint inequality. -/
theorem conditionIV_midpoint_unit_dotProduct
    (f : ℝ → ℝ) (hIV : QuasiEntropyDPI.quasiEntropyJointConcavityCondition f)
    {n : ℕ} {A₁ A₂ : Mₙ n} {x : Fin n → ℂ}
    (hA₁ : MatrixPosDef A₁) (hA₂ : MatrixPosDef A₂) :
    (1 / 2 : ℝ) *
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A₁).mulVec x)) +
      (1 - (1 / 2 : ℝ)) *
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A₂).mulVec x)) ≤
      Complex.re
        (dotProduct (star x)
          ((HansenPedersen.matrixCfcR f
            ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)).mulVec x)) := by
  cases n with
  | zero =>
      have hx0 : x = 0 := by ext i; exact Fin.elim0 i
      subst hx0
      simp
  | succ k =>
      let X : Mₙ (k + 1) := Matrix.vecMulVec x (Pi.single 0 (1 : ℂ))
      have htrace :=
        conditionIV_midpoint_unit_matrixCfcR f hIV (n := k + 1)
          (A₁ := A₁) (A₂ := A₂) (X := X) hA₁ hA₂
      have hmid_eq :
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) =
            ((1 / 2 : ℝ) • (A₁ + A₂)) := by
        have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
        have hsmul :
            (1 / 2 : ℝ) • (A₁ + A₂) = (1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ := by
          ext i j
          exact smul_add (1 / 2 : ℝ) (A₁ i j) (A₂ i j)
        calc
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)
              = (1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ := by rw [hhalf]
          _ = (1 / 2 : ℝ) • (A₁ + A₂) := hsmul.symm
      rw [trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f A₁) (x := x) (j := 0),
        trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f A₂) (x := x) (j := 0),
        trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f
            ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)) (x := x) (j := 0)] at htrace
      simpa [hmid_eq] using htrace

/--
The theorem-facing HP62 matrix condition (i) is definitionally the same as
condition (i) on the Loewner bridge surface.
-/
theorem matrix_surface_condition_to_conditionI (f : ℝ → ℝ) :
    QuasiEntropyDPI.matrixMonotoneConditionMatrix f →
      QuasiEntropyDPI.matrixMonotoneCondition f := by
  intro hI
  exact hI

/-! ### Operator Order and Positive Spectra on the Loewner Segment -/

/-- Convex combinations of positive-spectrum self-adjoint operators keep positive spectrum. -/
theorem spectrum_convexCombo_Ioi_clm
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {A B : HansenPedersen.L K} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : HansenPedersen.L K := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using
      ((IsSelfAdjoint.all (1 - t)).smul hA).add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (HansenPedersen.L K) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := HansenPedersen.L K) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact hσA hx
  have hBpos : ∃ r > 0, algebraMap ℝ (HansenPedersen.L K) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := HansenPedersen.L K) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact hσB hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne' (sub_nonneg.mpr ht1) h1t
      have hleft : 0 < (1 - t) * rA := mul_pos h1t_pos hrA
      have hright : 0 ≤ t * rB := mul_nonneg ht0 (le_of_lt hrB)
      simpa [rC] using add_pos_of_pos_of_nonneg hleft hright
  have hrC_le : algebraMap ℝ (HansenPedersen.L K) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (HansenPedersen.L K) rA +
            t • algebraMap ℝ (HansenPedersen.L K) rB ≤
          C := by
      simpa [C] using
        add_le_add
          (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (HansenPedersen.L K) rA +
            t • algebraMap ℝ (HansenPedersen.L K) rB =
          algebraMap ℝ (HansenPedersen.L K) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := HansenPedersen.L K) (a := C) (ha := hC)).1
      ⟨rC, hrC, hrC_le⟩ x hx

end

end Quantum.TraceInequality.Loewner.HiaiPetz
