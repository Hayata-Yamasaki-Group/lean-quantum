/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.ConditionIToLoewner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.PositiveInverse
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.AdjointHelpers
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBound
-- positive-part decomposition for positive maps

/-!
# Carlen rectangle infrastructure

This module contains the infrastructure stage of the Carlen 2022 Theorem 1.46
rectangle argument: Hilbert--Schmidt CFC transport, square-root rectangle
operators, and positive-spectrum CFC identities.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

/-! ### Hilbert--Schmidt CFC and Loewner-order infrastructure -/
attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance instCarlenRectangleHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
    (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance instCarlenRectangleHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance instCarlenRectangleHSOpStarRing {n : ℕ} :
    StarRing (HSOp n) :=
  (instCarlenRectangleHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance instCarlenRectangleHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance (instCarlenRectangleHSOpPartialOrder (n := n))
      (instCarlenRectangleHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
    (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance instCarlenRectangleComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance instCarlenRectangleRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance instCarlenRectangleHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (instCarlenRectangleHSOpCStarAlgebra (n := n))
    (instCarlenRectangleHSOpPartialOrder (n := n))
    (instCarlenRectangleHSOpStarOrderedRing (n := n))

/-- Complex scalar multiplication on `HSOp n` preserves zero. -/
noncomputable local instance instCarlenRectangleHSOpSMulZeroClass {n : ℕ} :
    SMulZeroClass ℂ (HSOp n) :=
  inferInstanceAs (SMulZeroClass ℂ (HSOp n))

/-- Complex scalar multiplication on `HSOp n` is norm-bounded. -/
local instance instCarlenRectangleHSOpIsBoundedSMul {n : ℕ} :
    IsBoundedSMul ℂ (HSOp n) :=
  IsBoundedSMul.of_norm_smul_le (fun r x => NormedSpace.norm_smul_le r x)

/-- Complex scalar multiplication on `HSOp n` is continuous. -/
local instance instCarlenRectangleHSOpContinuousSMul {n : ℕ} :
    ContinuousSMul ℂ (HSOp n) :=
  IsBoundedSMul.continuousSMul

noncomputable section

/-! ### Conjugate-transpose star equivalence and real CFC transport -/
/-- The real algebra structure on Hilbert--Schmidt operators used by the
real continuous functional calculus transport through conjugate transpose. -/
noncomputable local instance instCarlenRectangleHSOpRealAlgebra {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  NormedAlgebra.complexToReal.toAlgebra

/-- The real scalar action on `HSOp n` is a trivial scalar tower over itself. -/
local instance instCarlenRectangleHSOpRealRealTower {n : ℕ} :
    IsScalarTower ℝ ℝ (HSOp n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Conjugating Hilbert--Schmidt operators by matrix conjugate transpose
commutes with the star operation on operators. -/
theorem conjTransposeConjHSOp_map_star {n : ℕ} (T : HSOp n) :
    conjTransposeConjHSOp (star T) = star (conjTransposeConjHSOp T) := by
  change conjTransposeConjHSOp (hsAdjoint T) =
    hsAdjoint (conjTransposeConjHSOp T)
  apply ContinuousLinearMap.ext
  intro Z
  rw [Matrix.ext_iff_trace_mul_left]
  intro X
  calc
    Matrix.trace (X * conjTransposeConjHSOp (hsAdjoint T) Z)
        = Matrix.trace (T X * Z) := by
          simpa [conjTransposeConjHSOp, Matrix.conjTranspose_conjTranspose] using
            (trace_mul_hsAdjoint_conjTranspose' T X (Matrix.conjTranspose Z))
    _ = Matrix.trace (X * hsAdjoint (conjTransposeConjHSOp T) Z) := by
          have h := trace_hsAdjoint_eq
            (conjTransposeConjHSOp T) (Matrix.conjTranspose X) Z
          simpa [conjTransposeConjHSOp_apply, Matrix.conjTranspose_conjTranspose] using h.symm

/-- The conjugate-transpose conjugation of Hilbert--Schmidt operators as a
real star-algebra equivalence.  It is real-linear, not complex-linear. -/
noncomputable def conjTransposeConjHSOpStarAlgEquivR (n : ℕ) :
    HSOp n ≃⋆ₐ[ℝ] HSOp n where
  toFun := conjTransposeConjHSOp
  invFun := conjTransposeConjHSOp
  left_inv := by
    intro T
    apply ContinuousLinearMap.ext
    intro Z
    simp [conjTransposeConjHSOp_apply]
  right_inv := by
    intro T
    apply ContinuousLinearMap.ext
    intro Z
    simp [conjTransposeConjHSOp_apply]
  map_mul' := by
    intro S T
    apply ContinuousLinearMap.ext
    intro Z
    simp [conjTransposeConjHSOp_apply, ContinuousLinearMap.mul_apply]
  map_add' := by
    intro S T
    apply ContinuousLinearMap.ext
    intro Z
    simp [conjTransposeConjHSOp_apply]
  map_star' := conjTransposeConjHSOp_map_star
  map_smul' := by
    intro r T
    apply ContinuousLinearMap.ext
    intro Z
    simp [conjTransposeConjHSOp_apply]

/-- The real star-algebra equivalence induced by conjugate transpose is
continuous. -/
theorem continuous_conjTransposeConjHSOpStarAlgEquivR (n : ℕ) :
    Continuous (conjTransposeConjHSOpStarAlgEquivR n : HSOp n → HSOp n) := by
  have hnorm : ∀ T : HSOp n, ‖conjTransposeConjHSOp T‖ ≤ ‖T‖ := by
    intro T
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro Z
    calc
      ‖conjTransposeConjHSOp T Z‖ = ‖T (Matrix.conjTranspose Z)‖ := by
        simp [conjTransposeConjHSOp_apply]
      _ ≤ ‖T‖ * ‖Matrix.conjTranspose Z‖ := T.le_opNorm (Matrix.conjTranspose Z)
      _ = ‖T‖ * ‖Z‖ := by simp
  have hlip : LipschitzWith 1 (conjTransposeConjHSOpStarAlgEquivR n : HSOp n → HSOp n) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro S T
    have hsub :
        conjTransposeConjHSOpStarAlgEquivR n S -
          conjTransposeConjHSOpStarAlgEquivR n T =
          conjTransposeConjHSOp (S - T) := by
      apply ContinuousLinearMap.ext
      intro Z
      change Matrix.conjTranspose (S (Matrix.conjTranspose Z)) +
          -Matrix.conjTranspose (T (Matrix.conjTranspose Z)) =
        Matrix.conjTranspose (S (Matrix.conjTranspose Z) + -T (Matrix.conjTranspose Z))
      simp
    rw [NormedRing.dist_eq, NormedRing.dist_eq]
    rw [add_comm (-(conjTransposeConjHSOpStarAlgEquivR n S)),
      add_comm (-S)]
    change ‖conjTransposeConjHSOpStarAlgEquivR n T -
      conjTransposeConjHSOpStarAlgEquivR n S‖ ≤ (1 : ℝ) * ‖T - S‖
    rw [norm_sub_rev (conjTransposeConjHSOpStarAlgEquivR n T),
      norm_sub_rev T, hsub]
    simpa using hnorm (S - T)
  exact hlip.continuous

/-- Real continuous functional calculus is natural under conjugating
Hilbert--Schmidt operators by matrix conjugate transpose. -/
theorem hsCfcR_conjTransposeConjHSOp {n : ℕ} {f : ℝ → ℝ} {T : HSOp n}
    (hf : ContinuousOn f (spectrum ℝ T)) (hT : IsSelfAdjoint T) :
    conjTransposeConjHSOp (hsCfcR f T) =
      hsCfcR f (conjTransposeConjHSOp T) := by
  have htower : IsScalarTower ℝ ℝ (HSOp n) := inferInstance
  let e := conjTransposeConjHSOpStarAlgEquivR n
  let φ : HSOp n →⋆ₐ[ℝ] HSOp n := StarAlgHomClass.toStarAlgHom e
  have hcont : Continuous (e : HSOp n → HSOp n) :=
    continuous_conjTransposeConjHSOpStarAlgEquivR n
  have hcontφ : Continuous (φ : HSOp n → HSOp n) := by
    simpa [φ] using hcont
  have hCT : IsSelfAdjoint (e T) := by
    change star (e T) = e T
    rw [← map_star e, hT]
  have hmap :
      φ (cfc f T) = cfc f (φ T) :=
    @StarAlgHom.map_cfc ℝ ℝ (HSOp n) (HSOp n) IsSelfAdjoint IsSelfAdjoint
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htower htower _ _ _
      φ f T hf hcontφ hT hCT
  simpa [e, φ, hsCfcR] using hmap

/-! ### Square-root rectangle operators and positive-spectrum CFC identities -/
/-- Positive square root in the Hilbert--Schmidt operator CFC. -/
noncomputable def carlenRectSqrt {n : ℕ} (T : HSOp n) : HSOp n :=
  hsCfcR (fun x : ℝ => x ^ ((1 : ℝ) / 2)) T

/-- Positive inverse square root in the Hilbert--Schmidt operator CFC. -/
noncomputable def carlenRectInvSqrt {n : ℕ} (T : HSOp n) : HSOp n :=
  hsCfcR (fun x : ℝ => x ^ ((-1 : ℝ) / 2)) T

/-- Carlen's normalized rectangular map `sqrt(TA) V invsqrt(TΦ)`. -/
noncomputable def carlenRectU {n m : ℕ}
    (V : HSMap n m) (TA : HSOp m) (TΦ : HSOp n) : HSMap n m :=
  (carlenRectSqrt TA).comp (V.comp (carlenRectInvSqrt TΦ))

/-- Direct rectangle operator `V† TA V`. -/
noncomputable def carlenRectDirectOp {n m : ℕ}
    (V : HSMap n m) (TA : HSOp m) : HSOp n :=
  (hsAdjoint V).comp (TA.comp V)

/-- Inverse rectangle operator `V TΦ⁻¹ V†`. -/
noncomputable def carlenRectInverseOp {n m : ℕ}
    (V : HSMap n m) (TΦ : HSOp n) : HSOp m :=
  V.comp ((Ring.inverse TΦ).comp (hsAdjoint V))

/-- On a positive real spectrum, the real-power function `x ↦ x ^ q` is continuous. -/
theorem carlenContinuousOn_rpow_const_of_IoiSpectrum {n : ℕ} {T : HSOp n} {q : ℝ}
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn (fun x : ℝ => x ^ q) (spectrum ℝ T) := by
  intro x hx
  have hx0 : 0 < x := by
    simpa [Set.mem_Ioi] using hσT hx
  exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt

/-- The positive square-root CFC of a self-adjoint Hilbert-Schmidt operator is self-adjoint. -/
theorem carlenRectSqrt_isSelfAdjoint {n : ℕ} {T : HSOp n} (_hT : IsSelfAdjoint T) :
    IsSelfAdjoint (carlenRectSqrt T) := by
  simp [carlenRectSqrt, hsCfcR]

/--
The inverse square-root CFC of a self-adjoint Hilbert-Schmidt operator is
self-adjoint.
-/
theorem carlenRectInvSqrt_isSelfAdjoint {n : ℕ} {T : HSOp n}
    (_hT : IsSelfAdjoint T) :
    IsSelfAdjoint (carlenRectInvSqrt T) := by
  simp [carlenRectInvSqrt, hsCfcR]

/-- On positive spectrum, `sqrt(T) * invsqrt(T)` is the identity. -/
theorem carlenRectSqrt_mul_invSqrt {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectSqrt T * carlenRectInvSqrt T = (1 : HSOp n) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (1 : ℝ) / 2) hσT
  have hcont_inv :
      ContinuousOn (fun x : ℝ => x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    carlenRectSqrt T * carlenRectInvSqrt T
        = hsCfcR
            (fun x : ℝ => x ^ ((1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) T := by
              simpa [carlenRectSqrt, carlenRectInvSqrt, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ => x ^ ((1 : ℝ) / 2))
                  (g := fun x : ℝ => x ^ ((-1 : ℝ) / 2))
                  (a := T) hcont_sqrt hcont_inv).symm
    _ = hsCfcR (fun _ : ℝ => (1 : ℝ)) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((1 : ℝ) / 2) ((-1 : ℝ) / 2)
          have hsum : ((1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = 0 := by ring
          rw [hsum, Real.rpow_zero] at hpow
          simpa using hpow.symm
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (a := T) (ha := hT))

/-- On positive spectrum, `invsqrt(T) * sqrt(T)` is the identity. -/
theorem carlenRectInvSqrt_mul_sqrt {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectInvSqrt T * carlenRectSqrt T = (1 : HSOp n) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (1 : ℝ) / 2) hσT
  have hcont_inv :
      ContinuousOn (fun x : ℝ => x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    carlenRectInvSqrt T * carlenRectSqrt T
        = hsCfcR
            (fun x : ℝ => x ^ ((-1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) T := by
              simpa [carlenRectSqrt, carlenRectInvSqrt, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ => x ^ ((-1 : ℝ) / 2))
                  (g := fun x : ℝ => x ^ ((1 : ℝ) / 2))
                  (a := T) hcont_inv hcont_sqrt).symm
    _ = hsCfcR (fun _ : ℝ => (1 : ℝ)) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((-1 : ℝ) / 2) ((1 : ℝ) / 2)
          have hsum : (((-1 : ℝ) / 2) + (1 : ℝ) / 2 : ℝ) = 0 := by ring
          rw [hsum, Real.rpow_zero] at hpow
          simpa using hpow.symm
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (a := T) (ha := hT))

/-- On positive spectrum, the square of the CFC square root is the operator itself. -/
theorem carlenRectSqrt_sq {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectSqrt T * carlenRectSqrt T = T := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (1 : ℝ) / 2) hσT
  calc
    carlenRectSqrt T * carlenRectSqrt T
        = hsCfcR (fun x : ℝ => x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) T := by
              simpa [carlenRectSqrt, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ => x ^ ((1 : ℝ) / 2))
                  (g := fun x : ℝ => x ^ ((1 : ℝ) / 2))
                  (a := T) hcont_sqrt hcont_sqrt).symm
    _ = hsCfcR (fun x : ℝ => x) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((1 : ℝ) / 2) ((1 : ℝ) / 2)
          have hsum : (((1 : ℝ) / 2) + (1 : ℝ) / 2 : ℝ) = 1 := by ring
          rw [hsum, Real.rpow_one] at hpow
          simpa using hpow.symm
    _ = T := by
          simpa [hsCfcR] using (cfc_id' (R := ℝ) (a := T) (ha := hT))

/-- On positive spectrum, CFC by `x ↦ x⁻¹` is the ring inverse. -/
theorem carlenCfcR_inv_eq_ringInverse {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsCfcR (fun x : ℝ => x⁻¹) T = Ring.inverse T := by
  dsimp [hsCfcR]
  simpa [cfc_id' (R := ℝ) (a := T) (ha := hT)] using
    (cfc_inv (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (f := fun x : ℝ => x) (a := T)
      (fun x hx => ne_of_gt (by simpa [Set.mem_Ioi] using hσT hx)) (ha := hT))

/--
The ring inverse of a positive-spectrum self-adjoint Hilbert--Schmidt operator
is self-adjoint.
-/
theorem carlenRingInverse_isSelfAdjoint {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    IsSelfAdjoint (Ring.inverse T) := by
  rw [← carlenCfcR_inv_eq_ringInverse hT hσT]
  simp [hsCfcR]

/-- Self-adjointness of the direct fixed kernel from the inverse-form facts. -/
theorem jKuboKernel_isSelfAdjoint_of_invForm_facts {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (hInv_sa : IsSelfAdjoint (jKuboKernelInvForm t A B))
    (hσInv : spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ)) :
    IsSelfAdjoint (jKuboKernel t A B) := by
  simpa [jKuboKernel] using
    carlenRingInverse_isSelfAdjoint hInv_sa hσInv

/-- Positive real spectrum of the direct fixed kernel from the inverse-form facts. -/
theorem jKuboKernel_spectrum_subset_Ioi_of_invForm_facts {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (hInv_sa : IsSelfAdjoint (jKuboKernelInvForm t A B))
    (hσInv : spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ (jKuboKernel t A B) ⊆ Set.Ioi (0 : ℝ) := by
  rw [jKuboKernel, ← carlenCfcR_inv_eq_ringInverse hInv_sa hσInv]
  dsimp [hsCfcR]
  have hmap := cfc_map_spectrum (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
    (f := fun x : ℝ => x⁻¹) (a := jKuboKernelInvForm t A B)
    (ha := hInv_sa)
    (hf := by
      intro x hx
      exact
        (continuousAt_inv₀
          (ne_of_gt (by simpa [Set.mem_Ioi] using hσInv hx))).continuousWithinAt)
  refine hmap.symm ▸ ?_
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact inv_pos.mpr (by simpa [Set.mem_Ioi] using hσInv hy)

/-- The fixed-kernel inverse formula from unitness of the inverse form. -/
theorem jKuboKernel_inverse_eq_invForm_of_invForm_facts {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (hInv_unit : IsUnit (jKuboKernelInvForm t A B)) :
    Ring.inverse (jKuboKernel t A B) = jKuboKernelInvForm t A B :=
  jKuboKernel_inverse_eq_invForm_of_isUnit t A B hInv_unit

/-- On positive spectrum, the square of `invsqrt(T)` is the ring inverse of `T`. -/
theorem carlenRectInvSqrt_mul_self_eq_ringInverse {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectInvSqrt T * carlenRectInvSqrt T = Ring.inverse T := by
  have hcont_inv :
      ContinuousOn (fun x : ℝ => x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    carlenContinuousOn_rpow_const_of_IoiSpectrum (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    carlenRectInvSqrt T * carlenRectInvSqrt T
        = hsCfcR (fun x : ℝ => x ^ ((-1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) T := by
              simpa [carlenRectInvSqrt, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ => x ^ ((-1 : ℝ) / 2))
                  (g := fun x : ℝ => x ^ ((-1 : ℝ) / 2))
                  (a := T) hcont_inv hcont_inv).symm
    _ = hsCfcR (fun x : ℝ => x⁻¹) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((-1 : ℝ) / 2) ((-1 : ℝ) / 2)
          have hsum : (((-1 : ℝ) / 2) + (-1 : ℝ) / 2 : ℝ) = -1 := by ring
          rw [hsum, Real.rpow_neg_one] at hpow
          simpa using hpow.symm
    _ = Ring.inverse T := carlenCfcR_inv_eq_ringInverse hT hσT

/-- The rectangle identity `sqrt(T) * T⁻¹ * sqrt(T) = 1`. -/
theorem carlenRectSqrt_mul_ringInverse_mul_sqrt_eq_one {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    carlenRectSqrt T * Ring.inverse T * carlenRectSqrt T = (1 : HSOp n) := by
  rw [← carlenRectInvSqrt_mul_self_eq_ringInverse hT hσT]
  calc
    carlenRectSqrt T * (carlenRectInvSqrt T * carlenRectInvSqrt T) *
        carlenRectSqrt T
        = (carlenRectSqrt T * carlenRectInvSqrt T) *
            (carlenRectInvSqrt T * carlenRectSqrt T) := by
              simp [mul_assoc]
    _ = (1 : HSOp n) := by
          simp [carlenRectSqrt_mul_invSqrt hT hσT, carlenRectInvSqrt_mul_sqrt hT hσT]

/-- The inverse rectangle operator is fixed by Hilbert-Schmidt adjoint when `TΦ⁻¹` is. -/
theorem hsAdjoint_carlenRectInverseOp {n m : ℕ} {V : HSMap n m} {TΦ : HSOp n}
    (hTΦinv_sa : IsSelfAdjoint (Ring.inverse TΦ)) :
    hsAdjoint (carlenRectInverseOp V TΦ) = carlenRectInverseOp V TΦ := by
  have hTΦinv : hsAdjoint (Ring.inverse TΦ) = Ring.inverse TΦ := by
    simpa [hsAdjoint] using hTΦinv_sa
  have hV : hsAdjoint (hsAdjoint V) = V := by
    simp [hsAdjoint]
  calc
    hsAdjoint (carlenRectInverseOp V TΦ)
        = (hsAdjoint ((Ring.inverse TΦ).comp (hsAdjoint V))).comp (hsAdjoint V) := by
            dsimp [carlenRectInverseOp, hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ m) (Mₙ n) (Mₙ m)
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := m))
                (instMatrixNormedAddCommGroup (n := n))
                (instMatrixNormedAddCommGroup (n := m))
                (instMatrixInnerProductSpace (n := m))
                (instMatrixInnerProductSpace (n := n))
                (instMatrixInnerProductSpace (n := m))
                (instMatrixCompleteSpace (n := m))
                (instMatrixCompleteSpace (n := m))
                (instMatrixCompleteSpace (n := n))
                V ((Ring.inverse TΦ).comp (hsAdjoint V)))
    _ = ((hsAdjoint (hsAdjoint V)).comp (hsAdjoint (Ring.inverse TΦ))).comp (hsAdjoint V) := by
          rw [show hsAdjoint ((Ring.inverse TΦ).comp (hsAdjoint V)) =
              (hsAdjoint (hsAdjoint V)).comp (hsAdjoint (Ring.inverse TΦ)) by
            dsimp [hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ m) (Mₙ n) (Mₙ n)
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := m))
                (instMatrixNormedAddCommGroup (n := n))
                (instMatrixNormedAddCommGroup (n := n))
                (instMatrixInnerProductSpace (n := m))
                (instMatrixInnerProductSpace (n := n))
                (instMatrixInnerProductSpace (n := n))
                (instMatrixCompleteSpace (n := m))
                (instMatrixCompleteSpace (n := n))
                (instMatrixCompleteSpace (n := n))
                (Ring.inverse TΦ) (hsAdjoint V))]
    _ = carlenRectInverseOp V TΦ := by
          rw [hV, hTΦinv, ContinuousLinearMap.comp_assoc]
          rfl

/--
For self-adjoint positive-spectrum rectangle data, Hilbert-Schmidt quadratic
order implies the ambient Loewner order for the inverse rectangle.
-/
theorem carlenRectangle_inverse_HSLE_to_le {n m : ℕ}
    {V : HSMap n m} {TA : HSOp m} {TΦ : HSOp n}
    (hTA_sa : IsSelfAdjoint TA) (hTΦ_sa : IsSelfAdjoint TΦ)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ)) :
    HSLE (carlenRectInverseOp V TΦ) (Ring.inverse TA) →
      carlenRectInverseOp V TΦ ≤ Ring.inverse TA := by
  intro hrect
  have hTAinv_sa : IsSelfAdjoint (Ring.inverse TA) :=
    carlenRingInverse_isSelfAdjoint hTA_sa hσTA
  have hTΦinv_sa : IsSelfAdjoint (Ring.inverse TΦ) :=
    carlenRingInverse_isSelfAdjoint hTΦ_sa hσTΦ
  have hlhs_sa : IsSelfAdjoint (carlenRectInverseOp V TΦ) := by
    simpa [hsAdjoint] using
      hsAdjoint_carlenRectInverseOp (V := V) (TΦ := TΦ) hTΦinv_sa
  exact le_of_HSLE_of_isSelfAdjoint hrect (IsSelfAdjoint.sub hTAinv_sa hlhs_sa)


end

end Quantum.TraceInequality.Loewner.HiaiPetz
