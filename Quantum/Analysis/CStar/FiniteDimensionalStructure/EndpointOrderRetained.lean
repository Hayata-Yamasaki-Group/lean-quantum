/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.TransportRetained
import Quantum.Analysis.CStar.CayleySpectrum
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.TraceInequality.LownerHeinz.Defs

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 endpoint order

Carlen 2022 Theorem 1.45 (AH1): CFC twist, endpoint linear control,
inverse-square order, endpoint quotient comparison, and Cayley normalization.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

/-!
### Local instance caches for heavy real-scalar searches

The endpoint CFC comparison repeatedly elaborates real scalar actions on
complex operator algebras.  These local instances register the same winner
terms as the D1 cache fix, avoiding repeated restricted-scalar searches after
local instance changes.
-/

/-- Local cache: real scalar multiplication on operators over an ambient space. -/
private noncomputable local instance instRealSMulCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    SMul ℝ (T →L[ℂ] T) :=
  Algebra.complexToReal.toSMul

/-- Local cache: real module structure on operators over an ambient space. -/
private noncomputable local instance instRealModuleCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    Module ℝ (T →L[ℂ] T) :=
  Module.complexToReal (T →L[ℂ] T)

/-- Local cache: real algebra structure on operators over an ambient space. -/
private noncomputable local instance instRealAlgebraCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    Algebra ℝ (T →L[ℂ] T) :=
  Algebra.complexToReal

/--
Endpoint control reuses the Euclidean compression bridge with expanded CFC
instances.
-/
theorem positiveRayEuclidean_compression_sub_value_zero_of_closedMatrixCfcConvex_endpointControl
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A X : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hA : IsSelfAdjoint A)
    (hAs : spectrum ℝ A ⊆ Set.Ici (0 : ℝ)) (hX : ‖X‖ ≤ 1) :
    LownerHeinzTheorem.cfcR
        (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0)
        (star X * A * X) ≤
      star X *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) A *
        X := by
  exact positiveRayEuclidean_compression_sub_value_zero_of_closedMatrixCfcConvex
    hclosed (continuousOn_Ici_of_closedMatrixConvex_endpointControl hclosed hlin)
    hA hAs hX

private lemma positiveRayEuclidean_star_conjugate_le_of_le
    {n : ℕ}
    {A B T : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hAB : A ≤ B) :
    star T * A * T ≤ star T * B * T := by
  have hnonneg : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hconj : 0 ≤ star T * (B - A) * T := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hnonneg T
  have hsub :
      star T * (B - A) * T = star T * B * T - star T * A * T := by
    simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
  exact sub_nonneg.mp (by simpa [hsub] using hconj)

/--
The endpoint-shift factorization combines endpoint control with CFC order
instances.
-/
theorem positiveRayEuclidean_endpoint_shift_invsqrt_le_of_factorization
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y C IX IY : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hY : IsSelfAdjoint Y)
    (hYs : spectrum ℝ Y ⊆ Set.Ici (0 : ℝ)) (hC : ‖C‖ ≤ 1)
    (hXeq : X = star C * Y * C)
    (hIX : IsSelfAdjoint IX) (hIY : IsSelfAdjoint IY)
    (hCX : C * IX = IY) :
    IX *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
        IX ≤
      IY *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) Y *
        IY := by
  let H := EuclideanSpace ℂ (Fin n)
  have hcomp :
      LownerHeinzTheorem.cfcR
          (ℋ := H) (fun x : ℝ => h x - h 0) X ≤
        star C *
            LownerHeinzTheorem.cfcR
              (ℋ := H) (fun x : ℝ => h x - h 0) Y *
          C := by
    simpa [H, hXeq] using
      positiveRayEuclidean_compression_sub_value_zero_of_closedMatrixCfcConvex_endpointControl
        (h := h) hclosed hlin (n := n) (A := Y) (X := C) hY hYs hC
  have hconj :=
    positiveRayEuclidean_star_conjugate_le_of_le
      (n := n) (T := IX) hcomp
  have hright :
      star IX *
            (star C *
                LownerHeinzTheorem.cfcR
                  (ℋ := H) (fun x : ℝ => h x - h 0) Y *
              C) *
          IX =
        IY *
            LownerHeinzTheorem.cfcR
              (ℋ := H) (fun x : ℝ => h x - h 0) Y *
          IY := by
    calc
      star IX *
            (star C *
                LownerHeinzTheorem.cfcR
                  (ℋ := H) (fun x : ℝ => h x - h 0) Y *
              C) *
          IX =
          star (C * IX) *
              LownerHeinzTheorem.cfcR
                (ℋ := H) (fun x : ℝ => h x - h 0) Y *
            (C * IX) := by
            simp [StarMul.star_mul, mul_assoc]
      _ =
          star IY *
              LownerHeinzTheorem.cfcR
                (ℋ := H) (fun x : ℝ => h x - h 0) Y *
            IY := by
            rw [hCX]
      _ =
          IY *
              LownerHeinzTheorem.cfcR
                (ℋ := H) (fun x : ℝ => h x - h 0) Y *
            IY := by
            rw [hIY.star_eq]
  calc
    IX *
          LownerHeinzTheorem.cfcR
            (ℋ := H) (fun x : ℝ => h x - h 0) X *
        IX =
        star IX *
          LownerHeinzTheorem.cfcR
            (ℋ := H) (fun x : ℝ => h x - h 0) X *
        IX := by
        rw [hIX.star_eq]
    _ ≤
        star IX *
            (star C *
                LownerHeinzTheorem.cfcR
                  (ℋ := H) (fun x : ℝ => h x - h 0) Y *
              C) *
          IX := hconj
    _ =
        IY *
            LownerHeinzTheorem.cfcR
              (ℋ := H) (fun x : ℝ => h x - h 0) Y *
          IY := hright

/-! ### Inverse-square endpoint shift order -/
section PositiveRayEndpointShiftOrder

attribute [local instance] positiveRayEndpointShiftOrderCFC

attribute [local instance] positiveRayEndpointShiftOrderNonnegSpectrumClass

-- The order comparison lemma expands CFC sqrt/rpow instances on Euclidean operators.
private lemma positiveRayEuclidean_norm_invsqrt_mul_sqrt_le_one_of_le
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) (hYpos : IsStrictlyPositive Y)
    (hXY : X ≤ Y) :
    ‖Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X‖ ≤ 1 := by
  have hnorm : ‖CFC.sqrt X * (Y ^ (-(1 / 2) : ℝ))‖ ≤ 1 := by
    exact (le_iff_norm_sqrt_mul_rpow X Y
      (ha := hXpos.nonneg) (hb := hYpos)).mp hXY
  have hsqrt_sa : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hyneg_sa : IsSelfAdjoint (Y ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg
      (CFC.rpow_nonneg (a := Y) (y := (-(1 / 2) : ℝ)))
  have hstar :
      star (CFC.sqrt X * (Y ^ (-(1 / 2) : ℝ))) =
        Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X := by
    rw [StarMul.star_mul, hsqrt_sa.star_eq, hyneg_sa.star_eq]
  calc
    ‖Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X‖ =
        ‖star (CFC.sqrt X * (Y ^ (-(1 / 2) : ℝ)))‖ := by
          rw [hstar]
    _ = ‖CFC.sqrt X * (Y ^ (-(1 / 2) : ℝ))‖ := norm_star _
    _ ≤ 1 := hnorm

-- The sqrt/invsqrt factorization requires repeated CFC rpow instance synthesis.
private lemma positiveRayEuclidean_invsqrt_mul_sqrt_factorization
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) (hYpos : IsStrictlyPositive Y) :
    X =
      star (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) * Y *
        (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) := by
  have hYconj :
      Y ^ (-(1 / 2) : ℝ) * Y * Y ^ (-(1 / 2) : ℝ) =
        (1 : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := by
    simpa using CFC.conjugate_rpow_neg_one_half (a := Y) (ha := hYpos)
  have hsqrt_mul : CFC.sqrt X * CFC.sqrt X = X := by
    simpa using CFC.sqrt_mul_sqrt_self (a := X) (ha := hXpos.nonneg)
  have hsqrt_sa : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hyneg_sa : IsSelfAdjoint (Y ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg
      (CFC.rpow_nonneg (a := Y) (y := (-(1 / 2) : ℝ)))
  calc
    X = CFC.sqrt X * CFC.sqrt X := by rw [hsqrt_mul]
    _ =
        CFC.sqrt X *
            (Y ^ (-(1 / 2) : ℝ) * Y * Y ^ (-(1 / 2) : ℝ)) *
          CFC.sqrt X := by
          rw [hYconj]
          simp
    _ =
        star (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) * Y *
          (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) := by
          rw [StarMul.star_mul, hsqrt_sa.star_eq, hyneg_sa.star_eq]
          simp [mul_assoc]

-- The rpow cancellation proof invokes CFC sqrt and negative half-power instances.
private lemma positiveRayEuclidean_sqrt_mul_invsqrt_eq_one
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) :
    CFC.sqrt X * X ^ (-(1 / 2) : ℝ) =
      (1 : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := by
  rw [CFC.sqrt_eq_rpow]
  rw [← CFC.rpow_add hXpos.isUnit]
  convert CFC.rpow_zero (a := X)
  ring

-- The mixed sqrt/invsqrt cancellation chains the preceding CFC rpow identities.
private lemma positiveRayEuclidean_invsqrt_mul_sqrt_times_invsqrt_eq
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) :
    (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) *
        (X ^ (-(1 / 2) : ℝ)) =
      Y ^ (-(1 / 2) : ℝ) := by
  have hsqrt_inv :
      CFC.sqrt X * X ^ (-(1 / 2) : ℝ) =
        (1 : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) :=
    positiveRayEuclidean_sqrt_mul_invsqrt_eq_one (n := n) hXpos
  calc
    (Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X) *
        X ^ (-(1 / 2) : ℝ) =
        Y ^ (-(1 / 2) : ℝ) *
          (CFC.sqrt X * X ^ (-(1 / 2) : ℝ)) := by
          simp [mul_assoc]
    _ = Y ^ (-(1 / 2) : ℝ) := by
          rw [hsqrt_inv, mul_one]

/-- The theorem-level order bridge assembles the endpoint CFC factorization pipeline. -/
theorem positiveRayEuclidean_endpoint_shift_invsqrt_le_of_order
    {h : ℝ → ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) (hYpos : IsStrictlyPositive Y)
    (hXY : X ≤ Y) :
    X ^ (-(1 / 2) : ℝ) *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
        X ^ (-(1 / 2) : ℝ) ≤
      Y ^ (-(1 / 2) : ℝ) *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) Y *
        Y ^ (-(1 / 2) : ℝ) := by
  let H := EuclideanSpace ℂ (Fin n)
  let C : (H →L[ℂ] H) :=
    Y ^ (-(1 / 2) : ℝ) * CFC.sqrt X
  have hYs : spectrum ℝ Y ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact (hYpos.spectrum_pos hx).le
  have hC : ‖C‖ ≤ 1 := by
    simpa [C, H] using
      positiveRayEuclidean_norm_invsqrt_mul_sqrt_le_one_of_le
        (n := n) hXpos hYpos hXY
  have hXeq : X = star C * Y * C := by
    simpa [C, H] using
      positiveRayEuclidean_invsqrt_mul_sqrt_factorization
        (n := n) hXpos hYpos
  have hIX : IsSelfAdjoint (X ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg
      (CFC.rpow_nonneg (a := X) (y := (-(1 / 2) : ℝ)))
  have hIY : IsSelfAdjoint (Y ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg
      (CFC.rpow_nonneg (a := Y) (y := (-(1 / 2) : ℝ)))
  have hCX : C * (X ^ (-(1 / 2) : ℝ)) =
      Y ^ (-(1 / 2) : ℝ) := by
    simpa [C, H] using
      positiveRayEuclidean_invsqrt_mul_sqrt_times_invsqrt_eq
        (n := n) (Y := Y) hXpos
  exact positiveRayEuclidean_endpoint_shift_invsqrt_le_of_factorization
    (h := h) hclosed hlin (n := n) (X := X) (Y := Y) (C := C)
    (IX := X ^ (-(1 / 2) : ℝ)) (IY := Y ^ (-(1 / 2) : ℝ))
    hYpos.isSelfAdjoint hYs hC hXeq hIX hIY hCX

end PositiveRayEndpointShiftOrder

section PositiveRayEndpointQuotientCFC

attribute [local instance] positiveRayEndpointQuotientCFCCFC

attribute [local instance] positiveRayEndpointQuotientCFCNonnegSpectrumClass

-- The quotient identity unfolds the endpoint quotient through CFC rpow on spectra.
private lemma positiveRayEndpointQuotient_eq_invsqrt_expr_on_spectrum
    {h : ℝ → ℝ} {d : ℝ}
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) :
    Set.EqOn (positiveRayEndpointQuotient h d)
      (fun x : ℝ => x ^ (-(1 / 2) : ℝ) *
        ((h x - h 0) * x ^ (-(1 / 2) : ℝ)))
      (spectrum ℝ X) := by
  intro x hx
  have hxpos : 0 < x := hXpos.spectrum_pos hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hpowmul :
      x ^ (-(1 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) = x⁻¹ := by
    rw [← Real.rpow_add hxpos]
    rw [show (-(1 / 2) + -(1 / 2) : ℝ) = -1 by ring]
    exact Real.rpow_neg_one x
  calc
    positiveRayEndpointQuotient h d x = (h x - h 0) / x := by
      simp [positiveRayEndpointQuotient, hxne]
    _ = (h x - h 0) * x⁻¹ := by
      rw [div_eq_mul_inv]
    _ = x ^ (-(1 / 2) : ℝ) *
        ((h x - h 0) * x ^ (-(1 / 2) : ℝ)) := by
      rw [← hpowmul]
      ring

/-- The CFC quotient equality combines endpoint quotient and invsqrt CFC instances. -/
theorem positiveRayEuclidean_endpointQuotient_cfc_eq_invsqrt
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) :
    LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (positiveRayEndpointQuotient h d) X =
      X ^ (-(1 / 2) : ℝ) *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
        X ^ (-(1 / 2) : ℝ) := by
  have hspec : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hXpos.spectrum_pos hx
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) h :=
    positiveRayScalarConvexOn_Ici_of_closedMatrixOperatorConvex hclosed
  have hcont_ioi : ContinuousOn h (Set.Ioi (0 : ℝ)) := by
    simpa [interior_Ici] using hconv.continuousOn_interior
  have hshift_cont :
      ContinuousOn (fun x : ℝ => h x - h 0) (spectrum ℝ X) := by
    exact (hcont_ioi.mono hspec).sub continuousOn_const
  have hinv_cont :
      ContinuousOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (spectrum ℝ X) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(1 / 2) : ℝ)
      (Or.inl (ne_of_gt (hspec hx)))).continuousWithinAt
  have hquot :
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (positiveRayEndpointQuotient h d) X =
        LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (fun x : ℝ => x ^ (-(1 / 2) : ℝ) *
            ((h x - h 0) * x ^ (-(1 / 2) : ℝ))) X := by
    dsimp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
    apply cfc_congr
    exact positiveRayEndpointQuotient_eq_invsqrt_expr_on_spectrum
      (h := h) (d := d) (n := n) hXpos
  have hmul_right :
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (fun x : ℝ => (h x - h 0) * x ^ (-(1 / 2) : ℝ)) X =
        LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X := by
    simpa [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR] using
      (cfc_mul (R := ℝ)
        (A := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
        (p := IsSelfAdjoint)
        (fun x : ℝ => h x - h 0)
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X
        hshift_cont hinv_cont)
  have hmul_left :
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (fun x : ℝ => x ^ (-(1 / 2) : ℝ) *
            ((h x - h 0) * x ^ (-(1 / 2) : ℝ))) X =
        LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (fun x : ℝ => (h x - h 0) * x ^ (-(1 / 2) : ℝ)) X := by
    simpa [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR] using
      (cfc_mul (R := ℝ)
        (A := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
        (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (-(1 / 2) : ℝ))
        (fun x : ℝ => (h x - h 0) * x ^ (-(1 / 2) : ℝ)) X
        hinv_cont (hshift_cont.mul hinv_cont))
  have hinv_eq :
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X =
        X ^ (-(1 / 2) : ℝ) := by
    simpa [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR] using
      (CFC.rpow_eq_cfc_real
        (A := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
        (a := X) (y := (-(1 / 2) : ℝ)) (ha := hXpos.nonneg)).symm
  calc
    LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (positiveRayEndpointQuotient h d) X =
        LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (fun x : ℝ => x ^ (-(1 / 2) : ℝ) *
            ((h x - h 0) * x ^ (-(1 / 2) : ℝ))) X := hquot
    _ =
        LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X *
          LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (fun x : ℝ => (h x - h 0) * x ^ (-(1 / 2) : ℝ)) X := hmul_left
    _ =
        LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X *
          (LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
            LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) X) := by
          rw [hmul_right]
    _ =
        X ^ (-(1 / 2) : ℝ) *
            LownerHeinzTheorem.cfcR
              (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => h x - h 0) X *
          X ^ (-(1 / 2) : ℝ) := by
          rw [hinv_eq]
          simp [mul_assoc]

/-- The final quotient order comparison composes all endpoint CFC order bridges. -/
theorem positiveRayEuclidean_endpointQuotient_cfc_le_of_order
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {X Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hXpos : IsStrictlyPositive X) (hYpos : IsStrictlyPositive Y)
    (hXY : X ≤ Y) :
    LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (positiveRayEndpointQuotient h d) X ≤
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n)) (positiveRayEndpointQuotient h d) Y := by
  have hXeq := positiveRayEuclidean_endpointQuotient_cfc_eq_invsqrt
    (h := h) (d := d) hclosed (n := n) hXpos
  have hYeq := positiveRayEuclidean_endpointQuotient_cfc_eq_invsqrt
    (h := h) (d := d) hclosed (n := n) hYpos
  rw [hXeq, hYeq]
  exact positiveRayEuclidean_endpoint_shift_invsqrt_le_of_order
    (h := h) hclosed hlin (n := n) hXpos hYpos hXY

private theorem positiveRayEndpointQuotientCFC_cfc_unitToPositiveCayley_eq_one_add_two_kernel
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {a : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (ha_sa : IsSelfAdjoint a)
    (ha : spectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfc unitToPositiveCayley a =
      1 + (2 : ℝ) • cfc (unitIntervalOperatorKernel (-1 : ℝ)) a := by
  have hker :
      ContinuousOn (unitIntervalOperatorKernel (-1 : ℝ)) (spectrum ℝ a) := by
    intro x hx
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := ha hx
    have hden : 1 + (-1 : ℝ) * x ≠ 0 := by
      have : 1 - x ≠ 0 := by linarith [hxI.2]
      simpa [sub_eq_add_neg, mul_comm] using this
    unfold unitIntervalOperatorKernel
    exact continuousAt_id.div
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden
      |>.continuousWithinAt
  calc
    cfc unitToPositiveCayley a =
        cfc (fun y : ℝ => 1 + 2 * unitIntervalOperatorKernel (-1 : ℝ) y) a := by
          apply cfc_congr
          intro y hy
          exact unitToPositiveCayley_eq_one_add_two_kernel
            (ha hy)
    _ =
        1 + (2 : ℝ) • cfc (unitIntervalOperatorKernel (-1 : ℝ)) a := by
          rw [cfc_add (f := fun _ : ℝ => 1)
            (g := fun y : ℝ => 2 * unitIntervalOperatorKernel (-1 : ℝ) y)
            (a := a)
            (hf := continuousOn_const) (hg := continuousOn_const.mul hker)]
          rw [cfc_const_one ℝ (a := a) (ha := ha_sa)]
          rw [cfc_const_mul (r := (2 : ℝ))
            (f := unitIntervalOperatorKernel (-1 : ℝ))
            (a := a) (hf := hker)]

private theorem positiveRayEndpointQuotientCFC_quasispectrum_subset_Ioo_of_spectrum_subset_Ioo
    {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : spectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  rcases (mem_quasispectrum_iff (a := a) (x := x)).mp hx with rfl | hxspec
  · constructor <;> norm_num
  · exact ha hxspec

/-- On an operator with quasispectrum in `(-1, 1)`, the non-unital and unital CFC of the
kernel `unitIntervalOperatorKernel (-1)` agree. -/
private theorem positiveRayEndpointQuotientCFC_cfcₙ_kernel_eq_cfc
    {n : ℕ} {a : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (haq : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a =
      cfc (unitIntervalOperatorKernel (-1 : ℝ)) a := by
  have hcont :
      ContinuousOn (unitIntervalOperatorKernel (-1 : ℝ)) (quasispectrum ℝ a) := by
    intro x hx
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := haq hx
    have hden : 1 + (-1 : ℝ) * x ≠ 0 := by
      have : 1 - x ≠ 0 := by linarith [hxI.2]
      simpa [sub_eq_add_neg, mul_comm] using this
    unfold unitIntervalOperatorKernel
    exact continuousAt_id.div
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden
      |>.continuousWithinAt
  rw [cfcₙ_eq_cfc (hf := hcont)]

private theorem positiveRayEndpointQuotientCFC_cfc_unitToPositiveCayley_mono_of_interval
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A B : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAspec : spectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hBspec : spectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAB : A ≤ B) :
    cfc unitToPositiveCayley A ≤ cfc unitToPositiveCayley B := by
  have hAq : quasispectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1 :=
    positiveRayEndpointQuotientCFC_quasispectrum_subset_Ioo_of_spectrum_subset_Ioo hAspec
  have hBq : quasispectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1 :=
    positiveRayEndpointQuotientCFC_quasispectrum_subset_Ioo_of_spectrum_subset_Ioo hBspec
  have hkerₙ :
      cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) A ≤
        cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) B := by
    exact unitIntervalOperatorKernel_cfcₙ_le_of_neg
      (A := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
      (lambda := (-1 : ℝ))
      (by norm_num) (by constructor <;> norm_num)
      hA hB hAq hBq hAB
  have hker :
      cfc (unitIntervalOperatorKernel (-1 : ℝ)) A ≤
        cfc (unitIntervalOperatorKernel (-1 : ℝ)) B := by
    rwa [positiveRayEndpointQuotientCFC_cfcₙ_kernel_eq_cfc hAq,
      positiveRayEndpointQuotientCFC_cfcₙ_kernel_eq_cfc hBq] at hkerₙ
  rw [positiveRayEndpointQuotientCFC_cfc_unitToPositiveCayley_eq_one_add_two_kernel
      (n := n) hA hAspec,
    positiveRayEndpointQuotientCFC_cfc_unitToPositiveCayley_eq_one_add_two_kernel
      (n := n) hB hBspec]
  exact add_le_add_right
    (smul_le_smul_of_nonneg_left hker (by norm_num : (0 : ℝ) ≤ 2)) 1

private theorem positiveRayEndpointQuotientCFC_cfc_pullback_eq_cfc_cayley
    {h : ℝ → ℝ} {d : ℝ}
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hA : IsSelfAdjoint A)
    (hAspec : spectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1) :
    LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A =
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (positiveRayEndpointQuotient h d) (cfc unitToPositiveCayley A) := by
  haveI : FiniteDimensional ℂ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.finiteDimensional
  have hphiCont : ContinuousOn unitToPositiveCayley (spectrum ℝ A) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo
      hAspec
  have hfinite : (spectrum ℝ A).Finite :=
    positiveRayEndpointQuotientCFC_spectrum_real_finite_of_finiteDimensional_complex
      (B := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) A
  have hqCont :
      ContinuousOn (positiveRayEndpointQuotient h d)
        (unitToPositiveCayley '' spectrum ℝ A) :=
    (hfinite.image unitToPositiveCayley).continuousOn _
  dsimp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  simpa [positiveCayleyPullback] using
    (cfc_comp' (R := ℝ)
      (A := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
      (p := IsSelfAdjoint)
      (g := positiveRayEndpointQuotient h d)
      (f := unitToPositiveCayley) (a := A)
      (hg := hqCont) (hf := hphiCont) (ha := hA))

/--
CFC composition and strict-positivity goals create many concrete matrix
instances.  The proof normalizes several CFC expressions before applying the
positive-ray order theorem.
-/
theorem positiveRayEuclidean_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A B : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAspec : spectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hBspec : spectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAB : A ≤ B) :
    LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A ≤
      LownerHeinzTheorem.cfcR
          (ℋ := EuclideanSpace ℂ (Fin n))
          (positiveCayleyPullback (positiveRayEndpointQuotient h d)) B := by
  let X : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    cfc unitToPositiveCayley A
  let Y : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    cfc unitToPositiveCayley B
  have hphiA : ContinuousOn unitToPositiveCayley (spectrum ℝ A) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo
      hAspec
  have hphiB : ContinuousOn unitToPositiveCayley (spectrum ℝ B) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo
      hBspec
  have hXpos : IsStrictlyPositive X := by
    dsimp [X]
    rw [cfc_isStrictlyPositive_iff (R := ℝ) (p := IsSelfAdjoint)
      (f := unitToPositiveCayley) (a := A) hphiA hA]
    intro x hx
    exact unitToPositiveCayley_mem_Ioi (hAspec hx)
  have hYpos : IsStrictlyPositive Y := by
    dsimp [Y]
    rw [cfc_isStrictlyPositive_iff (R := ℝ) (p := IsSelfAdjoint)
      (f := unitToPositiveCayley) (a := B) hphiB hB]
    intro x hx
    exact unitToPositiveCayley_mem_Ioi (hBspec hx)
  have hXY : X ≤ Y := by
    simpa [X, Y] using
      positiveRayEndpointQuotientCFC_cfc_unitToPositiveCayley_mono_of_interval
        (n := n) hA hB hAspec hBspec hAB
  have hmono := positiveRayEuclidean_endpointQuotient_cfc_le_of_order
    (h := h) (d := d) hclosed hlin (n := n)
    (X := X) (Y := Y) hXpos hYpos hXY
  have hAe :=
    positiveRayEndpointQuotientCFC_cfc_pullback_eq_cfc_cayley
      (h := h) (d := d) (n := n) hA hAspec
  have hBe :=
    positiveRayEndpointQuotientCFC_cfc_pullback_eq_cfc_cayley
      (h := h) (d := d) (n := n) hB hBspec
  simpa [X, Y, hAe, hBe] using hmono

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
