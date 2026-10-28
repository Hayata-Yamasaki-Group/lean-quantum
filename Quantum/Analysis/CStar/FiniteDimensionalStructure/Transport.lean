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
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.Trace

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 transport

Carlen 2022 Theorem 1.45 (AH1): star-equivalence transport, Euclidean
compression, endpoint perturbation continuity, and scalar restriction.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

-- Keep the complex-to-real algebra local to the real-spectrum transport proofs.
noncomputable local instance instAH1TransportCStarMatrixRealAlgebra {n : ℕ} :
    Algebra ℝ (CStarMatrix (Fin n) (Fin n) ℂ) := Algebra.complexToReal

/-! ### Star-equivalence transport and Euclidean compression -/
/-- Regard a unital star algebra equivalence as a unital star algebra homomorphism. -/
def starAlgEquivToStarAlgHom {A B : Type*}
    [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (e : A ≃⋆ₐ[ℂ] B) : A →⋆ₐ[ℂ] B :=
  { e.toAlgEquiv.toAlgHom with
    map_star' := by
      intro x
      exact map_star e x }

/-- Regard a star algebra equivalence as a non-unital star algebra homomorphism. -/
def starAlgEquivToNonUnitalStarAlgHom {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B] [Star B]
    (e : A ≃⋆ₐ[ℂ] B) : A →⋆ₙₐ[ℂ] B where
  toFun := e
  map_zero' := map_zero e
  map_add' := map_add e
  map_mul' := map_mul e
  map_smul' := map_smul e
  map_star' := map_star e

private lemma starAlgEquiv_reflect_le {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x y : A} (hxy : e x ≤ e y) :
    x ≤ y := by
  have hback := OrderHomClass.mono e.symm hxy
  simpa using hback

/--
Subtracting the endpoint value preserves closed-positive operator convexity.

This is the normalization used before applying the Bendat--Sherman compression:
`x ↦ h x - h 0` has value `0` at the endpoint.
-/
theorem operatorConvexOn_Ici_sub_value_zero
    {𝓐 : Type*}
    [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [ContinuousFunctionalCalculus ℝ 𝓐 IsSelfAdjoint] [Nontrivial 𝓐]
    [NonnegSpectrumClass ℝ 𝓐]
    {h : ℝ → ℝ}
    (hconv : LownerHeinzCore.OperatorConvexOn
      (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ => h x - h 0) := by
  intro A B t hA hB ht0 ht1 hAs hBs
  let C : 𝓐 := (1 - t) • A + t • B
  let c0 : 𝓐 := algebraMap ℝ 𝓐 (h 0)
  have hA0 : (0 : 𝓐) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    exact hAs hx
  have hB0 : (0 : 𝓐) ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    exact hBs hx
  have hCsa : IsSelfAdjoint C := by
    dsimp [C]
    exact (IsSelfAdjoint.smul (IsSelfAdjoint.all (1 - t)) hA).add
      (IsSelfAdjoint.smul (IsSelfAdjoint.all t) hB)
  have hC0 : (0 : 𝓐) ≤ C := by
    dsimp [C]
    exact add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hA0) (smul_nonneg ht0 hB0)
  have hCs : spectrum ℝ C ⊆ Set.Ici (0 : ℝ) := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) C (ha := hCsa)).1 hC0
  have hleft :
      LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) C =
        LownerHeinzCore.cfcR (𝓐 := 𝓐) h C - c0 := by
    dsimp [LownerHeinzCore.cfcR, c0]
    rw [cfc_sub (f := h) (g := fun _ : ℝ => h 0) (a := C)
      (hf := hcont.mono hCs) (hg := continuousOn_const)]
    rw [cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := h 0)
      (a := C) (ha := hCsa)]
  have hAeq :
      LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) A =
        LownerHeinzCore.cfcR (𝓐 := 𝓐) h A - c0 := by
    dsimp [LownerHeinzCore.cfcR, c0]
    rw [cfc_sub (f := h) (g := fun _ : ℝ => h 0) (a := A)
      (hf := hcont.mono hAs) (hg := continuousOn_const)]
    rw [cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := h 0)
      (a := A) (ha := hA)]
  have hBeq :
      LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) B =
        LownerHeinzCore.cfcR (𝓐 := 𝓐) h B - c0 := by
    dsimp [LownerHeinzCore.cfcR, c0]
    rw [cfc_sub (f := h) (g := fun _ : ℝ => h 0) (a := B)
      (hf := hcont.mono hBs) (hg := continuousOn_const)]
    rw [cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := h 0)
      (a := B) (ha := hB)]
  have hconv' :
      LownerHeinzCore.cfcR (𝓐 := 𝓐) h C ≤
        (1 - t) • LownerHeinzCore.cfcR (𝓐 := 𝓐) h A +
          t • LownerHeinzCore.cfcR (𝓐 := 𝓐) h B := by
    simpa [C] using hconv (A := A) (B := B) (t := t) hA hB ht0 ht1 hAs hBs
  calc
    LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) C
        ≤ ((1 - t) • LownerHeinzCore.cfcR (𝓐 := 𝓐) h A +
            t • LownerHeinzCore.cfcR (𝓐 := 𝓐) h B) - c0 := by
          rw [hleft]
          exact sub_le_sub_right hconv' c0
    _ = (1 - t) • LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) A +
          t • LownerHeinzCore.cfcR (𝓐 := 𝓐) (fun x : ℝ => h x - h 0) B := by
          rw [hAeq, hBeq]
          module

/-- A continuous star-algebra homomorphism into `CStarMatrix` commutes with real CFC. -/
lemma cstarMatrix_starAlgHom_map_cfc {𝓑 : Type*}
    [CStarAlgebra 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint]
    {h : ℝ → ℝ} {n : ℕ}
    (φ : 𝓑 →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    {A : 𝓑} (hA : IsSelfAdjoint A)
    (hf : ContinuousOn h (spectrum ℝ A))
    (hφ : Continuous φ)
    (hφA : IsSelfAdjoint (φ A)) :
    φ (cfc h A) = cfc h (φ A) := by
  exact @StarAlgHomClass.map_cfc
    (𝓑 →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    ℝ ℂ 𝓑 (CStarMatrix (Fin n) (Fin n) ℂ)
    IsSelfAdjoint IsSelfAdjoint
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CStarMatrix.instIsScalarTower
    _ _ _ _ _ _
    φ h A hf hφ hA hφA

/--
Transport closed positive-ray operator convexity from a finite `CStarMatrix` model
across a star-algebra equivalence.
-/
theorem operatorConvexOnClosedPositive_starAlgEquiv_of_cstarMatrix
    {𝓑 : Type*}
    [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑]
    {h : ℝ → ℝ} {n : ℕ}
    (e : 𝓑 ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hcont :
      ∀ ⦃X : 𝓑⦄, IsSelfAdjoint X → ContinuousOn h (spectrum ℝ X))
    (hcstar :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) (Set.Ici (0 : ℝ)) h) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑) (Set.Ici (0 : ℝ)) h := by
  intro A B t hA hB ht0 ht1 hAs hBs
  let φ : 𝓑 →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ :=
    starAlgEquivToStarAlgHom e
  have hφcont : Continuous φ := by
    simpa [φ, starAlgEquivToStarAlgHom] using
      (StarAlgEquiv.isometry e).continuous
  have hAe : IsSelfAdjoint (φ A) := hA.map φ
  have hBe : IsSelfAdjoint (φ B) := hB.map φ
  have hAs_e : spectrum ℝ (φ A) ⊆ Set.Ici (0 : ℝ) := by
    have hφinj : Function.Injective φ := by
      simpa [φ, starAlgEquivToStarAlgHom] using e.injective
    rw [hA.map_spectrum_real φ hφinj]
    exact hAs
  have hBs_e : spectrum ℝ (φ B) ⊆ Set.Ici (0 : ℝ) := by
    have hφinj : Function.Injective φ := by
      simpa [φ, starAlgEquivToStarAlgHom] using e.injective
    rw [hB.map_spectrum_real φ hφinj]
    exact hBs
  have htarget := hcstar hAe hBe ht0 ht1 hAs_e hBs_e
  have hmap_real_smul :
      ∀ (r : ℝ) (X : 𝓑), φ (r • X) = r • φ X := by
    intro r X
    have hsrc : (r • X : 𝓑) = (r : ℂ) • X := by
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) r X
    calc
      φ (r • X) = φ ((r : ℂ) • X) := by rw [hsrc]
      _ = (r : ℂ) • φ X := by exact map_smul φ (r : ℂ) X
      _ = r • φ X := by
        ext i j
        simp [CStarMatrix.smul_apply, Complex.real_smul]
  have hcombo :
      φ ((1 - t) • A + t • B) = (1 - t) • φ A + t • φ B := by
    calc
      φ ((1 - t) • A + t • B) =
          φ ((1 - t) • A) + φ (t • B) := by rw [map_add]
      _ = (1 - t) • φ A + t • φ B := by
        rw [hmap_real_smul (1 - t) A, hmap_real_smul t B]
  have hcombo_sa : IsSelfAdjoint ((1 - t) • A + t • B) :=
    (IsSelfAdjoint.smul (IsSelfAdjoint.all (1 - t)) hA).add
      (IsSelfAdjoint.smul (IsSelfAdjoint.all t) hB)
  have hleft :
      φ (LownerHeinzCore.cfcR h ((1 - t) • A + t • B)) =
        LownerHeinzCore.cfcR h ((1 - t) • φ A + t • φ B) := by
    dsimp [LownerHeinzCore.cfcR]
    have hmap_combo :
        φ (cfc h ((1 - t) • A + t • B)) =
      cfc h (φ ((1 - t) • A + t • B)) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hcombo_sa (hcont hcombo_sa) hφcont (hcombo_sa.map φ)
    calc
      φ (cfc h ((1 - t) • A + t • B)) =
          cfc h (φ ((1 - t) • A + t • B)) := hmap_combo
      _ = cfc h ((1 - t) • φ A + t • φ B) := by rw [hcombo]
  have hright :
      φ ((1 - t) • LownerHeinzCore.cfcR h A + t • LownerHeinzCore.cfcR h B) =
        (1 - t) • LownerHeinzCore.cfcR h (φ A) +
          t • LownerHeinzCore.cfcR h (φ B) := by
    dsimp [LownerHeinzCore.cfcR]
    have hmapA : φ (cfc h A) = cfc h (φ A) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hA (hcont hA) hφcont hAe
    have hmapB : φ (cfc h B) = cfc h (φ B) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hB (hcont hB) hφcont hBe
    calc
      φ ((1 - t) • cfc h A + t • cfc h B) =
          (1 - t) • φ (cfc h A) + t • φ (cfc h B) := by
        rw [map_add, hmap_real_smul (1 - t) (cfc h A),
          hmap_real_smul t (cfc h B)]
      _ = (1 - t) • cfc h (φ A) + t • cfc h (φ B) := by
        rw [hmapA, hmapB]
  have hφineq :
      φ (LownerHeinzCore.cfcR h ((1 - t) • A + t • B)) ≤
        φ ((1 - t) • LownerHeinzCore.cfcR h A + t • LownerHeinzCore.cfcR h B) := by
    simpa [hleft, hright] using htarget
  apply starAlgEquiv_reflect_le (A := 𝓑)
    (B := CStarMatrix (Fin n) (Fin n) ℂ) e
  simpa [φ, starAlgEquivToStarAlgHom] using hφineq

/--
Closed positive-ray matrix CFC convexity gives operator convexity after transport
across a finite-dimensional star-algebra equivalence.
-/
theorem operatorConvexOnClosedPositive_starAlgEquiv_of_closedMatrixCfcConvex
    {𝓑 : Type*}
    [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑]
    {h : ℝ → ℝ} {n : ℕ}
    (e : 𝓑 ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hcont :
      ∀ ⦃X : 𝓑⦄, IsSelfAdjoint X → ContinuousOn h (spectrum ℝ X))
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h)) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑) (Set.Ici (0 : ℝ)) h :=
  operatorConvexOnClosedPositive_starAlgEquiv_of_cstarMatrix e hcont
    (operatorConvexOnClosedPositive_cstarMatrix_of_closedMatrixCfcConvex hclosed n)

/--
Transport finite-dimensional closed-positive operator convexity across a
star-algebra equivalence, using only continuity on the closed positive ray.
-/
theorem operatorConvexOnClosedPositive_starAlgEquiv_of_cstarMatrix_on_Ici
    {𝓑 : Type*}
    [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑]
    [NonnegSpectrumClass ℝ 𝓑]
    {h : ℝ → ℝ} {n : ℕ}
    (e : 𝓑 ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hcontIci : ContinuousOn h (Set.Ici (0 : ℝ)))
    (hcstar :
    LownerHeinzCore.OperatorConvexOn
      (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) (Set.Ici (0 : ℝ)) h) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑) (Set.Ici (0 : ℝ)) h := by
  intro A B t hA hB ht0 ht1 hAs hBs
  let φ : 𝓑 →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ :=
    starAlgEquivToStarAlgHom e
  have hφcont : Continuous φ := by
    simpa [φ, starAlgEquivToStarAlgHom] using
      (StarAlgEquiv.isometry e).continuous
  have hAe : IsSelfAdjoint (φ A) := hA.map φ
  have hBe : IsSelfAdjoint (φ B) := hB.map φ
  have hAs_e : spectrum ℝ (φ A) ⊆ Set.Ici (0 : ℝ) := by
    have hφinj : Function.Injective φ := by
      simpa [φ, starAlgEquivToStarAlgHom] using e.injective
    rw [hA.map_spectrum_real φ hφinj]
    exact hAs
  have hBs_e : spectrum ℝ (φ B) ⊆ Set.Ici (0 : ℝ) := by
    have hφinj : Function.Injective φ := by
      simpa [φ, starAlgEquivToStarAlgHom] using e.injective
    rw [hB.map_spectrum_real φ hφinj]
    exact hBs
  have htarget := hcstar hAe hBe ht0 ht1 hAs_e hBs_e
  have hmap_real_smul :
      ∀ (r : ℝ) (X : 𝓑), φ (r • X) = r • φ X := by
    intro r X
    have hsrc : (r • X : 𝓑) = (r : ℂ) • X := by
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) r X
    calc
      φ (r • X) = φ ((r : ℂ) • X) := by rw [hsrc]
      _ = (r : ℂ) • φ X := by exact map_smul φ (r : ℂ) X
      _ = r • φ X := by
        ext i j
        simp [CStarMatrix.smul_apply, Complex.real_smul]
  have hcombo :
      φ ((1 - t) • A + t • B) = (1 - t) • φ A + t • φ B := by
    calc
      φ ((1 - t) • A + t • B) =
          φ ((1 - t) • A) + φ (t • B) := by rw [map_add]
      _ = (1 - t) • φ A + t • φ B := by
        rw [hmap_real_smul (1 - t) A, hmap_real_smul t B]
  have hcombo_sa : IsSelfAdjoint ((1 - t) • A + t • B) :=
    (IsSelfAdjoint.smul (IsSelfAdjoint.all (1 - t)) hA).add
      (IsSelfAdjoint.smul (IsSelfAdjoint.all t) hB)
  have hA0 : (0 : 𝓑) ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    exact hAs hx
  have hB0 : (0 : 𝓑) ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    exact hBs hx
  have hcombo0 : (0 : 𝓑) ≤ (1 - t) • A + t • B := by
    exact add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hA0) (smul_nonneg ht0 hB0)
  have hcombo_spec : spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ici (0 : ℝ) := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg
      (R := ℝ) ((1 - t) • A + t • B) (ha := hcombo_sa)).1 hcombo0
  have hleft :
      φ (LownerHeinzCore.cfcR h ((1 - t) • A + t • B)) =
        LownerHeinzCore.cfcR h ((1 - t) • φ A + t • φ B) := by
    dsimp [LownerHeinzCore.cfcR]
    have hmap_combo :
        φ (cfc h ((1 - t) • A + t • B)) =
      cfc h (φ ((1 - t) • A + t • B)) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hcombo_sa (hcontIci.mono hcombo_spec) hφcont (hcombo_sa.map φ)
    calc
      φ (cfc h ((1 - t) • A + t • B)) =
          cfc h (φ ((1 - t) • A + t • B)) := hmap_combo
      _ = cfc h ((1 - t) • φ A + t • φ B) := by rw [hcombo]
  have hright :
      φ ((1 - t) • LownerHeinzCore.cfcR h A + t • LownerHeinzCore.cfcR h B) =
        (1 - t) • LownerHeinzCore.cfcR h (φ A) +
          t • LownerHeinzCore.cfcR h (φ B) := by
    dsimp [LownerHeinzCore.cfcR]
    have hmapA : φ (cfc h A) = cfc h (φ A) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hA (hcontIci.mono hAs) hφcont hAe
    have hmapB : φ (cfc h B) = cfc h (φ B) := by
      exact cstarMatrix_starAlgHom_map_cfc
        (φ := φ) hB (hcontIci.mono hBs) hφcont hBe
    calc
      φ ((1 - t) • cfc h A + t • cfc h B) =
          (1 - t) • φ (cfc h A) + t • φ (cfc h B) := by
        rw [map_add, hmap_real_smul (1 - t) (cfc h A),
          hmap_real_smul t (cfc h B)]
      _ = (1 - t) • cfc h (φ A) + t • cfc h (φ B) := by
        rw [hmapA, hmapB]
  have hφineq :
      φ (LownerHeinzCore.cfcR h ((1 - t) • A + t • B)) ≤
        φ ((1 - t) • LownerHeinzCore.cfcR h A + t • LownerHeinzCore.cfcR h B) := by
    simpa [hleft, hright] using htarget
  apply starAlgEquiv_reflect_le (A := 𝓑)
    (B := CStarMatrix (Fin n) (Fin n) ℂ) e
  simpa [φ, starAlgEquivToStarAlgHom] using hφineq

/--
Closed positive-ray matrix CFC convexity transports across a star-algebra equivalence
using only continuity on `[0,∞)`.
-/
theorem operatorConvexOnClosedPositive_starAlgEquiv_of_closedMatrixCfcConvex_on_Ici
    {𝓑 : Type*}
    [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑]
    [NonnegSpectrumClass ℝ 𝓑]
    {h : ℝ → ℝ} {n : ℕ}
    (e : 𝓑 ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hcontIci : ContinuousOn h (Set.Ici (0 : ℝ)))
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h)) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑) (Set.Ici (0 : ℝ)) h :=
  operatorConvexOnClosedPositive_starAlgEquiv_of_cstarMatrix_on_Ici e hcontIci
    (operatorConvexOnClosedPositive_cstarMatrix_of_closedMatrixCfcConvex hclosed n)

/--
The direct star-algebra equivalence from operators on a finite Euclidean space
to the corresponding `CStarMatrix` algebra.
-/
noncomputable def positiveRayOperatorCStarMatrixEquiv (n : ℕ) :
    (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm.trans
    (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin n))

/-! ### Endpoint perturbation continuity and scalar restriction -/
private lemma positiveRayMatrix_spectrum_nonneg_of_posSemidef {n : ℕ}
    {X : HansenPedersen.Mₙ n} (hX : X.PosSemidef) :
    spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  classical
  obtain ⟨i, rfl⟩ := Set.ext_iff.mp
    (Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues (𝕜 := ℂ) hX.isHermitian) x |>.mp hx
  exact hX.eigenvalues_nonneg _

/--
If a scalar function is continuous on the closed positive ray, then its
finite-dimensional CFC values are continuous under the perturbation
`X ↦ X + ε I` from the right at every positive semidefinite Hermitian matrix.
-/
theorem positiveRayMatrixEndpointPerturbationContinuous_of_continuousOn_Ici
    {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) :
    PositiveRayMatrixEndpointPerturbationContinuous h := by
  intro n X hXherm hXpsd
  obtain ⟨S, ⟨hSnhds, hScompact⟩, _⟩ :=
    spectrum.isCompact (𝕜 := ℝ) X |>.nhdsSet_basis_isCompact.mem_iff.mp
      (univ_mem : Set.univ ∈ 𝓝ˢ (spectrum ℝ X))
  let K : Set ℝ := S ∩ Set.Ici (0 : ℝ)
  have hKcompact : IsCompact K := hScompact.inter_right isClosed_Ici
  have hfcont : ContinuousOn h K := hcont.mono (by intro x hx; exact hx.2)
  have hshift :
      Tendsto (fun ε : ℝ => X + ε • (1 : HansenPedersen.Mₙ n))
        (𝓝[>] (0 : ℝ)) (𝓝 X) := by
    have hcont_shift :
        ContinuousAt (fun ε : ℝ => X + ε • (1 : HansenPedersen.Mₙ n)) 0 := by
      fun_prop
    have hzero : X + (0 : ℝ) • (1 : HansenPedersen.Mₙ n) = X := by
      ext i j
      simp
    simpa [hzero] using
      hcont_shift.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hspecS_near :
      ∀ᶠ Y : HansenPedersen.Mₙ n in 𝓝 X, spectrum ℝ Y ⊆ S := by
    exact (upperHemicontinuous_spectrum ℝ (HansenPedersen.Mₙ n)).upperHemicontinuousAt
      X _ hSnhds |>.mono fun _ => subset_of_mem_nhdsSet
  have hspecS_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (X + ε • (1 : HansenPedersen.Mₙ n)) ⊆ S :=
    hshift.eventually hspecS_near
  have hspec_nonneg_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (X + ε • (1 : HansenPedersen.Mₙ n)) ⊆ Set.Ici (0 : ℝ) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    exact positiveRayMatrix_spectrum_nonneg_of_posSemidef
      (n := n) ((positiveRayMat_add_pos_scalar_one_posDef hXpsd hε.1).posSemidef)
  have hspec_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (X + ε • (1 : HansenPedersen.Mₙ n)) ⊆ K := by
    filter_upwards [hspecS_eventually, hspec_nonneg_eventually] with ε hS hnon x hx
    exact ⟨hS hx, hnon hx⟩
  have hpred_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsSelfAdjoint (X + ε • (1 : HansenPedersen.Mₙ n)) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    have hXε : (X + ε • (1 : HansenPedersen.Mₙ n)).PosDef :=
      positiveRayMat_add_pos_scalar_one_posDef hXpsd hε.1
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact hXε.isHermitian
  have hXsa : IsSelfAdjoint X := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact hXherm
  have hcfc :
      Tendsto
        (fun ε : ℝ => cfc h (X + ε • (1 : HansenPedersen.Mₙ n)))
        (𝓝[>] (0 : ℝ)) (𝓝 (cfc h X)) :=
    hshift.cfc
      hKcompact
      h hspec_eventually hpred_eventually
      (by
        intro x hx
        exact ⟨subset_of_mem_nhdsSet hSnhds hx,
          positiveRayMatrix_spectrum_nonneg_of_posSemidef hXpsd hx⟩)
      hXsa hfcont
  have hsource :
      (fun ε : ℝ => positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => cfc h (X + ε • (1 : HansenPedersen.Mₙ n))) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    dsimp [positiveRayMatrixCfc]
    have hXε : (X + ε • (1 : HansenPedersen.Mₙ n)).PosDef :=
      positiveRayMat_add_pos_scalar_one_posDef hXpsd hε.1
    rw [dif_pos hXε.isHermitian]
    exact (Matrix.IsHermitian.cfc_eq hXε.isHermitian h).symm
  have htarget : positiveRayMatrixCfc h n X = cfc h X := by
    dsimp [positiveRayMatrixCfc]
    rw [dif_pos hXherm]
    exact (Matrix.IsHermitian.cfc_eq hXherm h).symm
  have hsource_tendsto :
      Tendsto
        (fun ε : ℝ => positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
        (𝓝[>] (0 : ℝ)) (𝓝 (cfc h X)) :=
    hcfc.congr' hsource.symm
  simpa [htarget] using hsource_tendsto

/-- The `1 × 1` scalar matrix is the real algebra map into `PositiveRayMat 1`. -/
lemma positiveRayScalarMatrix_eq_algebraMap (x : ℝ) :
    positiveRayScalarMatrix x = algebraMap ℝ (HansenPedersen.Mₙ 1) x := by
  ext i j
  fin_cases i
  fin_cases j
  have hentry :=
    congrFun
      (congrFun
        (Matrix.algebraMap_eq_diagonal (n := Fin 1) (R := ℝ) (α := ℂ) x) 0) 0
  change (x : ℂ) = (algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ) x) 0 0
  calc
    (x : ℂ) = diagonal ((algebraMap ℝ (Fin 1 → ℂ)) x) 0 0 := by
      simp [Pi.algebraMap_def]
    _ = (algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ) x) 0 0 := hentry.symm

/-- A `1 × 1` scalar matrix over a real scalar is Hermitian. -/
lemma positiveRayScalarMatrix_isHermitian (x : ℝ) :
    (positiveRayScalarMatrix x).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  ext i j
  fin_cases i
  fin_cases j
  simp [positiveRayScalarMatrix]

/-- A nonnegative real scalar gives a positive semidefinite `1 × 1` scalar matrix. -/
lemma positiveRayScalarMatrix_posSemidef {x : ℝ} (hx : 0 ≤ x) :
    (positiveRayScalarMatrix x).PosSemidef := by
  unfold positiveRayScalarMatrix
  apply Matrix.PosSemidef.diagonal
  change ∀ _ : Fin 1, (0 : ℂ) ≤ (x : ℂ)
  intro _
  exact_mod_cast hx

/-- Matrix CFC on a `1 × 1` scalar matrix evaluates the scalar function. -/
lemma positiveRayMatrixCfc_scalarMatrix_of_real {g : ℝ → ℝ} (x : ℝ) :
    positiveRayMatrixCfc g 1 (positiveRayScalarMatrix x) =
      positiveRayScalarMatrix (g x) := by
  unfold positiveRayMatrixCfc
  rw [dif_pos (positiveRayScalarMatrix_isHermitian x)]
  rw [← Matrix.IsHermitian.cfc_eq (positiveRayScalarMatrix_isHermitian x) g]
  rw [positiveRayScalarMatrix_eq_algebraMap x]
  have hcfc :
      cfc g ((algebraMap ℝ (HansenPedersen.Mₙ 1)) x) =
        (algebraMap ℝ (HansenPedersen.Mₙ 1)) (g x) :=
    cfc_algebraMap (A := HansenPedersen.Mₙ 1) x g
  exact hcfc.trans (positiveRayScalarMatrix_eq_algebraMap (g x)).symm

/-- Matrix CFC on a positive `1 × 1` scalar matrix evaluates the scalar function. -/
lemma positiveRayMatrixCfc_scalarMatrix {g : ℝ → ℝ} {x : ℝ} (_hx : 0 < x) :
    positiveRayMatrixCfc g 1 (positiveRayScalarMatrix x) =
      positiveRayScalarMatrix (g x) := by
  exact positiveRayMatrixCfc_scalarMatrix_of_real (g := g) x

/-- The quadratic form of a `1 × 1` scalar matrix on the scalar vector is its entry. -/
lemma positiveRayQForm_scalarMatrix (y : ℝ) :
    positiveRayQForm (positiveRayScalarMatrix y) (positiveRayScalarVector 1) = y := by
  unfold positiveRayQForm positiveRayScalarMatrix positiveRayScalarVector
  simp [dotProduct, Matrix.mulVec]

/-- A `1 × 1` matrix order inequality is the corresponding scalar inequality. -/
lemma positiveRayScalarMatrix_entry_le_of_matrix_le {a b : ℝ}
    (h : positiveRayScalarMatrix a ≤ positiveRayScalarMatrix b) : a ≤ b := by
  rw [Matrix.le_iff] at h
  have hq := h.dotProduct_mulVec_nonneg (positiveRayScalarVector 1)
  have hre :
      0 ≤ Complex.re (star (positiveRayScalarVector 1) ⬝ᵥ
        (positiveRayScalarMatrix b - positiveRayScalarMatrix a) *ᵥ
          positiveRayScalarVector 1) := by
    exact (Complex.nonneg_iff.mp hq).1
  change
      0 ≤ positiveRayQForm
        (positiveRayScalarMatrix b - positiveRayScalarMatrix a)
        (positiveRayScalarVector 1) at hre
  rw [positiveRayQForm_sub, positiveRayQForm_scalarMatrix,
    positiveRayQForm_scalarMatrix] at hre
  exact sub_nonneg.mp hre

/--
Restricting finite-dimensional positive-ray matrix CFC convexity to `1 × 1`
matrices gives ordinary scalar convexity on `(0,∞)`.
-/
theorem positiveRayScalarConvex_of_matrixOperatorConvex {h : ℝ → ℝ}
    (hconvex : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfc h)) :
    PositiveRayScalarConvex h := by
  intro x y θ hx hy hθ0 hθ1
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hcombo_pos : 0 < θ * x + (1 - θ) * y := by
    by_cases hθzero : θ = 0
    · subst θ
      simpa using hy
    · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθzero)
      exact add_pos_of_pos_of_nonneg (mul_pos hθpos hx) (mul_nonneg h1θ hy.le)
  have hmat := hconvex
    (n := 1)
    (X := positiveRayScalarMatrix x)
    (Y := positiveRayScalarMatrix y)
    (θ := θ)
    (positiveRayScalarMatrix_posDef hx)
    (positiveRayScalarMatrix_posDef hy)
    hθ0 hθ1
  rw [positiveRayScalarMatrix_convexCombo] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix (g := h) hcombo_pos] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix (g := h) hx] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix (g := h) hy] at hmat
  rw [positiveRayScalarMatrix_convexCombo] at hmat
  exact positiveRayScalarMatrix_entry_le_of_matrix_le hmat

/--
Restricting closed positive-ray matrix CFC convexity to `1 × 1` matrices gives
ordinary scalar convexity on the closed positive ray.
-/
theorem positiveRayScalarConvexOn_Ici_of_closedMatrixOperatorConvex {h : ℝ → ℝ}
    (hclosed : PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h)) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) h := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  have ha_le_one : a ≤ 1 := by linarith
  have hmat := hclosed
    (n := 1)
    (X := positiveRayScalarMatrix x)
    (Y := positiveRayScalarMatrix y)
    (θ := a)
    (positiveRayScalarMatrix_isHermitian x)
    (positiveRayScalarMatrix_isHermitian y)
    (positiveRayScalarMatrix_posSemidef hx)
    (positiveRayScalarMatrix_posSemidef hy)
    ha ha_le_one
  rw [positiveRayScalarMatrix_convexCombo] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix_of_real (g := h)] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix_of_real (g := h)] at hmat
  rw [positiveRayMatrixCfc_scalarMatrix_of_real (g := h)] at hmat
  rw [positiveRayScalarMatrix_convexCombo] at hmat
  have hscalar := positiveRayScalarMatrix_entry_le_of_matrix_le hmat
  simpa [hb_eq, smul_eq_mul] using hscalar

/-- Scalar convexity on `(0,∞)` gives continuity there. -/
theorem PositiveRayScalarConvex.continuousOn_Ioi {h : ℝ → ℝ}
    (hscalar : PositiveRayScalarConvex h) :
    ContinuousOn h (Set.Ioi (0 : ℝ)) := by
  have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) h := by
    refine ⟨convex_Ioi (0 : ℝ), ?_⟩
    intro x hx y hy a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    have ha_le_one : a ≤ 1 := by linarith
    have hxpos : 0 < x := hx
    have hypos : 0 < y := hy
    have hscalar' := hscalar hxpos hypos ha ha_le_one
    simpa [hb_eq, smul_eq_mul] using hscalar'
  exact hconv.continuousOn isOpen_Ioi

end Quantum.TraceInequality.Loewner
