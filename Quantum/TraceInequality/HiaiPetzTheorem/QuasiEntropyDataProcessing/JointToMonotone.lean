/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport
import Quantum.TraceInequality.HiaiPetz.JArgAction
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagCFCTransport

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

@[simp] private lemma real_smul_clm_apply {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (c : ℝ) (T : HansenPedersen.L K) (y : K) :
    (c • T) y = c • T y := by
  rfl

private lemma re_inner_real_smul_add_right {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y z : K) (a b : ℝ) :
    Complex.re (inner ℂ x (a • y + b • z)) =
      a * Complex.re (inner ℂ x y) + b * Complex.re (inner ℂ x z) := by
  rw [← Complex.coe_smul a y, ← Complex.coe_smul b z]
  rw [inner_add_right, inner_smul_right, inner_smul_right, Complex.add_re]
  simp [Complex.mul_re]

private lemma re_inner_real_smul_add_left {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y z : K) (a b : ℝ) :
    Complex.re (inner ℂ (a • y + b • z) x) =
      a * Complex.re (inner ℂ y x) + b * Complex.re (inner ℂ z x) := by
  rw [← Complex.coe_smul a y, ← Complex.coe_smul b z]
  rw [inner_add_left, inner_smul_left, inner_smul_left, Complex.add_re]
  simp [Complex.mul_re]

-- The remaining work here is a local `cfc_neg` transport on matrix CFC expressions.
private theorem matrix_midpoint_convex_neg_Ioi_of_jointConcavity (f : ℝ → ℝ) :
    QuasiEntropyDataProcessing.JointConcavity f →
      HansenPedersen.MatrixOperatorMidpointConvexOnInterval
        (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) := by
  intro hIV
  let g : ℝ → ℝ := fun x => -f x
  intro n A B hA hB hσA hσB
  have hmid_f :=
    matrix_midpoint_concave_Ioi_of_jointConcavity f
      hIV (n := n) (A := A) (B := B) hA hB hσA hσB
  have hdiff_psd :
      (HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
          (1 / 2 : ℝ) •
            (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)).PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hmid_f)
  have hdiff_eq :
      (1 / 2 : ℝ) •
          (HansenPedersen.matrixCfcR g A + HansenPedersen.matrixCfcR g B) -
        HansenPedersen.matrixCfcR g ((1 / 2 : ℝ) • (A + B)) =
      HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
        (1 / 2 : ℝ) •
          (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) := by
    calc
      (1 / 2 : ℝ) •
            (HansenPedersen.matrixCfcR g A + HansenPedersen.matrixCfcR g B) -
          HansenPedersen.matrixCfcR g ((1 / 2 : ℝ) • (A + B))
          =
        (1 / 2 : ℝ) •
            (-HansenPedersen.matrixCfcR f A + -HansenPedersen.matrixCfcR f B) -
          (-HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))) := by
            simp [HansenPedersen.matrixCfcR, g, cfc_neg]
      _ = HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
            (1 / 2 : ℝ) •
              (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) := by
            ext i j
            simp [sub_eq_add_neg, add_comm]
            ring
  refine sub_nonneg.mp ?_
  rw [hdiff_eq]
  exact (Matrix.nonneg_iff_posSemidef).2 hdiff_psd

private theorem matrixMidpointConvex_neg_implies_allHOperatorMidpointConvex_neg_Ioi (f : ℝ
  → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.MatrixOperatorMidpointConvexOnInterval
      (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) →
      HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0}
        (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) := by
  intro hmid
  exact HansenPedersen.matrixConvexImpliesAllHOperatorMidpointConvex
    (J := Set.Ioi (0 : ℝ)) (f := fun x : ℝ ↦ -f x)
    (convex_Ioi (0 : ℝ)) (hf.neg) hmid

private theorem allHOperatorMidpointConvex_neg_Ioi_of_jointConcavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.JointConcavity f →
      HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0}
        (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) := by
  intro hIV
  exact matrixMidpointConvex_neg_implies_allHOperatorMidpointConvex_neg_Ioi f hf
    (matrix_midpoint_convex_neg_Ioi_of_jointConcavity f hIV)

private theorem spectrum_convexCombo_Ioi_clm
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
      (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
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

private noncomputable def midpointConvexNegGap
    (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    (A B : HansenPedersen.L K) (s t : ℝ) : HansenPedersen.L K :=
  let C : HansenPedersen.L K := (1 - s) • A + s • B
  let D : HansenPedersen.L K := (1 - t) • A + t • B
  ((1 / 2 : ℝ) •
      (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) C +
        HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) D)) -
    HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 / 2 : ℝ) • (C + D))

private theorem hOperatorMidpointConvex_neg_scalar_gap_nonneg
    (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    (hmid :
      HansenPedersen.OperatorMidpointConvexOnInterval
        (ℋ := K) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x))
    {A B : HansenPedersen.L K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (ξ : K) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Complex.re (inner ℂ ξ ((midpointConvexNegGap f K A B s t) ξ)) := by
  have hC : IsSelfAdjoint ((1 - s) • A + s • B) := by
    simpa using (IsSelfAdjoint.all (1 - s)).smul hA |>.add ((IsSelfAdjoint.all s).smul hB)
  have hD : IsSelfAdjoint ((1 - t) • A + t • B) := by
    simpa using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hσC :
      spectrum ℝ ((1 - s) • A + s • B) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_convexCombo_Ioi_clm hA hB hs.1 hs.2 hσA hσB
  have hσD :
      spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_convexCombo_Ioi_clm hA hB ht.1 ht.2 hσA hσB
  have hgap :
      HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
          ((1 / 2 : ℝ) • (((1 - s) • A + s • B) + ((1 - t) • A + t • B))) ≤
        (1 / 2 : ℝ) •
          (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - s) • A + s • B) +
            HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - t) • A + t • B)) := by
    exact hmid hC hD hσC hσD
  -- The gap operator is definitionally `½•(cfc C + cfc D) - cfc (½•(C+D))`, so the
  -- nonnegativity transfers by `sub_nonneg` directly; no AC `simp` normalization of the
  -- large inner-product expression is needed.
  have h0 : (0 : HansenPedersen.L K) ≤ midpointConvexNegGap f K A B s t := by
    unfold midpointConvexNegGap
    exact sub_nonneg.mpr hgap
  simpa using h0.re_inner_nonneg_right ξ

private noncomputable def midpointConvexNegScalarFn
    (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    (A B : HansenPedersen.L K) (ξ : K) (u : ℝ) : ℝ :=
  Complex.re (inner ℂ ξ ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - u) •
    A + u • B)) ξ))

@[fun_prop] private theorem midpointConvexNegScalarFn_continuousOn (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)] :
    ∀ {A B : HansenPedersen.L K},
      IsSelfAdjoint A →
      IsSelfAdjoint B →
      spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
      spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) →
      ∀ ξ : K,
        ContinuousOn (midpointConvexNegScalarFn f K A B ξ) (Set.Icc (0 : ℝ) 1) := by
  intro A B hA hB hσA hσB ξ
  let a : ℝ → HansenPedersen.L K := fun u => (1 - u) • A + u • B
  have ha_cont : ContinuousOn a (Set.Icc (0 : ℝ) 1) := by
    have hcont : Continuous a := by
      fun_prop
    exact hcont.continuousOn
  have hs :
      Set.Ioi (0 : ℝ) ∈ nhdsSet (⋃ u ∈ Set.Icc (0 : ℝ) 1, spectrum ℝ (a u)) := by
    rw [isOpen_Ioi.mem_nhdsSet]
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨u, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hu, hxu⟩
    exact spectrum_convexCombo_Ioi_clm hA hB hu.1 hu.2 hσA hσB hxu
  have ha_sa : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsSelfAdjoint (a u) := by
    intro u hu
    simpa [a] using
      ((IsSelfAdjoint.all (1 - u)).smul hA).add ((IsSelfAdjoint.all u).smul hB)
  have hcfc :
      ContinuousOn
        (fun u ↦ HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) (a u))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [HansenPedersen.cfcR] using
      (ContinuousOn.cfc_of_mem_nhdsSet (A := HansenPedersen.L K)
        (X := ℝ) (t := Set.Icc (0 : ℝ) 1) (s := Set.Ioi (0 : ℝ))
        (f := fun x : ℝ ↦ -f x) hs ha_cont ha_sa hf.neg)
  have hvec :
      ContinuousOn
        (fun u ↦ (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) (a u)) ξ)
        (Set.Icc (0 : ℝ) 1) := by
    exact (ContinuousLinearMap.apply ℂ K ξ).continuous.comp_continuousOn hcfc
  have hinner :
      ContinuousOn
        (fun u ↦ innerSL ℂ ξ
          ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) (a u)) ξ))
        (Set.Icc (0 : ℝ) 1) := by
    exact (innerSL ℂ ξ).continuous.comp_continuousOn hvec
  simpa [midpointConvexNegScalarFn, a] using
    (Complex.continuous_re.comp_continuousOn hinner)

@[fun_prop] private theorem midpointConvexNegScalarFn_swap_continuousOn (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)] :
    ∀ {A B : HansenPedersen.L K},
      IsSelfAdjoint A →
      IsSelfAdjoint B →
      spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
      spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) →
      ∀ ξ : K,
        ContinuousOn
          (fun u : ℝ =>
            Complex.re
              (inner ℂ ξ
                ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) (u • B + (1 - u) •
                  A)) ξ)))
          (Set.Icc (0 : ℝ) 1) := by
  intro A B hA hB hσA hσB ξ
  have hbase :=
    midpointConvexNegScalarFn_continuousOn (f := f) (K := K)
      (A := A) (B := B) hf hA hB hσA hσB ξ
  have hfun :
      (fun u : ℝ =>
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) (u • B + (1 - u) • A))
              ξ))) =
        midpointConvexNegScalarFn f K A B ξ := by
    funext u
    simp [midpointConvexNegScalarFn, sub_eq_add_neg, add_comm]
  simpa [hfun] using hbase

private theorem midpointConvexNegScalarFn_zero (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    (A B : HansenPedersen.L K) (ξ : K) :
    midpointConvexNegScalarFn f K A B ξ 0 =
      Complex.re (inner ℂ ξ ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)) := by
  simp [midpointConvexNegScalarFn]

private theorem midpointConvexNegScalarFn_one (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    (A B : HansenPedersen.L K) (ξ : K) :
    midpointConvexNegScalarFn f K A B ξ 1 =
      Complex.re (inner ℂ ξ ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)) := by
  simp [midpointConvexNegScalarFn]

private theorem midpointConvexNeg_mix_eq
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    (A B : HansenPedersen.L K) (s t : ℝ) :
    (1 / 2 : ℝ) • (((1 - s) • A + s • B) + ((1 - t) • A + t • B)) =
      (1 - (s + t) / 2) • A + ((s + t) / 2) • B := by
  calc
    (1 / 2 : ℝ) • (((1 - s) • A + s • B) + ((1 - t) • A + t • B))
        =
          (((1 / 2 : ℝ) * (1 - s)) • A +
            (((1 / 2 : ℝ) * s) • B +
              (((1 / 2 : ℝ) * (1 - t)) • A + ((1 / 2 : ℝ) * t) • B))) := by
            simp [smul_add, smul_smul, add_assoc]
    _ =
          ((((1 / 2 : ℝ) * (1 - s)) • A + ((1 / 2 : ℝ) * (1 - t)) • A) +
            ((((1 / 2 : ℝ) * s) • B) + ((1 / 2 : ℝ) * t) • B)) := by
            abel
    _ =
          (((((1 / 2 : ℝ) * (1 - s)) + ((1 / 2 : ℝ) * (1 - t))) : ℝ) • A +
            ((((1 / 2 : ℝ) * s) + ((1 / 2 : ℝ) * t) : ℝ) • B)) := by
            rw [← add_smul, ← add_smul]
    _ = (1 - (s + t) / 2) • A + ((s + t) / 2) • B := by
            congr 1 <;> ring_nf

-- The midpoint endpoint proof combines the scalar gap with compact interval maximization.
private theorem midpointConvexNegScalarFn_midpoint_le (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    (hmid :
      HansenPedersen.OperatorMidpointConvexOnInterval
        (ℋ := K) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x))
    {A B : HansenPedersen.L K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (ξ : K) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    midpointConvexNegScalarFn f K A B ξ ((s + t) / 2) ≤
      (1 / 2 : ℝ) *
        (midpointConvexNegScalarFn f K A B ξ s + midpointConvexNegScalarFn f K A B ξ t) := by
  have hgap :=
    hOperatorMidpointConvex_neg_scalar_gap_nonneg
      (f := f) (K := K) hmid hA hB hσA hσB ξ hs ht
  have hgap'' := hgap
  rw [midpointConvexNegGap, midpointConvexNeg_mix_eq] at hgap''
  have hgap0 :
      0 ≤
        (1 / 2 : ℝ) *
            (Complex.re
                (inner ℂ ξ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - s) • A + s
                    • B)) ξ)) +
              Complex.re
                (inner ℂ ξ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - t) • A + t
                    • B)) ξ))) -
          Complex.re
            (inner ℂ ξ
              ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                  ((1 - (s + t) / 2) • A + ((s + t) / 2) • B)) ξ)) := by
    let Ys :=
      (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - s) • A + s • B)) ξ
    let Yt :=
      (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - t) • A + t • B)) ξ
    rw [ContinuousLinearMap.sub_apply, real_smul_clm_apply,
      ContinuousLinearMap.add_apply] at hgap''
    rw [inner_sub_right, Complex.sub_re] at hgap''
    have hfirst :
        Complex.re (inner ℂ ξ ((1 / 2 : ℝ) • (Ys + Yt))) =
          (1 / 2 : ℝ) * (Complex.re (inner ℂ ξ Ys) + Complex.re (inner ℂ ξ Yt)) := by
      rw [smul_add, re_inner_real_smul_add_right]
      ring
    rw [hfirst] at hgap''
    simpa [Ys, Yt] using hgap''
  have hineq' :
      Complex.re
        (inner ℂ ξ
          ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
              ((1 - (s + t) / 2) • A + ((s + t) / 2) • B)) ξ)) ≤
        (1 / 2 : ℝ) *
          (Complex.re
              (inner ℂ ξ
                ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - s) • A + s •
                  B)) ξ)) +
            Complex.re
              (inner ℂ ξ
                ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) ((1 - t) • A + t •
                  B)) ξ))) := by
    linarith [hgap0]
  have hineq :
      midpointConvexNegScalarFn f K A B ξ ((s + t) / 2) ≤
        (1 / 2 : ℝ) *
          (midpointConvexNegScalarFn f K A B ξ s + midpointConvexNegScalarFn f K A B ξ t) := by
    simpa [midpointConvexNegScalarFn] using hineq'
  exact hineq

private theorem midpointConvexNegScalarFn_le_endpoints
    (f : ℝ → ℝ)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {A B : HansenPedersen.L K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hmid :
      HansenPedersen.OperatorMidpointConvexOnInterval
        (ℋ := K) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x))
    (ξ : K) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
      midpointConvexNegScalarFn f K A B ξ t ≤
        (1 - t) * midpointConvexNegScalarFn f K A B ξ 0 +
          t * midpointConvexNegScalarFn f K A B ξ 1 := by
  let g : ℝ → ℝ := midpointConvexNegScalarFn f K A B ξ
  let h : ℝ → ℝ := fun u => g u - ((1 - u) * g 0 + u * g 1)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    simpa [g] using
      midpointConvexNegScalarFn_continuousOn (f := f) (K := K)
        (A := A) (B := B) hf hA hB hσA hσB ξ
  have hcont : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
    have hlin : Continuous fun u : ℝ => (1 - u) * g 0 + u * g 1 := by
      fun_prop
    exact hgcont.sub hlin.continuousOn
  have hmid_h :
      ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        h ((s + t) / 2) ≤ (h s + h t) / 2 := by
    intro s t hs ht
    have hgmid :=
      midpointConvexNegScalarFn_midpoint_le (f := f) (K := K) hmid hA hB hσA hσB ξ hs ht
    have haff :
        (1 - (s + t) / 2) * g 0 + ((s + t) / 2) * g 1 =
          (((1 - s) * g 0 + s * g 1) + ((1 - t) * g 0 + t * g 1)) / 2 := by
      ring
    dsimp [h]
    linarith
  have h0 : h 0 = 0 := by
    dsimp [h]
    ring
  have h1 : h 1 = 0 := by
    dsimp [h]
    ring
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (show (0 : ℝ) ≤ 1 by norm_num))
    hcont with
    ⟨c, hc, hcmax⟩
  have hcmax' : ∀ x ∈ Set.Icc (0 : ℝ) 1, h x ≤ h c := by
    simpa [IsMaxOn, IsMaxFilter] using hcmax
  have hcle : h c ≤ 0 := by
    by_cases hlt : c < (1 / 2 : ℝ)
    · have h2c : 2 * c ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · nlinarith [hc.1]
        · nlinarith [hc.2, hlt]
      have hmidc : h c ≤ (h 0 + h (2 * c)) / 2 := by
        simpa [show (0 + 2 * c) / 2 = c by ring] using
          hmid_h (s := 0) (t := 2 * c) (by norm_num) h2c
      have hmax2c : h (2 * c) ≤ h c := hcmax' _ h2c
      linarith
    · by_cases heq : c = (1 / 2 : ℝ)
      · have hmidc : h c ≤ (h 0 + h 1) / 2 := by
          simpa [heq] using
            hmid_h (s := 0) (t := 1) (by norm_num) (by norm_num)
        linarith [h0, h1]
      · have hhalf_le : (1 / 2 : ℝ) ≤ c := le_of_not_gt hlt
        have hgt : (1 / 2 : ℝ) < c := lt_of_le_of_ne hhalf_le (by
          intro hEq
          exact heq hEq.symm)
        have h2c1 : 2 * c - 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · nlinarith [hgt]
          · nlinarith [hc.2]
        have hmidc : h c ≤ (h (2 * c - 1) + h 1) / 2 := by
          simpa [show ((2 * c - 1) + 1) / 2 = c by ring] using
            hmid_h (s := 2 * c - 1) (t := 1) h2c1 (by norm_num)
        have hmax2c1 : h (2 * c - 1) ≤ h c := hcmax' _ h2c1
        linarith [h1]
  intro t ht
  have htmax : h t ≤ h c := hcmax' _ ht
  have htnonpos : h t ≤ 0 := le_trans htmax hcle
  dsimp [h, g] at htnonpos
  linarith

private theorem midpointConvexNeg_cfc_isSelfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {f : ℝ → ℝ} {A : HansenPedersen.L K} :
    IsSelfAdjoint (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) := by
  simp [HansenPedersen.cfcR]

private theorem midpointConvexNeg_rhs_isSelfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    (f : ℝ → ℝ) {A B : HansenPedersen.L K} {t : ℝ} :
    IsSelfAdjoint
      ((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
        t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) := by
  change
    star (((1 - t) : ℝ) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
      (t : ℝ) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) =
    (((1 - t) : ℝ) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
      (t : ℝ) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B)
  simp [sub_eq_add_neg, add_comm,
    (midpointConvexNeg_cfc_isSelfAdjoint (K := K) (f := f)
      (A := A)).star_eq,
    (midpointConvexNeg_cfc_isSelfAdjoint (K := K) (f := f)
      (A := B)).star_eq]

private theorem qform_sub_nonneg_of_inner_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {S T : HansenPedersen.L K} (ξ : K)
    (h : Complex.re (inner ℂ (S ξ) ξ) ≤ Complex.re (inner ℂ (T ξ) ξ)) :
    0 ≤ Complex.re (inner ℂ ((T - S) ξ) ξ) := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re]
  exact sub_nonneg.mpr h

private theorem hOperatorMidpointConvex_neg_implies_hOperatorConvex_neg_Ioi (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)] :
    HansenPedersen.OperatorMidpointConvexOnInterval
      (ℋ := K) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) →
      HansenPedersen.OperatorConvexOnInterval
        (ℋ := K) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) := by
  intro hmid A B t hA hB ht0 ht1 hσA hσB
  /- Step 1: Reduce operator convexity to nonnegativity of the difference quadratic form. -/
  refine le_of_quadratic_form_nonneg ?_ ?_
  · exact
      ((midpointConvexNeg_rhs_isSelfAdjoint (K := K) (f := f) (A := A) (B := B) (t := t)).sub
        (midpointConvexNeg_cfc_isSelfAdjoint (K := K) (f := f)
          (A := (1 - t) • A + t • B)))
  · intro ξ
    /- Step 2: Derive the scalar convexity g(t) ≤ (1-t)·g(0) + t·g(1) from midpoint
      convexity. -/
    let g : ℝ → ℝ := midpointConvexNegScalarFn f K A B ξ
    have hconv_t :
        g t ≤ (1 - t) * g 0 + t * g 1 :=
      by
        simpa [g] using
          midpointConvexNegScalarFn_le_endpoints
            (f := f) (K := K) hf hA hB hσA hσB hmid ξ ⟨ht0, ht1⟩
    /- Step 3: Rewrite the scalar values g(0), g(t), g(1) as inner-product quadratic forms. -/
    have hmidpt : g t =
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)) := by
      rfl
    have hrhs :
        (1 - t) * g 0 + t * g 1 =
          Complex.re
            (inner ℂ ξ
              (((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
                  t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)) := by
      dsimp [g]
      rw [midpointConvexNegScalarFn_zero, midpointConvexNegScalarFn_one]
      rw [real_smul_clm_apply, real_smul_clm_apply, re_inner_real_smul_add_right]
    have hfinal :
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)) ≤
          Complex.re
            (inner ℂ ξ
              (((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
                  t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)) := by
      simpa [hmidpt, hrhs] using hconv_t
    /- Step 4: Swap to the ⟨Tξ, ξ⟩ form via Hermitian symmetry and collect the endpoint
      bound. -/
    have hmid_symm :
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)) =
        Complex.re
          (inner ℂ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)
            ξ) := by
      simpa using
        (inner_re_symm (𝕜 := ℂ) ξ
          ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
              ((1 - t) • A + t • B)) ξ))
    have hA_symm :
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)) =
        Complex.re
          (inner ℂ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
            ξ) := by
      simpa using
        (inner_re_symm (𝕜 := ℂ) ξ
          ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ))
    have hB_symm :
        Complex.re
          (inner ℂ ξ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)) =
        Complex.re
          (inner ℂ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
            ξ) := by
      simpa using
        (inner_re_symm (𝕜 := ℂ) ξ
          ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ))
    have hrhs' :
        (1 - t) * g 0 + t * g 1 =
          (1 - t) *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                  ξ) +
            t *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                  ξ) := by
      calc
        (1 - t) * g 0 + t * g 1
            =
              (1 - t) *
                  Complex.re
                    (inner ℂ ξ
                      ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)) +
                t *
                  Complex.re
                    (inner ℂ ξ
                      ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)) := by
                  dsimp [g]
                  rw [midpointConvexNegScalarFn_zero, midpointConvexNegScalarFn_one]
        _ =
              (1 - t) *
                  Complex.re
                    (inner ℂ
                      ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                      ξ) +
                t *
                  Complex.re
                    (inner ℂ
                      ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                      ξ) := by
                  rw [hA_symm, hB_symm]
    have hfinal' :
        Complex.re
          (inner ℂ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)
            ξ) ≤
          (1 - t) *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                  ξ) +
            t *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                  ξ) := by
      linarith [hfinal, hmid_symm, hrhs']
    /- Step 5: Expand the convex-combination operator form and record the nonnegative gap. -/
    have hgap0 :
        0 ≤
          ((1 - t) *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                  ξ) +
            t *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                  ξ)) -
            Complex.re
              (inner ℂ
                ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                    ((1 - t) • A + t • B)) ξ)
                ξ) := by
      linarith
    have hrhs_inner :
        Complex.re
          (inner ℂ
            ((((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
                t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ))
            ξ) =
          (1 - t) *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                  ξ) +
            t *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                  ξ) := by
      rw [ContinuousLinearMap.add_apply, real_smul_clm_apply,
        real_smul_clm_apply, re_inner_real_smul_add_left]
    /- Step 6: Assemble the final operator quadratic-form inequality and conclude. -/
    have hgoal_le :
        Complex.re
          (inner ℂ
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                ((1 - t) • A + t • B)) ξ)
            ξ) ≤
        Complex.re
          (inner ℂ
            ((((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
                t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ))
            ξ) := by
      calc
        Complex.re
            (inner ℂ
              ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x)
                  ((1 - t) • A + t • B)) ξ)
              ξ)
            ≤
          (1 - t) *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A) ξ)
                  ξ) +
            t *
              Complex.re
                (inner ℂ
                  ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ)
                  ξ) := by
              linarith [hgap0]
        _ =
          Complex.re
            (inner ℂ
              ((((1 - t) • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) A +
                  t • HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ -f x) B) ξ))
              ξ) := by
              symm
              exact hrhs_inner
    exact qform_sub_nonneg_of_inner_le ξ hgoal_le

private theorem allHOperatorMidpointConvex_neg_implies_allHOperatorConvex_neg_Ioi (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0}
      (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) →
      HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f
        x) := by
  intro hmid K _ _ _ _ _
  exact hOperatorMidpointConvex_neg_implies_hOperatorConvex_neg_Ioi f hf K (hmid K)

private theorem allHOperatorConvex_neg_implies_allHOperatorConcave_Ioi (f : ℝ → ℝ) :
    HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) →
      HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f
  := by
  intro hconv K _ _ _ _ _
  simpa [HansenPedersen.HOperatorConcaveOnInterval, HansenPedersen.HOperatorConvexOnInterval,
    HansenPedersen.OperatorConcaveOnInterval, HansenPedersen.OperatorConvexOnInterval] using hconv K

private theorem allHOperatorConvex_neg_Ioi_of_jointConcavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.JointConcavity f →
      HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f
        x) := by
  intro hIV
  exact allHOperatorMidpointConvex_neg_implies_allHOperatorConvex_neg_Ioi f hf
    (allHOperatorMidpointConvex_neg_Ioi_of_jointConcavity f hf hIV)

private theorem allHOperatorConcave_Ioi_of_jointConcavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.JointConcavity f →
      HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  intro hIV
  exact allHOperatorConvex_neg_implies_allHOperatorConcave_Ioi f
    (allHOperatorConvex_neg_Ioi_of_jointConcavity f hf hIV)

section PositiveConcavity

open Set Filter HansenPedersen
open scoped Topology

/-- One step of the limit argument in
`QuasiEntropyDataProcessing.allHOperatorMonotone_of_positiveConcave`: for `0 < t < 1`,
concavity at the point `C = A + (1 - t)⁻¹ • (B - A)` and positivity of `f` give
`t • f(A) ≤ f(B)`. -/
private theorem positiveConcave_smul_cfcR_le
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) → 0 < f x)
    (hconc : AllHOperatorConcaveOnInterval.{0} (Ioi (0 : ℝ)) f)
    {A B : L K} (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Ioi (0 : ℝ)) (hAB : A ≤ B)
    {t : ℝ} (htpos : 0 < t) (htlt : t < 1) :
    t • cfcR (ℋ := K) f A ≤ cfcR (ℋ := K) f B := by
  have hAsp : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hA, fun x hx => hσA hx⟩
  have h1t : 0 < 1 - t := sub_pos.mpr htlt
  let C : L K := A + (1 - t)⁻¹ • (B - A)
  have hCsp : IsStrictlyPositive C := by
    dsimp [C]
    exact hAsp.add_nonneg
      (smul_nonneg (inv_nonneg.mpr h1t.le) (sub_nonneg.mpr hAB))
  have hC := CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hCsp
  have hcombo : (1 - (1 - t)) • A + (1 - t) • C = B := by
    have hmul : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h1t)
    dsimp only [C]
    rw [smul_add, smul_smul, hmul, one_smul, ← add_assoc, ← add_smul, sub_add_cancel,
      one_smul]
    abel
  have hneg := hconc K (A := A) (B := C) (t := 1 - t)
    hA hC.1 h1t.le (by linarith) hσA (fun x hx => hC.2 x hx)
  rw [hcombo, show (1 : ℝ) - (1 - t) = t by ring] at hneg
  have hconcineq :
      t • cfcR (ℋ := K) f A + (1 - t) • cfcR (ℋ := K) f C ≤
        cfcR (ℋ := K) f B := by
    simp only [HansenPedersen.cfcR, cfc_neg, smul_neg, ← neg_add] at hneg
    exact neg_le_neg_iff.mp hneg
  have hfcC : 0 ≤ cfcR (ℋ := K) f C :=
    cfc_nonneg (fun x hx => (hpos x (hC.2 x hx)).le)
  exact
    (le_add_of_nonneg_right (smul_nonneg (sub_nonneg.mpr htlt.le) hfcC)).trans hconcineq

/-- Positive operator concavity on the positive ray implies operator monotonicity. -/
theorem QuasiEntropyDataProcessing.allHOperatorMonotone_of_positiveConcave
    (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) → 0 < f x)
    (hconc : AllHOperatorConcaveOnInterval.{0} (Ioi (0 : ℝ)) f) :
    AllHOperatorMonotoneOnInterval.{0} (Ioi (0 : ℝ)) f := by
  intro K instNorm instInner instComplete instCFC instNontrivial
  letI : NormedAddCommGroup K := instNorm
  letI : InnerProductSpace ℂ K := instInner
  letI : CompleteSpace K := instComplete
  letI : ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint := instCFC
  letI : Nontrivial (L K) := instNontrivial
  intro A B hA hB hσA hσB hAB
  have hlim :
      Tendsto (fun t : ℝ => t • cfcR (ℋ := K) f A)
        (𝓝[<] (1 : ℝ)) (𝓝 (cfcR (ℋ := K) f A)) := by
    have hc : Continuous (fun t : ℝ => t • cfcR (ℋ := K) f A) := by
      fun_prop
    simpa using (hc.tendsto (1 : ℝ)).mono_left inf_le_left
  apply le_of_tendsto hlim
  have htpos : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 < t := by
    exact Filter.Eventually.filter_mono inf_le_left
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  filter_upwards [htpos, self_mem_nhdsWithin] with t htpos htlt
  exact positiveConcave_smul_cfcR_le f hpos hconc hA hσA hAB htpos htlt

end PositiveConcavity

/-- Joint concavity implies the matrix-monotone condition.
Source: Hiai, Theorem 6.2, output-nondegenerate case,
condition (iv) implies condition (i_mat). -/
theorem QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDataProcessing.JointConcavity f →
      QuasiEntropyDataProcessing.MatrixMonotoneCondition f := by
  intro hIV
  exact @MatrixFunctionalCalculus.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi f
    (QuasiEntropyDataProcessing.allHOperatorMonotone_of_positiveConcave f hpos
      (allHOperatorConcave_Ioi_of_jointConcavity f hf hIV))

/-- Continuity upgrades midpoint operator convexity on the positive ray to convexity. -/
theorem QuasiEntropyDataProcessing.allHOperatorConvex_of_midpointConvex
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  simpa only [neg_neg] using
    allHOperatorMidpointConvex_neg_implies_allHOperatorConvex_neg_Ioi (fun x ↦ -f x) hf.neg


end MatrixScopedInstances

end HiaiPetz
