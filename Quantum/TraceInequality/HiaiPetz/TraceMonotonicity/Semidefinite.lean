/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.StrictlyPositiveRetained
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Semidefinite output-support trace powers
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private lemma supportEuclideanSubspace_eq_range {n : ℕ} (C : Mₙ n) :
    (let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
     (matrixSupportSubspace C).map e.symm.toLinearMap) =
      LinearMap.range (Matrix.toEuclideanLin C) := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  ext y
  constructor
  · intro hy
    rcases hy with ⟨v, hv, rfl⟩
    rcases hv with ⟨w, rfl⟩
    refine ⟨WithLp.toLp 2 w, ?_⟩
    simp [Matrix.mulVecLin]
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨C.mulVec (e z), ?_, ?_⟩
    · exact ⟨e z, rfl⟩
    · rw [← hz]
      rw [Matrix.toLpLin_apply]
      rfl

private lemma matrixSupportProj_mulVec_zero_of_selfAdjoint {n : ℕ} {C : Mₙ n}
    (hC : IsSelfAdjoint C) {x : Fin n → ℂ} (hx : C.mulVec x = 0) :
    (matrixSupportProj C).mulVec x = 0 := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    (matrixSupportSubspace C).map e.symm.toLinearMap
  have hUeq : U = LinearMap.range (Matrix.toEuclideanLin C) := by
    simp [e, U, supportEuclideanSubspace_eq_range C]
  have hproj : Matrix.toEuclideanLin (matrixSupportProj C) = U.starProjection := by
    simp [e, U, matrixSupportProj_toEuclideanLin C]
  have hxKer : WithLp.toLp 2 x ∈ (Matrix.toEuclideanLin C).ker := by
    rw [LinearMap.mem_ker]
    simp [Matrix.toLpLin_toLp, hx]
  have hsymm : (Matrix.toEuclideanLin C).IsSymmetric := by
    rw [← Matrix.isHermitian_iff_isSymmetric]
    simpa [IsSelfAdjoint, Matrix.IsHermitian] using hC
  have hxOrthRange : WithLp.toLp 2 x ∈ (LinearMap.range (Matrix.toEuclideanLin C))ᗮ := by
    simpa [LinearMap.IsSymmetric.orthogonal_range hsymm] using hxKer
  have hxOrthU : e.symm x ∈ Uᗮ := by
    change WithLp.toLp 2 x ∈ Uᗮ
    simpa [hUeq] using hxOrthRange
  have hzero : U.starProjection (e.symm x) = 0 := by
    rw [Submodule.starProjection_apply]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hxOrthU)
  have hxEuclid : Matrix.toEuclideanLin (matrixSupportProj C) (WithLp.toLp 2 x) = 0 := by
    simpa [e, hproj] using hzero
  have hxFunc : WithLp.toLp 2 ((matrixSupportProj C).mulVec x) =
      WithLp.toLp 2 (0 : Fin n → ℂ) := by
    simpa only [Matrix.toLpLin_toLp] using hxEuclid
  simpa using congrArg WithLp.ofLp hxFunc

private lemma matrix_eq_sum_eigenmatrix_right_selfAdjoint
    {n : ℕ} {C : Mₙ n} (hC : IsSelfAdjoint C) (X : Mₙ n) :
    X =
      ∑ j : Fin n,
        Matrix.vecMulVec (Matrix.mulVec X (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  let U : Mₙ n := hC.isHermitian.eigenvectorUnitary
  have hU : U * star U = (1 : Mₙ n) := by
    simp [U]
  calc
    X = X * (1 : Mₙ n) := by rw [Matrix.mul_one]
    _ = X * (U * star U) := by rw [hU]
    _ = (X * U) * star U := by rw [Matrix.mul_assoc]
    _ =
      ∑ j : Fin n,
        Matrix.vecMulVec (Matrix.mulVec X (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hC.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
        ext a b
        rw [Matrix.sum_apply]
        simp [U, Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
          Matrix.IsHermitian.eigenvectorUnitary_apply]

private lemma matrixPower_eq_sum_eigenmatrix_nonneg {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (p : ℝ) :
    matrixPower p C =
      ∑ i : Fin n,
        (powerFn p ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i) : ℂ) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    matrixPower p C =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (matrixPower p C) (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint hsa (matrixPower p C)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixPower, HiaiPetz.matrixCfcR_mulVec_eigenvectorBasis_transport
          (f := powerFn p) (A := C) hsa i, Matrix.smul_vecMulVec]

private lemma matrixSupportProj_mulVec_eigenvectorBasis_nonneg {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (i : Fin n) :
    (matrixSupportProj C).mulVec
        ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ) =
      (if (Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i = 0 then (0 : ℂ) else 1) •
        ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let μ : ℝ := hherm.eigenvalues i
  let v : Fin n → ℂ := hherm.eigenvectorBasis i
  have hmul : C.mulVec v = (μ : ℂ) • v := by
    simpa [hherm, μ, v] using hherm.mulVec_eigenvectorBasis i
  by_cases hμ : μ = 0
  · have hx : C.mulVec v = 0 := by simp [hmul, hμ]
    have hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hherm
    have hz := matrixSupportProj_mulVec_zero_of_selfAdjoint (C := C) hsa hx
    simp [μ, v, hμ, hz]
  · have hv_mem : v ∈ matrixSupportSubspace C := by
      refine ⟨((μ : ℂ)⁻¹) • v, ?_⟩
      calc
        C.mulVec (((μ : ℂ)⁻¹) • v)
            = ((μ : ℂ)⁻¹) • C.mulVec v := by simp [Matrix.mulVec_smul]
        _ = ((μ : ℂ)⁻¹) • ((μ : ℂ) • v) := by rw [hmul]
        _ = v := by
            have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
            ext k
            change (μ : ℂ)⁻¹ * ((μ : ℂ) * v k) = v k
            field_simp [hμC]
    have hprojv : (matrixSupportProj C).mulVec v = v :=
      (MatrixSupportProj.mulVec_eq_self_iff C v).2 hv_mem
    simp [μ, v, hμ, hprojv]

private lemma matrixSupportProj_eq_sum_eigenmatrix_nonneg {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) :
    matrixSupportProj C =
      ∑ i : Fin n,
        (if (Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvalues i = 0 then (0 : ℂ) else 1) •
          Matrix.vecMulVec
            ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)
            (star ((Matrix.nonneg_iff_posSemidef.mp hC).1.eigenvectorBasis i : Fin n → ℂ)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hsa : IsSelfAdjoint C := by simpa [IsSelfAdjoint, Matrix.IsHermitian] using hpsd.1
  calc
    matrixSupportProj C =
        ∑ i : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec (matrixSupportProj C)
              (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star (hsa.isHermitian.eigenvectorBasis i : Fin n → ℂ)) := by
          exact matrix_eq_sum_eigenmatrix_right_selfAdjoint hsa (matrixSupportProj C)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [matrixSupportProj_mulVec_eigenvectorBasis_nonneg (C := C) hC i,
          Matrix.smul_vecMulVec]

private lemma powerFn_tendsto_supportCoeff_zero {μ : ℝ} (_hμ : 0 ≤ μ) :
    Filter.Tendsto (fun p : ℝ => (powerFn p μ : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (if μ = 0 then (0 : ℂ) else 1)) := by
  by_cases hzero : μ = 0
  · have hconst : ∀ᶠ p in 𝓝[Set.Ioo (0 : ℝ) 1] 0, (powerFn p μ : ℂ) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hpne : p ≠ 0 := ne_of_gt hp.1
      simp [powerFn, hzero, Real.zero_rpow hpne]
    have hconst' :
        (fun p : ℝ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] 0]
          fun p : ℝ => (powerFn p μ : ℂ) :=
      hconst.mono fun p hp => hp.symm
    simpa [hzero] using ((tendsto_const_nhds (x := (0 : ℂ))).congr' hconst')
  · have hreal :
        Filter.Tendsto (fun p : ℝ => μ ^ p) (𝓝[Set.Ioo (0 : ℝ) 1] 0)
          (𝓝 (1 : ℝ)) := by
      simpa [Real.rpow_zero] using
        ((Real.continuousAt_const_rpow hzero).tendsto.comp
          (Filter.tendsto_id.mono_left
            (nhdsWithin_le_nhds : 𝓝[Set.Ioo (0 : ℝ) 1] 0 ≤ 𝓝 (0 : ℝ))))
    have hcomplex :
        Filter.Tendsto (fun p : ℝ => ((μ ^ p : ℝ) : ℂ))
          (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 ((1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [powerFn, hzero] using hcomplex

private lemma powerFn_tendsto_at_one {μ : ℝ} (_hμ : 0 ≤ μ) :
    Filter.Tendsto (fun p : ℝ => (powerFn p μ : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (powerFn 1 μ : ℂ)) := by
  by_cases hzero : μ = 0
  · have hconst : ∀ᶠ p in 𝓝[Set.Ioo (0 : ℝ) 1] 1, (powerFn p μ : ℂ) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hpne : p ≠ 0 := ne_of_gt hp.1
      simp [powerFn, hzero, Real.zero_rpow hpne]
    have hconst' :
        (fun p : ℝ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] 1]
          fun p : ℝ => (powerFn p μ : ℂ) :=
      hconst.mono fun p hp => hp.symm
    simpa [powerFn, hzero, Real.zero_rpow (by norm_num : (1 : ℝ) ≠ 0)] using
      ((tendsto_const_nhds (x := (0 : ℂ))).congr' hconst')
  · have hreal :
        Filter.Tendsto (fun p : ℝ => μ ^ p) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
          (𝓝 (μ ^ (1 : ℝ))) := by
      simpa using
        ((Real.continuousAt_const_rpow hzero).tendsto.comp
          (Filter.tendsto_id.mono_left
            (nhdsWithin_le_nhds : 𝓝[Set.Ioo (0 : ℝ) 1] 1 ≤ 𝓝 (1 : ℝ))))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

private lemma powerFn_one_sub_tendsto_supportCoeff_one {μ : ℝ} (_hμ : 0 ≤ μ) :
    Filter.Tendsto (fun p : ℝ => (powerFn (1 - p) μ : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (if μ = 0 then (0 : ℂ) else 1)) := by
  by_cases hzero : μ = 0
  · have hconst : ∀ᶠ p in 𝓝[Set.Ioo (0 : ℝ) 1] 1, (powerFn (1 - p) μ : ℂ) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hpne : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
      simp [powerFn, hzero, Real.zero_rpow hpne]
    have hconst' :
        (fun p : ℝ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] 1]
          fun p : ℝ => (powerFn (1 - p) μ : ℂ) :=
      hconst.mono fun p hp => hp.symm
    simpa [hzero] using ((tendsto_const_nhds (x := (0 : ℂ))).congr' hconst')
  · have hsub :
        Filter.Tendsto (fun p : ℝ => 1 - p) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
          (𝓝 (0 : ℝ)) := by
      have hid : Filter.Tendsto (fun p : ℝ => p) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
          (𝓝 (1 : ℝ)) :=
        nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hid
    have hreal :
        Filter.Tendsto (fun p : ℝ => μ ^ (1 - p)) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
          (𝓝 (1 : ℝ)) := by
      simpa [Real.rpow_zero] using (Real.continuousAt_const_rpow hzero).tendsto.comp hsub
    have hcomplex :
        Filter.Tendsto (fun p : ℝ => ((μ ^ (1 - p) : ℝ) : ℂ))
          (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [powerFn, hzero] using hcomplex

private lemma powerFn_one_sub_tendsto_at_zero {μ : ℝ} (_hμ : 0 ≤ μ) :
    Filter.Tendsto (fun p : ℝ => (powerFn (1 - p) μ : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (powerFn 1 μ : ℂ)) := by
  by_cases hzero : μ = 0
  · have hconst : ∀ᶠ p in 𝓝[Set.Ioo (0 : ℝ) 1] 0, (powerFn (1 - p) μ : ℂ) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hpne : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
      simp [powerFn, hzero, Real.zero_rpow hpne]
    have hconst' :
        (fun p : ℝ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] 0]
          fun p : ℝ => (powerFn (1 - p) μ : ℂ) :=
      hconst.mono fun p hp => hp.symm
    simpa [powerFn, hzero, Real.zero_rpow (by norm_num : (1 : ℝ) ≠ 0)] using
      ((tendsto_const_nhds (x := (0 : ℂ))).congr' hconst')
  · have hsub :
        Filter.Tendsto (fun p : ℝ => 1 - p) (𝓝[Set.Ioo (0 : ℝ) 1] 0)
          (𝓝 (1 : ℝ)) := by
      have hid : Filter.Tendsto (fun p : ℝ => p) (𝓝[Set.Ioo (0 : ℝ) 1] 0)
          (𝓝 (0 : ℝ)) :=
        Filter.tendsto_id.mono_left
          (nhdsWithin_le_nhds : 𝓝[Set.Ioo (0 : ℝ) 1] 0 ≤ 𝓝 (0 : ℝ))
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hid
    have hreal :
        Filter.Tendsto (fun p : ℝ => μ ^ (1 - p)) (𝓝[Set.Ioo (0 : ℝ) 1] 0)
          (𝓝 (μ ^ (1 : ℝ))) := by
      simpa using (Real.continuousAt_const_rpow hzero).tendsto.comp hsub
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

private lemma matrixPower_tendsto_supportProj_at_zero {n : ℕ} {C : Mₙ n} (hC : 0 ≤ C) :
    Filter.Tendsto (fun p : ℝ => matrixPower p C)
      (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 (matrixSupportProj C)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let E : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec (hherm.eigenvectorBasis i : Fin n → ℂ)
      (star (hherm.eigenvectorBasis i : Fin n → ℂ))
  have hsum :
      Filter.Tendsto
        (fun p : ℝ =>
          ∑ i : Fin n, (powerFn p (hherm.eigenvalues i) : ℂ) • E i)
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑ i : Fin n,
          (if hherm.eigenvalues i = 0 then (0 : ℂ) else 1) • E i)) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun i hi =>
          (powerFn_tendsto_supportCoeff_zero
            (Matrix.PosSemidef.eigenvalues_nonneg hpsd i)).smul
              (tendsto_const_nhds (x := E i)))
  simpa [hpsd, hherm, E, matrixPower_eq_sum_eigenmatrix_nonneg hC,
    matrixSupportProj_eq_sum_eigenmatrix_nonneg hC] using hsum

private lemma matrixPower_tendsto_at_one {n : ℕ} {C : Mₙ n} (hC : 0 ≤ C) :
    Filter.Tendsto (fun p : ℝ => matrixPower p C)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 (matrixPower 1 C)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let E : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec (hherm.eigenvectorBasis i : Fin n → ℂ)
      (star (hherm.eigenvectorBasis i : Fin n → ℂ))
  have hsum :
      Filter.Tendsto
        (fun p : ℝ =>
          ∑ i : Fin n, (powerFn p (hherm.eigenvalues i) : ℂ) • E i)
        (𝓝[Set.Ioo (0 : ℝ) 1] 1)
        (𝓝 (∑ i : Fin n, (powerFn 1 (hherm.eigenvalues i) : ℂ) • E i)) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun i hi =>
          (powerFn_tendsto_at_one (Matrix.PosSemidef.eigenvalues_nonneg hpsd i)).smul
            (tendsto_const_nhds (x := E i)))
  simpa [hpsd, hherm, E, matrixPower_eq_sum_eigenmatrix_nonneg hC] using hsum

private lemma matrixPower_one_sub_tendsto_at_zero {n : ℕ} {C : Mₙ n} (hC : 0 ≤ C) :
    Filter.Tendsto (fun p : ℝ => matrixPower (1 - p) C)
      (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 (matrixPower 1 C)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let E : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec (hherm.eigenvectorBasis i : Fin n → ℂ)
      (star (hherm.eigenvectorBasis i : Fin n → ℂ))
  have hsum :
      Filter.Tendsto
        (fun p : ℝ =>
          ∑ i : Fin n, (powerFn (1 - p) (hherm.eigenvalues i) : ℂ) • E i)
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑ i : Fin n, (powerFn 1 (hherm.eigenvalues i) : ℂ) • E i)) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun i hi =>
          (powerFn_one_sub_tendsto_at_zero (Matrix.PosSemidef.eigenvalues_nonneg hpsd i)).smul
            (tendsto_const_nhds (x := E i)))
  simpa [hpsd, hherm, E, matrixPower_eq_sum_eigenmatrix_nonneg hC] using hsum

private lemma matrixPower_one_sub_tendsto_supportProj_at_one {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) :
    Filter.Tendsto (fun p : ℝ => matrixPower (1 - p) C)
      (𝓝[Set.Ioo (0 : ℝ) 1] 1) (𝓝 (matrixSupportProj C)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let E : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec (hherm.eigenvectorBasis i : Fin n → ℂ)
      (star (hherm.eigenvectorBasis i : Fin n → ℂ))
  have hsum :
      Filter.Tendsto
        (fun p : ℝ =>
          ∑ i : Fin n, (powerFn (1 - p) (hherm.eigenvalues i) : ℂ) • E i)
        (𝓝[Set.Ioo (0 : ℝ) 1] 1)
        (𝓝 (∑ i : Fin n,
          (if hherm.eigenvalues i = 0 then (0 : ℂ) else 1) • E i)) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun i hi =>
          (powerFn_one_sub_tendsto_supportCoeff_one
            (Matrix.PosSemidef.eigenvalues_nonneg hpsd i)).smul
              (tendsto_const_nhds (x := E i)))
  simpa [hpsd, hherm, E, matrixPower_eq_sum_eigenmatrix_nonneg hC,
    matrixSupportProj_eq_sum_eigenmatrix_nonneg hC] using hsum

private lemma liebTracePower_tendsto_zeroSupport {n : ℕ} {A B X : Mₙ n}
    {l : Filter ℝ}
    (hApow : Filter.Tendsto (fun p : ℝ => matrixPower p A) l (𝓝 (matrixSupportProj A)))
    (hBpow : Filter.Tendsto (fun p : ℝ => matrixPower (1 - p) B) l
      (𝓝 (matrixPower 1 B))) :
    Filter.Tendsto (fun p : ℝ => liebTracePower p A B X) l
      (𝓝 (Complex.re
        (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj A * X * matrixPower 1 B)))) := by
  have hprod :
      Filter.Tendsto
        (fun p : ℝ =>
          Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B)
        l
        (𝓝 (Matrix.conjTranspose X * matrixSupportProj A * X * matrixPower 1 B)) := by
    simpa [Matrix.mul_assoc] using
      (((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow)
  have htrace :
      Filter.Tendsto
        (fun p : ℝ =>
          Matrix.trace (Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * matrixSupportProj A * X * matrixPower 1 B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [liebTracePower, powerTrace] using Complex.continuous_re.continuousAt.tendsto.comp htrace

private lemma liebTracePower_tendsto_oneSupport {n : ℕ} {A B X : Mₙ n}
    {l : Filter ℝ}
    (hApow : Filter.Tendsto (fun p : ℝ => matrixPower p A) l (𝓝 (matrixPower 1 A)))
    (hBpow : Filter.Tendsto (fun p : ℝ => matrixPower (1 - p) B) l
      (𝓝 (matrixSupportProj B))) :
    Filter.Tendsto (fun p : ℝ => liebTracePower p A B X) l
      (𝓝 (Complex.re
        (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 A * X * matrixSupportProj B)))) := by
  have hprod :
      Filter.Tendsto
        (fun p : ℝ =>
          Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B)
        l
        (𝓝 (Matrix.conjTranspose X * matrixPower 1 A * X * matrixSupportProj B)) := by
    simpa [Matrix.mul_assoc] using
      (((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow)
  have htrace :
      Filter.Tendsto
        (fun p : ℝ =>
          Matrix.trace (Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * matrixPower 1 A * X * matrixSupportProj B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [liebTracePower, powerTrace] using Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Semidefinite output-support trace-power form of Theorem 6.3(1), restricted to
`0 < p < 1`.  The endpoints are not covered here because the book uses the
support-projection convention for zero powers, while `matrixPower` is the raw real CFC
power; the closed range `0 ≤ p ≤ 1` in the support-power convention is
`directSupportTracePowerOutputSupport` (`SupportPower.lean`).
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_le_map_semidef_Ioo :
    ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Ioo (0 : ℝ) 1 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    0 ≤ A →
    0 ≤ B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      liebTracePower p A B ((hsAdjoint Ψ) X) ≤
        liebTracePower p (Ψ A) (Ψ B) X := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X
  let l : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
  let Aε : ℝ → Mₙ n := fun ε => A + (ε : ℂ) • (1 : Mₙ n)
  let Bε : ℝ → Mₙ n := fun ε => B + (ε : ℂ) • (1 : Mₙ n)
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  have hε_tendsto : Filter.Tendsto (fun ε : ℝ => ε) l (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hεC_tendsto : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hε_tendsto
  have hAεlim : Filter.Tendsto Aε l (𝓝 A) := by
    simpa [Aε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hBεlim : Filter.Tendsto Bε l (𝓝 B) := by
    simpa [Bε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hAε_nonneg : ∀ᶠ ε in l, 0 ≤ Aε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A) hA hε)
  have hBε_nonneg : ∀ᶠ ε in l, 0 ≤ Bε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B) hB hε)
  have hΨAεlim : Filter.Tendsto (fun ε : ℝ => Ψ (Aε ε)) l (𝓝 (Ψ A)) :=
    Ψ.continuous.continuousAt.tendsto.comp hAεlim
  have hΨBεlim : Filter.Tendsto (fun ε : ℝ => Ψ (Bε ε)) l (𝓝 (Ψ B)) :=
    Ψ.continuous.continuousAt.tendsto.comp hBεlim
  have hΨA_nonneg : 0 ≤ Ψ A := hΨpos hA
  have hΨB_nonneg : 0 ≤ Ψ B := hΨpos hB
  have hΨAε_nonneg : ∀ᶠ ε in l, 0 ≤ Ψ (Aε ε) := by
    exact hAε_nonneg.mono fun ε hε => hΨpos hε
  have hΨBε_nonneg : ∀ᶠ ε in l, 0 ≤ Ψ (Bε ε) := by
    exact hBε_nonneg.mono fun ε hε => hΨpos hε
  have hleft_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => liebTracePower p (Ψ (Aε ε)) (Ψ (Bε ε)) X)
        l
        (𝓝 (liebTracePower p (Ψ A) (Ψ B) X)) :=
    _root_.HiaiPetz.liebTracePower_tendsto_of_tendsto_nonneg hp hΨAεlim hΨBεlim
      hΨA_nonneg hΨB_nonneg hΨAε_nonneg hΨBε_nonneg
  have hright_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => liebTracePower p (Aε ε) (Bε ε) ((hsAdjoint Ψ) X))
        l
        (𝓝 (liebTracePower p A B ((hsAdjoint Ψ) X))) :=
    _root_.HiaiPetz.liebTracePower_tendsto_of_tendsto_nonneg hp hAεlim hBεlim
      hA hB hAε_nonneg hBε_nonneg
  have hEventually :
      ∀ᶠ ε in l,
        liebTracePower p (Aε ε) (Bε ε) ((hsAdjoint Ψ) X) ≤
          liebTracePower p (Ψ (Aε ε)) (Ψ (Bε ε)) X := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAεpd : Matrix.PosDef (Aε ε) := by
      simpa [Aε] using _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A) hA hε
    have hBεpd : Matrix.PosDef (Bε ε) := by
      simpa [Bε] using _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B) hB hε
    have h :=
      directTracePowerOutputSupport Φ (p := p) (A := Aε ε) (B := Bε ε)
        hpIcc hPos hTrace hSch hAεpd hBεpd (X := X)
    simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
      MatrixCornerModel.transportMap] using h
  exact le_of_tendsto_of_tendsto hright_tendsto hleft_tendsto hEventually

/-- Endpoint `p = 0` support-power form of Theorem 6.3(1) on the output-support
reduced corner.  The zero power of `A` is read as `matrixSupportProj A`; `matrixPower`
itself is deliberately left as the raw CFC power.
Source: Hiai, Theorem 6.3. -/
theorem trace_supportProj_le_map_zero :
    ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    0 ≤ A →
    0 ≤ B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixSupportProj A *
            ((hsAdjoint Ψ) X) * matrixPower 1 B)) ≤
        Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj (Ψ A) * X *
            matrixPower 1 (Ψ B))) := by
  intro n m Φ A B
  dsimp
  intro hPos hTrace hSch hA hB X
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) 1] 0
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨA_nonneg : 0 ≤ Ψ A := hΨpos hA
  have hΨB_nonneg : 0 ≤ Ψ B := hΨpos hB
  have hleft_tendsto :
      Filter.Tendsto (fun p : ℝ => liebTracePower p (Ψ A) (Ψ B) X) l
        (𝓝 (Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixSupportProj (Ψ A) * X *
            matrixPower 1 (Ψ B))))) :=
    liebTracePower_tendsto_zeroSupport
      (A := Ψ A) (B := Ψ B) (X := X) (l := l)
      (matrixPower_tendsto_supportProj_at_zero hΨA_nonneg)
      (matrixPower_one_sub_tendsto_at_zero hΨB_nonneg)
  have hright_tendsto :
      Filter.Tendsto (fun p : ℝ => liebTracePower p A B ((hsAdjoint Ψ) X)) l
        (𝓝 (Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixSupportProj A *
            ((hsAdjoint Ψ) X) * matrixPower 1 B)))) :=
    liebTracePower_tendsto_zeroSupport
      (A := A) (B := B) (X := (hsAdjoint Ψ) X) (l := l)
      (matrixPower_tendsto_supportProj_at_zero hA)
      (matrixPower_one_sub_tendsto_at_zero hB)
  have hEventually :
      ∀ᶠ p in l,
        liebTracePower p A B ((hsAdjoint Ψ) X) ≤
          liebTracePower p (Ψ A) (Ψ B) X := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have h :=
      liebTracePower_le_map_semidef_Ioo Φ
        (p := p) (A := A) (B := B) hp hPos hTrace hSch hA hB (X := X)
    simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
      MatrixCornerModel.transportMap] using h
  exact le_of_tendsto_of_tendsto hright_tendsto hleft_tendsto hEventually

/-- Endpoint `p = 1` support-power form of Theorem 6.3(1) on the output-support
reduced corner.  The zero power of `B` is read as `matrixSupportProj B`; `matrixPower`
itself is deliberately left as the raw CFC power.
Source: Hiai, Theorem 6.3. -/
theorem trace_supportProj_le_map_one :
    ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    0 ≤ A →
    0 ≤ B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixPower 1 A *
            ((hsAdjoint Ψ) X) * matrixSupportProj B)) ≤
        Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 (Ψ A) * X *
            matrixSupportProj (Ψ B))) := by
  intro n m Φ A B
  dsimp
  intro hPos hTrace hSch hA hB X
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) 1] 1
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨA_nonneg : 0 ≤ Ψ A := hΨpos hA
  have hΨB_nonneg : 0 ≤ Ψ B := hΨpos hB
  have hleft_tendsto :
      Filter.Tendsto (fun p : ℝ => liebTracePower p (Ψ A) (Ψ B) X) l
        (𝓝 (Complex.re
          (Matrix.trace (Matrix.conjTranspose X * matrixPower 1 (Ψ A) * X *
            matrixSupportProj (Ψ B))))) :=
    liebTracePower_tendsto_oneSupport
      (A := Ψ A) (B := Ψ B) (X := X) (l := l)
      (matrixPower_tendsto_at_one hΨA_nonneg)
      (matrixPower_one_sub_tendsto_supportProj_at_one hΨB_nonneg)
  have hright_tendsto :
      Filter.Tendsto (fun p : ℝ => liebTracePower p A B ((hsAdjoint Ψ) X)) l
        (𝓝 (Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Ψ) X) * matrixPower 1 A *
            ((hsAdjoint Ψ) X) * matrixSupportProj B)))) :=
    liebTracePower_tendsto_oneSupport
      (A := A) (B := B) (X := (hsAdjoint Ψ) X) (l := l)
      (matrixPower_tendsto_at_one hA)
      (matrixPower_one_sub_tendsto_supportProj_at_one hB)
  have hEventually :
      ∀ᶠ p in l,
        liebTracePower p A B ((hsAdjoint Ψ) X) ≤
          liebTracePower p (Ψ A) (Ψ B) X := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have h :=
      liebTracePower_le_map_semidef_Ioo Φ
        (p := p) (A := A) (B := B) hp hPos hTrace hSch hA hB (X := X)
    simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
      MatrixCornerModel.transportMap] using h
  exact le_of_tendsto_of_tendsto hright_tendsto hleft_tendsto hEventually


end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
