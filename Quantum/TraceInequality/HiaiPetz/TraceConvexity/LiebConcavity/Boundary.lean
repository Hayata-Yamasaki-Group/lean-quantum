/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceConvexity.LiebConcavity.Basic

/-!
# Lieb concavity: boundary exponents

Joint concavity of the support-projected Lieb trace-power functional
`supportLiebTracePower` at the boundary exponents, completing the interior case
from `LiebConcavity/Basic.lean` (Hiai–Petz Theorem 6.4).  The interior result on
the open unit square is extended to the exponents `0` and `1` by continuity
(limits of nonnegative matrix powers), and the three cases are assembled into the
full joint-concavity statement and its scaled variant.

## Main results

* `re_trace_mul_nonneg_of_nonneg_nonneg`: nonnegativity of the real trace of a
  product of nonnegative matrices, used in the boundary estimates.
* `supportLiebTracePower_jointlyConcave_Ioo` / `_zero` / `_one`: joint concavity
  on the open square and at the two boundary exponents.
* `supportLiebTracePower_jointlyConcave`: the combined joint-concavity statement.
* `supportPowerTrace_scaled_jointlyConcave_Ioo` /
  `supportPowerTrace_scaled_jointlyConcave`: the scaled trace-power variants.

## References

* Hiai, Theorem 6.4.
-/

namespace HiaiPetz
namespace TraceConvexity
open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
noncomputable section MatrixScopedInstances

private theorem matrix_nonneg_convex_combo {n : ℕ} {A1 A2 : Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) :
    0 ≤ t • A1 + (1 - t) • A2 :=
  add_nonneg (smul_nonneg ht.1 hA1) (smul_nonneg (sub_nonneg.mpr ht.2) hA2)

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem re_trace_mul_nonneg_of_nonneg_nonneg {n : ℕ} {B D : Mₙ n}
    (hB : 0 ≤ B) (hD : 0 ≤ D) :
    0 ≤ Complex.re (Matrix.trace (B * D)) := by
  have hD_psd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
  have hS_psd : (matrixSqrtPos B).PosSemidef :=
    matrixSqrtPos_posSemidef_of_nonneg hB
  have hS_sa : IsSelfAdjoint (matrixSqrtPos B) := hS_psd.1
  have hconj_psd :
      (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)).PosSemidef := by
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same hD_psd (matrixSqrtPos B)
  have htrace_nonneg :
      0 ≤ Matrix.trace (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)) :=
    Matrix.PosSemidef.trace_nonneg hconj_psd
  have hsqrt_star : Matrix.conjTranspose (matrixSqrtPos B) = matrixSqrtPos B := by
    simpa [IsSelfAdjoint] using hS_sa.star_eq
  have htrace_eq :
      Matrix.trace (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)) =
        Matrix.trace (B * D) := by
    rw [hsqrt_star]
    calc
      Matrix.trace ((matrixSqrtPos B * D) * matrixSqrtPos B)
          = Matrix.trace (matrixSqrtPos B * (matrixSqrtPos B * D)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((matrixSqrtPos B * matrixSqrtPos B) * D) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (B * D) := by
            rw [matrixSqrtPos_mul_self_of_nonneg hB]
  have htrace_nonneg' : 0 ≤ Matrix.trace (B * D) := by
    simpa [htrace_eq] using htrace_nonneg
  exact (RCLike.nonneg_iff.mp htrace_nonneg').1

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem supportPowerTrace_le_of_right_power_le {n : ℕ} {r s : ℝ}
    {A B1 B2 X : Mₙ n} (hA : 0 ≤ A)
    (hle : supportMatrixPower s B1 ≤ supportMatrixPower s B2) :
    supportPowerTrace r s A B1 X ≤ supportPowerTrace r s A B2 X := by
  let Ar : Mₙ n := supportMatrixPower r A
  let D : Mₙ n := supportMatrixPower s B2 - supportMatrixPower s B1
  have hAr_nonneg : 0 ≤ Ar := by
    simpa [Ar] using supportMatrixPower_nonneg hA r
  have hC_nonneg : 0 ≤ Matrix.conjTranspose X * Ar * X := by
    have hAr_psd : Ar.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hAr_nonneg
    exact (Matrix.nonneg_iff_posSemidef).mpr
      (Matrix.PosSemidef.conjTranspose_mul_mul_same hAr_psd X)
  have hD_nonneg : 0 ≤ D := by
    simpa [D] using sub_nonneg.mpr hle
  have htrace :
      0 ≤ Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) :=
    re_trace_mul_nonneg_of_nonneg_nonneg hC_nonneg hD_nonneg
  rw [← sub_nonneg]
  have hdiff :
      supportPowerTrace r s A B2 X - supportPowerTrace r s A B1 X =
        Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) := by
    have hmat :
        Matrix.conjTranspose X * supportMatrixPower r A * X * supportMatrixPower s B2 -
            Matrix.conjTranspose X * supportMatrixPower r A * X * supportMatrixPower s B1 =
          (Matrix.conjTranspose X * Ar * X) * D := by
      simp [Ar, D, Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add]
    calc
      supportPowerTrace r s A B2 X - supportPowerTrace r s A B1 X
          = Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * supportMatrixPower r A * X *
                  supportMatrixPower s B2)) -
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * supportMatrixPower r A * X *
                  supportMatrixPower s B1)) := by
              rfl
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * supportMatrixPower r A * X *
                supportMatrixPower s B2) -
              Matrix.trace
                (Matrix.conjTranspose X * supportMatrixPower r A * X *
                  supportMatrixPower s B1)) := by
            rw [Complex.sub_re]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * supportMatrixPower r A * X *
                supportMatrixPower s B2 -
                Matrix.conjTranspose X * supportMatrixPower r A * X *
                  supportMatrixPower s B1)) := by
            rw [Matrix.trace_sub]
      _ = Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) := by
            rw [hmat]
  simpa [hdiff]
    using htrace

/-- Source: Hiai, Theorem 6.4. -/
theorem supportLiebTracePower_jointlyConcave_Ioo :
    ∀ {n : ℕ} {p : ℝ} {X : Mₙ n},
      p ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportLiebTracePower p A1 B1 X +
            (1 - t) * supportLiebTracePower p A2 B2 X ≤
          supportLiebTracePower p (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n p X hp A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  /- Step 1: Introduce ε-regularized positive-definite perturbations of the four matrices. -/
  let l : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
  let A1ε : ℝ → Mₙ n := fun ε => A1 + (ε : ℂ) • (1 : Mₙ n)
  let A2ε : ℝ → Mₙ n := fun ε => A2 + (ε : ℂ) • (1 : Mₙ n)
  let B1ε : ℝ → Mₙ n := fun ε => B1 + (ε : ℂ) • (1 : Mₙ n)
  let B2ε : ℝ → Mₙ n := fun ε => B2 + (ε : ℂ) • (1 : Mₙ n)
  let Atε : ℝ → Mₙ n := fun ε => t • A1ε ε + (1 - t) • A2ε ε
  let Btε : ℝ → Mₙ n := fun ε => t • B1ε ε + (1 - t) • B2ε ε
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  /- Step 2: Show each perturbed family converges to its limit as ε → 0⁺. -/
  have hε_tendsto : Filter.Tendsto (fun ε : ℝ => ε) l (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hεC_tendsto : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hε_tendsto
  have hA1εlim : Filter.Tendsto A1ε l (𝓝 A1) := by
    simpa [A1ε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hA2εlim : Filter.Tendsto A2ε l (𝓝 A2) := by
    simpa [A2ε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hB1εlim : Filter.Tendsto B1ε l (𝓝 B1) := by
    simpa [B1ε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hB2εlim : Filter.Tendsto B2ε l (𝓝 B2) := by
    simpa [B2ε] using tendsto_const_nhds.add
      (hεC_tendsto.smul_const (1 : Mₙ n))
  have hAtlim : Filter.Tendsto Atε l (𝓝 At) :=
    (hA1εlim.const_smul t).add (hA2εlim.const_smul (1 - t))
  have hBtlim : Filter.Tendsto Btε l (𝓝 Bt) :=
    (hB1εlim.const_smul t).add (hB2εlim.const_smul (1 - t))
  /- Step 3: Record positivity of the perturbations and nonnegativity of the limits. -/
  have hA1ε_nonneg : ∀ᶠ ε in l, 0 ≤ A1ε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A1) hA1 hε)
  have hA2ε_nonneg : ∀ᶠ ε in l, 0 ≤ A2ε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A2) hA2 hε)
  have hB1ε_nonneg : ∀ᶠ ε in l, 0 ≤ B1ε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B1) hB1 hε)
  have hB2ε_nonneg : ∀ᶠ ε in l, 0 ≤ B2ε ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.PosDef.nonneg
      (_root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B2) hB2 hε)
  have hAt_nonneg : 0 ≤ At := matrix_nonneg_convex_combo ht hA1 hA2
  have hBt_nonneg : 0 ≤ Bt := matrix_nonneg_convex_combo ht hB1 hB2
  have hAtε_nonneg : ∀ᶠ ε in l, 0 ≤ Atε ε := by
    filter_upwards [hA1ε_nonneg, hA2ε_nonneg] with ε hA1ε hA2ε
    exact matrix_nonneg_convex_combo ht hA1ε hA2ε
  have hBtε_nonneg : ∀ᶠ ε in l, 0 ≤ Btε ε := by
    filter_upwards [hB1ε_nonneg, hB2ε_nonneg] with ε hB1ε hB2ε
    exact matrix_nonneg_convex_combo ht hB1ε hB2ε
  /- Step 4: Transport continuity of the support functional to the families and the RHS. -/
  have hAt_tendsto :
      Filter.Tendsto (fun ε : ℝ => supportLiebTracePower p (Atε ε) (Btε ε) X)
        l (𝓝 (supportLiebTracePower p At Bt X)) := by
    have hraw :=
      _root_.HiaiPetz.liebTracePower_tendsto_of_tendsto_nonneg hp hAtlim hBtlim
        hAt_nonneg hBt_nonneg hAtε_nonneg hBtε_nonneg (X := X)
    have heq_event :
        (fun ε : ℝ => supportLiebTracePower p (Atε ε) (Btε ε) X) =ᶠ[l]
          fun ε : ℝ => liebTracePower p (Atε ε) (Btε ε) X := by
      filter_upwards [hAtε_nonneg, hBtε_nonneg] with ε hAε hBε
      exact supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hAε hBε
    have hlim_eq :
        supportLiebTracePower p At Bt X = liebTracePower p At Bt X :=
      supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hAt_nonneg hBt_nonneg
    rw [hlim_eq]
    exact hraw.congr' (heq_event.mono fun ε hε => hε.symm)
  have hA1_tendsto :
      Filter.Tendsto (fun ε : ℝ => supportLiebTracePower p (A1ε ε) (B1ε ε) X)
        l (𝓝 (supportLiebTracePower p A1 B1 X)) := by
    have hraw :=
      _root_.HiaiPetz.liebTracePower_tendsto_of_tendsto_nonneg hp hA1εlim hB1εlim
        hA1 hB1 hA1ε_nonneg hB1ε_nonneg (X := X)
    have heq_event :
        (fun ε : ℝ => supportLiebTracePower p (A1ε ε) (B1ε ε) X) =ᶠ[l]
          fun ε : ℝ => liebTracePower p (A1ε ε) (B1ε ε) X := by
      filter_upwards [hA1ε_nonneg, hB1ε_nonneg] with ε hAε hBε
      exact supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hAε hBε
    have hlim_eq :
        supportLiebTracePower p A1 B1 X = liebTracePower p A1 B1 X :=
      supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hA1 hB1
    rw [hlim_eq]
    exact hraw.congr' (heq_event.mono fun ε hε => hε.symm)
  have hA2_tendsto :
      Filter.Tendsto (fun ε : ℝ => supportLiebTracePower p (A2ε ε) (B2ε ε) X)
        l (𝓝 (supportLiebTracePower p A2 B2 X)) := by
    have hraw :=
      _root_.HiaiPetz.liebTracePower_tendsto_of_tendsto_nonneg hp hA2εlim hB2εlim
        hA2 hB2 hA2ε_nonneg hB2ε_nonneg (X := X)
    have heq_event :
        (fun ε : ℝ => supportLiebTracePower p (A2ε ε) (B2ε ε) X) =ᶠ[l]
          fun ε : ℝ => liebTracePower p (A2ε ε) (B2ε ε) X := by
      filter_upwards [hA2ε_nonneg, hB2ε_nonneg] with ε hAε hBε
      exact supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hAε hBε
    have hlim_eq :
        supportLiebTracePower p A2 B2 X = liebTracePower p A2 B2 X :=
      supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo hp hA2 hB2
    rw [hlim_eq]
    exact hraw.congr' (heq_event.mono fun ε hε => hε.symm)
  have hright_tendsto :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * supportLiebTracePower p (A1ε ε) (B1ε ε) X +
            (1 - t) * supportLiebTracePower p (A2ε ε) (B2ε ε) X)
        l
        (𝓝 (t * supportLiebTracePower p A1 B1 X +
          (1 - t) * supportLiebTracePower p A2 B2 X)) := by
    exact (tendsto_const_nhds.mul hA1_tendsto).add
      (tendsto_const_nhds.mul hA2_tendsto)
  /- Step 5: Apply the positive-definite joint concavity for every ε > 0. -/
  have hEventually :
      ∀ᶠ ε in l,
        t * supportLiebTracePower p (A1ε ε) (B1ε ε) X +
          (1 - t) * supportLiebTracePower p (A2ε ε) (B2ε ε) X ≤
            supportLiebTracePower p (Atε ε) (Btε ε) X := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hA1pd : Matrix.PosDef (A1ε ε) := by
      simpa [A1ε] using
        _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A1) hA1 hε
    have hA2pd : Matrix.PosDef (A2ε ε) := by
      simpa [A2ε] using
        _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := A2) hA2 hε
    have hB1pd : Matrix.PosDef (B1ε ε) := by
      simpa [B1ε] using
        _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B1) hB1 hε
    have hB2pd : Matrix.PosDef (B2ε ε) := by
      simpa [B2ε] using
        _root_.HiaiPetz.matrixPosDef_add_pos_smul_one_of_nonneg (A := B2) hB2 hε
    exact supportLiebTracePower_jointlyConcave_posDef ⟨le_of_lt hp.1, le_of_lt hp.2⟩ ht
      hA1pd hA2pd hB1pd hB2pd
  /- Step 6: Take the ε → 0⁺ limit to conclude concavity at the boundary exponent. -/
  exact le_of_tendsto_of_tendsto hright_tendsto hAt_tendsto hEventually

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma supportPowerCoeff_tendsto_of_tendsto {α : Type*} {l : Filter α}
    {g : α → ℝ} {r μ : ℝ} (hg : Filter.Tendsto g l (𝓝 r)) :
    Filter.Tendsto (fun a : α => (supportPowerCoeff (g a) μ : ℂ)) l
      (𝓝 (supportPowerCoeff r μ : ℂ)) := by
  by_cases hzero : μ = 0
  · simpa [supportPowerCoeff, hzero] using tendsto_const_nhds (x := (0 : ℂ))
  · have hreal : Filter.Tendsto (fun a : α => μ ^ g a) l (𝓝 (μ ^ r)) :=
      (Real.continuousAt_const_rpow hzero).tendsto.comp hg
    simpa [supportPowerCoeff, hzero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma supportMatrixPower_tendsto_exponent_nonneg {α : Type*} {n : ℕ}
    {g : α → ℝ} {l : Filter α} {r : ℝ} {C : Mₙ n}
    (hg : Filter.Tendsto g l (𝓝 r)) (hC : 0 ≤ C) :
    Filter.Tendsto (fun a : α => supportMatrixPower (g a) C) l
      (𝓝 (supportMatrixPower r C)) := by
  let hpsd : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hC
  let hherm : C.IsHermitian := hpsd.1
  let E : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec (hherm.eigenvectorBasis i : Fin n → ℂ)
      (star (hherm.eigenvectorBasis i : Fin n → ℂ))
  have hsum :
      Filter.Tendsto
        (fun a : α =>
          ∑ i : Fin n, (supportPowerCoeff (g a) (hherm.eigenvalues i) : ℂ) • E i)
        l
        (𝓝 (∑ i : Fin n, (supportPowerCoeff r (hherm.eigenvalues i) : ℂ) • E i)) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun i hi =>
          (supportPowerCoeff_tendsto_of_tendsto
            (μ := hherm.eigenvalues i) hg).smul (tendsto_const_nhds (x := E i)))
  simpa [hpsd, hherm, E, supportMatrixPower_eq_sum_eigenmatrix_nonneg hC] using hsum

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma supportLiebTracePower_tendsto_exponent_nonneg {α : Type*} {n : ℕ}
    {g : α → ℝ} {l : Filter α} {p : ℝ} {A B X : Mₙ n}
    (hg : Filter.Tendsto g l (𝓝 p)) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Filter.Tendsto (fun a : α => supportLiebTracePower (g a) A B X) l
      (𝓝 (supportLiebTracePower p A B X)) := by
  have hApow :
      Filter.Tendsto (fun a : α => supportMatrixPower (g a) A) l
        (𝓝 (supportMatrixPower p A)) :=
    supportMatrixPower_tendsto_exponent_nonneg hg hA
  have hBpow :
      Filter.Tendsto (fun a : α => supportMatrixPower (1 - g a) B) l
        (𝓝 (supportMatrixPower (1 - p) B)) := by
    exact supportMatrixPower_tendsto_exponent_nonneg
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hg) hB
  have hprod :
      Filter.Tendsto
        (fun a : α =>
          Matrix.conjTranspose X * supportMatrixPower (g a) A * X *
            supportMatrixPower (1 - g a) B)
        l
        (𝓝 (Matrix.conjTranspose X * supportMatrixPower p A * X *
          supportMatrixPower (1 - p) B)) := by
    simpa [Matrix.mul_assoc] using
      (((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow)
  have htrace :
      Filter.Tendsto
        (fun a : α =>
          Matrix.trace
            (Matrix.conjTranspose X * supportMatrixPower (g a) A * X *
              supportMatrixPower (1 - g a) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower p A * X *
            supportMatrixPower (1 - p) B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [supportLiebTracePower, supportPowerTrace] using
    Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma supportPowerTrace_tendsto_exponents_nonneg {α : Type*} {n : ℕ}
    {g h : α → ℝ} {l : Filter α} {p q : ℝ} {A B X : Mₙ n}
    (hg : Filter.Tendsto g l (𝓝 p)) (hh : Filter.Tendsto h l (𝓝 q))
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Filter.Tendsto (fun a : α => supportPowerTrace (g a) (h a) A B X) l
      (𝓝 (supportPowerTrace p q A B X)) := by
  have hApow :
      Filter.Tendsto (fun a : α => supportMatrixPower (g a) A) l
        (𝓝 (supportMatrixPower p A)) :=
    supportMatrixPower_tendsto_exponent_nonneg hg hA
  have hBpow :
      Filter.Tendsto (fun a : α => supportMatrixPower (h a) B) l
        (𝓝 (supportMatrixPower q B)) :=
    supportMatrixPower_tendsto_exponent_nonneg hh hB
  have hprod :
      Filter.Tendsto
        (fun a : α =>
          Matrix.conjTranspose X * supportMatrixPower (g a) A * X *
            supportMatrixPower (h a) B)
        l
        (𝓝 (Matrix.conjTranspose X * supportMatrixPower p A * X *
          supportMatrixPower q B)) := by
    simpa [Matrix.mul_assoc] using
      (((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow)
  have htrace :
      Filter.Tendsto
        (fun a : α =>
          Matrix.trace
            (Matrix.conjTranspose X * supportMatrixPower (g a) A * X *
              supportMatrixPower (h a) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * supportMatrixPower p A * X *
            supportMatrixPower q B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [supportPowerTrace] using
    Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Source: Hiai, Theorem 6.4. -/
theorem supportLiebTracePower_jointlyConcave_zero :
    ∀ {n : ℕ} {X : Mₙ n},
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportLiebTracePower 0 A1 B1 X +
            (1 - t) * supportLiebTracePower 0 A2 B2 X ≤
          supportLiebTracePower 0 (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n X A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) 1] 0
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  have hAt_nonneg : 0 ≤ At := by
    simpa [At] using matrix_nonneg_convex_combo ht hA1 hA2
  have hBt_nonneg : 0 ≤ Bt := by
    simpa [Bt] using matrix_nonneg_convex_combo ht hB1 hB2
  have hid : Filter.Tendsto (fun p : ℝ => p) l (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hleft_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p At Bt X) l
        (𝓝 (supportLiebTracePower 0 At Bt X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hAt_nonneg hBt_nonneg
  have hA1_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p A1 B1 X) l
        (𝓝 (supportLiebTracePower 0 A1 B1 X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hA1 hB1
  have hA2_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p A2 B2 X) l
        (𝓝 (supportLiebTracePower 0 A2 B2 X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hA2 hB2
  have hright_tendsto :
      Filter.Tendsto
        (fun p : ℝ =>
          t * supportLiebTracePower p A1 B1 X +
            (1 - t) * supportLiebTracePower p A2 B2 X)
        l
        (𝓝 (t * supportLiebTracePower 0 A1 B1 X +
          (1 - t) * supportLiebTracePower 0 A2 B2 X)) :=
    (tendsto_const_nhds.mul hA1_tendsto).add
      (tendsto_const_nhds.mul hA2_tendsto)
  have hEventually :
      ∀ᶠ p in l,
        t * supportLiebTracePower p A1 B1 X +
          (1 - t) * supportLiebTracePower p A2 B2 X ≤
            supportLiebTracePower p At Bt X := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact supportLiebTracePower_jointlyConcave_Ioo hp ht hA1 hA2 hB1 hB2
  simpa [At, Bt] using le_of_tendsto_of_tendsto hright_tendsto hleft_tendsto hEventually

/-- Source: Hiai, Theorem 6.4. -/
theorem supportLiebTracePower_jointlyConcave_one :
    ∀ {n : ℕ} {X : Mₙ n},
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportLiebTracePower 1 A1 B1 X +
            (1 - t) * supportLiebTracePower 1 A2 B2 X ≤
          supportLiebTracePower 1 (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n X A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) 1] 1
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  have hAt_nonneg : 0 ≤ At := by
    simpa [At] using matrix_nonneg_convex_combo ht hA1 hA2
  have hBt_nonneg : 0 ≤ Bt := by
    simpa [Bt] using matrix_nonneg_convex_combo ht hB1 hB2
  have hid : Filter.Tendsto (fun p : ℝ => p) l (𝓝 (1 : ℝ)) :=
    nhdsWithin_le_nhds
  have hleft_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p At Bt X) l
        (𝓝 (supportLiebTracePower 1 At Bt X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hAt_nonneg hBt_nonneg
  have hA1_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p A1 B1 X) l
        (𝓝 (supportLiebTracePower 1 A1 B1 X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hA1 hB1
  have hA2_tendsto :
      Filter.Tendsto (fun p : ℝ => supportLiebTracePower p A2 B2 X) l
        (𝓝 (supportLiebTracePower 1 A2 B2 X)) :=
    supportLiebTracePower_tendsto_exponent_nonneg hid hA2 hB2
  have hright_tendsto :
      Filter.Tendsto
        (fun p : ℝ =>
          t * supportLiebTracePower p A1 B1 X +
            (1 - t) * supportLiebTracePower p A2 B2 X)
        l
        (𝓝 (t * supportLiebTracePower 1 A1 B1 X +
          (1 - t) * supportLiebTracePower 1 A2 B2 X)) :=
    (tendsto_const_nhds.mul hA1_tendsto).add
      (tendsto_const_nhds.mul hA2_tendsto)
  have hEventually :
      ∀ᶠ p in l,
        t * supportLiebTracePower p A1 B1 X +
          (1 - t) * supportLiebTracePower p A2 B2 X ≤
            supportLiebTracePower p At Bt X := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact supportLiebTracePower_jointlyConcave_Ioo hp ht hA1 hA2 hB1 hB2
  simpa [At, Bt] using le_of_tendsto_of_tendsto hright_tendsto hleft_tendsto hEventually

/-- Source: Hiai, Theorem 6.4. -/
theorem supportLiebTracePower_jointlyConcave :
    ∀ {n : ℕ} {p : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportLiebTracePower p A1 B1 X +
            (1 - t) * supportLiebTracePower p A2 B2 X ≤
          supportLiebTracePower p (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n p X hp A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  by_cases hp0 : p = 0
  · subst p
    exact supportLiebTracePower_jointlyConcave_zero ht hA1 hA2 hB1 hB2
  by_cases hp1 : p = 1
  · subst p
    exact supportLiebTracePower_jointlyConcave_one ht hA1 hA2 hB1 hB2
  have hpIoo : p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
  exact supportLiebTracePower_jointlyConcave_Ioo hpIoo ht hA1 hA2 hB1 hB2

/-- Source: Hiai, Theorem 6.4. -/
private theorem supportPowerTrace_scaled_jointlyConcave_Ioo_core {n : ℕ} {p r : ℝ} {X : Mₙ n}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    {A1 A2 B1 B2 : Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    supportPowerTrace p (r * (1 - p)) (t • A1 + (1 - t) • A2)
        (t • B1 + (1 - t) • B2) X ≥
      t * supportPowerTrace p (r * (1 - p)) A1 B1 X +
        (1 - t) * supportPowerTrace p (r * (1 - p)) A2 B2 X := by
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  let C1 : Mₙ n := supportMatrixPower r B1
  let C2 : Mₙ n := supportMatrixPower r B2
  let Ct : Mₙ n := t • C1 + (1 - t) • C2
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hs_pos : 0 < 1 - p := sub_pos.mpr hp.2
  have hsIcc : 1 - p ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨hs_pos.le, by linarith [hp.1.le]⟩
  have hAt_nonneg : 0 ≤ At := matrix_nonneg_convex_combo ht hA1 hA2
  have hBt_nonneg : 0 ≤ Bt := matrix_nonneg_convex_combo ht hB1 hB2
  have hC1_nonneg : 0 ≤ C1 := supportMatrixPower_nonneg hB1 r
  have hC2_nonneg : 0 ≤ C2 := supportMatrixPower_nonneg hB2 r
  have hCt_nonneg : 0 ≤ Ct := matrix_nonneg_convex_combo ht hC1_nonneg hC2_nonneg
  have hBr_nonneg : 0 ≤ supportMatrixPower r Bt :=
    supportMatrixPower_nonneg hBt_nonneg r
  have hCt_le : Ct ≤ supportMatrixPower r Bt := by
    have hconc :=
      matrixPower_concave_nonneg hrIcc ht hB1 hB2
    change t • supportMatrixPower r B1 + (1 - t) • supportMatrixPower r B2 ≤
      supportMatrixPower r Bt
    rw [supportMatrixPower_eq_matrixPower_of_pos_nonneg hr.1 hB1,
      supportMatrixPower_eq_matrixPower_of_pos_nonneg hr.1 hB2,
      supportMatrixPower_eq_matrixPower_of_pos_nonneg hr.1 hBt_nonneg]
    exact hconc
  have hpow_le :
      supportMatrixPower (1 - p) Ct ≤
        supportMatrixPower (1 - p) (supportMatrixPower r Bt) := by
    have hraw :=
      matrixPower_monotone_nonneg hsIcc hCt_nonneg hBr_nonneg hCt_le
    rw [supportMatrixPower_eq_matrixPower_of_pos_nonneg hs_pos hCt_nonneg,
      supportMatrixPower_eq_matrixPower_of_pos_nonneg hs_pos hBr_nonneg]
    exact hraw
  have hboundary :=
    supportLiebTracePower_jointlyConcave hpIcc ht hA1 hA2 hC1_nonneg hC2_nonneg (X := X)
  have hC1_comp :=
    supportLiebTracePower_right_comp_pos (A := A1) (B := B1) (X := X)
      hp hr.1 hB1
  have hC2_comp :=
    supportLiebTracePower_right_comp_pos (A := A2) (B := B2) (X := X)
      hp hr.1 hB2
  have hboundary' :
      t * supportPowerTrace p (r * (1 - p)) A1 B1 X +
          (1 - t) * supportPowerTrace p (r * (1 - p)) A2 B2 X ≤
        supportLiebTracePower p At Ct X := by
    rw [← hC1_comp, ← hC2_comp]
    exact hboundary
  have hleft_le :
      supportLiebTracePower p At Ct X ≤
        supportPowerTrace p (r * (1 - p)) At Bt X := by
    have hmono :=
      supportPowerTrace_le_of_right_power_le
        (r := p) (s := 1 - p) (A := At) (B1 := Ct)
        (B2 := supportMatrixPower r Bt) (X := X) hAt_nonneg hpow_le
    have hcomp :=
      supportLiebTracePower_right_comp_pos (A := At) (B := Bt) (X := X)
        hp hr.1 hBt_nonneg
    rw [← hcomp]
    exact hmono
  exact le_trans hboundary' hleft_le

/-- Source: Hiai, Theorem 6.4. -/
theorem supportPowerTrace_scaled_jointlyConcave_Ioo :
    ∀ {n : ℕ} {p r : ℝ} {X : Mₙ n},
      p ∈ Set.Ioo (0 : ℝ) 1 →
      r ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportPowerTrace p (r * (1 - p)) A1 B1 X +
            (1 - t) * supportPowerTrace p (r * (1 - p)) A2 B2 X ≤
          supportPowerTrace p (r * (1 - p)) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n p r X hp hr A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  exact supportPowerTrace_scaled_jointlyConcave_Ioo_core hp hr ht hA1 hA2 hB1 hB2

/-- Source: Hiai, proof of Theorem 6.4. -/
lemma unit_interval_affine_Ioo {x ε : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ε + (1 - 2 * ε) * x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hcoef_nonneg : 0 ≤ 1 - 2 * ε := by
    nlinarith [hε.2]
  constructor
  · have hterm_nonneg : 0 ≤ (1 - 2 * ε) * x :=
      mul_nonneg hcoef_nonneg hx.1
    nlinarith [hε.1, hterm_nonneg]
  · have hle : (1 - 2 * ε) * x ≤ (1 - 2 * ε) * 1 :=
      mul_le_mul_of_nonneg_left hx.2 hcoef_nonneg
    nlinarith [hε.1, hε.2, hle]

/-- Source: Hiai, Theorem 6.4. -/
theorem supportPowerTrace_scaled_jointlyConcave :
    ∀ {n : ℕ} {p r : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (0 : ℝ) 1 →
      r ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ A1 →
        0 ≤ A2 →
        0 ≤ B1 →
        0 ≤ B2 →
        t * supportPowerTrace p (r * (1 - p)) A1 B1 X +
            (1 - t) * supportPowerTrace p (r * (1 - p)) A2 B2 X ≤
          supportPowerTrace p (r * (1 - p)) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) X := by
  intro n p r X hp hr A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) (1 / 2)] 0
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    exact ⟨le_rfl, by norm_num⟩
  let pe : ℝ → ℝ := fun ε => ε + (1 - 2 * ε) * p
  let re : ℝ → ℝ := fun ε => ε + (1 - 2 * ε) * r
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  have hAt_nonneg : 0 ≤ At := by
    simpa [At] using matrix_nonneg_convex_combo ht hA1 hA2
  have hBt_nonneg : 0 ≤ Bt := by
    simpa [Bt] using matrix_nonneg_convex_combo ht hB1 hB2
  have hε_tendsto : Filter.Tendsto (fun ε : ℝ => ε) l (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hpe : Filter.Tendsto pe l (𝓝 p) := by
    have hcont :
        ContinuousAt (fun ε : ℝ => ε + (1 - 2 * ε) * p) 0 := by
      fun_prop
    simpa [pe] using hcont.tendsto.comp hε_tendsto
  have hre : Filter.Tendsto re l (𝓝 r) := by
    have hcont :
        ContinuousAt (fun ε : ℝ => ε + (1 - 2 * ε) * r) 0 := by
      fun_prop
    simpa [re] using hcont.tendsto.comp hε_tendsto
  have hq :
      Filter.Tendsto (fun ε : ℝ => re ε * (1 - pe ε)) l
        (𝓝 (r * (1 - p))) :=
    hre.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hpe)
  have hleft_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => supportPowerTrace (pe ε) (re ε * (1 - pe ε)) At Bt X)
        l
        (𝓝 (supportPowerTrace p (r * (1 - p)) At Bt X)) :=
    supportPowerTrace_tendsto_exponents_nonneg hpe hq hAt_nonneg hBt_nonneg
  have hA1_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A1 B1 X)
        l
        (𝓝 (supportPowerTrace p (r * (1 - p)) A1 B1 X)) :=
    supportPowerTrace_tendsto_exponents_nonneg hpe hq hA1 hB1
  have hA2_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A2 B2 X)
        l
        (𝓝 (supportPowerTrace p (r * (1 - p)) A2 B2 X)) :=
    supportPowerTrace_tendsto_exponents_nonneg hpe hq hA2 hB2
  have hright_tendsto :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A1 B1 X +
            (1 - t) * supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A2 B2 X)
        l
        (𝓝 (t * supportPowerTrace p (r * (1 - p)) A1 B1 X +
          (1 - t) * supportPowerTrace p (r * (1 - p)) A2 B2 X)) :=
    (tendsto_const_nhds.mul hA1_tendsto).add
      (tendsto_const_nhds.mul hA2_tendsto)
  have hEventually :
      ∀ᶠ ε in l,
        t * supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A1 B1 X +
          (1 - t) * supportPowerTrace (pe ε) (re ε * (1 - pe ε)) A2 B2 X ≤
            supportPowerTrace (pe ε) (re ε * (1 - pe ε)) At Bt X := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact supportPowerTrace_scaled_jointlyConcave_Ioo
      (unit_interval_affine_Ioo hp hε)
      (unit_interval_affine_Ioo hr hε) ht hA1 hA2 hB1 hB2
  simpa [At, Bt] using le_of_tendsto_of_tendsto
    hright_tendsto hleft_tendsto hEventually

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
