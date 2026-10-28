/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.TraceConvexity.ThreeVariableConvexity
import Quantum.TraceInequality.HiaiPetz.TraceConvexity.NegativeRectangle
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Ando joint convexity of the trace-power functional

Joint convexity of the trace-power functional `powerTrace p q A B X` in the
positive-definite regime, following Hiai–Petz Theorem 6.4.  The interior Lieb
range `p ∈ [1, 2]` is handled through the two-block-diagonal representation and a
homogeneity/scaling argument, and the negative-exponent rectangle and outer
regions are combined into the full `AndoConvexity` predicate.

## Main results

* `liebTracePower_jointlyConvex_posIcc` /
  `liebTracePower_scaled_jointlyConvex_posIcc`: joint convexity of
  `liebTracePower p` for `p ∈ [1, 2]`.
* `powerTrace_jointlyConvex_posNegOuter` /
  `powerTrace_jointlyConvex_negPosOuter`: convexity on the outer exponent
  regions.
* `AndoConvexity`: the full joint-convexity predicate over the admissible
  exponent range.
* `andoConvexity`: proof of `AndoConvexity`.
* `liebAndoConvexity`: the combined Lieb concavity, three-variable convexity, and
  Ando convexity package.

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

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem inAdjointMultiplicativeDomain_blockSumMap {n : ℕ} (X : Mₙ n) :
    TraceMonotonicity.InAdjointMultiplicativeDomain (blockSumMap n) X := by
  constructor
  · simp [twoBlockDiag_mul]
  · simp [twoBlockDiag_mul]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem liebTracePower_homogeneous {n : ℕ} {p r : ℝ}
    {A B X : Mₙ n} (hr : 0 < r) (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    liebTracePower p (r • A) (r • B) X =
      r * liebTracePower p A B X := by
  have hAs : Matrix.PosDef (r • A) := matrixPosDef_smul hA hr
  have hBs : Matrix.PosDef (r • B) := matrixPosDef_smul hB hr
  rw [← jPowerTrace_eq_liebTracePower_of_posDef (p := p) hAs hBs,
    ← jPowerTrace_eq_liebTracePower_of_posDef (p := p) hA hB]
  rw [← quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := r • A) (B := r • B)
      (X := X) hBs,
    ← quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := A) (B := B)
      (X := X) hB]
  exact quasiEntropy_homogeneous (f := powerFn p) (A := A) (B := B) (X := X) hr

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem liebTracePower_twoBlockDiag {n : ℕ} {p : ℝ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    liebTracePower p (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
        (twoBlockDiag X₁ X₂) =
      liebTracePower p A₁ B₁ X₁ + liebTracePower p A₂ B₂ X₂ := by
  rw [liebTracePower, liebTracePower, liebTracePower, powerTrace, powerTrace, powerTrace]
  rw [matrixPower_twoBlockDiag_posDef (r := p) hA₁ hA₂,
    matrixPower_twoBlockDiag_posDef (r := 1 - p) hB₁ hB₂,
    conjTranspose_twoBlockDiag]
  rw [twoBlockDiag_mul, twoBlockDiag_mul, twoBlockDiag_mul]
  rw [trace_twoBlockDiag]
  simp [Complex.add_re]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem liebTracePower_twoBlockDiag_weighted {n : ℕ} {p t : ℝ}
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    liebTracePower p (twoBlockDiag (t • A₁) ((1 - t) • A₂))
        (twoBlockDiag (t • B₁) ((1 - t) • B₂)) (twoBlockDiag X X) =
      t * liebTracePower p A₁ B₁ X + (1 - t) * liebTracePower p A₂ B₂ X := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  rw [liebTracePower_twoBlockDiag
    (hA₁ := matrixPosDef_smul hA₁ ht0) (hA₂ := matrixPosDef_smul hA₂ h1t)
    (hB₁ := matrixPosDef_smul hB₁ ht0) (hB₂ := matrixPosDef_smul hB₂ h1t)]
  rw [liebTracePower_homogeneous (p := p) (r := t) ht0 hA₁ hB₁,
    liebTracePower_homogeneous (p := p) (r := 1 - t) h1t hA₂ hB₂]

/-- Source: Hiai, Theorem 6.4. -/
private theorem powerTrace_p_one_sub_p_jointlyConvex_posIcc :
    ∀ {n : ℕ} {p : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (1 : ℝ) 2 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p (1 - p) (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * powerTrace p (1 - p) A₁ B₁ X +
            (1 - t) * powerTrace p (1 - p) A₂ B₂ X := by
  intro n p X hp A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  by_cases htzero : t = 0
  · subst t
    have hA : (0 : ℝ) • A₁ + (1 : ℝ) • A₂ = A₂ := by
      ext i j
      simp
    have hB : (0 : ℝ) • B₁ + (1 : ℝ) • B₂ = B₂ := by
      ext i j
      simp
    simp only [sub_zero]
    rw [hA, hB, zero_mul, one_mul, zero_add]
  by_cases htone : t = 1
  · subst t
    have hA : (1 : ℝ) • A₁ + (0 : ℝ) • A₂ = A₁ := by
      ext i j
      simp
    have hB : (1 : ℝ) • B₁ + (0 : ℝ) • B₂ = B₁ := by
      ext i j
      simp
    simp only [sub_self]
    rw [hA, hB, zero_mul, one_mul, add_zero]
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htone
  let Ablock : Mₙ (2 * n) := twoBlockDiag (t • A₁) ((1 - t) • A₂)
  let Bblock : Mₙ (2 * n) := twoBlockDiag (t • B₁) ((1 - t) • B₂)
  have hAblock : Matrix.PosDef Ablock := by
    dsimp [Ablock]
    exact twoBlockDiag_posDef (matrixPosDef_smul hA₁ ht0)
      (matrixPosDef_smul hA₂ (sub_pos.mpr ht1))
  have hBblock : Matrix.PosDef Bblock := by
    dsimp [Bblock]
    exact twoBlockDiag_posDef (matrixPosDef_smul hB₁ ht0)
      (matrixPosDef_smul hB₂ (sub_pos.mpr ht1))
  have hAsum : blockSumMap n Ablock = t • A₁ + (1 - t) • A₂ := blockSumMap_twoBlockDiag _ _
  have hBsum : blockSumMap n Bblock = t • B₁ + (1 - t) • B₂ := blockSumMap_twoBlockDiag _ _
  have hAt : Matrix.PosDef (blockSumMap n Ablock) := by
    rw [hAsum]
    exact matrixPosDef_convex_combo ht hA₁ hA₂
  have hBt : Matrix.PosDef (blockSumMap n Bblock) := by
    rw [hBsum]
    exact matrixPosDef_convex_combo ht hB₁ hB₂
  have hmain :=
    TraceMonotonicity.liebTracePower_map_le_strictlyPositive_posIcc (blockSumMap n)
      (p := p) (A := Ablock) (B := Bblock) (X := X)
      hp (blockSumMap_positive n) (blockSumMap_tracePreserving n)
      (blockSumMap_hsAdjointSchwarz n)
      hAblock hBblock (blockSumMap_one_posDef n) hBt
      (inAdjointMultiplicativeDomain_blockSumMap X)
  have hsplit :
      liebTracePower p Ablock Bblock (twoBlockDiag X X) =
        t * liebTracePower p A₁ B₁ X + (1 - t) * liebTracePower p A₂ B₂ X := by
    dsimp [Ablock, Bblock]
    exact liebTracePower_twoBlockDiag_weighted
      (p := p) ht0 ht1 hA₁ hA₂ hB₁ hB₂
  rw [hAsum, hBsum, blockDiagMap_apply] at hmain
  dsimp [liebTracePower] at hmain hsplit
  calc
    powerTrace p (1 - p) (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) X
        ≤ powerTrace p (1 - p) Ablock Bblock (twoBlockDiag X X) := hmain
    _ = t * powerTrace p (1 - p) A₁ B₁ X +
        (1 - t) * powerTrace p (1 - p) A₂ B₂ X := hsplit

/-- Source: Hiai, Theorem 6.4.

`liebTracePower p` is represented internally as `powerTrace p (1 - p)`. -/
theorem liebTracePower_jointlyConvex_posIcc :
    ∀ {n : ℕ} {p : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (1 : ℝ) 2 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        liebTracePower p (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * liebTracePower p A₁ B₁ X +
            (1 - t) * liebTracePower p A₂ B₂ X := by
  intro n p X hp A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  simpa [liebTracePower] using
    (powerTrace_p_one_sub_p_jointlyConvex_posIcc
      (p := p) (X := X) hp (t := t) ht hA₁ hA₂ hB₁ hB₂)

/-- Source: Hiai, Theorem 6.4. -/
private theorem liebTracePower_scaled_jointlyConvex_posIoo_core {n : ℕ} {p r : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    {A₁ A₂ B₁ B₂ X : Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    powerTrace p (r * (1 - p)) (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) X ≤
      t * powerTrace p (r * (1 - p)) A₁ B₁ X +
        (1 - t) * powerTrace p (r * (1 - p)) A₂ B₂ X := by
  let At : Mₙ n := t • A₁ + (1 - t) • A₂
  let Bt : Mₙ n := t • B₁ + (1 - t) • B₂
  let C₁ : Mₙ n := matrixPower r B₁
  let C₂ : Mₙ n := matrixPower r B₂
  let Ct : Mₙ n := t • C₁ + (1 - t) • C₂
  have hpIcc : p ∈ Set.Icc (1 : ℝ) 2 := ⟨hp.1.le, hp.2.le⟩
  have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hsIcc : 1 - p ∈ Set.Icc (-1 : ℝ) 0 := by
    constructor <;> linarith [hp.1.le, hp.2.le]
  have hAt_pos : Matrix.PosDef At := matrixPosDef_convex_combo ht hA₁ hA₂
  have hBt_pos : Matrix.PosDef Bt := matrixPosDef_convex_combo ht hB₁ hB₂
  have hC₁_pos : Matrix.PosDef C₁ := matrixPower_posDef_of_posDef (r := r) hB₁
  have hC₂_pos : Matrix.PosDef C₂ := matrixPower_posDef_of_posDef (r := r) hB₂
  have hCt_pos : Matrix.PosDef Ct := matrixPosDef_convex_combo ht hC₁_pos hC₂_pos
  have hBr_pos : Matrix.PosDef (matrixPower r Bt) :=
    matrixPower_posDef_of_posDef (r := r) hBt_pos
  have hCt_le : Ct ≤ matrixPower r Bt :=
    matrixPower_concave_nonneg hrIcc ht
      (Matrix.PosDef.nonneg hB₁) (Matrix.PosDef.nonneg hB₂)
  have hpow_le :
      matrixPower (1 - p) (matrixPower r Bt) ≤ matrixPower (1 - p) Ct :=
    matrixPower_antitone_neg_Icc_posDef hsIcc hCt_pos hBr_pos hCt_le
  have hleft_le :
      powerTrace p (r * (1 - p)) At Bt X ≤
        powerTrace p (1 - p) At Ct X := by
    have hmono :=
      powerTrace_le_of_right_power_le_posDef
        (r := p) (s := 1 - p) (A := At) (B1 := matrixPower r Bt)
        (B2 := Ct) (X := X) hAt_pos hpow_le
    have hcomp :=
      powerTrace_right_comp_posDef (a := p) (r := r) (s := 1 - p)
        (A := At) (B := Bt) (X := X) hBt_pos
    rw [← hcomp]
    exact hmono
  have hboundary :=
    liebTracePower_jointlyConvex_posIcc (p := p) (X := X) hpIcc (t := t) ht
      hA₁ hA₂ hC₁_pos hC₂_pos
  have hC₁_comp :=
    powerTrace_right_comp_posDef (a := p) (r := r) (s := 1 - p)
      (A := A₁) (B := B₁) (X := X) hB₁
  have hC₂_comp :=
    powerTrace_right_comp_posDef (a := p) (r := r) (s := 1 - p)
      (A := A₂) (B := B₂) (X := X) hB₂
  have hboundary' :
      powerTrace p (1 - p) At Ct X ≤
        t * powerTrace p (r * (1 - p)) A₁ B₁ X +
          (1 - t) * powerTrace p (r * (1 - p)) A₂ B₂ X := by
    rw [← hC₁_comp, ← hC₂_comp]
    exact hboundary
  exact le_trans hleft_le hboundary'

/-- Source: Hiai, Theorem 6.4. -/
theorem liebTracePower_scaled_jointlyConvex_posIoo :
    ∀ {n : ℕ} {p r : ℝ} {X : Mₙ n},
      p ∈ Set.Ioo (1 : ℝ) 2 →
      r ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p (r * (1 - p)) (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * powerTrace p (r * (1 - p)) A₁ B₁ X +
            (1 - t) * powerTrace p (r * (1 - p)) A₂ B₂ X := by
  intro n p r X hp hr A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  exact liebTracePower_scaled_jointlyConvex_posIoo_core hp hr ht hA₁ hA₂ hB₁ hB₂

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma one_two_interval_affine_Ioo {p ε : ℝ}
    (hp : p ∈ Set.Icc (1 : ℝ) 2) (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    1 + ε + (1 - 2 * ε) * (p - 1) ∈ Set.Ioo (1 : ℝ) 2 := by
  have hcoef_nonneg : 0 ≤ 1 - 2 * ε := by
    nlinarith [hε.2]
  constructor
  · have hterm_nonneg : 0 ≤ (1 - 2 * ε) * (p - 1) :=
      mul_nonneg hcoef_nonneg (by linarith [hp.1])
    nlinarith [hε.1, hterm_nonneg]
  · have hle : (1 - 2 * ε) * (p - 1) ≤ (1 - 2 * ε) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith [hp.2]) hcoef_nonneg
    nlinarith [hε.1, hε.2, hle]

/-- Source: Hiai, Theorem 6.4. -/
theorem liebTracePower_scaled_jointlyConvex_posIcc :
    ∀ {n : ℕ} {p r : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (1 : ℝ) 2 →
      r ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p (r * (1 - p)) (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * powerTrace p (r * (1 - p)) A₁ B₁ X +
            (1 - t) * powerTrace p (r * (1 - p)) A₂ B₂ X := by
  intro n p r X hp hr A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  let l : Filter ℝ := 𝓝[Set.Ioo (0 : ℝ) (1 / 2)] 0
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    exact ⟨le_rfl, by norm_num⟩
  let pe : ℝ → ℝ := fun ε => 1 + ε + (1 - 2 * ε) * (p - 1)
  let re : ℝ → ℝ := fun ε => ε + (1 - 2 * ε) * r
  let At : Mₙ n := t • A₁ + (1 - t) • A₂
  let Bt : Mₙ n := t • B₁ + (1 - t) • B₂
  have hAt_pos : Matrix.PosDef At := by
    simpa [At] using matrixPosDef_convex_combo ht hA₁ hA₂
  have hBt_pos : Matrix.PosDef Bt := by
    simpa [Bt] using matrixPosDef_convex_combo ht hB₁ hB₂
  have hε_tendsto : Filter.Tendsto (fun ε : ℝ => ε) l (𝓝 (0 : ℝ)) :=
    nhdsWithin_le_nhds
  have hpe : Filter.Tendsto pe l (𝓝 p) := by
    have hcont :
        ContinuousAt (fun ε : ℝ => 1 + ε + (1 - 2 * ε) * (p - 1)) 0 := by
      fun_prop
    simpa [pe] using hcont.tendsto.comp hε_tendsto
  have hre : Filter.Tendsto re l (𝓝 r) := by
    have hcont :
        ContinuousAt (fun ε : ℝ => ε + (1 - 2 * ε) * r) 0 := by
      fun_prop
    simpa [re] using hcont.tendsto.comp hε_tendsto
  have hrightExp :
      Filter.Tendsto (fun ε : ℝ => re ε * (1 - pe ε)) l
        (𝓝 (r * (1 - p))) :=
    hre.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hpe)
  have hleft_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (pe ε) (re ε * (1 - pe ε)) At Bt X)
        l
        (𝓝 (powerTrace p (r * (1 - p)) At Bt X)) :=
    powerTrace_tendsto_exponents_posDef hAt_pos hBt_pos hpe hrightExp
  have hA₁_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (pe ε) (re ε * (1 - pe ε)) A₁ B₁ X)
        l
        (𝓝 (powerTrace p (r * (1 - p)) A₁ B₁ X)) :=
    powerTrace_tendsto_exponents_posDef hA₁ hB₁ hpe hrightExp
  have hA₂_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (pe ε) (re ε * (1 - pe ε)) A₂ B₂ X)
        l
        (𝓝 (powerTrace p (r * (1 - p)) A₂ B₂ X)) :=
    powerTrace_tendsto_exponents_posDef hA₂ hB₂ hpe hrightExp
  have hright_tendsto :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * powerTrace (pe ε) (re ε * (1 - pe ε)) A₁ B₁ X +
            (1 - t) * powerTrace (pe ε) (re ε * (1 - pe ε)) A₂ B₂ X)
        l
        (𝓝 (t * powerTrace p (r * (1 - p)) A₁ B₁ X +
          (1 - t) * powerTrace p (r * (1 - p)) A₂ B₂ X)) :=
    (tendsto_const_nhds.mul hA₁_tendsto).add
      (tendsto_const_nhds.mul hA₂_tendsto)
  have hEventually :
      ∀ᶠ ε in l,
        powerTrace (pe ε) (re ε * (1 - pe ε)) At Bt X ≤
          t * powerTrace (pe ε) (re ε * (1 - pe ε)) A₁ B₁ X +
            (1 - t) * powerTrace (pe ε) (re ε * (1 - pe ε)) A₂ B₂ X := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact liebTracePower_scaled_jointlyConvex_posIoo
      (one_two_interval_affine_Ioo hp hε)
      (unit_interval_affine_Ioo hr hε) ht hA₁ hA₂ hB₁ hB₂
  simpa [At, Bt] using le_of_tendsto_of_tendsto
    hleft_tendsto hright_tendsto hEventually

/-- Source: Hiai, Theorem 6.4. -/
theorem powerTrace_jointlyConvex_posNegOuter :
    ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      q ∈ Set.Icc (-1 : ℝ) 0 →
      p ∈ Set.Icc (1 - q) 2 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p q (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * powerTrace p q A₁ B₁ X +
            (1 - t) * powerTrace p q A₂ B₂ X := by
  intro n p q X hq hp A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  by_cases hp_one : p = 1
  · subst p
    have hq_zero : q = 0 := by
      nlinarith [hq.1, hq.2, hp.1]
    subst q
    have hscaled :=
      liebTracePower_scaled_jointlyConvex_posIcc (p := (1 : ℝ)) (r := (0 : ℝ)) (X := X)
        ⟨le_rfl, by norm_num⟩ ⟨le_rfl, zero_le_one⟩ ht hA₁ hA₂ hB₁ hB₂
    simpa using hscaled
  · have hp_ge_one : 1 ≤ p := by
      linarith [hp.1, hq.2]
    have hp_gt_one : 1 < p := lt_of_le_of_ne hp_ge_one (Ne.symm hp_one)
    have hpIcc : p ∈ Set.Icc (1 : ℝ) 2 := ⟨hp_ge_one, hp.2⟩
    have hden_neg : 1 - p < 0 := sub_neg.mpr hp_gt_one
    have hden_pos : 0 < p - 1 := sub_pos.mpr hp_gt_one
    let r : ℝ := q / (1 - p)
    have hq_ge : 1 - p ≤ q := by
      linarith [hp.1]
    have hr_alt : r = (-q) / (p - 1) := by
      dsimp [r]
      calc
        q / (1 - p) = q / (-(p - 1)) := by
          rw [show 1 - p = -(p - 1) by ring]
        _ = -(q / (p - 1)) := by
          rw [div_neg]
        _ = (-q) / (p - 1) := by
          rw [neg_div]
    have hr_nonneg : 0 ≤ r := by
      rw [hr_alt]
      exact div_nonneg (by linarith [hq.2]) hden_pos.le
    have hr_le_one : r ≤ 1 := by
      rw [hr_alt]
      have hnum_le : -q ≤ p - 1 := by
        linarith [hq_ge]
      have hmul : (-q) / (p - 1) * (p - 1) ≤ 1 * (p - 1) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hden_pos)]
        simpa using hnum_le
      exact le_of_mul_le_mul_right hmul hden_pos
    have hq_eq : q = r * (1 - p) := by
      dsimp [r]
      rw [div_mul_cancel₀ q (ne_of_lt hden_neg)]
    have hscaled :=
      liebTracePower_scaled_jointlyConvex_posIcc (p := p) (r := r) (X := X)
        hpIcc ⟨hr_nonneg, hr_le_one⟩ ht hA₁ hA₂ hB₁ hB₂
    simpa [hq_eq] using hscaled

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_conjTranspose_swap {n : ℕ} (p q : ℝ) (A B X : Mₙ n) :
    powerTrace p q A B X =
      powerTrace q p B A (Matrix.conjTranspose X) := by
  rw [powerTrace, powerTrace]
  simp only [Matrix.conjTranspose_conjTranspose]
  congr 1
  calc
    Matrix.trace (Matrix.conjTranspose X * matrixPower p A * X * matrixPower q B)
        = Matrix.trace (matrixPower p A * X * matrixPower q B *
            Matrix.conjTranspose X) := by
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_comm (Matrix.conjTranspose X)
              (matrixPower p A * X * matrixPower q B)
    _ = Matrix.trace (X * matrixPower q B * Matrix.conjTranspose X *
          matrixPower p A) := by
        simpa [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (matrixPower p A)
            (X * matrixPower q B * Matrix.conjTranspose X)

/-- Source: Hiai, Theorem 6.4. -/
theorem powerTrace_jointlyConvex_negPosOuter :
    ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (-1 : ℝ) 0 →
      q ∈ Set.Icc (1 - p) 2 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p q (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) X ≤
          t * powerTrace p q A₁ B₁ X +
            (1 - t) * powerTrace p q A₂ B₂ X := by
  intro n p q X hp hq A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  have hswapped :=
    powerTrace_jointlyConvex_posNegOuter (n := n) (p := q) (q := p)
      (X := Matrix.conjTranspose X) hp hq (A₁ := B₁) (A₂ := B₂)
      (B₁ := A₁) (B₂ := A₂) (t := t) ht hB₁ hB₂ hA₁ hA₂
  rw [powerTrace_conjTranspose_swap (p := p) (q := q)
      (A := t • A₁ + (1 - t) • A₂) (B := t • B₁ + (1 - t) • B₂) (X := X),
    powerTrace_conjTranspose_swap (p := p) (q := q)
      (A := A₁) (B := B₁) (X := X),
    powerTrace_conjTranspose_swap (p := p) (q := q)
      (A := A₂) (B := B₂) (X := X)]
  exact hswapped

/-- Source: Hiai, Theorem 6.4. -/
def AndoConvexity : Prop :=
  ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
    AndoConvexityRange p q →
    ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
      t ∈ Set.Icc (0 : ℝ) 1 →
      Matrix.PosDef A1 →
      Matrix.PosDef A2 →
      Matrix.PosDef B1 →
      Matrix.PosDef B2 →
      powerTrace p q (t • A1 + (1 - t) • A2)
          (t • B1 + (1 - t) • B2) X ≤
        t * powerTrace p q A1 B1 X +
          (1 - t) * powerTrace p q A2 B2 X

/-- Source: Hiai, Theorem 6.4. -/
theorem andoConvexity :
    AndoConvexity := by
  intro n p q X hpq A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact powerTrace_jointlyConvex_negRectangle hp hq ht hA1 hA2 hB1 hB2
  · exact powerTrace_jointlyConvex_negPosOuter hp hq ht hA1 hA2 hB1 hB2
  · exact powerTrace_jointlyConvex_posNegOuter hq hp ht hA1 hA2 hB1 hB2


/-- Source: Hiai, Theorem 6.4. -/
theorem liebAndoConvexity :
    LiebConcavity ∧ LiebThreeVariableConvexity ∧ AndoConvexity := by
  exact ⟨liebConcavity, liebThreeVariableConvexity, andoConvexity⟩

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
