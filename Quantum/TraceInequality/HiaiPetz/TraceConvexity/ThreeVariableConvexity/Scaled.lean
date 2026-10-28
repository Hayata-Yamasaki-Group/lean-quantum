/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceConvexity.ThreeVariableConvexity.Basic

/-!
# Three-variable convexity: scaled joint convexity

Scaled joint convexity of the power trace and the packaged three-variable convexity of
Hiai–Petz Theorem 6.4.

## Main results

* `inverseTracePower_scaled_jointlyConvex_Ioo` / `inverseTracePower_scaled_jointlyConvex`:
  joint convexity of `powerTrace (-p) (r * (p - 1))` for scaled exponents, on the open and
  closed unit intervals respectively.
* `LiebThreeVariableConvexity` / `liebThreeVariableConvexity`: the packaged three-variable
  convexity statement and its proof.

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

/-- Source: Hiai, Theorem 6.4. -/
private theorem inverseTracePower_scaled_jointlyConvex_Ioo_core {n : ℕ} {p r : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hA1 : Matrix.PosDef A1) (hA2 : Matrix.PosDef A2)
    (hB1 : Matrix.PosDef B1) (hB2 : Matrix.PosDef B2) :
    powerTrace (-p) (r * (p - 1)) (t • A1 + (1 - t) • A2)
        (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
      t * powerTrace (-p) (r * (p - 1)) A1 B1 X1 +
        (1 - t) * powerTrace (-p) (r * (p - 1)) A2 B2 X2 := by
  let At : Mₙ n := t • A1 + (1 - t) • A2
  let Bt : Mₙ n := t • B1 + (1 - t) • B2
  let C1 : Mₙ n := matrixPower r B1
  let C2 : Mₙ n := matrixPower r B2
  let Ct : Mₙ n := t • C1 + (1 - t) • C2
  let Xt : Mₙ n := t • X1 + (1 - t) • X2
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hsIcc : p - 1 ∈ Set.Icc (-1 : ℝ) 0 := by
    constructor <;> linarith [hp.1.le, hp.2.le]
  have hAt_pos : Matrix.PosDef At := matrixPosDef_convex_combo ht hA1 hA2
  have hBt_pos : Matrix.PosDef Bt := matrixPosDef_convex_combo ht hB1 hB2
  have hC1_pos : Matrix.PosDef C1 := matrixPower_posDef_of_posDef (r := r) hB1
  have hC2_pos : Matrix.PosDef C2 := matrixPower_posDef_of_posDef (r := r) hB2
  have hCt_pos : Matrix.PosDef Ct := matrixPosDef_convex_combo ht hC1_pos hC2_pos
  have hBr_pos : Matrix.PosDef (matrixPower r Bt) :=
    matrixPower_posDef_of_posDef (r := r) hBt_pos
  have hCt_le : Ct ≤ matrixPower r Bt :=
    matrixPower_concave_nonneg hrIcc ht
      (Matrix.PosDef.nonneg hB1) (Matrix.PosDef.nonneg hB2)
  have hpow_le :
      matrixPower (p - 1) (matrixPower r Bt) ≤ matrixPower (p - 1) Ct :=
    matrixPower_antitone_neg_Icc_posDef hsIcc hCt_pos hBr_pos hCt_le
  have hleft_le :
      powerTrace (-p) (r * (p - 1)) At Bt Xt ≤
        powerTrace (-p) (p - 1) At Ct Xt := by
    have hmono :=
      powerTrace_le_of_right_power_le_posDef
        (r := -p) (s := p - 1) (A := At) (B1 := matrixPower r Bt)
        (B2 := Ct) (X := Xt) hAt_pos hpow_le
    have hcomp :=
      powerTrace_right_comp_posDef (a := -p) (r := r) (s := p - 1)
        (A := At) (B := Bt) (X := Xt) hBt_pos
    rw [← hcomp]
    exact hmono
  have hboundary :=
    inverseTracePower_jointlyConvex (p := p) hpIcc (t := t) ht hA1 hA2 hC1_pos hC2_pos
      (X1 := X1) (X2 := X2)
  have hC1_comp :=
    powerTrace_right_comp_posDef (a := -p) (r := r) (s := p - 1)
      (A := A1) (B := B1) (X := X1) hB1
  have hC2_comp :=
    powerTrace_right_comp_posDef (a := -p) (r := r) (s := p - 1)
      (A := A2) (B := B2) (X := X2) hB2
  have hboundary' :
      powerTrace (-p) (p - 1) At Ct Xt ≤
        t * powerTrace (-p) (r * (p - 1)) A1 B1 X1 +
          (1 - t) * powerTrace (-p) (r * (p - 1)) A2 B2 X2 := by
    rw [← hC1_comp, ← hC2_comp]
    exact hboundary
  exact le_trans hleft_le hboundary'

/-- Source: Hiai, Theorem 6.4. -/
theorem inverseTracePower_scaled_jointlyConvex_Ioo :
    ∀ {n : ℕ} {p r : ℝ},
      p ∈ Set.Ioo (0 : ℝ) 1 →
      r ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        powerTrace (-p) (r * (p - 1)) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
          t * powerTrace (-p) (r * (p - 1)) A1 B1 X1 +
            (1 - t) * powerTrace (-p) (r * (p - 1)) A2 B2 X2 := by
  intro n p r hp hr A1 A2 B1 B2 X1 X2 t ht hA1 hA2 hB1 hB2
  exact inverseTracePower_scaled_jointlyConvex_Ioo_core hp hr ht hA1 hA2 hB1 hB2

/-- Source: Hiai, Theorem 6.4. -/
theorem inverseTracePower_scaled_jointlyConvex :
    ∀ {n : ℕ} {p r : ℝ},
      p ∈ Set.Icc (0 : ℝ) 1 →
      r ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        powerTrace (-p) (r * (p - 1)) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
          t * powerTrace (-p) (r * (p - 1)) A1 B1 X1 +
            (1 - t) * powerTrace (-p) (r * (p - 1)) A2 B2 X2 := by
  intro n p r hp hr A1 A2 B1 B2 X1 X2 t ht hA1 hA2 hB1 hB2
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
  let Xt : Mₙ n := t • X1 + (1 - t) • X2
  have hAt_pos : Matrix.PosDef At := by
    simpa [At] using matrixPosDef_convex_combo ht hA1 hA2
  have hBt_pos : Matrix.PosDef Bt := by
    simpa [Bt] using matrixPosDef_convex_combo ht hB1 hB2
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
  have hleftExp :
      Filter.Tendsto (fun ε : ℝ => -pe ε) l (𝓝 (-p)) :=
    hpe.neg
  have hrightExp :
      Filter.Tendsto (fun ε : ℝ => re ε * (pe ε - 1)) l
        (𝓝 (r * (p - 1))) :=
    hre.mul (hpe.sub tendsto_const_nhds)
  have hleft_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (-pe ε) (re ε * (pe ε - 1)) At Bt Xt)
        l
        (𝓝 (powerTrace (-p) (r * (p - 1)) At Bt Xt)) :=
    powerTrace_tendsto_exponents_posDef hAt_pos hBt_pos hleftExp hrightExp
  have hA1_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (-pe ε) (re ε * (pe ε - 1)) A1 B1 X1)
        l
        (𝓝 (powerTrace (-p) (r * (p - 1)) A1 B1 X1)) :=
    powerTrace_tendsto_exponents_posDef hA1 hB1 hleftExp hrightExp
  have hA2_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => powerTrace (-pe ε) (re ε * (pe ε - 1)) A2 B2 X2)
        l
        (𝓝 (powerTrace (-p) (r * (p - 1)) A2 B2 X2)) :=
    powerTrace_tendsto_exponents_posDef hA2 hB2 hleftExp hrightExp
  have hright_tendsto :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * powerTrace (-pe ε) (re ε * (pe ε - 1)) A1 B1 X1 +
            (1 - t) * powerTrace (-pe ε) (re ε * (pe ε - 1)) A2 B2 X2)
        l
        (𝓝 (t * powerTrace (-p) (r * (p - 1)) A1 B1 X1 +
          (1 - t) * powerTrace (-p) (r * (p - 1)) A2 B2 X2)) :=
    (tendsto_const_nhds.mul hA1_tendsto).add
      (tendsto_const_nhds.mul hA2_tendsto)
  have hEventually :
      ∀ᶠ ε in l,
        powerTrace (-pe ε) (re ε * (pe ε - 1)) At Bt Xt ≤
          t * powerTrace (-pe ε) (re ε * (pe ε - 1)) A1 B1 X1 +
            (1 - t) * powerTrace (-pe ε) (re ε * (pe ε - 1)) A2 B2 X2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact inverseTracePower_scaled_jointlyConvex_Ioo
      (unit_interval_affine_Ioo hp hε)
      (unit_interval_affine_Ioo hr hε) ht hA1 hA2 hB1 hB2
  simpa [At, Bt, Xt] using le_of_tendsto_of_tendsto
    hleft_tendsto hright_tendsto hEventually

/-- Source: Hiai, Theorem 6.4. -/
def LiebThreeVariableConvexity : Prop :=
  ∀ {n : ℕ} {p q : ℝ},
    0 ≤ p →
    0 ≤ q →
    p + q ≤ 1 →
    ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
      t ∈ Set.Icc (0 : ℝ) 1 →
      Matrix.PosDef A1 →
      Matrix.PosDef A2 →
      Matrix.PosDef B1 →
      Matrix.PosDef B2 →
      powerTrace (-p) (-q) (t • A1 + (1 - t) • A2)
          (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
        t * powerTrace (-p) (-q) A1 B1 X1 +
          (1 - t) * powerTrace (-p) (-q) A2 B2 X2

/-- Source: Hiai, Theorem 6.4. -/
theorem liebThreeVariableConvexity :
    LiebThreeVariableConvexity := by
  intro n p q hp_nonneg hq_nonneg hpq A1 A2 B1 B2 X1 X2 t ht hA1 hA2 hB1 hB2
  by_cases hp_one : p = 1
  · subst p
    have hq_zero : q = 0 := by
      nlinarith [hq_nonneg, hpq]
    subst q
    have hscaled :=
      inverseTracePower_scaled_jointlyConvex (p := (1 : ℝ)) (r := (0 : ℝ))
        ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ht hA1 hA2 hB1 hB2
        (X1 := X1) (X2 := X2)
    simpa using hscaled
  · have hp_lt_one : p < 1 := lt_of_le_of_ne (by linarith [hpq, hq_nonneg]) hp_one
    have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp_nonneg, hp_lt_one.le⟩
    have hden_pos : 0 < 1 - p := sub_pos.mpr hp_lt_one
    let r : ℝ := q / (1 - p)
    have hq_le : q ≤ 1 - p := by
      linarith
    have hr_nonneg : 0 ≤ r := by
      exact div_nonneg hq_nonneg hden_pos.le
    have hr_le_one : r ≤ 1 := by
      have hmul : r * (1 - p) ≤ 1 * (1 - p) := by
        dsimp [r]
        rw [div_mul_cancel₀ q (ne_of_gt hden_pos)]
        simpa using hq_le
      exact le_of_mul_le_mul_right hmul hden_pos
    have hq_eq : q = r * (1 - p) := by
      dsimp [r]
      rw [div_mul_cancel₀ q (ne_of_gt hden_pos)]
    have hq_neg : -q = r * (p - 1) := by
      rw [hq_eq]
      ring
    have hscaled :=
      inverseTracePower_scaled_jointlyConvex (p := p) (r := r)
        hpIcc ⟨hr_nonneg, hr_le_one⟩ ht hA1 hA2 hB1 hB2
        (X1 := X1) (X2 := X2)
    simpa [hq_neg] using hscaled

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
