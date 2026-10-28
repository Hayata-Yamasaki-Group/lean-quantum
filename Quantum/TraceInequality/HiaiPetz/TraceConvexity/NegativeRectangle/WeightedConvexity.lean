/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.TraceConvexity.NegativeRectangle.MidpointKernel

/-!
Weighted convexity on the negative rectangle, obtained from the midpoint kernel.
-/

namespace HiaiPetz

namespace TraceConvexity

open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem continuousOn_midpointConvex_le_endpoints_Icc {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hmid :
      ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        g ((s + t) / 2) ≤ (g s + g t) / 2) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
      g t ≤ (1 - t) * g 0 + t * g 1 := by
  let h : ℝ → ℝ := fun u => g u - ((1 - u) * g 0 + u * g 1)
  have hcont : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
    have hlin : Continuous fun u : ℝ => (1 - u) * g 0 + u * g 1 := by
      fun_prop
    exact hgcont.sub hlin.continuousOn
  have hmid_h :
      ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        h ((s + t) / 2) ≤ (h s + h t) / 2 := by
    intro s t hs ht
    have hgmid := hmid hs ht
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
  dsimp [h] at htnonpos
  linarith

/-- Source: Hiai, proof of Theorem 6.4. -/
@[fun_prop] private theorem continuous_leftMul {n : ℕ} :
    Continuous (fun A : Mₙ n => leftMul A) := by
  let L : Mₙ n →ₗ[ℂ] HSOp n :=
    { toFun := fun A => leftMul A
      map_add' := by
        intro A B
        ext X i j
        simp [leftMul_apply]
      map_smul' := by
        intro z A
        ext X i j
        simp [leftMul_apply] }
  simpa [L] using LinearMap.continuous_of_finiteDimensional L

/-- Source: Hiai, proof of Theorem 6.4. -/
@[fun_prop] private theorem continuous_rightMul {n : ℕ} :
    Continuous (fun B : Mₙ n => rightMul B) := by
  let L : Mₙ n →ₗ[ℂ] HSOp n :=
    { toFun := fun B => rightMul B
      map_add' := by
        intro A B
        ext X i j
        simp [rightMul_apply]
      map_smul' := by
        intro z B
        ext X i j
        simp [rightMul_apply] }
  simpa [L] using LinearMap.continuous_of_finiteDimensional L

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_tendsto_of_tendsto_neg_posDef {n : ℕ}
    {p q : ℝ} (hp : p ≤ 0) (hq : q ≤ 0)
    {l : Filter ℝ} {Aε Bε : ℝ → Mₙ n} {A B X : Mₙ n}
    (hAlim : Filter.Tendsto Aε l (𝓝 A))
    (hBlim : Filter.Tendsto Bε l (𝓝 B))
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hAε : ∀ᶠ a in l, Matrix.PosDef (Aε a))
    (hBε : ∀ᶠ a in l, Matrix.PosDef (Bε a)) :
    Filter.Tendsto (fun a : ℝ => powerTrace p q (Aε a) (Bε a) X) l
      (𝓝 (powerTrace p q A B X)) := by
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  let Tε : ℝ → HSOp n :=
    fun a => leftMul (matrixPower (-p) (Aε a)) * rightMul (matrixPower (-q) (Bε a))
  let T : HSOp n := leftMul (matrixPower (-p) A) * rightMul (matrixPower (-q) B)
  have hApow :
      Filter.Tendsto (fun a : ℝ => matrixPower (-p) (Aε a)) l
        (𝓝 (matrixPower (-p) A)) := by
    exact matrixPower_tendsto_of_tendsto_nonneg (show 0 ≤ -p by linarith)
      hAlim (Matrix.PosDef.nonneg hA)
      (hAε.mono fun a ha => Matrix.PosDef.nonneg ha)
  have hBpow :
      Filter.Tendsto (fun a : ℝ => matrixPower (-q) (Bε a)) l
        (𝓝 (matrixPower (-q) B)) := by
    exact matrixPower_tendsto_of_tendsto_nonneg (show 0 ≤ -q by linarith)
      hBlim (Matrix.PosDef.nonneg hB)
      (hBε.mono fun a hb => Matrix.PosDef.nonneg hb)
  have hL :
      Filter.Tendsto (fun a : ℝ => leftMul (matrixPower (-p) (Aε a))) l
        (𝓝 (leftMul (matrixPower (-p) A))) :=
    continuous_leftMul.continuousAt.tendsto.comp hApow
  have hR :
      Filter.Tendsto (fun a : ℝ => rightMul (matrixPower (-q) (Bε a))) l
        (𝓝 (rightMul (matrixPower (-q) B))) :=
    continuous_rightMul.continuousAt.tendsto.comp hBpow
  have hT : Filter.Tendsto Tε l (𝓝 T) := by
    simpa [Tε, T] using hL.mul hR
  have hTunit : IsUnit T :=
    leftRightMul_matrixPower_product_isUnit (p := -p) (q := -q) hA hB
  have hInv :
      Filter.Tendsto (fun a : ℝ => Ring.inverse (Tε a)) l (𝓝 (Ring.inverse T)) := by
    rcases hTunit with ⟨u, hu⟩
    have hT' : Filter.Tendsto Tε l (𝓝 (u : HSOp n)) := by
      simpa [T, hu] using hT
    simpa [hu] using (NormedRing.inverse_continuousAt u).tendsto.comp hT'
  have hInvX :
      Filter.Tendsto (fun a : ℝ => Ring.inverse (Tε a) X) l (𝓝 (Ring.inverse T X)) :=
    (ContinuousLinearMap.apply ℂ (Mₙ n) X).continuous.continuousAt.tendsto.comp hInv
  have hqform :
      Filter.Tendsto
        (fun a : ℝ => (Matrix.conjTranspose X * (Ring.inverse (Tε a) X)).trace.re)
        l
        (𝓝 ((Matrix.conjTranspose X * (Ring.inverse T X)).trace.re)) := by
    have hprod :
        Filter.Tendsto
          (fun a : ℝ => Matrix.conjTranspose X * (Ring.inverse (Tε a) X))
          l
          (𝓝 (Matrix.conjTranspose X * (Ring.inverse T X))) :=
      tendsto_const_nhds.mul hInvX
    have htrace :
        Filter.Tendsto
          (fun a : ℝ => Matrix.trace (Matrix.conjTranspose X * (Ring.inverse (Tε a) X)))
          l
          (𝓝 (Matrix.trace (Matrix.conjTranspose X * (Ring.inverse T X)))) := by
      have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
        dsimp [Matrix.trace]
        fun_prop
      exact hcont.continuousAt.tendsto.comp hprod
    exact Complex.continuous_re.continuousAt.tendsto.comp htrace
  have hTarget :
      (Matrix.conjTranspose X * (Ring.inverse T X)).trace.re = powerTrace p q A B X := by
    dsimp [T]
    rw [ringInverse_leftRightMul_matrixPower_product (r := -p) (s := -q) hA hB]
    simpa using
      leftRightMul_matrixPower_product_qform_eq_powerTrace
        (p := p) (q := q) (A := A) (B := B) (X := X)
  have hEq :
      ∀ᶠ a in l,
        (Matrix.conjTranspose X * (Ring.inverse (Tε a) X)).trace.re =
          powerTrace p q (Aε a) (Bε a) X := by
    filter_upwards [hAε, hBε] with a hAa hBa
    dsimp [Tε]
    rw [ringInverse_leftRightMul_matrixPower_product (r := -p) (s := -q) hAa hBa]
    simpa using
      leftRightMul_matrixPower_product_qform_eq_powerTrace
        (p := p) (q := q) (A := Aε a) (B := Bε a) (X := X)
  have hqform' :
      Filter.Tendsto
        (fun a : ℝ => (Matrix.conjTranspose X * (Ring.inverse (Tε a) X)).trace.re)
        l
        (𝓝 (powerTrace p q A B X)) := by
    simpa [hTarget] using hqform
  exact hqform'.congr' hEq

/-- Source: Hiai, proof of Theorem 6.4. -/
@[fun_prop] private theorem powerTrace_continuousOn_segment_negRectangle {n : ℕ}
    {p q : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0) (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn
      (fun t : ℝ =>
        powerTrace p q (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X)
      (Set.Icc (0 : ℝ) 1) := by
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : NormedSpace ℝ (Mₙ n) := NormedSpace.restrictScalars ℝ ℂ (Mₙ n)
  intro t ht
  have hAcont : Continuous fun u : ℝ => u • A₁ + (1 - u) • A₂ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [add_apply, smul_apply, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    fun_prop
  have hBcont : Continuous fun u : ℝ => u • B₁ + (1 - u) • B₂ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [add_apply, smul_apply, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    fun_prop
  refine powerTrace_tendsto_of_tendsto_neg_posDef hp.2 hq.2
    (Aε := fun u : ℝ => u • A₁ + (1 - u) • A₂)
    (Bε := fun u : ℝ => u • B₁ + (1 - u) • B₂)
    (tendsto_nhdsWithin_of_tendsto_nhds hAcont.continuousAt.tendsto)
    (tendsto_nhdsWithin_of_tendsto_nhds hBcont.continuousAt.tendsto)
    (matrixPosDef_convex_combo ht hA₁ hA₂)
    (matrixPosDef_convex_combo ht hB₁ hB₂) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact matrixPosDef_convex_combo hu hA₁ hA₂
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact matrixPosDef_convex_combo hu hB₁ hB₂

/-- Source: Hiai, Theorem 6.4. -/
private theorem powerTrace_jointlyConvex_negRectangle_core {n : ℕ}
    {p q : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0) (hq : q ∈ Set.Icc (-1 : ℝ) 0)
    {A₁ A₂ B₁ B₂ X : Mₙ n} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    powerTrace p q (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X ≤
      t * powerTrace p q A₁ B₁ X + (1 - t) * powerTrace p q A₂ B₂ X := by
  -- Danger note: the previous proof funnelled every step through `simp [g, As, ...]`
  -- on `let`-bound abbreviations, so the default simp set re-traversed the heavy
  -- `powerTrace`/`matrixPower` terms at each call (isDefEq timeout at 200k, budget
  -- 800k). All conversions below are pure beta/zeta (`exact`/`show`/`rw`), which
  -- never unfold `powerTrace`.
  let g : ℝ → ℝ := fun u =>
    powerTrace p q (u • A₁ + (1 - u) • A₂) (u • B₁ + (1 - u) • B₂) X
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    powerTrace_continuousOn_segment_negRectangle
      (p := p) (q := q) hp hq (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      (X := X) hA₁ hA₂ hB₁ hB₂
  have hmid :
      ∀ {s u : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → u ∈ Set.Icc (0 : ℝ) 1 →
        g ((s + u) / 2) ≤ (g s + g u) / 2 := by
    intro s u hs hu
    have hAs : Matrix.PosDef (s • A₁ + (1 - s) • A₂) := matrixPosDef_convex_combo hs hA₁ hA₂
    have hAu : Matrix.PosDef (u • A₁ + (1 - u) • A₂) := matrixPosDef_convex_combo hu hA₁ hA₂
    have hBs : Matrix.PosDef (s • B₁ + (1 - s) • B₂) := matrixPosDef_convex_combo hs hB₁ hB₂
    have hBu : Matrix.PosDef (u • B₁ + (1 - u) • B₂) := matrixPosDef_convex_combo hu hB₁ hB₂
    have hmp :=
      powerTrace_midpointConvex_negRectangle
        (n := n) (p := p) (q := q) (X := X) hp hq hAs hAu hBs hBu
    have hAeq :
        ((2 : ℂ)⁻¹) • ((s • A₁ + (1 - s) • A₂) + (u • A₁ + (1 - u) • A₂)) =
          ((s + u) / 2) • A₁ + (1 - (s + u) / 2) • A₂ := by
      ext i j
      simp
      ring
    have hBeq :
        ((2 : ℂ)⁻¹) • ((s • B₁ + (1 - s) • B₂) + (u • B₁ + (1 - u) • B₂)) =
          ((s + u) / 2) • B₁ + (1 - (s + u) / 2) • B₂ := by
      ext i j
      simp
      ring
    rw [hAeq, hBeq] at hmp
    exact hmp
  have hle := continuousOn_midpointConvex_le_endpoints_Icc hgcont hmid ht
  have hg0 : g 0 = powerTrace p q A₂ B₂ X := by
    have hA : (0 : ℝ) • A₁ + (1 - (0 : ℝ)) • A₂ = A₂ := by
      ext i j
      simp
    have hB : (0 : ℝ) • B₁ + (1 - (0 : ℝ)) • B₂ = B₂ := by
      ext i j
      simp
    change powerTrace p q ((0 : ℝ) • A₁ + (1 - (0 : ℝ)) • A₂)
        ((0 : ℝ) • B₁ + (1 - (0 : ℝ)) • B₂) X = powerTrace p q A₂ B₂ X
    rw [hA, hB]
  have hg1 : g 1 = powerTrace p q A₁ B₁ X := by
    have hA : (1 : ℝ) • A₁ + (1 - (1 : ℝ)) • A₂ = A₁ := by
      ext i j
      simp
    have hB : (1 : ℝ) • B₁ + (1 - (1 : ℝ)) • B₂ = B₁ := by
      ext i j
      simp
    change powerTrace p q ((1 : ℝ) • A₁ + (1 - (1 : ℝ)) • A₂)
        ((1 : ℝ) • B₁ + (1 - (1 : ℝ)) • B₂) X = powerTrace p q A₁ B₁ X
    rw [hA, hB]
  have hgt : g t =
      powerTrace p q (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X := rfl
  rw [hg0, hg1, hgt] at hle
  linarith

/-- Source: Hiai, Theorem 6.4. -/
theorem powerTrace_jointlyConvex_negRectangle :
    ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (-1 : ℝ) 0 →
      q ∈ Set.Icc (-1 : ℝ) 0 →
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
  exact powerTrace_jointlyConvex_negRectangle_core hp hq ht hA₁ hA₂ hB₁ hB₂

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
