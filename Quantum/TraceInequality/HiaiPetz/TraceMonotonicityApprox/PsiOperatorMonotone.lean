/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.ScalarApprox
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculusRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.BasicTheorems
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import
  Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.OrthogonalConjugation
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagProjection
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransportRetained
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule

/-!
# Operator monotonicity of the truncated integral `ψ_n`

Continuity, strict positivity, and all-Hilbert-space operator monotonicity of
the truncated integrals `psiApprox` on `(0, ∞)`, via the clipped
weighted-kernel integral representation; culminates in
`psiApprox_allHOperatorMonotone_Ioi` and `psiApprox_operatorMonotone`.
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology Interval
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- The positive weight multiplying the kernel in `ψ_n`.
Source: Hiai, proof of Theorem 6.3. -/
private noncomputable def psiWeight (p t : ℝ) : ℝ :=
  sinCoeff p * t ^ (p - 1)

/-- The weight in `ψ_n` is positive on the truncated interval for `1 < p < 2`.
Source: Hiai, proof of Theorem 6.3. -/
private theorem psiWeight_pos {p t : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (ht : 0 < t) :
    0 < psiWeight p t := by
  exact mul_pos (sinCoeff_pos hp) (Real.rpow_pos_of_pos ht (p - 1))

/-- Weighted-kernel form of the `ψ_n` integrand.
Source: Hiai, proof of Theorem 6.3. -/
private noncomputable def weightedKernel (p t : ℝ) : ℝ → ℝ :=
  fun x : ℝ => psiWeight p t * mobiusKernel t x

/-- The definition of `ψ_n` can be read as the interval integral of the weighted kernel.
Source: Hiai, proof of Theorem 6.3. -/
private theorem psiApprox_eq_integral_weightedKernel (p : ℝ) (k : ℕ) (x : ℝ) :
    psiApprox p k x =
      ∫ t in (cutoff k)⁻¹..cutoff k, weightedKernel p t x := by
  dsimp [psiApprox]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  dsimp [weightedKernel, psiWeight, mobiusKernel]
  ring_nf

/-- A globally continuous auxiliary integrand agreeing with the weighted kernel on
`x > 0` and `a ≤ t`.
Local API: Lean-side continuity device for Hiai, proof of Theorem 6.3. -/
private noncomputable def clippedWeightedKernel (p a : ℝ) : ℝ → ℝ → ℝ :=
  fun x t : ℝ =>
    sinCoeff p * (max t a) ^ (p - 1) *
      (max x 0 / (max x 0 + max t a))

@[fun_prop] private theorem clippedWeightedKernel_continuous {p a : ℝ} (ha : 0 < a) :
    Continuous (Function.uncurry (clippedWeightedKernel p a)) := by
  change Continuous fun q : ℝ × ℝ =>
    sinCoeff p * (max q.2 a) ^ (p - 1) *
      (max q.1 0 / (max q.1 0 + max q.2 a))
  have hx : Continuous fun q : ℝ × ℝ => max q.1 (0 : ℝ) :=
    continuous_fst.max continuous_const
  have ht : Continuous fun q : ℝ × ℝ => max q.2 a :=
    continuous_snd.max continuous_const
  have htpos : ∀ q : ℝ × ℝ, 0 < max q.2 a := by
    intro q
    exact ha.trans_le (le_max_right q.2 a)
  have hden : ∀ q : ℝ × ℝ, max q.1 (0 : ℝ) + max q.2 a ≠ 0 := by
    intro q
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right q.1 (0 : ℝ)) (htpos q))
  exact
    (continuous_const.mul
        (ht.rpow_const fun q => Or.inl (ne_of_gt (htpos q)))).mul
      (hx.div (hx.add ht) hden)

/-- The truncated function `ψ_n` is continuous on `(0,∞)` for `1 < p < 2`.
Source: Hiai, proof of Theorem 6.3. -/
@[fun_prop] theorem psiApprox_continuousOn_Ioi {p : ℝ} (_hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (k : ℕ) :
    ContinuousOn (psiApprox p k) (Set.Ioi (0 : ℝ)) := by
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hab : a ≤ b := by
    simpa [a, b] using cutoff_inv_le k
  have hcontAux :
      Continuous fun x : ℝ => ∫ t in a..b, clippedWeightedKernel p a x t := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun x t : ℝ => clippedWeightedKernel p a x t)
      (clippedWeightedKernel_continuous ha) a b
  refine hcontAux.continuousOn.congr ?_
  intro x hx
  rw [psiApprox_eq_integral_weightedKernel]
  symm
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have htIcc : t ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using ht
  have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx
  have ht_lower : a ≤ t := htIcc.1
  dsimp [clippedWeightedKernel, weightedKernel, psiWeight, mobiusKernel, a]
  rw [max_eq_left hx_nonneg, max_eq_left ht_lower]

@[fun_prop] private theorem weightedKernel_continuousOn_Icc {p a b x : ℝ} (ha : 0 < a)
    (hx_nonneg : 0 ≤ x) :
    ContinuousOn (fun t : ℝ => weightedKernel p t x) (Set.Icc a b) := by
  have hclip :
      Continuous fun t : ℝ => clippedWeightedKernel p a x t := by
    exact (clippedWeightedKernel_continuous (p := p) ha).comp
      (continuous_const.prodMk continuous_id)
  refine hclip.continuousOn.congr ?_
  intro t ht
  dsimp [clippedWeightedKernel, weightedKernel, psiWeight, mobiusKernel]
  rw [max_eq_left hx_nonneg, max_eq_left ht.1]

/-- The kernel `x ↦ x / (x + t)` is continuous on `(0,∞)` for `0 < t`.
Source: Hiai, proof of Theorem 6.3. -/
@[fun_prop] theorem mobiusKernel_continuousOn_Ioi {t : ℝ} (ht : 0 < t) :
    ContinuousOn (mobiusKernel t) (Set.Ioi (0 : ℝ)) := by
  have hden : ∀ x ∈ Set.Ioi (0 : ℝ), x + t ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos hx ht)
  simpa [mobiusKernel] using
    (continuousOn_id.div (continuousOn_id.add continuousOn_const) hden)

/-- The kernel `x ↦ x / (x + t)` is strictly positive on `(0,∞)` for `0 < t`.
Source: Hiai, proof of Theorem 6.3. -/
theorem mobiusKernel_pos_Ioi {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < mobiusKernel t x := by
  intro x hx
  exact div_pos hx (add_pos hx ht)

/-- The truncated `ψ_n` is strictly positive on `(0,∞)` for nondegenerate cutoffs.
Source: Hiai, proof of Theorem 6.3. -/
theorem psiApprox_pos_Ioi {p : ℝ} {k : ℕ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hk : 0 < k) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < psiApprox p k x := by
  intro x hx
  rw [psiApprox_eq_integral_weightedKernel]
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hb : 0 < b := by
    simpa [b] using cutoff_pos k
  have hab : a < b := by
    simpa [a, b] using cutoff_inv_lt_of_pos hk
  have hcont :
      ContinuousOn (fun t : ℝ => weightedKernel p t x) (Set.Icc a b) :=
    weightedKernel_continuousOn_Icc (p := p) ha (le_of_lt hx)
  refine intervalIntegral.integral_pos hab hcont ?_ ?_
  · intro t ht
    have ht_pos : 0 < t := ha.trans ht.1
    exact le_of_lt (mul_pos (psiWeight_pos hp ht_pos) (mobiusKernel_pos_Ioi ht_pos x hx))
  · refine ⟨b, ⟨hab.le, le_rfl⟩, ?_⟩
    exact mul_pos (psiWeight_pos hp hb) (mobiusKernel_pos_Ioi hb x hx)

/-- Löwner--Heinz gives all-Hilbert-space operator monotonicity of
`x ↦ x / (x + t)` on `(0,∞)`.
Source: Hiai, proof of Theorem 6.3. -/
theorem mobiusKernel_allHOperatorMonotone_Ioi {t : ℝ} (ht : 0 < t) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ))
      (mobiusKernel t) := by
  intro K _ _ _ _ _
  have hmonoIci :
      HansenPedersen.HOperatorMonotoneOnInterval K (Set.Ici (0 : ℝ))
        (mobiusKernel t) := by
    have hwrap :
        LownerHeinzTheorem.OperatorMonotoneOn (ℋ := K) (Set.Ici (0 : ℝ))
          (mobiusKernel t) := by
      simpa [mobiusKernel] using
        (LownerHeinzTheorem.ratio_add_t_operatorMonotoneOn_Ici (ℋ := K) t ht)
    exact HansenPedersen.operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici (ℋ := K) hwrap
  intro A B hA hB hσA hσB hAB
  apply hmonoIci hA hB
  · intro x hx
    exact le_of_lt (show (0 : ℝ) < x from hσA hx)
  · intro x hx
    exact le_of_lt (show (0 : ℝ) < x from hσB hx)
  · exact hAB

/-- The positive kernel `x ↦ x / (x + t)` satisfies Hiai--Petz condition (i).
Source: Hiai, proof of Theorem 6.3. -/
theorem mobiusKernel_operatorMonotone {t : ℝ} (ht : 0 < t) :
    QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi (mobiusKernel t) :=
  mobiusKernel_allHOperatorMonotone_Ioi ht

/-- The clipped weighted kernel agrees with the genuine weighted kernel on the positive
spectral range and the truncated integration interval.
Local API: Lean-side continuity device for Hiai, proof of Theorem 6.3. -/
private theorem clippedWeightedKernel_eq_weightedKernel_on
    {p a x t : ℝ} (hx : 0 < x) (hat : a ≤ t) :
    clippedWeightedKernel p a x t = weightedKernel p t x := by
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  dsimp [clippedWeightedKernel, weightedKernel, psiWeight, mobiusKernel]
  rw [max_eq_left hx_nonneg, max_eq_left hat]

private theorem psiApprox_eq_setIntegral_clipped {p : ℝ} (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    psiApprox p k x =
      ∫ t in Set.Ioc ((cutoff k)⁻¹) (cutoff k),
        clippedWeightedKernel p ((cutoff k)⁻¹) x t := by
  have hab : (cutoff k)⁻¹ ≤ cutoff k := cutoff_inv_le k
  rw [psiApprox_eq_integral_weightedKernel, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro t ht
  exact (clippedWeightedKernel_eq_weightedKernel_on (p := p)
    (a := (cutoff k)⁻¹) (x := x) (t := t) hx (le_of_lt ht.1)).symm

private noncomputable def cfcIntegralBound (p a : ℝ) : ℝ → ℝ :=
  fun t : ℝ => ‖sinCoeff p * (max t a) ^ (p - 1)‖

@[fun_prop] private theorem cfcIntegralBound_continuous {p a : ℝ} (ha : 0 < a) :
    Continuous (cfcIntegralBound p a) := by
  have hmax : Continuous fun t : ℝ => max t a :=
    continuous_id.max continuous_const
  have hpos : ∀ t : ℝ, max t a ≠ 0 := by
    intro t
    exact ne_of_gt (ha.trans_le (le_max_right t a))
  change Continuous fun t : ℝ => ‖sinCoeff p * (max t a) ^ (p - 1)‖
  exact (continuous_const.mul (hmax.rpow_const fun t => Or.inl (hpos t))).norm

private theorem cfcIntegralBound_hasFiniteIntegral {p a b : ℝ} (ha : 0 < a) :
    MeasureTheory.HasFiniteIntegral (cfcIntegralBound p a)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  have hIcc :
      MeasureTheory.IntegrableOn (cfcIntegralBound p a) (Set.Icc a b) :=
    (cfcIntegralBound_continuous (p := p) ha).continuousOn.integrableOn_compact
      isCompact_Icc
  have hIoc :
      MeasureTheory.IntegrableOn (cfcIntegralBound p a) (Set.Ioc a b) :=
    hIcc.mono_set Set.Ioc_subset_Icc_self
  exact hIoc.hasFiniteIntegral

private theorem clippedWeightedKernel_norm_le_bound {p a x t : ℝ} (ha : 0 < a) :
    ‖clippedWeightedKernel p a x t‖ ≤ cfcIntegralBound p a t := by
  let y : ℝ := max x 0
  let s : ℝ := max t a
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact le_max_right x 0
  have hs_pos : 0 < s := by
    dsimp [s]
    exact ha.trans_le (le_max_right t a)
  have hden_pos : 0 < y + s := add_pos_of_nonneg_of_pos hy_nonneg hs_pos
  have hratio_nonneg : 0 ≤ y / (y + s) :=
    div_nonneg hy_nonneg (le_of_lt hden_pos)
  have hratio_le_one : y / (y + s) ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (le_of_lt hden_pos)
    exact le_add_of_nonneg_right (le_of_lt hs_pos)
  have hratio_norm : ‖y / (y + s)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg hratio_nonneg]
    exact hratio_le_one
  dsimp [clippedWeightedKernel, cfcIntegralBound, y, s]
  rw [abs_mul, abs_div]
  have hmul :
      |sinCoeff p * max t a ^ (p - 1)| *
          (|max x 0| / |max x 0 + max t a|) ≤
        |sinCoeff p * max t a ^ (p - 1)| * 1 := by
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs, y, s] using hratio_norm)
      (abs_nonneg _)
  simpa using hmul

private theorem cfcR_psiApprox_eq_setIntegral_clipped
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {p : ℝ} (k : ℕ) {A : HansenPedersen.L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    HansenPedersen.cfcR (ℋ := K) (psiApprox p k) A =
      ∫ t in Set.Ioc ((cutoff k)⁻¹) (cutoff k),
        HansenPedersen.cfcR (ℋ := K)
          (fun x : ℝ => clippedWeightedKernel p ((cutoff k)⁻¹) x t) A := by
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  let s : Set ℝ := Set.Ioc a b
  let F : ℝ → ℝ → ℝ := fun t x => clippedWeightedKernel p a x t
  let bound : ℝ → ℝ := cfcIntegralBound p a
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hs : MeasurableSet s := by
    simp [s]
  have hcont :
      ContinuousOn (Function.uncurry F) (s ×ˢ spectrum ℝ A) := by
    have hswap :
        Continuous fun q : ℝ × ℝ => clippedWeightedKernel p a q.2 q.1 :=
      (clippedWeightedKernel_continuous (p := p) (a := a) ha).comp
        (continuous_snd.prodMk continuous_fst)
    exact hswap.continuousOn
  have hbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict s),
        ∀ z ∈ spectrum ℝ A, ‖F t z‖ ≤ bound t := by
    exact Filter.Eventually.of_forall fun t z hz => by
      simpa [F, bound] using
        clippedWeightedKernel_norm_le_bound (p := p) (a := a) (x := z) (t := t) ha
  have hfinite :
      MeasureTheory.HasFiniteIntegral bound (MeasureTheory.volume.restrict s) := by
    simpa [bound, s, a, b] using
      cfcIntegralBound_hasFiniteIntegral (p := p) (a := a) (b := b) ha
  have hcfc :
      cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
          (fun r : ℝ => ∫ t in s, F t r) A =
        ∫ t in s,
          cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (F t) A := by
    exact cfc_setIntegral (μ := MeasureTheory.volume) hs F bound A hcont hbound hfinite hA
  have hscalar :
      Set.EqOn (psiApprox p k) (fun r : ℝ => ∫ t in s, F t r)
        (spectrum ℝ A) := by
    intro r hr
    have hrpos : 0 < r := hσA hr
    simpa [s, F, a, b] using psiApprox_eq_setIntegral_clipped (p := p) k hrpos
  dsimp [HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  calc
    cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
        (psiApprox p k) A
        = cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (fun r : ℝ => ∫ t in s, F t r) A := by
            exact cfc_congr hscalar
    _ = ∫ t in s,
          cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (F t) A := hcfc
    _ = ∫ t in Set.Ioc ((cutoff k)⁻¹) (cutoff k),
          cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (fun x : ℝ => clippedWeightedKernel p ((cutoff k)⁻¹) x t) A := by
            rfl

private theorem cfcR_clippedWeightedKernel_eq_smul_kernel
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {p a t : ℝ} (ha : 0 < a) (hat : a ≤ t) {A : HansenPedersen.L K}
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    HansenPedersen.cfcR (ℋ := K)
        (fun x : ℝ => clippedWeightedKernel p a x t) A =
      psiWeight p t • HansenPedersen.cfcR (ℋ := K) (mobiusKernel t) A := by
  have ht : 0 < t := ha.trans_le hat
  have hcont :
      ContinuousOn (mobiusKernel t) (spectrum ℝ A) :=
    (mobiusKernel_continuousOn_Ioi ht).mono hσA
  dsimp [HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  calc
    cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
        (fun x : ℝ => clippedWeightedKernel p a x t) A
        = cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (fun x : ℝ => weightedKernel p t x) A := by
            apply cfc_congr
            intro x hx
            exact clippedWeightedKernel_eq_weightedKernel_on
              (p := p) (a := a) (x := x) (t := t) (hσA hx) hat
    _ = cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (fun x : ℝ => psiWeight p t * mobiusKernel t x) A := by
            rfl
    _ = psiWeight p t •
          cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint)
            (mobiusKernel t) A := by
            exact cfc_const_mul (R := ℝ) (A := HansenPedersen.L K)
              (p := IsSelfAdjoint) (r := psiWeight p t)
              (f := mobiusKernel t) (a := A) (hf := hcont)

private theorem integrableOn_cfcR_clippedWeightedKernel
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {p : ℝ} (k : ℕ) {A : HansenPedersen.L K} (hA : IsSelfAdjoint A) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        HansenPedersen.cfcR (ℋ := K)
          (fun x : ℝ => clippedWeightedKernel p ((cutoff k)⁻¹) x t) A)
      (Set.Ioc ((cutoff k)⁻¹) (cutoff k)) := by
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  let s : Set ℝ := Set.Ioc a b
  let F : ℝ → ℝ → ℝ := fun t x => clippedWeightedKernel p a x t
  let bound : ℝ → ℝ := cfcIntegralBound p a
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hs : MeasurableSet s := by
    simp [s]
  have hcont :
      ContinuousOn (Function.uncurry F) (s ×ˢ spectrum ℝ A) := by
    have hswap :
        Continuous fun q : ℝ × ℝ => clippedWeightedKernel p a q.2 q.1 :=
      (clippedWeightedKernel_continuous (p := p) (a := a) ha).comp
        (continuous_snd.prodMk continuous_fst)
    exact hswap.continuousOn
  have hbound :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict s),
        ∀ z ∈ spectrum ℝ A, ‖F t z‖ ≤ bound t := by
    exact Filter.Eventually.of_forall fun t z hz => by
      simpa [F, bound] using
        clippedWeightedKernel_norm_le_bound (p := p) (a := a) (x := z) (t := t) ha
  have hfinite :
      MeasureTheory.HasFiniteIntegral bound (MeasureTheory.volume.restrict s) := by
    simpa [bound, s, a, b] using
      cfcIntegralBound_hasFiniteIntegral (p := p) (a := a) (b := b) ha
  have hint :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          cfc (R := ℝ) (A := HansenPedersen.L K) (p := IsSelfAdjoint) (F t) A)
        s :=
    integrableOn_cfc (μ := MeasureTheory.volume) hs F bound A hcont hbound hfinite hA
  simpa [HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR,
    F, s, a, b] using hint

/-- The truncated integral `ψ_n` is operator monotone on `(0,∞)` for `1 < p < 2`.
Source: Hiai, proof of Theorem 6.3. -/
theorem psiApprox_allHOperatorMonotone_Ioi {p : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (k : ℕ) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ))
      (psiApprox p k) := by
  intro K _ _ _ _ _ A B hA hB hσA hσB hAB
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  let s : Set ℝ := Set.Ioc a b
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hAeq :=
    cfcR_psiApprox_eq_setIntegral_clipped (K := K) (p := p) k
      (A := A) hA hσA
  have hBeq :=
    cfcR_psiApprox_eq_setIntegral_clipped (K := K) (p := p) k
      (A := B) hB hσB
  rw [hAeq, hBeq]
  refine MeasureTheory.setIntegral_mono_on
    (integrableOn_cfcR_clippedWeightedKernel (K := K) (p := p) k (A := A) hA)
    (integrableOn_cfcR_clippedWeightedKernel (K := K) (p := p) k (A := B) hB)
    measurableSet_Ioc ?_
  intro t ht
  have htpos : 0 < t := by
    exact ha.trans ht.1
  have hweight_nonneg : 0 ≤ psiWeight p t :=
    le_of_lt (psiWeight_pos hp htpos)
  have hkernel :
      HansenPedersen.cfcR (ℋ := K) (mobiusKernel t) A ≤
        HansenPedersen.cfcR (ℋ := K) (mobiusKernel t) B := by
    exact (mobiusKernel_allHOperatorMonotone_Ioi (t := t) htpos K)
      hA hB hσA hσB hAB
  rw [cfcR_clippedWeightedKernel_eq_smul_kernel (K := K) (p := p)
      (a := a) (t := t) ha (le_of_lt ht.1) (A := A) hσA,
    cfcR_clippedWeightedKernel_eq_smul_kernel (K := K) (p := p)
      (a := a) (t := t) ha (le_of_lt ht.1) (A := B) hσB]
  exact smul_le_smul_of_nonneg_left hkernel hweight_nonneg

/-- The truncated function `ψ_n` satisfies Hiai--Petz condition (i).
Source: Hiai, proof of Theorem 6.3. -/
theorem psiApprox_operatorMonotone {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) (k : ℕ) :
    QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi (psiApprox p k) :=
  psiApprox_allHOperatorMonotone_Ioi hp k

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
