/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.TraceInequality.LiebAndo.Concavity
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.Trace
import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem toContinuousLinearMap_convexCombo
    {H : Type u} [Qudit H] (A₁ A₂ : L H) (θ : ℝ) :
    ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap =
      (1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap := by
  ext x
  rfl

theorem petzTracePower_jointlyConcave_pd_liebAndo :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ},
  α ∈ Set.Ioo (0 : ℝ) 1 →
  JointlyConcaveOn (pdSetLM (ℋ := H)) (pdSetLM (ℋ := H))
    (petzTracePower α) := by
  intro H _ _ α hα A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hA₁n := ((pdSetLM_strictPositivity_certificate A₁).1 hA₁).nonneg
  have hA₂n := ((pdSetLM_strictPositivity_certificate A₂).1 hA₂).nonneg
  have hB₁n := ((pdSetLM_strictPositivity_certificate B₁).1 hB₁).nonneg
  have hB₂n := ((pdSetLM_strictPositivity_certificate B₂).1 hB₂).nonneg
  have hAθ : 0 ≤ (1 - θ) • A₁ + θ • A₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hA₁n) (smul_nonneg hθ0 hA₂n)
  have hBθ : 0 ≤ (1 - θ) • B₁ + θ • B₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hB₁n) (smul_nonneg hθ0 hB₂n)
  rw [petzTracePower_eq_liebTrace_one hα hA₁n hB₁n,
    petzTracePower_eq_liebTrace_one hα hA₂n hB₂n,
    petzTracePower_eq_liebTrace_one hα hAθ hBθ]
  have h := LiebAndoTrace.liebTrace_jointlyConcaveOn_pdSet
    hα.1 hα.2 (1 : L H).toContinuousLinearMap
    (A₁ := A₁.toContinuousLinearMap) (A₂ := A₂.toContinuousLinearMap)
    (B₁ := B₁.toContinuousLinearMap) (B₂ := B₂.toContinuousLinearMap) (θ := θ)
    hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa only [liebTraceMapLM, toContinuousLinearMap_convexCombo] using h

private theorem p04_regularization_continuous
    {H : Type u} [Qudit H] (A B : L H) :
    Continuous (fun ε : ℝ ↦ (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1)) := by
  have hsmul : Continuous (fun ε : ℝ ↦ (ε : ℂ) • (1 : L H)) :=
    Complex.continuous_ofReal.smul continuous_const
  exact (continuous_const.add hsmul).prodMk (continuous_const.add hsmul)

private theorem p04_regularization_tendsto_pair
    {H : Type u} [Qudit H] [Nontrivial H]
    (A B : L H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Filter.Tendsto (fun ε : ℝ ↦ (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (A, B) ({X : L H | 0 ≤ X} ×ˢ {X : L H | 0 ≤ X})) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using ((p04_regularization_continuous A B).tendsto 0).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsmul : (0 : L H) ≤ (ε : ℂ) • (1 : L H) :=
      nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε)
    exact ⟨add_nonneg hA hsmul, add_nonneg hB hsmul⟩

private theorem p04_regularization_tendsto
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ}
    (hcont : ContinuousOn (Function.uncurry (petzTracePower (ℋ := H) α))
      ({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A}))
    (A B : L H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Filter.Tendsto
      ((Function.uncurry (petzTracePower (ℋ := H) α)).comp
        (fun ε : ℝ ↦ (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Function.uncurry (petzTracePower (ℋ := H) α) (A, B))) := by
  exact (hcont (A, B) ⟨hA, hB⟩).tendsto.comp
    (p04_regularization_tendsto_pair A B hA hB)

private theorem p04_regularization_convexCombo
    {H : Type u} [Qudit H] (X₁ X₂ : L H) (θ ε : ℝ) :
    ((1 - θ) • X₁ + θ • X₂) + (ε : ℂ) • 1 =
      (1 - θ) • (X₁ + (ε : ℂ) • 1) + θ • (X₂ + (ε : ℂ) • 1) := by
  have hone : (1 - θ : ℝ) • ((ε : ℂ) • (1 : L H)) +
      θ • ((ε : ℂ) • (1 : L H)) = (ε : ℂ) • (1 : L H) := by
    rw [← add_smul]
    norm_num
  simp only [smul_add]
  rw [show (1 - θ) • X₁ + (1 - θ) • (ε : ℂ) • 1 +
      (θ • X₂ + θ • (ε : ℂ) • 1) =
      ((1 - θ) • X₁ + θ • X₂) +
        ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) by abel, hone]

theorem petzTracePower_jointlyConcave_nonneg_liebAndo :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ},
  α ∈ Set.Ioo (0 : ℝ) 1 →
  JointlyConcaveOn {A : L H | 0 ≤ A} {A : L H | 0 ≤ A}
    (petzTracePower α) := by
  intro H instH instNontrivial α hα
  have hlimit := p04_regularization_tendsto (petzTracePower_continuousOn_nonneg (H := H) hα)
  have hpd := petzTracePower_jointlyConcave_pd_liebAndo (H := H) hα
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hA₁ hA₂ hB₁ hB₂
  have hAc : 0 ≤ (1 - θ) • A₁ + θ • A₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hA₁) (smul_nonneg hθ0 hA₂)
  have hBc : 0 ≤ (1 - θ) • B₁ + θ • B₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hB₁) (smul_nonneg hθ0 hB₂)
  refine le_of_tendsto_of_tendsto
    (((hlimit A₁ B₁ hA₁ hB₁).const_smul (1 - θ)).add
      ((hlimit A₂ B₂ hA₂ hB₂).const_smul θ))
    (hlimit _ _ hAc hBc) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (1 - θ) • petzTracePower α
      (A₁ + (ε : ℂ) • 1) (B₁ + (ε : ℂ) • 1) +
    θ • petzTracePower α
      (A₂ + (ε : ℂ) • 1) (B₂ + (ε : ℂ) • 1) ≤
    petzTracePower α
      ((1 - θ) • A₁ + θ • A₂ + (ε : ℂ) • 1)
      ((1 - θ) • B₁ + θ • B₂ + (ε : ℂ) • 1)
  rw [p04_regularization_convexCombo A₁ A₂ θ ε,
    p04_regularization_convexCombo B₁ B₂ θ ε]
  exact hpd (nonneg_add_pos_smul_one_pdSetLM hA₁ hε)
    (nonneg_add_pos_smul_one_pdSetLM hA₂ hε)
    (nonneg_add_pos_smul_one_pdSetLM hB₁ hε)
    (nonneg_add_pos_smul_one_pdSetLM hB₂ hε) hθ0 hθ1

end RenyiDPI
