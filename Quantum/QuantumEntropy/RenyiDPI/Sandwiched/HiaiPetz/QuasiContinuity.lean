/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.Common.OperatorCFC

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem c10_quasiVar_continuousOn_clm
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z : B H}
    (hα : 1 < α) (hZ : 0 ≤ Z) :
    ContinuousOn (Function.uncurry (fun ρ σ : B H ↦
      (quasiVar α (ρ : L H) (σ : L H) (Z : L H)).re))
      ({A : B H | 0 ≤ A} ×ˢ {A : B H | 0 ≤ A}) := by
  let c : ℝ := (α - 1) / (2 * α)
  let q : ℝ := α / (α - 1)
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hc : 0 ≤ c :=
    (div_pos (sub_pos.mpr hα) (mul_pos (by norm_num) hα0)).le
  have hq : 0 ≤ q := (div_pos hα0 (sub_pos.mpr hα)).le
  let S : Set (B H) := {A : B H | 0 ≤ A}
  have hTr : Continuous (fun A : B H ↦ (traceCLM A).re) :=
    Complex.continuous_re.comp traceCLM.continuous
  have hρ : Continuous (fun p : B H × B H ↦ (traceCLM (Z * p.1)).re) :=
    hTr.comp (continuous_const.mul continuous_fst)
  have hσpow : ContinuousOn (fun p : B H × B H ↦ CFC.rpow p.2 c) (S ×ˢ S) :=
    (rpow_continuousOn_nonneg hc).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have hinner : ContinuousOn
      (fun p : B H × B H ↦ CFC.rpow p.2 c * Z * CFC.rpow p.2 c) (S ×ˢ S) :=
    (hσpow.mul continuousOn_const).mul hσpow
  have hnonneg : ∀ p ∈ S ×ˢ S,
      0 ≤ CFC.rpow p.2 c * Z * CFC.rpow p.2 c := by
    intro p _
    have hself : IsSelfAdjoint (CFC.rpow p.2 c) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    simpa only [hself.star_eq] using star_left_conjugate_nonneg hZ (CFC.rpow p.2 c)
  have hpow : ContinuousOn
      (fun p : B H × B H ↦
        CFC.rpow (CFC.rpow p.2 c * Z * CFC.rpow p.2 c) q) (S ×ˢ S) :=
    (rpow_continuousOn_nonneg hq).comp hinner hnonneg
  have hσ : ContinuousOn
      (fun p : B H × B H ↦
        (traceCLM (CFC.rpow (CFC.rpow p.2 c * Z * CFC.rpow p.2 c) q)).re)
      (S ×ˢ S) := hTr.comp_continuousOn hpow
  have hfinal : ContinuousOn
      (fun p : B H × B H ↦ α * (traceCLM (Z * p.1)).re -
        (α - 1) *
          (traceCLM (CFC.rpow (CFC.rpow p.2 c * Z * CFC.rpow p.2 c) q)).re)
      (S ×ˢ S) :=
    (continuous_const.mul hρ).continuousOn.sub (continuousOn_const.mul hσ)
  refine hfinal.congr ?_
  rintro ⟨ρ, σ⟩ _
  simpa only [c, q, traceCLM, Complex.sub_re, Complex.re_ofReal_mul] using
    congrArg Complex.re (quasiVar_eq_clm_direct α ρ σ Z)

theorem quasiVar_continuousOn_nonneg_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z : L H},
  1 < α → 0 ≤ Z →
  ContinuousOn (Function.uncurry (fun ρ σ : L H => (quasiVar α ρ σ Z).re))
    ({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A}) := by
  intro H _ _ α Z hα hZ
  let e := linearToContinuousEndStarAlgEquiv H
  have he : Continuous e := (StarAlgEquiv.isometry e).continuous
  have hZe : (0 : B H) ≤ e Z :=
    (ContinuousLinearMap.coe_le_coe_iff (0 : B H) (e Z)).mp hZ
  have hcont : Continuous (fun p : L H × L H ↦ (e p.1, e p.2)) :=
    (he.comp continuous_fst).prodMk (he.comp continuous_snd)
  have hmap : Set.MapsTo (fun p : L H × L H ↦ (e p.1, e p.2))
      ({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A})
      ({A : B H | 0 ≤ A} ×ˢ {A : B H | 0 ≤ A}) := by
    intro p hp
    exact ⟨(ContinuousLinearMap.coe_le_coe_iff (0 : B H) (e p.1)).mp hp.1,
      (ContinuousLinearMap.coe_le_coe_iff (0 : B H) (e p.2)).mp hp.2⟩
  have hcomp := (c10_quasiVar_continuousOn_clm hα hZe).comp hcont.continuousOn hmap
  exact hcomp

end RenyiDPI
