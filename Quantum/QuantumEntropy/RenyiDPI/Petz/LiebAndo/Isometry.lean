/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Petz.TracePower
import Quantum.QuantumEntropy.RenyiDPI.Common.IsometricRpow

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma p06_tracePower_eq_trace
    {H : Type u} [Qudit H] {α : ℝ} {ρ σ : L H}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    petzTracePower α ρ σ = (Tr (CFC.rpow ρ α * CFC.rpow σ (1 - α))).re := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · unfold petzTracePower QuantumEntropy.realTrace
    exact congrArg (fun X : L H => (Tr X).re) (Subsingleton.elim _ _)
  · exact petzTracePower_eq_trace_rpow_mul hα hρ hσ

theorem petzTracePower_isometric_conj :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H},
    α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ ρ → 0 ≤ σ →
  petzTracePower α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) = petzTracePower α ρ σ := by
  intro H K _ _ V hV α ρ σ hα hρ hσ
  have hVρ : 0 ≤ (V.comp ρ).comp (LinearMap.adjoint V) := by
    rw [LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hρ).conj_adjoint V
  have hVσ : 0 ≤ (V.comp σ).comp (LinearMap.adjoint V) := by
    rw [LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hσ).conj_adjoint V
  rw [p06_tracePower_eq_trace hα hVρ hVσ,
    p06_tracePower_eq_trace hα hρ hσ,
    rpow_isometric_conj_of_ne_zero V hV hρ (ne_of_gt hα.1),
    rpow_isometric_conj_of_ne_zero V hV hσ (ne_of_gt (sub_pos.mpr hα.2))]
  have hmul :
      (V.comp (CFC.rpow ρ α)).comp (LinearMap.adjoint V) *
          (V.comp (CFC.rpow σ (1 - α))).comp (LinearMap.adjoint V) =
        (V.comp (CFC.rpow ρ α * CFC.rpow σ (1 - α))).comp
          (LinearMap.adjoint V) := by
    ext x
    have hid : ∀ y : H, (LinearMap.adjoint V) (V y) = y := fun y => by
      simpa only [LinearMap.comp_apply, Module.End.one_apply] using
        LinearMap.congr_fun hV y
    change V ((CFC.rpow ρ α) ((LinearMap.adjoint V)
      (V ((CFC.rpow σ (1 - α)) ((LinearMap.adjoint V) x))))) =
        V ((CFC.rpow ρ α) ((CFC.rpow σ (1 - α)) ((LinearMap.adjoint V) x)))
    rw [hid]
  rw [hmul, LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc, hV]
  rfl

end RenyiDPI
