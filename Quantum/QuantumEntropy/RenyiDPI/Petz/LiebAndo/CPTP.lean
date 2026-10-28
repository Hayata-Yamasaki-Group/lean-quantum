/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.TraceOut
import Quantum.QuantumEntropy.RenyiDPI.Petz.NonNegLift
import Quantum.QuantumMechanics.Channel.Stinespring

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem petzTracePower_le_cptp_liebAndo :
∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (E : CPTP H K) {α : ℝ} {ρ σ : L H},
  α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ ρ → 0 ≤ σ →
  petzTracePower α ρ σ ≤ petzTracePower α (E.toFun ρ) (E.toFun σ) := by
  intro H K _ _ _ _ E α ρ σ hα hρ hσ
  obtain ⟨Env, hEnvQudit, hEnvNontrivial, V, hV, hE⟩ :=
    QuantumChannel.CPTP.exists_isometric_stinespring_dilation E
  letI := hEnvQudit
  letI := hEnvNontrivial
  letI : Nontrivial (K ⊗[ℂ] Env) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  have hVρ : 0 ≤ (V.comp ρ).comp (LinearMap.adjoint V) := by
    rw [LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hρ).conj_adjoint V
  have hVσ : 0 ≤ (V.comp σ).comp (LinearMap.adjoint V) := by
    rw [LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hσ).conj_adjoint V
  calc
    petzTracePower α ρ σ =
        petzTracePower α ((V.comp ρ).comp (LinearMap.adjoint V))
          ((V.comp σ).comp (LinearMap.adjoint V)) :=
      (petzTracePower_isometric_conj V hV hα hρ hσ).symm
    _ ≤ petzTracePower α
        (traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)))
        (traceOutRight ((V.comp σ).comp (LinearMap.adjoint V))) :=
      petzTracePower_le_traceOutRight hα hVρ hVσ
    _ = petzTracePower α (E.toFun ρ) (E.toFun σ) := by
      rw [← hE ρ, ← hE σ]

theorem petzTracePowerMonotoneOnPosDef_liebAndo :
PetzTracePowerMonotoneOnPosDef.{u} := by
  intro H K _ _ _ _ E ρ σ hρ hσ _ _ α hα
  exact petzTracePower_le_cptp_liebAndo E hα (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)

theorem petzMonotoneOnNonNeg_liebAndo :
PetzMonotoneOnNonNeg.{u} := by
  exact RenyiDPI.petzMonotoneOnNonNeg_of_posDef.{u} petzTracePowerMonotoneOnPosDef_liebAndo

end RenyiDPI
