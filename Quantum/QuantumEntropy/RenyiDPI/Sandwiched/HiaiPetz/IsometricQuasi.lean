/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.IsometricRpow
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem c07_renyi_sym_c07_of_rpow
    (hU_P05 :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {A : L H} {p : ℝ}, 0 ≤ A → p ≠ 0 →
  CFC.rpow ((V.comp A).comp (LinearMap.adjoint V)) p =
    (V.comp (CFC.rpow A p)).comp (LinearMap.adjoint V)) :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H}, 1 < α → 0 ≤ ρ → 0 ≤ σ →
  sandwichedQuasi α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) = sandwichedQuasi α ρ σ := by
  intro H K _ _ V hV α ρ σ hα hρ hσ
  let ψ : L H → L K := fun X ↦ (V.comp X).comp (LinearMap.adjoint V)
  have hid (x : H) : (LinearMap.adjoint V) (V x) = x := by
    have hx := LinearMap.congr_fun hV x
    simpa [LinearMap.comp_apply] using hx
  have hmul (X Y : L H) : ψ X * ψ Y = ψ (X * Y) := by
    ext x
    change V (X ((LinearMap.adjoint V) (V (Y ((LinearMap.adjoint V) x))))) =
      V (X (Y ((LinearMap.adjoint V) x)))
    rw [hid]
  have htrace (X : L H) : Tr (ψ X) = Tr X := by
    change Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]
    rfl
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hβ_ne : (1 - α) / (2 * α) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (ne_of_lt hα)) (mul_ne_zero two_ne_zero hα0.ne')
  have hinner_nn : (0 : L H) ≤
      CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α)) := by
    have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hconj := star_left_conjugate_nonneg hρ (CFC.rpow σ ((1 - α) / (2 * α)))
    rwa [hP_sa.star_eq] at hconj
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct]
  change Tr (CFC.rpow
      (CFC.rpow (ψ σ) ((1 - α) / (2 * α)) * ψ ρ *
        CFC.rpow (ψ σ) ((1 - α) / (2 * α))) α) =
    Tr (CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α)
  rw [hU_P05 V hV hσ hβ_ne, hmul, hmul,
    hU_P05 V hV hinner_nn hα0.ne', htrace]

theorem sandwichedQuasi_isometric_conj_gt :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H}, 1 < α → 0 ≤ ρ → 0 ≤ σ →
  sandwichedQuasi α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) = sandwichedQuasi α ρ σ := by
  exact c07_renyi_sym_c07_of_rpow @RenyiDPI.rpow_isometric_conj_of_ne_zero.{u}

private theorem c08_renyi_sym_c08_of_rpow
    (hU_P05 :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {A : L H} {p : ℝ}, 0 ≤ A → p ≠ 0 →
  CFC.rpow ((V.comp A).comp (LinearMap.adjoint V)) p =
    (V.comp (CFC.rpow A p)).comp (LinearMap.adjoint V)) :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H} {Z : L K}, 1 < α → 0 ≤ σ → 0 ≤ Z →
  quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) Z =
      quasiVar α ρ σ ((LinearMap.adjoint V).comp (Z.comp V)) := by
  intro H K _ _ V hV α ρ σ Z hα hσ hZ
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hα1 : α - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hα)
  let ψ : L H → L K := fun X ↦ (V.comp X).comp (LinearMap.adjoint V)
  let ZV : L H := (LinearMap.adjoint V).comp (Z.comp V)
  let c : ℝ := (α - 1) / (2 * α)
  let q : ℝ := α / (α - 1)
  have hc : c ≠ 0 := div_ne_zero hα1 (mul_ne_zero (by norm_num) (ne_of_gt hα0))
  have hq : q ≠ 0 := div_ne_zero (ne_of_gt hα0) hα1
  have hZV : (0 : L H) ≤ ZV := by
    exact (LinearMap.nonneg_iff_isPositive _).mpr
      (((LinearMap.nonneg_iff_isPositive Z).mp hZ).adjoint_conj V)
  have htrace (X : L H) : Tr (ψ X) = Tr X := by
    change Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]
    rfl
  have hlinear : Tr (Z * ψ ρ) = Tr (ZV * ρ) := by
    change Tr (((Z.comp V).comp ρ).comp (LinearMap.adjoint V)) =
      Tr (((LinearMap.adjoint V).comp (Z.comp V)).comp ρ)
    rw [LinearMap.trace_comp_comm']
    rfl
  have hinner : ψ (CFC.rpow σ c) * Z * ψ (CFC.rpow σ c) =
      ψ (CFC.rpow σ c * ZV * CFC.rpow σ c) := by
    ext x
    rfl
  have hY : (0 : L H) ≤ CFC.rpow σ c * ZV * CFC.rpow σ c := by
    have hP : (0 : L H) ≤ CFC.rpow σ c := CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hZV (CFC.rpow σ c)
    rwa [(IsSelfAdjoint.of_nonneg hP).star_eq] at h
  change quasiVar α (ψ ρ) (ψ σ) Z = quasiVar α ρ σ ZV
  rw [quasiVar_eq_direct, quasiVar_eq_direct]
  change (α : ℂ) * Tr (Z * ψ ρ) - ((α - 1 : ℝ) : ℂ) *
      Tr (CFC.rpow (CFC.rpow (ψ σ) c * Z * CFC.rpow (ψ σ) c) q) =
    (α : ℂ) * Tr (ZV * ρ) - ((α - 1 : ℝ) : ℂ) *
      Tr (CFC.rpow (CFC.rpow σ c * ZV * CFC.rpow σ c) q)
  rw [hU_P05 V hV hσ hc, hinner, hU_P05 V hV hY hq, htrace, hlinear]

theorem quasiVar_isometric_conj_gt :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H} {Z : L K}, 1 < α → 0 ≤ σ → 0 ≤ Z →
  quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) Z =
      quasiVar α ρ σ ((LinearMap.adjoint V).comp (Z.comp V)) := by
  exact c08_renyi_sym_c08_of_rpow @RenyiDPI.rpow_isometric_conj_of_ne_zero.{u}

end RenyiDPI
