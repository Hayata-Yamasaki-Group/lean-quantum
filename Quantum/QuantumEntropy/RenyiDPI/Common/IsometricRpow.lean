/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

private noncomputable def p05IsometricConjHom
    {H K : Type u} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K)
    (hV : (LinearMap.adjoint V).comp V = (1 : L H)) :
    L H →⋆ₙₐ[ℂ] L K where
  toFun X := (V.comp X).comp (LinearMap.adjoint V)
  map_add' X Y := by
    change (V.comp (X + Y)).comp (LinearMap.adjoint V) =
      (V.comp X).comp (LinearMap.adjoint V) +
        (V.comp Y).comp (LinearMap.adjoint V)
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c X := by
    change (V.comp (c • X)).comp (LinearMap.adjoint V) =
      c • ((V.comp X).comp (LinearMap.adjoint V))
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
  map_zero' := by
    change (V.comp 0).comp (LinearMap.adjoint V) = 0
    rw [LinearMap.comp_zero, LinearMap.zero_comp]
  map_mul' X Y := by
    change (V.comp (X * Y)).comp (LinearMap.adjoint V) =
      ((V.comp X).comp (LinearMap.adjoint V)) *
        ((V.comp Y).comp (LinearMap.adjoint V))
    ext x
    have hid : ∀ y : H, (LinearMap.adjoint V) (V y) = y := fun y ↦ by
      have h := LinearMap.congr_fun hV y
      simpa [LinearMap.comp_apply] using h
    change V (X (Y ((LinearMap.adjoint V) x))) =
      V (X ((LinearMap.adjoint V) (V (Y ((LinearMap.adjoint V) x)))))
    rw [hid]
  map_star' X := by
    change (V.comp (star X)).comp (LinearMap.adjoint V) =
      star ((V.comp X).comp (LinearMap.adjoint V))
    rw [show (star X : L H) = LinearMap.adjoint X from
        LinearMap.star_eq_adjoint X,
      show (star ((V.comp X).comp (LinearMap.adjoint V)) : L K) =
        LinearMap.adjoint ((V.comp X).comp (LinearMap.adjoint V)) from
          LinearMap.star_eq_adjoint _,
      LinearMap.adjoint_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, ← LinearMap.comp_assoc]

private noncomputable def p05IsometricConjLM
    {H K : Type u} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K) : L H →ₗ[ℂ] L K where
  toFun X := (V.comp X).comp (LinearMap.adjoint V)
  map_add' X Y := by rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c X := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
    rfl

private lemma p05IsometricConjHomContinuous
    {H K : Type u} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K)
    (hV : (LinearMap.adjoint V).comp V = (1 : L H)) :
    Continuous (p05IsometricConjHom V hV) := by
  have hcoe : (p05IsometricConjHom V hV : L H → L K) =
      p05IsometricConjLM V := rfl
  rw [hcoe]
  exact (p05IsometricConjLM V).continuous_of_finiteDimensional

private lemma p05QuasispectrumFinite
    {H : Type u} [Qudit H] (A : L H) :
    (quasispectrum ℝ A).Finite := by
  have hC : (spectrum ℂ A).Finite := Module.End.finite_spectrum A
  have hR : (spectrum ℝ A).Finite := by
    rw [(spectrum.preimage_algebraMap ℂ (a := A)).symm]
    exact hC.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  rw [quasispectrum_eq_spectrum_union_zero]
  exact hR.union (Set.finite_singleton 0)

theorem rpow_isometric_conj_of_ne_zero :
∀ {H K : Type u} [Qudit H] [Qudit K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {A : L H} {p : ℝ}, 0 ≤ A → p ≠ 0 →
  CFC.rpow ((V.comp A).comp (LinearMap.adjoint V)) p =
    (V.comp (CFC.rpow A p)).comp (LinearMap.adjoint V) := by
  intro H K _ _ V hV A p hA hp
  let phi : L H →⋆ₙₐ[ℂ] L K := p05IsometricConjHom V hV
  have hphiCont : Continuous phi := p05IsometricConjHomContinuous V hV
  have hphiApply : ∀ X : L H,
      phi X = (V.comp X).comp (LinearMap.adjoint V) := fun _ ↦ rfl
  have hphiNN : (0 : L K) ≤ phi A := by
    rw [hphiApply, LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hA).conj_adjoint V
  let f : ℝ → ℝ := fun x ↦ x ^ p
  have hf0 : f 0 = 0 := by simp [f, Real.zero_rpow hp]
  have hVA : phi A =
      (V.comp A).comp (LinearMap.adjoint V) := hphiApply A
  have hrpowOmega : CFC.rpow A p = cfc f A :=
    CFC.rpow_eq_cfc_real (ha := hA)
  have hrpowVOmega :
      CFC.rpow ((V.comp A).comp (LinearMap.adjoint V)) p =
        cfc f ((V.comp A).comp (LinearMap.adjoint V)) := by
    have h := CFC.rpow_eq_cfc_real (a := phi A) (y := p) (ha := hphiNN)
    rw [hVA] at h
    exact h
  rw [hrpowOmega, hrpowVOmega]
  have hcontOmega : ContinuousOn f (quasispectrum ℝ A) :=
    (p05QuasispectrumFinite A).continuousOn _
  have hcontVOmega : ContinuousOn f (quasispectrum ℝ (phi A)) :=
    (p05QuasispectrumFinite (phi A)).continuousOn _
  have hcnOmega : cfcₙ f A = cfc f A :=
    cfcₙ_eq_cfc hcontOmega hf0
  have hcnVOmega : cfcₙ f (phi A) = cfc f (phi A) :=
    cfcₙ_eq_cfc hcontVOmega hf0
  have hmap : phi (cfcₙ f A) = cfcₙ f (phi A) :=
    NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) phi f A
      hcontOmega hf0 hphiCont
      (IsSelfAdjoint.of_nonneg hA) (IsSelfAdjoint.of_nonneg hphiNN)
  change cfc f ((V.comp A).comp (LinearMap.adjoint V)) =
    (V.comp (cfc f A)).comp (LinearMap.adjoint V)
  rw [← hVA, ← hcnVOmega, ← hmap, hcnOmega, hphiApply]

end RenyiDPI
