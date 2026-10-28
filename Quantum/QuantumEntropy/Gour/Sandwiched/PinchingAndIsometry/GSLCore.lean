/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.PetzRenyiFiniteAdditivity.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)


/-!
# Standard sandwiched Rényi divergence and isometric conjugation

`standardSandwichedRenyiBitsFinite` is the finite-order standard sandwiched divergence with
explicit extended-value dispatch.  Isometric conjugation is defined first from a raw linear
isometry (by a private auxiliary map) and then bundled as the CPTP channel
`isometricConjugationChannel`.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder NNReal Topology


universe u v w

/-! ## finite standard API -/

/-- The standard finite-order sandwiched Rényi divergence in bits.

The order-one branch and both extended-value branches are dispatched before
the raw real logarithm is evaluated.  In particular, orthogonal states for
`alpha < 1` never fall through Lean's convention `Real.log 0 = 0`.

The value at `alpha = 1` is only a totalization sentinel outside the formal
finite-order domain; it is not the Umegaki order-one endpoint of the all-order API. -/
noncomputable def standardSandwichedRenyiBitsFinite
    {H : Type u} [Qudit H] [Nontrivial H]
    (alpha : ℝ) (rho sigma : L H) : EReal :=
  letI : Decidable ((1 < alpha ∧ ¬ suppLE rho sigma) ∨
      (alpha < 1 ∧ rho ≠ 0 ∧ (sandwichedQuasi alpha rho sigma).re = 0)) :=
    Classical.propDecidable _
  if alpha = 1 then 0
  else if (1 < alpha ∧ ¬ suppLE rho sigma) ∨
      (alpha < 1 ∧ rho ≠ 0 ∧ (sandwichedQuasi alpha rho sigma).re = 0) then
    ⊤
  else
    (((1 / (alpha - 1)) *
      Real.logb 2 ((sandwichedQuasi alpha rho sigma).re / (Tr rho).re) : ℝ) : EReal)

/-! ## raw isometry and channel wrapper -/

/-- The non-unital star homomorphism induced by a raw isometry. -/
private noncomputable def b1IsometricConjHom
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K)
    (hV : (LinearMap.adjoint V).comp V = (1 : L H)) :
    L H →⋆ₙₐ[ℂ] L K where
  toFun X := (V.comp X).comp (LinearMap.adjoint V)
  map_add' X Y := by
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c X := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
    simp
  map_zero' := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp]
  map_mul' X Y := by
    ext x
    have h_id : ∀ y : H, (LinearMap.adjoint V) (V y) = y := fun y => by
      have h := LinearMap.congr_fun hV y
      simpa [LinearMap.comp_apply] using h
    change V (X (Y ((LinearMap.adjoint V) x))) =
      V (X ((LinearMap.adjoint V) (V (Y ((LinearMap.adjoint V) x)))))
    rw [h_id]
  map_star' X := by
    rw [show (star X : L H) = LinearMap.adjoint X from LinearMap.star_eq_adjoint X,
      show (star ((V.comp X).comp (LinearMap.adjoint V)) : L K) =
        LinearMap.adjoint ((V.comp X).comp (LinearMap.adjoint V)) from
        LinearMap.star_eq_adjoint _,
      LinearMap.adjoint_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, ← LinearMap.comp_assoc]

private theorem b1Trace_isometricConj
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K) (hV : (LinearMap.adjoint V).comp V = (1 : L H))
    (X : L H) :
    Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X := by
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc, hV]
  rfl

/-- The CPTP channel explicitly constructed from a raw isometry. -/
noncomputable def isometricConjugationChannel
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K)
    (hV : (LinearMap.adjoint V).comp V = (1 : L H)) : CPTP H K where
  toFun := krausTerm V
  map_add' := (krausTerm V).map_add
  map_smul' := (krausTerm V).map_smul
  map_cstarMatrix_nonneg' k M hM := by
    exact (isCompletelyPositive_iff_cstarMatrix_nonneg _).mp
      (krausTerm_isCompletelyPositive V) k M hM
  trace_map X := by
    change Tr X = Tr ((V.comp X).comp (LinearMap.adjoint V))
    exact (b1Trace_isometricConj V hV X).symm

@[simp]
theorem isometricConjugationChannel_apply
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (V : H →ₗ[ℂ] K)
    (hV : (LinearMap.adjoint V).comp V = (1 : L H)) (X : L H) :
    (isometricConjugationChannel V hV).toFun X =
      (V.comp X).comp (LinearMap.adjoint V) := rfl

private theorem b1Rpow_apply_densityEigenvector
    {H : Type u} [Qudit H] [Nontrivial H]
    {tau : L H} (htau : IsDensity tau) (p : ℝ)
    (i : Fin (Module.finrank ℂ H)) :
    CFC.rpow tau p (htau.1.isSymmetric.eigenvectorBasis rfl i) =
      (((htau.1.isSymmetric.eigenvalues rfl i) ^ p : ℝ) : ℂ) •
        htau.1.isSymmetric.eigenvectorBasis rfl i := by
  have heq : CFC.rpow tau p = cfc (fun x : ℝ => x ^ p) tau := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real
      (ha := (LinearMap.nonneg_iff_isPositive _).mpr htau.1)
  rw [heq]
  exact cfc_real_apply_eigenvector_lm htau.1.isSelfAdjoint (fun x : ℝ => x ^ p)
    (htau.1.isSymmetric.apply_eigenvectorBasis rfl i)
    (mem_spectrum_real_of_eigenvector_lm
      ((htau.1.isSymmetric.eigenvectorBasis rfl).orthonormal.ne_zero i)
      (htau.1.isSymmetric.apply_eigenvectorBasis rfl i))

/-- The raw quasi-entropy of any, possibly singular, density operator with
itself equals one for every positive order. -/
theorem sandwichedQuasi_self_density
    {H : Type u} [Qudit H] [Nontrivial H]
    {alpha : ℝ} (halpha : 0 < alpha)
    (tau : L H) (htau : IsDensity tau) :
    sandwichedQuasi alpha tau tau = 1 := by
  let b := htau.1.isSymmetric.eigenvectorBasis
    (n := Module.finrank ℂ H) rfl
  let eig := htau.1.isSymmetric.eigenvalues
    (n := Module.finrank ℂ H) rfl
  let beta : ℝ := (1 - alpha) / (2 * alpha)
  have heigNonneg : ∀ i, 0 ≤ eig i := fun i => htau.1.nonneg_eigenvalues rfl i
  have hmiddle : CFC.rpow tau beta * tau * CFC.rpow tau beta =
      CFC.rpow tau (1 / alpha) := by
    have hbapply (i : Fin (Module.finrank ℂ H)) :
        (CFC.rpow tau beta * tau * CFC.rpow tau beta) (b i) =
          CFC.rpow tau (1 / alpha) (b i) := by
      rw [Module.End.mul_apply, Module.End.mul_apply,
        b1Rpow_apply_densityEigenvector htau beta i,
        map_smul,
        htau.1.isSymmetric.apply_eigenvectorBasis rfl i,
        map_smul, map_smul,
        b1Rpow_apply_densityEigenvector htau beta i,
        b1Rpow_apply_densityEigenvector htau (1 / alpha) i]
      rw [smul_smul, smul_smul]
      congr 1
      change (((eig i) ^ beta : ℝ) : ℂ) * (eig i : ℂ) *
          (((eig i) ^ beta : ℝ) : ℂ) =
        (((eig i) ^ (1 / alpha) : ℝ) : ℂ)
      norm_cast
      by_cases hi : eig i = 0
      · rw [hi, Real.zero_rpow (ne_of_gt (one_div_pos.mpr halpha))]
        simp
      · have hiPos : 0 < eig i := lt_of_le_of_ne (heigNonneg i) (Ne.symm hi)
        calc
          (eig i) ^ beta * eig i * (eig i) ^ beta =
              (eig i) ^ beta * (eig i) ^ (1 : ℝ) * (eig i) ^ beta := by
                exact congrArg (fun z : ℝ => (eig i) ^ beta * z * (eig i) ^ beta)
                  (Real.rpow_one (eig i)).symm
          _ = (eig i) ^ (beta + 1 + beta) := by
                rw [Real.rpow_add hiPos, Real.rpow_add hiPos]
          _ = (eig i) ^ (1 / alpha) := by
                congr 1
                dsimp [beta]
                field_simp [ne_of_gt halpha]
                ring
    apply LinearMap.ext
    intro x
    rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, hbapply]
  have houter : CFC.rpow (CFC.rpow tau (1 / alpha)) alpha = tau := by
    change (tau ^ (1 / alpha)) ^ alpha = tau
    rw [CFC.rpow_rpow_of_exponent_nonneg tau (1 / alpha) alpha
      (by positivity) halpha.le
      ((LinearMap.nonneg_iff_isPositive _).mpr htau.1)]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt halpha),
      CFC.rpow_one tau ((LinearMap.nonneg_iff_isPositive _).mpr htau.1)]
  unfold sandwichedQuasi
  change Tr (CFC.rpow
    (CFC.rpow tau beta * tau * CFC.rpow tau beta) alpha) = 1
  rw [hmiddle, houter, htau.2]

end SandwichedRenyiRelativeEntropy
