/-
Trace norm and Hilbert--Schmidt norm of Hermitian operators: for a Hermitian `M`,
`T₁(M) = Σ_i |λ_i(M)|`, the maximum of `Re Tr (K M)` over Hermitian contractions
`−I ≤ K ≤ I` is `T₁(M)`, attained at `K = sign(M)`, and `T₁`, `H₂` are finite and continuous
(cf. Gour §7.7).
-/

import Quantum.QuantumEntropy.CFCDerivLMCompat.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesCollisionDefinitions.GSLCore
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

namespace GourConditionalEntropy

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

private theorem w40h26a_cfc_eigenvector {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) (f : ℝ → ℝ)
    (i : Fin (Module.finrank ℂ H)) :
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    cfc f M (hsym.eigenvectorBasis rfl i) =
      (f (hsym.eigenvalues rfl i) : ℂ) • hsym.eigenvectorBasis rfl i := by
  dsimp only
  let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
  apply SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm hM f
    (hsym.apply_eigenvectorBasis rfl i)
  exact SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm
    (hsym.hasEigenvector_eigenvectorBasis rfl i).2
    (hsym.apply_eigenvectorBasis rfl i)

private theorem w40h26a_trace_cfc {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) (f : ℝ → ℝ) :
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    (Tr (cfc f M)).re = ∑ i, f (hsym.eigenvalues rfl i) := by
  classical
  dsimp only
  let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
  rw [LinearMap.trace_eq_sum_inner _ (hsym.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [w40h26a_cfc_eigenvector M hM f i, inner_smul_right]
  simp

private theorem w40h26a_trace_mul_spectral {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) (K : L H) :
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    (Tr (K * M)).re = ∑ i, hsym.eigenvalues rfl i *
      (inner ℂ (hsym.eigenvectorBasis rfl i) (K (hsym.eigenvectorBasis rfl i))).re := by
  classical
  dsimp only
  let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
  rw [LinearMap.trace_eq_sum_inner _ (hsym.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, hsym.apply_eigenvectorBasis rfl i, map_smul,
    inner_smul_right]
  simp

private theorem w40h26a_contraction_diagonal {H : Type u} [Qudit.{u} H]
    (K : L H) (hlo : -(1 : L H) ≤ K) (hhi : K ≤ 1)
    (v : H) (hv : inner ℂ v v = 1) :
    -1 ≤ (inner ℂ v (K v)).re ∧ (inner ℂ v (K v)).re ≤ 1 := by
  have h₁ := ((LinearMap.nonneg_iff_isPositive _).mp
    (sub_nonneg.mpr hlo)).re_inner_nonneg_right v
  have h₂ := ((LinearMap.nonneg_iff_isPositive _).mp
    (sub_nonneg.mpr hhi)).re_inner_nonneg_right v
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.one_apply,
    inner_sub_right, inner_neg_right, hv, map_sub, map_neg] at h₁ h₂
  change 0 ≤ (inner ℂ v (K v)).re - -1 at h₁
  change 0 ≤ 1 - (inner ℂ v (K v)).re at h₂
  constructor <;> linarith

private theorem w40h26a_trace_norm_spectral {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) :
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    w40T₁ M = ∑ i, |hsym.eigenvalues rfl i| := by
  change (Tr (CFC.abs M)).re = _
  rw [CFC.abs_eq_cfc_norm M hM, w40h26a_trace_cfc M hM]
  simp only [Real.norm_eq_abs]

private theorem w40h26a_trace_contraction_bound {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) (K : L H)
    (hlo : -(1 : L H) ≤ K) (hhi : K ≤ 1) :
    (Tr (K * M)).re ≤ w40T₁ M := by
  classical
  rw [w40h26a_trace_mul_spectral M hM K, w40h26a_trace_norm_spectral M hM]
  apply Finset.sum_le_sum
  intro i _
  let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
  let v := hsym.eigenvectorBasis rfl i
  have hv : inner ℂ v v = 1 := by simp [v]
  have hb := abs_le.mpr (w40h26a_contraction_diagonal K hlo hhi v hv)
  calc
    _ ≤ |hsym.eigenvalues rfl i * (inner ℂ v (K v)).re| := le_abs_self _
    _ = |hsym.eigenvalues rfl i| * |(inner ℂ v (K v)).re| := abs_mul _ _
    _ ≤ |hsym.eigenvalues rfl i| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := mul_one _

private theorem w40h26a_sign_contraction {H : Type u} [Qudit.{u} H] (M : L H) :
    let S := cfc (fun x : ℝ => if x = 0 then 0 else if x < 0 then -1 else 1) M
    IsSelfAdjoint S ∧ -(1 : L H) ≤ S ∧ S ≤ 1 := by
  dsimp only
  refine ⟨cfc_predicate _ _, ?_, ?_⟩
  · have h := cfc_le_one
      (fun x : ℝ => -(if x = 0 then 0 else if x < 0 then -1 else 1)) M (by
        intro x _
        dsimp only
        split_ifs <;> norm_num)
    rw [cfc_neg] at h
    simpa only [neg_neg] using neg_le_neg h
  · apply cfc_le_one
    intro x _
    dsimp only
    split_ifs <;> norm_num

private theorem w40h26a_sign_mul_scalar (x : ℝ) :
    x * (if x = 0 then 0 else if x < 0 then -1 else 1) = |x| := by
  split_ifs with h₀ hneg
  · simp [h₀]
  · simp [abs_of_neg hneg]
  · simp [abs_of_nonneg (le_of_not_gt hneg)]

private theorem w40h26a_sign_attains {H : Type u} [Qudit.{u} H] [Nontrivial H]
    (M : L H) (hM : IsSelfAdjoint M) :
    (Tr (cfc (fun x : ℝ => if x = 0 then 0 else if x < 0 then -1 else 1) M * M)).re =
      w40T₁ M := by
  classical
  rw [w40h26a_trace_mul_spectral M hM, w40h26a_trace_norm_spectral M hM]
  apply Finset.sum_congr rfl
  intro i _
  rw [w40h26a_cfc_eigenvector M hM _ i, inner_smul_right]
  simp only [OrthonormalBasis.inner_eq_ite, ite_true, mul_one, Complex.ofReal_re]
  exact w40h26a_sign_mul_scalar _

theorem w40_trace_norm_spectral_variational : ∀ {H : Type u} [Qudit.{u} H]
    [Nontrivial H] (M : L H) (hM : IsSelfAdjoint M),
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    w40T₁ M = ∑ i, |hsym.eigenvalues (rfl : Module.finrank ℂ H = Module.finrank ℂ H) i| ∧
    (∀ K : L H, IsSelfAdjoint K → -(1 : L H) ≤ K → K ≤ 1 →
      (Tr (K * M)).re ≤ w40T₁ M) ∧
    (let S := cfc (fun x : ℝ => if x = 0 then 0 else if x < 0 then -1 else 1) M
    IsSelfAdjoint S ∧ -(1 : L H) ≤ S ∧ S ≤ 1 ∧ (Tr (S * M)).re = w40T₁ M) := by
  intro H _ _ M hM
  refine ⟨w40h26a_trace_norm_spectral M hM, ?_, ?_⟩
  · intro K _ hlo hhi
    exact w40h26a_trace_contraction_bound M hM K hlo hhi
  · exact ⟨(w40h26a_sign_contraction M).1, (w40h26a_sign_contraction M).2.1,
      (w40h26a_sign_contraction M).2.2, w40h26a_sign_attains M hM⟩

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

/-- The Hilbert--Schmidt norm is continuous on the whole operator space. -/
private theorem w40H₂_continuous_aux {H : Type u} [Qudit.{u} H] :
    Continuous (fun M : L H => w40H₂ M) :=
  Real.continuous_sqrt.comp (continuous_re_trace_lm.comp (continuous_star.mul continuous_id))

theorem w40_trace_norm_continuity : ∀ {H : Type u} [Qudit.{u} H]
    [Nontrivial H],
    Continuous (fun M : {X : L H // IsSelfAdjoint X} => w40T₁ M.1) ∧
    Continuous (fun M : {X : L H // IsSelfAdjoint X} => w40H₂ M.1) := by
  intro H _ _
  letI : FiniteDimensional ℝ (selfAdjoint (L H)) :=
    FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (L H)).subtype
      Subtype.val_injective
  have hconvex : ConvexOn ℝ Set.univ
      (fun M : selfAdjoint (L H) => w40T₁ M.1) := by
    refine ⟨convex_univ, ?_⟩
    intro X _ Y _ a b ha hb _
    let Z : selfAdjoint (L H) := a • X + b • Y
    let S := cfc (fun x : ℝ => if x = 0 then 0 else if x < 0 then -1 else 1) Z.1
    have hmax : IsSelfAdjoint S ∧ -(1 : L H) ≤ S ∧ S ≤ 1 ∧
        (Tr (S * Z.1)).re = w40T₁ Z.1 :=
          ((GourConditionalEntropy.w40_trace_norm_spectral_variational.{u}) Z.1 Z.2).2.2
    have hX := ((GourConditionalEntropy.w40_trace_norm_spectral_variational.{u}) X.1 X.2).2.1 S
      hmax.1 hmax.2.1 hmax.2.2.1
    have hY := ((GourConditionalEntropy.w40_trace_norm_spectral_variational.{u}) Y.1 Y.2).2.1 S
      hmax.1 hmax.2.1 hmax.2.2.1
    calc
      w40T₁ (a • X + b • Y).1 = (Tr (S * Z.1)).re := hmax.2.2.2.symm
      _ = a * (Tr (S * X.1)).re + b * (Tr (S * Y.1)).re := by
        change (Tr (S * (a • X.1 + b • Y.1))).re = _
        simp only [mul_add, mul_smul_comm, map_add, ← Complex.coe_smul,
          map_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
      _ ≤ a • w40T₁ X.1 + b • w40T₁ Y.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
  refine ⟨continuousOn_univ.mp (hconvex.continuousOn isOpen_univ), ?_⟩
  exact w40H₂_continuous_aux.comp continuous_subtype_val

end

end GourConditionalEntropy
