import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorBridge

/-! Linear-map wrappers for the canonical continuous-linear tensor CFC API. -/
namespace TensorCFC
open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder NNReal
universe u u₁ u₂
variable {ℋ : Type u} [Qudit ℋ]

private lemma jc_toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

/-- The canonical operator equivalence preserves the `ℝ≥0`-spectrum. -/
private lemma lm_spectrum_nnreal_linearToContinuous (X : L ℋ) :
    spectrum NNReal (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X) =
      spectrum NNReal X := by
  letI : IsScalarTower NNReal ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower NNReal ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  exact AlgEquiv.spectrum_eq
    ((QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ).toAlgEquiv.restrictScalars NNReal) X

/-- The canonical operator equivalence commutes with a `ℝ≥0`-CFC that is continuous on the
spectrum of a nonnegative operator. -/
private lemma lm_linearToContinuous_cfc_nnreal_of_continuousOn (X : L ℋ)
    (f : NNReal → NNReal) (hX : 0 ≤ X) (hf : ContinuousOn f (spectrum NNReal X)) :
    QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ (cfc f X) =
      cfc f (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X) := by
  letI : IsScalarTower NNReal ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower NNReal ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  exact StarAlgHomClass.map_cfc (R := NNReal) (S := ℂ)
    (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ) f X hf
    (StarAlgEquiv.isometry _).continuous hX
    ((ContinuousLinearMap.coe_le_coe_iff (0 : B ℋ) X.toContinuousLinearMap).mp hX)

/-- The canonical operator equivalence commutes with every `ℝ≥0`-CFC (totalized). -/
private lemma lm_linearToContinuous_cfc_nnreal (X : L ℋ)
    (f : NNReal → NNReal) :
    QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ (cfc f X) =
      cfc f (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X) := by
  by_cases hX : 0 ≤ X
  · by_cases hf : ContinuousOn f (spectrum NNReal X)
    · exact lm_linearToContinuous_cfc_nnreal_of_continuousOn X f hX hf
    · rw [cfc_apply_of_not_continuousOn X hf, cfc_apply_of_not_continuousOn _
        (by rwa [lm_spectrum_nnreal_linearToContinuous]), map_zero]
  · rw [cfc_apply_of_not_predicate X hX,
      cfc_apply_of_not_predicate (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X)
        (fun heX => hX
          ((ContinuousLinearMap.coe_le_coe_iff (0 : B ℋ) X.toContinuousLinearMap).mpr heX)),
      map_zero]

lemma rpow_toContinuousLinearMap_lm (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p :=
  lm_linearToContinuous_cfc_nnreal A _

lemma rpow_toLinearMap_lm (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := rpow_toContinuousLinearMap_lm A.toLinearMap p
  rw [jc_toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

variable {ℋ₁ : Type u₁} {ℋ₂ : Type u₂} [Qudit ℋ₁] [Qudit ℋ₂]

theorem rpow_tensorProduct_lm (A : L ℋ₁) (B : L ℋ₂) (p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) := by
  have hAc : (0 : ℋ₁ →L[ℂ] ℋ₁) ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff
      (0 : ℋ₁ →L[ℂ] ℋ₁) A.toContinuousLinearMap).mp hA
  have hBc : (0 : ℋ₂ →L[ℂ] ℋ₂) ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff
      (0 : ℋ₂ →L[ℂ] ℋ₂) B.toContinuousLinearMap).mp hB
  have h := TensorCFC.rpow_tensorProduct
    A.toContinuousLinearMap B.toContinuousLinearMap p hAc hBc
  have h' := congrArg ContinuousLinearMap.toLinearMap h
  simpa only [rpow_toLinearMap_lm] using h'


end TensorCFC
