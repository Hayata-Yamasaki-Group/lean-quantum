import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.OperatorBridge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
namespace CFCTransport
open QuantumState

universe u

/-- The totalized logarithmic CFC commutes with the canonical operator equivalence. -/
theorem cfc_log_toCLM {ℋ : Type u} [Qudit ℋ] (X : L ℋ) :
    (CFC.log X).toContinuousLinearMap = CFC.log X.toContinuousLinearMap := by
  let e := QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eR : L ℋ ≃ₐ[ℝ] B ℋ := e.toAlgEquiv.restrictScalars ℝ
  change e (cfc Real.log X) = cfc Real.log (e X)
  by_cases hX : IsSelfAdjoint X
  · have heX : IsSelfAdjoint (e X) := hX.map e
    by_cases hf : ContinuousOn Real.log (spectrum ℝ X)
    · exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) e _ X hf
        (StarAlgEquiv.isometry e).continuous hX heX
    · have hf' : ¬ ContinuousOn Real.log (spectrum ℝ (e X)) := by
        rw [show e X = eR X from rfl, AlgEquiv.spectrum_eq eR X]
        exact hf
      rw [cfc_apply_of_not_continuousOn X hf,
        cfc_apply_of_not_continuousOn (e X) hf', map_zero]
  · have heX : ¬ IsSelfAdjoint (e X) := by
      intro heX
      apply hX
      simpa using heX.map e.symm
    rw [cfc_apply_of_not_predicate X hX,
      cfc_apply_of_not_predicate (e X) heX, map_zero]

/-- The canonical operator equivalence preserves the `ℝ≥0`-spectrum. -/
private lemma spectrum_nnreal_linearToContinuous {ℋ : Type u} [Qudit ℋ] (X : L ℋ) :
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
private lemma linearToContinuous_cfc_nnreal_of_continuousOn {ℋ : Type u} [Qudit ℋ] (X : L ℋ)
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
private lemma linearToContinuous_cfc_nnreal {ℋ : Type u} [Qudit ℋ] (X : L ℋ)
    (f : NNReal → NNReal) :
    QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ (cfc f X) =
      cfc f (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X) := by
  by_cases hX : 0 ≤ X
  · by_cases hf : ContinuousOn f (spectrum NNReal X)
    · exact linearToContinuous_cfc_nnreal_of_continuousOn X f hX hf
    · rw [cfc_apply_of_not_continuousOn X hf, cfc_apply_of_not_continuousOn _
        (by rwa [spectrum_nnreal_linearToContinuous]), map_zero]
  · rw [cfc_apply_of_not_predicate X hX,
      cfc_apply_of_not_predicate (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ X)
        (fun heX => hX
          ((ContinuousLinearMap.coe_le_coe_iff (0 : B ℋ) X.toContinuousLinearMap).mpr heX)),
      map_zero]

/-- The totalized real-power CFC commutes with the canonical operator equivalence. -/
theorem cfc_rpow_toCLM {ℋ : Type u} [Qudit ℋ] (X : L ℋ) (p : ℝ) :
    (CFC.rpow X p).toContinuousLinearMap = CFC.rpow X.toContinuousLinearMap p :=
  linearToContinuous_cfc_nnreal X _

end CFCTransport
