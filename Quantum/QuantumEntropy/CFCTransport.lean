import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.OperatorBridge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Transport of continuous functional calculus

Continuous functional calculus on finite-dimensional linear endomorphisms agrees with
continuous functional calculus on their associated bounded operators. This module
transports real powers and logarithms along that identification for entropy proofs.
-/
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

/-- The totalized real-power CFC commutes with the canonical operator equivalence. -/
theorem cfc_rpow_toCLM {ℋ : Type u} [Qudit ℋ] (X : L ℋ) (p : ℝ) :
    (CFC.rpow X p).toContinuousLinearMap = CFC.rpow X.toContinuousLinearMap p := by
  let e := QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ
  letI : IsScalarTower NNReal ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower NNReal ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eNN : L ℋ ≃ₐ[NNReal] B ℋ := e.toAlgEquiv.restrictScalars NNReal
  change e (cfc (fun x : NNReal => x ^ p) X) =
    cfc (fun x : NNReal => x ^ p) (e X)
  by_cases hX : 0 ≤ X
  · have heX : (0 : B ℋ) ≤ e X := by
      exact (ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) X.toContinuousLinearMap).mp hX
    by_cases hf : ContinuousOn (fun x : NNReal => x ^ p) (spectrum NNReal X)
    · exact StarAlgHomClass.map_cfc (R := NNReal) (S := ℂ) e _ X hf
        (StarAlgEquiv.isometry e).continuous hX heX
    · have hf' : ¬ ContinuousOn (fun x : NNReal => x ^ p)
          (spectrum NNReal (e X)) := by
        rw [show e X = eNN X from rfl, AlgEquiv.spectrum_eq eNN X]
        exact hf
      rw [cfc_apply_of_not_continuousOn X hf,
        cfc_apply_of_not_continuousOn (e X) hf', map_zero]
  · have heX : ¬ (0 : B ℋ) ≤ e X := by
      intro heX
      exact hX ((ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) X.toContinuousLinearMap).mpr heX)
    rw [cfc_apply_of_not_predicate X hX,
      cfc_apply_of_not_predicate (e X) heX, map_zero]

end CFCTransport
