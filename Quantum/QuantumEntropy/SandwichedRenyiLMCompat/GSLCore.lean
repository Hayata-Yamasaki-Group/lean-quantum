import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.TraceInequality.LiebTrace.Monotonicity

/-! Compatibility for positive-definite linear-map convex combinations. -/
namespace SandwichedRenyiRelativeEntropy
open QuantumState
variable {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]

theorem pdSetLM_convexCombo {A₁ A₂ : L ℋ} (hA₁ : A₁ ∈ pdSetLM (ℋ := ℋ))
    (hA₂ : A₂ ∈ pdSetLM (ℋ := ℋ)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) • A₁ + θ • A₂ ∈ pdSetLM (ℋ := ℋ) := by
  dsimp [pdSetLM] at hA₁ hA₂ ⊢
  have heq : ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap =
      (1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap := by
    ext x
    rfl
  rw [heq]
  exact LiebAndoTrace.pdSet_convexCombo hA₁ hA₂ hθ0 hθ1
omit [Nontrivial ℋ] in
lemma pdSetLM_pos_smul
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • A) ∈ pdSetLM (ℋ := ℋ) := by
  apply (pdSetLM_strictPositivity_certificate _).2
  rw [Complex.coe_smul]
  exact IsStrictlyPositive.smul hc ((pdSetLM_strictPositivity_certificate A).1 hA)

end SandwichedRenyiRelativeEntropy
