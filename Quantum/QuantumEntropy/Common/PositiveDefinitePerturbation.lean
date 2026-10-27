import Quantum.QuantumEntropy.Common.TracePositiveDefinite

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-- Sum of non-negative and positive-definite is positive-definite. -/
lemma pdSetLM_add_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : B ∈ pdSetLM (ℋ := ℋ)) :
    (A + B) ∈ pdSetLM (ℋ := ℋ) := by
  change (A + B).toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
  apply (pdSet_membership_certificate _).2
  exact IsStrictlyPositive.nonneg_add
    ((ContinuousLinearMap.coe_le_coe_iff
      (0 : ℋ →L[ℂ] ℋ) A.toContinuousLinearMap).1 hA)
    ((pdSet_membership_certificate B.toContinuousLinearMap).1 hB)

/-- The scalar operator `ε • 1` is positive-definite for `ε > 0` real. -/
lemma pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) := by
  set τ : L ℋ := (ε : ℂ) • (1 : L ℋ) with hτ_def
  have hε_ne_complex : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hε_nn_complex : (0 : ℂ) ≤ (ε : ℂ) := Complex.zero_le_real.mpr hε.le
  have h_isPos : τ.IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hε_nn_complex
  have h_nn : (0 : L ℋ) ≤ τ :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  have h_unit : IsUnit τ := by
    refine ⟨⟨τ, ((ε : ℂ))⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [hτ_def, smul_mul_smul_comm, mul_inv_cancel₀ hε_ne_complex, mul_one, one_smul]
    · rw [hτ_def, smul_mul_smul_comm, inv_mul_cancel₀ hε_ne_complex, mul_one, one_smul]
  apply (pdSetLM_strictPositivity_certificate _).2
  exact h_unit.isStrictlyPositive h_nn

/-- For non-negative `A` and `ε > 0`, the perturbation `A + ε • 1` is pd. -/
lemma nonneg_add_pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
  pdSetLM_add_nonneg hA (pos_smul_one_pdSetLM hε)

end SandwichedRenyiRelativeEntropy
