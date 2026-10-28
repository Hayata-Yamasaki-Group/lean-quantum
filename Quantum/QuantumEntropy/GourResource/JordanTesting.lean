/-
Shows positivity of the positive and negative parts of a Hermitian operator, reconstruction by their difference, and that their product is zero.
Source context: Gour, Theorem 11.4; Gour, Example 8.32; Hayashi–Yamasaki, Lemma S2.
-/
import Quantum.QuantumEntropy.GourResource.Definitions

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y26_positivePart_eq {A : Type u} [Qudit.{u} A]
    (X : L.{u} A) (hX : IsSelfAdjoint X) : positivePart X = X⁺ := by
  change (1 / 2 : ℝ) • (X + CFC.abs X) = X⁺
  rw [add_comm, CFC.abs_add_self X hX, two_smul]
  module

theorem gsl_y26 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : L.{u} A), X.IsSymmetric →
  (positivePart.{u} X).IsPositive ∧ (positivePart.{u} (-X)).IsPositive ∧
  X = positivePart.{u} X - positivePart.{u} (-X) ∧
  positivePart.{u} X * positivePart.{u} (-X) = 0
:= by
  intro A _ _ X hX
  have hsa : IsSelfAdjoint X := (LinearMap.isSymmetric_iff_isSelfAdjoint X).mp hX
  rw [gsl_y26_positivePart_eq X hsa, gsl_y26_positivePart_eq (-X) hsa.neg,
    CFC.posPart_neg]
  exact ⟨(LinearMap.nonneg_iff_isPositive _).mp (CFC.posPart_nonneg X),
    (LinearMap.nonneg_iff_isPositive _).mp (CFC.negPart_nonneg X),
    (CFC.posPart_sub_negPart X hsa).symm, CFC.posPart_mul_negPart X⟩

end GourResource

