import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.MatrixVocabulary
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.MatrixTransport
import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive
import Quantum.TraceInequality.LiebTrace.Monotonicity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.DirectToConcavity
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem s02_matrix_posDef {H : Type u} [Qudit H]
    {A : L H} (hA : A ∈ pdSetLM (ℋ := H)) :
    Matrix.PosDef (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) A) := by
  let e := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)
  have h := (pdSetLM_strictPositivity_certificate A).1 hA
  have hM : (e A).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℂ H)).2
      ((LinearMap.nonneg_iff_isPositive A).1 h.nonneg)
  exact hM.posDef_iff_isUnit.mpr (h.isUnit.map e)

private theorem s02_pd_convexCombo {H : Type u} [Qudit H] [Nontrivial H]
    {A₁ A₂ : L H} {θ : ℝ}
    (hA₁ : A₁ ∈ pdSetLM (ℋ := H)) (hA₂ : A₂ ∈ pdSetLM (ℋ := H))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) • A₁ + θ • A₂ ∈ pdSetLM (ℋ := H) := by
  change ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap ∈ pdSet
  have heq : ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap =
      (1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap := by
    ext x
    rfl
  rw [heq]
  exact pdSet_convexCombo hA₁ hA₂ hθ0 hθ1

theorem liebConcavityPD_hiaiPetz :
LiebConcavityPD.{u} := by
  intro H _ _ p hp0 hp1 K A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hM : MatrixLiebConcavity p :=
    RenyiDPI.matrixLiebConcavity_of_direct
    HiaiPetz.TraceMonotonicity.directTracePowerStrictlyPositive hp0 hp1
  have hA := s02_pd_convexCombo hA₁ hA₂ hθ0 hθ1
  have hB := s02_pd_convexCombo hB₁ hB₂ hθ0 hθ1
  rw [liebTraceMapLM_eq_matrix_liebTracePower p K A₁ B₁ hA₁ hB₁,
    liebTraceMapLM_eq_matrix_liebTracePower p K A₂ B₂ hA₂ hB₂,
    liebTraceMapLM_eq_matrix_liebTracePower p K _ _ hA hB]
  have h := hM (star (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) K))
    (t := 1 - θ) ⟨sub_nonneg.mpr hθ1, sub_le_self _ hθ0⟩
    (s02_matrix_posDef hA₁) (s02_matrix_posDef hA₂)
    (s02_matrix_posDef hB₁) (s02_matrix_posDef hB₂)
  simpa only [sub_sub_cancel, smul_eq_mul, map_add,
    ← Complex.coe_smul, map_smul] using h

end RenyiDPI
