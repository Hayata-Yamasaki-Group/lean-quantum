import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.IsometricQuasi
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.Common.TracePositiveDefinite

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem quasiVar_le_quasi_isometric_gt :
∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (V : H →ₗ[ℂ] K), (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H} {Z : L K},
  1 < α → 0 ≤ ρ → σ ∈ pdSetLM (ℋ := H) → 0 ≤ Z →
  (quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
    ((V.comp σ).comp (LinearMap.adjoint V)) Z).re ≤
      (sandwichedQuasi α ρ σ).re := by
  intro H K _ _ _ _ V hV α ρ σ Z hα hρ hσ hZ
  rw [quasiVar_isometric_conj_gt V hV hα (nonneg_of_pdSetLM hσ) hZ]
  exact (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα
    ((LinearMap.nonneg_iff_isPositive ρ).mp hρ)
    ((LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ))
    (((LinearMap.nonneg_iff_isPositive Z).mp hZ).adjoint_conj V)
    (isUnit_of_pdSetLM hσ))).1

private theorem pd_conj {H : Type u} [Qudit H] {A B : L H}
    (hA : A ∈ pdSetLM (ℋ := H)) (hB : IsUnit B) :
    star B * A * B ∈ pdSetLM (ℋ := H) := by
  exact (pdSetLM_strictPositivity_certificate _).2
    (hB.isStrictlyPositive_star_left_conjugate_iff.mpr
      ((pdSetLM_strictPositivity_certificate A).1 hA))

private theorem pd_rpow {H : Type u} [Qudit H] {A : L H}
    (hA : A ∈ pdSetLM (ℋ := H)) (p : ℝ) :
    CFC.rpow A p ∈ pdSetLM (ℋ := H) := by
  exact (pdSetLM_strictPositivity_certificate _).2
    (((pdSetLM_strictPositivity_certificate A).1 hA).rpow)

theorem exists_quasiVar_eq_quasi_pd_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ : L H},
  1 < α → ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
  ∃ Z ∈ pdSetLM (ℋ := H), quasiVar α ρ σ Z = sandwichedQuasi α ρ σ := by
  intro H _ _ α ρ σ hα hρ hσ
  refine ⟨quasiVarOpt α ρ σ, ?_, quasiVarOpt_eq_quasi_gt hα
    ((LinearMap.nonneg_iff_isPositive _).mp (nonneg_of_pdSetLM hρ))
    ((LinearMap.nonneg_iff_isPositive _).mp (nonneg_of_pdSetLM hσ))
    (isUnit_of_pdSetLM hσ)⟩
  rw [quasiVarOpt_eq_direct]
  have hP_unit := isUnit_of_pdSetLM (pd_rpow hσ ((1 - α) / (2 * α)))
  have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hZ := pd_conj (pd_rpow (pd_conj hρ hP_unit) (α - 1)) hP_unit
  simpa only [hP_sa.star_eq] using hZ

end RenyiDPI
