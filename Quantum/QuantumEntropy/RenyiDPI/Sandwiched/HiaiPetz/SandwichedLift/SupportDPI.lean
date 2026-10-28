import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SandwichedLift.FaithfulBound
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SandwichedLift.FaithfulDivLimit

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem s16_parameterFilter_neBot :
    (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (𝓝[>] (0 : ℝ))).NeBot := by
  apply Filter.comap_coe_neBot_of_le_principal
  exact Filter.le_principal_iff.mpr (Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))

theorem sandwichedRenyiDiv_le_of_support_core :
SandwichedMonotoneOnPosDefGt.{u} →
  ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (E : CPTP H K) {α : ℝ} {ρ σ : L H},
  1 < α → 0 ≤ ρ → 0 ≤ σ → SupportLE ρ σ → ρ ≠ 0 →
  sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  intro hcore H K _ _ _ _ E α ρ σ hα hρ hσ hsupp hρ0
  have hσ0 : σ ≠ 0 := by
    intro hzero
    apply hρ0
    ext x
    exact hsupp (by simp [hzero])
  haveI := s16_parameterFilter_neBot
  apply le_of_tendsto (RenyiDPI.sandwichedRenyiDiv_tendsto_faithful_gt E hα hρ hσ hσ0 hρ0
    (supportLE_map_of_cptp E hρ hσ hsupp))
  exact Filter.Eventually.of_forall fun l =>
    RenyiDPI.sandwichedRenyiDiv_faithfulApprox_le_of_core hcore E hα hρ hσ hρ0 hsupp
      l.property.1 l.property.2

end RenyiDPI
