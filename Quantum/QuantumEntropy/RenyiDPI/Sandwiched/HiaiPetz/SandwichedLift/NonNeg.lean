import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SandwichedLift.SupportDPI
import Quantum.QuantumEntropy.RenyiDPI.Interface

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem sandwichedMonotoneOnNonNeg_of_posDefGt :
SandwichedMonotoneOnPosDefGt.{u} → SandwichedMonotoneOnNonNeg.{u} := by
  intro hcore H _ _ K _ _ E α ρ σ hα hρ hσ
  by_cases hρ0 : ρ = 0
  · subst ρ
    rw [show E.toFun (0 : L H) = 0 from E.toLinearMap.map_zero]
    simp [sandwichedRenyiDivNN, sandwichedRenyiDiv, SupportLE]
  by_cases hsupp : SupportLE ρ σ
  · have hEsupp := supportLE_map_of_cptp E hρ hσ hsupp
    have hLHS : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) =
        ((sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) := by
      unfold sandwichedRenyiDivNN
      apply if_neg
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h hEsupp
      · exact (not_lt_of_gt hα) h
    have hRHS : sandwichedRenyiDivNN α ρ σ =
        ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal) := by
      unfold sandwichedRenyiDivNN
      apply if_neg
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h hsupp
      · exact (not_lt_of_gt hα) h
    rw [hLHS, hRHS]
    exact EReal.coe_le_coe_iff.mpr
      (RenyiDPI.sandwichedRenyiDiv_le_of_support_core hcore E hα hρ hσ hsupp hρ0)
  · have hRHS : sandwichedRenyiDivNN α ρ σ = (⊤ : EReal) := by
      unfold sandwichedRenyiDivNN
      exact if_pos (Or.inl ⟨hα, hsupp⟩)
    rw [hRHS]
    exact le_top

end RenyiDPI
