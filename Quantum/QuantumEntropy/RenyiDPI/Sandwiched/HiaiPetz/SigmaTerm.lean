import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.Common.SigmaTerm
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.Concavity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.TraceConjPowConcavity

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem sigmaTerm_concave_hiaiPetz :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z : L H},
  1 < α → Z ∈ pdSetLM (ℋ := H) →
  ConcaveOn ℝ (pdSetLM (ℋ := H))
    (fun σ => (Tr (CFC.rpow
      (CFC.rpow σ ((α - 1) / (2 * α)) * Z *
        CFC.rpow σ ((α - 1) / (2 * α))) (α / (α - 1)))).re) := by
  intro H _ _ α Z hα hZ
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hp0 : 0 < (α - 1) / α := div_pos (sub_pos.mpr hα) hα0
  have hp1 : (α - 1) / α < 1 := (div_lt_one hα0).mpr (by linarith)
  have hZpos := (pdSetLM_strictPositivity_certificate Z).mp hZ
  have hZsqrt : IsUnit (CFC.rpow Z (1 / 2)) := hZpos.rpow.isUnit
  refine (RenyiDPI.traceConjPow_concave_of_lieb RenyiDPI.liebConcavityPD_hiaiPetz (CFC.rpow Z (1
    / 2)) hp0 hp1 hZsqrt).congr ?_
  intro σ hσ
  exact (sigmaTerm_eq_traceConjPow_gt hα hZ hσ).symm

end RenyiDPI
