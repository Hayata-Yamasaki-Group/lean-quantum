import Quantum.QuantumEntropy.SandwichedRenyiLMCompat.GSLCore
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyiBase.MaxRelativeEntropy.Monotonicity
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.AlphaOne

/-! Linear-map interface for the concavity of trace conjugate powers. -/
namespace SandwichedRenyiRelativeEntropy
open QuantumState

theorem traceConjPow_concave_pos_lm {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (fun A => traceConjPow p B A) := by
  have h := traceConjPow_concave_pos hp0 hp1 B.toContinuousLinearMap
    ((ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap
      (f := B.toContinuousLinearMap)).mpr hB)
  constructor
  · intro x hx y hy a b ha hb hab
    rw [show a = 1 - b from by linarith]
    exact pdSetLM_convexCombo hx hy hb (by linarith)
  · intro x hx y hy a b ha hb hab
    exact h.2 (x := x.toContinuousLinearMap) (y := y.toContinuousLinearMap)
      hx hy ha hb hab
end SandwichedRenyiRelativeEntropy
