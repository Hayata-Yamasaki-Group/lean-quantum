import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Algebra.Order.Floor.Semifield
open scoped RenyiDPI.Sym
open scoped ComplexOrder
namespace RenyiDPI
def MatrixLiebConcavity (p : ℝ) : Prop :=
  ∀ {n : ℕ} (X : HiaiPetz.Mₙ n) {A₁ A₂ B₁ B₂ : HiaiPetz.Mₙ n} {t : ℝ},
    t ∈ Set.Icc (0 : ℝ) 1 →
    Matrix.PosDef A₁ → Matrix.PosDef A₂ →
    Matrix.PosDef B₁ → Matrix.PosDef B₂ →
    t * HiaiPetz.liebTracePower p A₁ B₁ X +
        (1 - t) * HiaiPetz.liebTracePower p A₂ B₂ X ≤
      HiaiPetz.liebTracePower p (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) X
end RenyiDPI
