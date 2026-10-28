/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.Monotone
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Tensor
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.AlphaOne

/-! # Sandwiched Rényi laws from Lieb–Ando inequalities -/

namespace RenyiDPI

universe u v

/-- Laws for the natural-log sandwiched divergences. -/
def sandwichedLiebAndoProvider : SandwichedSide.{u, v} where
  route := `liebAndo
  monotoneOnNonNeg := sandwichedMonotoneOnNonNeg_liebAndo
  tensorAdditivity := sandwichedTensorAdditiveOnDensity
  limitAtOne := sandwichedLimitAtOneOnPosDef

end RenyiDPI
