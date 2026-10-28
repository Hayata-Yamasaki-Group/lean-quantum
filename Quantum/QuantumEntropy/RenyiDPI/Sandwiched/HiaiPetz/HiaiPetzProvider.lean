/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.NonNeg
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Tensor
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.AlphaOne

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u v

namespace RenyiDPI

def sandwichedHiaiPetzProvider : SandwichedSide.{u, v} where
  route := `hiaiPetz
  monotoneOnNonNeg := sandwichedMonotoneOnNonNeg_hiaiPetz
  tensorAdditivity := sandwichedTensorAdditiveOnDensity
  limitAtOne := sandwichedLimitAtOneOnPosDef

end RenyiDPI
