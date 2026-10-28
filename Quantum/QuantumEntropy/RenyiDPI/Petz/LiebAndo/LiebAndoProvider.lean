/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.CPTP
import Quantum.QuantumEntropy.RenyiDPI.Petz.Tensor
import Quantum.QuantumEntropy.RenyiDPI.Petz.AlphaOne

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u v

namespace RenyiDPI

def petzLiebAndoProvider : PetzSide.{u, v} where
  route := `liebAndo
  monotoneOnNonNeg := petzMonotoneOnNonNeg_liebAndo
  tensorAdditivity := petzTensorAdditiveOnDensity
  limitAtOne := petzLimitAtOneOnPosDef

end RenyiDPI
