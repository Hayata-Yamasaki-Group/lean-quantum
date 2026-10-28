import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.PosDef
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SandwichedLift.NonNeg

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem sandwichedMonotoneOnNonNeg_hiaiPetz :
SandwichedMonotoneOnNonNeg.{u} := by
  exact RenyiDPI.sandwichedMonotoneOnNonNeg_of_posDefGt
    RenyiDPI.sandwichedMonotoneOnPosDefGt_hiaiPetz

end RenyiDPI
