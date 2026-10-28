/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.LiebAndoProvider

/-! # Selection of the sandwiched Rényi provider -/

namespace RenyiDPI

universe u v

/-- The unique entry point that selects the sandwiched Rényi provider (data processing, tensor
additivity and order-one continuity); independent of the Petz selection. It currently selects the
Lieb–Ando provider (`sandwichedLiebAndoProvider`). -/
def selectedSandwichedProvider : SandwichedSide.{u, v} := sandwichedLiebAndoProvider

end RenyiDPI
