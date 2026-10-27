/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorInstances

/-! # Lieb and Ando trace functionals on linear endomorphisms -/

open QuantumState

namespace LiebAndoTrace

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- The real part of `Tr (A ^ s * star K * B ^ (1 - s) * K)` on linear endomorphisms.
On the positive-definite cone, the powers are the usual real functional-calculus powers. -/
noncomputable def liebTraceMap (s : ℝ) (K A B : L ℋ) : ℝ :=
  (Tr (A ^ s * star K * B ^ (1 - s) * K)).re

/-- The real part of `Tr (A ^ q * star K * B ^ (-r) * K)` on linear endomorphisms.
On the positive-definite cone, the powers are the usual real functional-calculus powers. -/
noncomputable def andoTraceMap (q r : ℝ) (K A B : L ℋ) : ℝ :=
  (Tr (A ^ q * star K * B ^ (-r) * K)).re

end LiebAndoTrace
