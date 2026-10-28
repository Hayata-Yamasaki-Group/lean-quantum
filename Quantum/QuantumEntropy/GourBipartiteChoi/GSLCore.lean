/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.QuantumFDivergence.GSLCore

/-!
# Bipartite Choi conventions: Bob's monoidal unit

The concrete realization of Bob's monoidal unit is ℂ (`BobUnit` and its `Qudit` instance
`bobUnitQudit`), not a singleton type. This module contains only those declarations of the
original module that the public part uses.
-/

namespace GourChoi

open QuantumState QuantumChannel Lean
open scoped TensorProduct

universe u v w z x y

/-- Concrete Hilbert realization of the monoidal unit of OPT. -/
abbrev BobUnit := ℂ

noncomputable instance bobUnitQudit : Qudit BobUnit where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  toFinite := inferInstance

variable {Hin : Type u} {Hout : Type v} [Qudit Hin] [Qudit Hout]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

variable {A : Type w} {B : Type z} {Atilde : Type x} {Bprime : Type y}
variable [Qudit A] [Qudit B] [Qudit Atilde] [Qudit Bprime]

end GourChoi

open Lean
