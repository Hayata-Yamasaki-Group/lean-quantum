/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.Frontier
import Quantum.TraceInequality.HansenPedersen.Frontier.TraceMonotonicity

/-!
# Formalization-frontier root

This is a second aggregate root besides `Quantum`, in the same `Quantum` library
target, so the default `lake build` builds both; it additionally imports the frontier
modules below.  A frontier module states a proposition as a definition
`def … : Prop` without a proof term; building it checks the statement, not a proof.
The aggregate `Quantum` does not import
`Quantum.TraceInequality.HansenPedersen.Frontier.TraceMonotonicity`.  It does reach,
through the Hansen--Pedersen chapter aggregate, the statement-only modules under
`Quantum/TraceInequality/HansenPedersen/HansenPedersen/Frontier/`, which likewise
define propositions without proving them.
-/
