/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.SelectedProvider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.SelectedProvider

/-! # Consumer façade for both independently selected Rényi sides

Umegaki adapters import the relevant side-specific `Provider` module.
This root only re-exports the sides; it defines no combined provider value.
-/
