import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Mathlib.Algebra.Central.End

/-!
# Hilbert--Schmidt and trace norms as real numbers

`w40H₂ M` and `w40T₁ M` are the real-valued Hilbert--Schmidt norm and trace norm of an operator,
used for the collision quantities of Gour §7.7.  This module keeps the declarations of the
original module that the public development uses.
-/

open QuantumState QuantumChannel
open scoped TensorProduct ComplexOrder ENNReal
universe u
namespace GourConditionalEntropy

/-- Hilbert–Schmidt norm, distinct from both q and collision entropy. -/
noncomputable def w40H₂ {H : Type u} [Qudit.{u} H] (M : L H) : ℝ :=
  Real.sqrt (Tr (star M * M)).re

/-- Schatten one norm, not the operator norm on L H. -/
noncomputable def w40T₁ {H : Type u} [Qudit.{u} H] (M : L H) : ℝ :=
  (Tr (CFC.sqrt (star M * M))).re

end GourConditionalEntropy
