import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Shared real-scalar instances for complex modules

This module centralizes the real/complex scalar tower and norm instances used
throughout the Löwner development, together with monotonicity of the
lexicographic complex order under a nonnegative real scalar.
-/

namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder

noncomputable section

-- Opt in within HP proofs; exporting this shortcut changes operator Algebra
-- selection and can prevent downstream canonical real CFC synthesis.
noncomputable scoped instance instRealComplexScalarTower {E : Type*} [AddCommGroup E] [Module ℂ E] :
    IsScalarTower ℝ ℂ E :=
  IsScalarTower.complexToReal

end

end Quantum.TraceInequality.Loewner
