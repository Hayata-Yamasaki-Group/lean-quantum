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

noncomputable instance instRealComplexPosSMulMono : PosSMulMono ℝ ℂ where
  smul_le_smul_of_nonneg_left := by
    intro a ha z w hzw
    rw [RCLike.le_iff_re_im] at hzw ⊢
    constructor
    · simp only [RCLike.smul_re]
      exact mul_le_mul_of_nonneg_left hzw.1 ha
    · simp only [RCLike.smul_im, hzw.2]

noncomputable scoped instance instRealComplexNormSMulClass : NormSMulClass ℝ ℂ :=
  NormedSpace.toNormSMulClass

end

end Quantum.TraceInequality.Loewner
