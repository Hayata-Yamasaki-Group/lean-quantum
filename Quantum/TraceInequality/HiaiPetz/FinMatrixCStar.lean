import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Finite matrix C⋆-algebra bridge
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

-- Keep this bridge because Mathlib has no `CStarAlgebra` instance for plain `Matrix`.
namespace FinMatrixCStar

noncomputable scoped instance instFinMatrixCStarAlgebra {n : ℕ} :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where
  norm_mul_self_le M := Matrix.instCStarRing.norm_mul_self_le M

end FinMatrixCStar

end

end Quantum.TraceInequality.Loewner
