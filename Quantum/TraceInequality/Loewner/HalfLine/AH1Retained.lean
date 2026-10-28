import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Quantum.TraceInequality.Loewner.HalfLine.Convexity
import Quantum.TraceInequality.Loewner.HalfLine.ConvexityRetained
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing
import Quantum.Analysis.Topology.SOTContinuity
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.TransportRetained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransportRetained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.BlockDecomposition
import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerAlgebras
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Implementers
import Quantum.Analysis.CStar.FiniteDimensionalStructure.TraceRepair
import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerNormalization
import Quantum.Analysis.CStar.FiniteDimensionalStructure.ProductAssembly
import Quantum.Analysis.CStar.FiniteDimensionalStructure.ClassificationRetained
import Quantum.TraceInequality.Loewner.HalfLine.AH1
-- An instance name below is an indivisible token longer than the style limit.
set_option linter.style.longLine false

-- AH1 collects the theorem-facing matrix-order bridge statements on the positive ray.

/-!
# Positive-ray AH1 matrix-order bridge

This file contains the finite-dimensional matrix-order part of Carlen's
AH1 argument on the positive ray.  Most bridges are stated for abstract matrix
assignments `G,H`; the final wrappers name the concrete CFC realization
`G n X = g(X)` and its quadratic-form twist.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

section PositiveRayEndpointQuotientCFC

attribute [local instance]
    instContinuousFunctionalCalculusRealContinuousLinearMapComplexIdEuclideanSpaceFinIsSelfAdjointOfNontrivial_quantum_8

attribute [local instance]
    instNonnegSpectrumClassRealContinuousLinearMapComplexIdEuclideanSpaceFinOfNontrivial_quantum_8

end PositiveRayEndpointQuotientCFC

/--
The theorem-facing AH1 direction: joint convexity of the vector quadratic
forms for the concrete matrix CFC realization, together with positivity of the
scalar function on the positive ray, implies that the scalar function is
operator monotone decreasing on the positive ray.

The proof now uses the completed endpoint-quotient transport pipeline: the
twist convexity and endpoint control give the finite-matrix monotone endpoint
quotient, hence the closed-positive quotient monotonicity and the
finite-right-derivative representation required by the earlier CFC realization
assembly theorem.
-/
theorem operatorMonotoneDecreasingOnPositive_of_qformJointConvex
    {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex (positiveRayMatrixCfc g))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    OperatorMonotoneDecreasingOnPositive g := by
  refine
    operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationXsqRepSupplier
      hjoint hnonneg ?_
  intro hconvexH hcontrol
  have hclosed :
      PositiveRayClosedMatrixOperatorConvex
        (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)) :=
    positiveRayClosedMatrixOperatorConvex_xsqEndpointExtension_of_cfcTwist_endpointControl
      hconvexH hcontrol
  have hlin :
      PositiveRayEndpointLinearControl
        (fun x : ℝ =>
          positiveRayXsqEndpointExtension g x -
            positiveRayXsqEndpointExtension g 0) :=
    hcontrol.linear_control_sub_endpoint
  rcases exists_endpointQuotient_rightContinuous_of_closedMatrixConvex_endpointControl
      hclosed hlin with ⟨d, hright, _hquot⟩
  have hfinite :
      UnitIntervalFiniteMatrixMonotone.{0}
        (positiveCayleyPullback
          (positiveRayEndpointQuotient (positiveRayXsqEndpointExtension g) d)) := by
    refine ⟨?_⟩
    intro A _ _ _ _ a ha b hb hab
    exact
      positiveRay_cfcₙ_sub_endpoint_le
        (h := positiveRayXsqEndpointExtension g) (d := d)
        hclosed hlin ha.1 hb.1 ha.2 hb.2 hab
  exact
    exists_xsq_finiteRightDerivativeRep_of_endpointQuotient_finiteMatrixMonotone_of_xsq_nonneg
      (unitIntervalMatrixMonotone_of_finiteMatrixMonotone hfinite) hright hnonneg

end Quantum.TraceInequality.Loewner
