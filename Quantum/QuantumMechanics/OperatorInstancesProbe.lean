import Quantum.QuantumMechanics.OperatorInstances

/-!
# Operator instance resolution probe

This file checks operator instances in the environment imported above.
It tests the listed instance equalities, definitional reductions, and
instance-search outputs.
-/

namespace QuantumChannel

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

example :
    (inferInstance : Norm (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toNorm := by
  with_reducible_and_instances rfl

example :
    (inferInstance : MetricSpace (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toMetricSpace := by
  with_reducible_and_instances rfl

example :
    (Module.End.instRing : Ring (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toNormedRing.toRing := by
  with_reducible_and_instances rfl

example :
    (LinearMap.instStarRingId : StarRing (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toStarRing := by
  with_reducible_and_instances rfl

example :
    (Module.End.instAlgebra ℂ ℂ ℋ : Algebra ℂ (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toNormedAlgebra.toAlgebra := by
  with_reducible_and_instances rfl

example :
    (LinearMap.instStarModuleId : StarModule ℂ (L ℋ)) =
      (inferInstance : CStarAlgebra (L ℋ)).toStarModule := by
  with_reducible_and_instances rfl

example (X : L ℋ) : ‖X‖ = ‖X.toContinuousLinearMap‖ := rfl
example (x y : L ℋ) : dist x y = dist x.toContinuousLinearMap y.toContinuousLinearMap := rfl
example (x y : L ℋ) : (x ≤ y) = (y - x).IsPositive := rfl

/-- info: continuous_instance -/
#guard_msgs in
#synth CStarAlgebra (B ℋ)

/-- info: instNormL ℋ -/
#guard_msgs in
#synth Norm (L ℋ)

/-- info: instMetricSpaceL ℋ -/
#guard_msgs in
#synth MetricSpace (L ℋ)

/-- info: c_algebra_instance -/
#guard_msgs in
#synth Algebra ℂ (L ℋ)

/-- info: instCStarAlgebraL ℋ -/
#guard_msgs in
#synth CStarAlgebra (L ℋ)

/-- info: continuous_sor_instance -/
#guard_msgs in
#synth StarOrderedRing (B ℋ)

/-- info: instStarOrderedRingL ℋ -/
#guard_msgs in
#synth StarOrderedRing (L ℋ)

/-- info: LinearMap.instLoewnerPartialOrder -/
#guard_msgs in
#synth PartialOrder (L ℋ)

end QuantumChannel
