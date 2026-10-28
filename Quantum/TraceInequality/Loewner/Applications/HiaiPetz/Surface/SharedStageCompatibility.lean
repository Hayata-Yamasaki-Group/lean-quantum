import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.DirectToConcavity
import Quantum.TraceInequality.HiaiPetzTheorem.QuasiEntropyDataProcessing.JointToMonotone

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace

/-- The surface and core joint-concavity predicates differ only in positive-definite vocabulary. -/
theorem jointConcavity_iff_core {f : ℝ → ℝ} :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f ↔
      _root_.HiaiPetz.QuasiEntropyDataProcessing.JointConcavity f := by
  constructor
  · intro h n A₁ A₂ B₁ B₂ X t ht0 ht1 hA₁ hA₂ hB₁ hB₂
    exact h ht0 ht1
      (matrixPosDef_iff_posDef.mpr hA₁) (matrixPosDef_iff_posDef.mpr hA₂)
      (matrixPosDef_iff_posDef.mpr hB₁) (matrixPosDef_iff_posDef.mpr hB₂)
  · intro h n A₁ A₂ B₁ B₂ X t ht0 ht1 hA₁ hA₂ hB₁ hB₂
    exact h ht0 ht1
      (matrixPosDef_iff_posDef.mp hA₁) (matrixPosDef_iff_posDef.mp hA₂)
      (matrixPosDef_iff_posDef.mp hB₁) (matrixPosDef_iff_posDef.mp hB₂)

/-- Self-adjointness identifies the surface quadratic-form order with core operator order. -/
theorem strictDirectDPI_iff_core {f : ℝ → ℝ} :
    QuasiEntropyDPI.strictDirectDPICondition f ↔
      _root_.HiaiPetz.QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality f := by
  constructor
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    have hΦB := _root_.Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
    apply le_of_HSLE_of_isSelfAdjoint
      (h Φ hPos hTrace hSch
        (matrixPosDef_iff_posDef.mpr hA) (matrixPosDef_iff_posDef.mpr hB)
        (matrixPosDef_iff_posDef.mpr hΦ1))
    exact (_root_.HiaiPetz.jOperator_isSelfAdjoint hΦB).sub
      ((_root_.HiaiPetz.jOperator_isSelfAdjoint hB).conj_adjoint Φ)
  · intro h n m Φ A B hPos hTrace hSch hA hB hΦ1
    exact HSLE_of_le (h Φ hPos hTrace hSch
      (matrixPosDef_iff_posDef.mp hA) (matrixPosDef_iff_posDef.mp hB)
      (matrixPosDef_iff_posDef.mp hΦ1))

/-- The common strict-DPI stage, expressed with the unchanged surface predicates. -/
theorem jointConcavity_of_strictDirectDPI
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDPI.strictDirectDPICondition f →
      QuasiEntropyDPI.quasiEntropyJointConcavityCondition f := by
  intro h
  exact jointConcavity_iff_core.mpr
    (_root_.HiaiPetz.QuasiEntropyDataProcessing.jointConcavity_of_strictDirectDPI f hf
      (strictDirectDPI_iff_core.mp h))

/-- The common monotonicity stage, expressed with the unchanged surface predicates. -/
theorem matrixMonotone_of_jointConcavity
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneCondition f := by
  intro h
  exact _root_.HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos
    (jointConcavity_iff_core.mp h)

end Quantum.TraceInequality.Loewner.HiaiPetz
