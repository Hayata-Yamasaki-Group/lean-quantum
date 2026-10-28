import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.MatrixVocabulary
import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.DirectToConcavity
import Quantum.TraceInequality.TraceFunctionMonotonicity.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity
import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem s01_quasiEntropy_eq_liebTracePower
    {n : ℕ} (p : ℝ) {A B X : HiaiPetz.Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    HiaiPetz.quasiEntropy (HiaiPetz.powerFn p) A B X =
      HiaiPetz.liebTracePower p A B X := by
  rw [HiaiPetz.quasiEntropy_powerFn_eq_jPowerTrace p hB,
    HiaiPetz.jPowerTrace_eq_liebTracePower_of_posDef p hA hB]

private theorem s01_strictDirect_of_tracePower
    (hDirect : HiaiPetz.TraceMonotonicity.DirectTracePowerStrictlyPositive)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    HiaiPetz.QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality
      (HiaiPetz.powerFn p) := by
  intro n m Φ A B hPos hTrace hSch hA hB hΦ1
  letI := HiaiPetz.instMatrixNormedAddCommGroup (n := n)
  letI := HiaiPetz.instMatrixNormedSpace (n := n)
  letI := HiaiPetz.instMatrixInnerProductSpace (n := n)
  letI := HiaiPetz.instMatrixCompleteSpace (n := n)
  letI := HiaiPetz.instMatrixNormedAddCommGroup (n := m)
  letI := HiaiPetz.instMatrixNormedSpace (n := m)
  letI := HiaiPetz.instMatrixInnerProductSpace (n := m)
  letI := HiaiPetz.instMatrixCompleteSpace (n := m)
  have hΦA := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  apply HiaiPetz.le_of_quadratic_form_nonneg
  · apply (HiaiPetz.jOperator_isSelfAdjoint hΦB).sub
    simpa [HiaiPetz.hsAdjoint, ContinuousLinearMap.comp_assoc] using
      (HiaiPetz.jOperator_isSelfAdjoint
        (f := HiaiPetz.powerFn p) (A := A) hB).conj_adjoint Φ
  · intro X
    have hq := hDirect Φ (X := X) hp hPos hTrace hSch hA hB hΦ1
    rw [← s01_quasiEntropy_eq_liebTracePower p hA hB,
      ← s01_quasiEntropy_eq_liebTracePower p hΦA hΦB] at hq
    change Complex.re (Matrix.trace (Matrix.conjTranspose (HiaiPetz.hsAdjoint Φ X) *
        HiaiPetz.jOperator (HiaiPetz.powerFn p) A B (HiaiPetz.hsAdjoint Φ X))) ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X *
        HiaiPetz.jOperator (HiaiPetz.powerFn p) (Φ A) (Φ B) X)) at hq
    rw [← HiaiPetz.hsQForm_comp_hsAdjoint Φ
      (HiaiPetz.jOperator (HiaiPetz.powerFn p) A B) X,
      HiaiPetz.hsQForm_real_eq_inner_real,
      HiaiPetz.hsQForm_real_eq_inner_real] at hq
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub]
    exact sub_nonneg.mpr hq

private theorem s01_posDef_convexCombo
    {n : ℕ} {A B : HiaiPetz.Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Matrix.PosDef (t • A + (1 - t) • B) := by
  by_cases ht0 : t = 0
  · subst t
    have h : (0 : ℝ) • A + (1 - (0 : ℝ)) • B = B := by
      ext i j
      change (0 : ℂ) * A i j + (((1 - (0 : ℝ)) : ℝ) : ℂ) * B i j = B i j
      norm_num
    rwa [h]
  by_cases ht1 : t = 1
  · subst t
    have h : (1 : ℝ) • A + (1 - (1 : ℝ)) • B = A := by
      ext i j
      change (1 : ℂ) * A i j + (((1 - (1 : ℝ)) : ℝ) : ℂ) * B i j = A i j
      norm_num
    rwa [h]
  exact (hA.smul (lt_of_le_of_ne ht.1 (Ne.symm ht0))).add
    (hB.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)))

theorem matrixLiebConcavity_of_direct :
HiaiPetz.TraceMonotonicity.DirectTracePowerStrictlyPositive →
  ∀ {p : ℝ}, 0 < p → p < 1 → MatrixLiebConcavity p := by
  intro hDirect p hp0 hp1
  have hf : ContinuousOn (HiaiPetz.powerFn p) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt
  have hConc : HiaiPetz.QuasiEntropyDataProcessing.JointConcavity (HiaiPetz.powerFn p) :=
    HiaiPetz.QuasiEntropyDataProcessing.jointConcavity_of_strictDirectDPI
      (HiaiPetz.powerFn p) hf
      (s01_strictDirect_of_tracePower hDirect ⟨hp0.le, hp1.le⟩)
  intro n X A₁ A₂ B₁ B₂ t ht hA₁ hA₂ hB₁ hB₂
  have hAt := s01_posDef_convexCombo ht hA₁ hA₂
  have hBt := s01_posDef_convexCombo ht hB₁ hB₂
  have hq := hConc (X := X) ht.1 ht.2 hA₁ hA₂ hB₁ hB₂
  rw [s01_quasiEntropy_eq_liebTracePower p hA₁ hB₁,
    s01_quasiEntropy_eq_liebTracePower p hA₂ hB₂,
    s01_quasiEntropy_eq_liebTracePower p hAt hBt] at hq
  exact hq

end RenyiDPI
