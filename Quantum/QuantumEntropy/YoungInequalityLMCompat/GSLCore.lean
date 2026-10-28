import Quantum.QuantumEntropy.YoungInequality
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore

/-! Linear-map interface for the orthonormal matrix real-power formula. -/
open QuantumState
open scoped MatrixOrder Matrix.Norms.L2Operator
lemma toMatrixOrthonormal_rpow_lm {ℋ : Type*} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (X : L ℋ)
    (hX : X.IsPositive) (p : ℝ) (hp : 0 ≤ p) :
    LinearMap.toMatrixOrthonormal b (CFC.rpow X p) =
      @CFC.rpow _ _ _ _ _ _ _ _ Matrix.instNonnegSpectrumClass
        (LinearMap.toMatrixOrthonormal b X) p := by
  have h := toMatrixOrthonormal_rpow b X.toContinuousLinearMap
    (X.isPositive_toContinuousLinearMap_iff.mpr hX) p hp
  simpa only [TensorCFC.rpow_toLinearMap_lm] using h
