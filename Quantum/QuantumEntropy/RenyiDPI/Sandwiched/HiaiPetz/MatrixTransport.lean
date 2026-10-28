/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.MatrixVocabulary
import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Algebra.Order.Floor.Semifield

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

/-- The real CFC commutes with the transport from continuous endomorphisms to Euclidean
matrices (the `StarAlgHomClass.map_cfc` step of `c05_matrixPower_transport`, split off because
its instance search is the expensive part). -/
private theorem c05_map_cfc {H : Type u} [Qudit H] (f : ℝ → ℝ) (Y : H →L[ℂ] H)
    (hf : ContinuousOn f (spectrum ℝ Y)) (hY : IsSelfAdjoint Y) :
    ((linearToContinuousEndStarAlgEquiv H).symm.trans
        ((LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)).trans
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ H)) (𝕜 := ℂ)))) (cfc f Y) =
      cfc f (((linearToContinuousEndStarAlgEquiv H).symm.trans
        ((LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)).trans
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ H)) (𝕜 := ℂ)))) Y) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) _ f Y (hf := hf)
    (hφ := LinearMap.continuous_of_finiteDimensional
      ((linearToContinuousEndStarAlgEquiv H).symm.trans
        ((LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)).trans
          (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ H)) (𝕜 := ℂ)))).toAlgEquiv.toLinearMap)
    (ha := hY) (hφa := hY.map _)

private theorem c05_matrixPower_transport {H : Type u} [Qudit H]
    {X : L H} (hX : X ∈ pdSetLM (ℋ := H)) (p : ℝ) :
    HiaiPetz.matrixPower p
        (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) X) =
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)
        (((CFC.rpow X.toContinuousLinearMap p : B H) : L H)) := by
  let b := stdOrthonormalBasis ℂ H
  let e := Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ H)) (𝕜 := ℂ)
  let φ := (linearToContinuousEndStarAlgEquiv H).symm.trans
    ((LinearMap.toMatrixOrthonormal b).trans e)
  have hs : IsStrictlyPositive X.toContinuousLinearMap :=
    (pdSet_membership_certificate _).1 hX
  have hfinC : (spectrum ℂ X.toContinuousLinearMap).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum X
  have hfinR : (spectrum ℝ X.toContinuousLinearMap).Finite := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hfinC.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  have hmap := c05_map_cfc (HiaiPetz.powerFn p) X.toContinuousLinearMap
      (hfinR.continuousOn _) hs.isSelfAdjoint
  apply EquivLike.injective e
  simp only [HiaiPetz.matrixPower, HansenPedersen.matrixCfcR, e,
    StarAlgEquiv.apply_symm_apply]
  change cfc (HiaiPetz.powerFn p) (φ X.toContinuousLinearMap) =
    φ (CFC.rpow X.toContinuousLinearMap p)
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (ha := hs.nonneg)]
  exact hmap.symm

theorem liebTraceMapLM_eq_matrix_liebTracePower :
∀ {H : Type u} [Qudit H] [Nontrivial H]
  (p : ℝ) (K A B : L H),
  A ∈ pdSetLM (ℋ := H) → B ∈ pdSetLM (ℋ := H) →
  liebTraceMapLM p K A B =
    HiaiPetz.liebTracePower p
      (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) A)
      (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) B)
      (star (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) K)) := by
  intro H _ _ p K A B hA hB
  rw [HiaiPetz.liebTracePower, HiaiPetz.powerTrace,
    ← Matrix.star_eq_conjTranspose, star_star,
    c05_matrixPower_transport hA p, c05_matrixPower_transport hB (1 - p)]
  unfold liebTraceMapLM liebTraceMap traceRe
  rw [← CFC.rpow_eq_pow, ← CFC.rpow_eq_pow]
  change (Tr ((CFC.rpow A.toContinuousLinearMap p : QuantumState.B H).toLinearMap *
    star K * (CFC.rpow B.toContinuousLinearMap (1 - p) : QuantumState.B H).toLinearMap * K)).re = _
  rw [tr_eq_matrix_trace_orthonormal (stdOrthonormalBasis ℂ H)]
  simp only [map_mul, map_star]
  refine congrArg Complex.re ?_
  simpa only [mul_assoc] using Matrix.trace_mul_comm
    (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)
      ((CFC.rpow A.toContinuousLinearMap p : QuantumState.B H).toLinearMap) *
      star (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) K) *
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H)
        ((CFC.rpow B.toContinuousLinearMap (1 - p) : QuantumState.B H).toLinearMap))
    (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ H) K)

end RenyiDPI
