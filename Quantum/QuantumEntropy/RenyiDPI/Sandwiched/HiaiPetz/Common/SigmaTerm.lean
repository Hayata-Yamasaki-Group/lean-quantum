/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.YoungInequalityLMCompat.GSLCore
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs


open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma c06_trace_rpow_star_mul_eq_mul_star
    {H : Type u} [Qudit H] (C : L H) {q : ℝ} (hq : 0 ≤ q) :
    Tr (CFC.rpow (star C * C) q) = Tr (CFC.rpow (C * star C) q) := by
  classical
  have h₁ : (star C * C).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (star_mul_self_nonneg C)
  have h₂ : (C * star C).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (mul_star_self_nonneg C)
  let b := stdOrthonormalBasis ℂ H
  let M := LinearMap.toMatrixOrthonormal b C
  have hH₁ : (star M * M).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self M
  have hH₂ : (M * star M).IsHermitian :=
    Matrix.isHermitian_mul_conjTranspose_self M
  have hM₁ : LinearMap.toMatrixOrthonormal b (star C * C) = star M * M := by
    rw [map_mul, map_star]
  have hM₂ : LinearMap.toMatrixOrthonormal b (C * star C) = M * star M := by
    rw [map_mul, map_star]
  have heig : hH₁.eigenvalues = hH₂.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  have htrace₁ := matrix_trace_rpow_eq_sum_eigenvalues (star M * M) hH₁
    (Matrix.posSemidef_conjTranspose_mul_self M).nonneg q
  have htrace₂ := matrix_trace_rpow_eq_sum_eigenvalues (M * star M) hH₂
    (Matrix.posSemidef_self_mul_conjTranspose M).nonneg q
  have hmap₁ := congrArg Matrix.trace (toMatrixOrthonormal_rpow_lm b _ h₁ q hq)
  have hmap₂ := congrArg Matrix.trace (toMatrixOrthonormal_rpow_lm b _ h₂ q hq)
  rw [hM₁] at hmap₁
  rw [hM₂] at hmap₂
  calc
    Tr (CFC.rpow (star C * C) q) =
        Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (star C * C) q)) :=
      tr_eq_matrix_trace_orthonormal b _
    _ = ∑ i, (((hH₁.eigenvalues i) ^ q : ℝ) : ℂ) := hmap₁.trans htrace₁
    _ = ∑ i, (((hH₂.eigenvalues i) ^ q : ℝ) : ℂ) := by rw [heig]
    _ = Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (C * star C) q)) :=
      htrace₂.symm.trans hmap₂.symm
    _ = Tr (CFC.rpow (C * star C) q) :=
      (tr_eq_matrix_trace_orthonormal b _).symm

theorem sigmaTerm_eq_traceConjPow_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z σ : L H},
  1 < α → Z ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
  (Tr (CFC.rpow
    (CFC.rpow σ ((α - 1) / (2 * α)) * Z *
      CFC.rpow σ ((α - 1) / (2 * α))) (α / (α - 1)))).re =
  traceConjPow ((α - 1) / α) (CFC.rpow Z (1 / 2)) σ := by
  intro H _ _ α Z σ hα hZ hσ
  have hZpos := (pdSetLM_strictPositivity_certificate Z).mp hZ
  have hσpos := (pdSetLM_strictPositivity_certificate σ).mp hσ
  let P := CFC.rpow σ ((α - 1) / (2 * α))
  let Q := CFC.rpow Z (1 / 2)
  let C := P * Q
  have hP : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQQ : Q * Q = Z := by
    calc
      Q * Q = CFC.rpow Z (1 / 2 + 1 / 2) := (CFC.rpow_add hZpos.isUnit).symm
      _ = CFC.rpow Z 1 := by norm_num
      _ = Z := CFC.rpow_one Z hZpos.nonneg
  have hPP : P * P = CFC.rpow σ ((α - 1) / α) := by
    calc
      P * P = CFC.rpow σ ((α - 1) / (2 * α) + (α - 1) / (2 * α)) :=
        (CFC.rpow_add hσpos.isUnit).symm
      _ = CFC.rpow σ ((α - 1) / α) := by congr 1; ring
  have hstar : star C = Q * P := by
    change star (P * Q) = Q * P
    rw [star_mul, hP.star_eq, hQ.star_eq]
  have hCsC : C * star C = P * Z * P := by
    rw [hstar]
    change P * Q * (Q * P) = P * Z * P
    rw [← mul_assoc (P * Q) Q P, mul_assoc P Q Q, hQQ]
  have hsCC : star C * C = Q * CFC.rpow σ ((α - 1) / α) * Q := by
    rw [hstar]
    change Q * P * (P * Q) = Q * CFC.rpow σ ((α - 1) / α) * Q
    rw [← mul_assoc (Q * P) P Q, mul_assoc Q P P, hPP]
  have hq : 0 ≤ α / (α - 1) :=
    div_nonneg (by linarith) (by linarith)
  rw [traceConjPow_eq_direct]
  change (Tr (CFC.rpow (P * Z * P) (α / (α - 1)))).re =
    (Tr (CFC.rpow (star Q * CFC.rpow σ ((α - 1) / α) * Q)
      (1 / ((α - 1) / α)))).re
  rw [hQ.star_eq, show (1 : ℝ) / ((α - 1) / α) = α / (α - 1) by
    simp only [one_div, inv_div], ← hCsC, ← hsCC]
  exact congrArg Complex.re (c06_trace_rpow_star_mul_eq_mul_star C hq).symm

end RenyiDPI
