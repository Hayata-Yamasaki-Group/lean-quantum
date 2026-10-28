/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.HilbertSchmidtOperatorSpace
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.LiebTrace.Bridge

namespace LiebAndoTrace

universe u

open QuantumState LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

/-- Trace functional appearing in Lieb's extension theorem. -/
noncomputable def liebExtensionTraceMap (q p : ℝ) (K : (ℋ →L[ℂ] ℋ)) (A B
    : (ℋ →L[ℂ] ℋ)) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ p * K)

/-- The trace function `C_{q,r,K}` used in Corollary 1.3.

Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531–533, Corollary 1.3. -/
noncomputable def liebCorollaryTraceMap (q r : ℝ) (K : (ℋ →L[ℂ] ℋ)) (A B
    : (ℋ →L[ℂ] ℋ)) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (1 - r) * K)

/-- Trace functional appearing in Ando's convexity theorem. -/
noncomputable def andoTraceMap (q r : ℝ) (K : (ℋ →L[ℂ] ℋ)) (A B : (ℋ →L[ℂ] ℋ)) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (-r) * K)

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma leftMulHS_rankOne (A : B ℋ) (x y : ℋ) :
    leftMulHS (ℋ := ℋ) A (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ (A x) y) := by
  change (A * InnerProductSpace.rankOne ℂ x y) = InnerProductSpace.rankOne ℂ (A x) y
  simpa [leftMulHS_apply] using
    (InnerProductSpace.comp_rankOne (𝕜 := ℂ) (x := x) (y := y) (f := A))

omit [Nontrivial ℋ] in
private lemma rightMulHS_rankOne (B : (ℋ →L[ℂ] ℋ)) (x y : ℋ) :
    rightMulHS (ℋ := ℋ) B (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ x ((star B) y)) := by
  change (InnerProductSpace.rankOne ℂ x y * B) = InnerProductSpace.rankOne ℂ x ((star B) y)
  simpa [rightMulHS_apply, ContinuousLinearMap.star_eq_adjoint] using
    (InnerProductSpace.rankOne_comp (𝕜 := ℂ) (x := x) (y := y) (f := B))

end LiebAndoTrace

namespace LiebAndoTrace

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u''
variable {ℋ : Type u''} [Qudit ℋ]

private lemma real_smul_eq_complex_smul (r : ℝ) (X : B ℋ) :
    (r • X : B ℋ) = ((↑r : ℂ) • X : B ℋ) :=
  ContinuousLinearMap.ext fun x => by
    simp only [ContinuousLinearMap.smul_apply]
    change r • X x = (↑r : ℂ) • X x
    haveI : IsScalarTower ℝ ℂ ℋ := ⟨fun r c x => by
      change (r • c) • x = ((r : ℂ)) • c • x
      rw [Algebra.smul_def, mul_smul]; simp [RCLike.algebraMap_eq_ofReal]⟩
    exact algebraMap_smul ℂ r (X x)

end

end LiebAndoTrace

namespace LiebAndoTrace

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u''
variable {ℋ : Type u''} [Qudit ℋ]

private lemma traceRe_real_smul (r : ℝ) (X : B ℋ) :
    traceRe (ℋ := ℋ) (r • X) = r * traceRe (ℋ := ℋ) X := by
  rw [real_smul_eq_complex_smul r X]
  change (LinearMap.trace ℂ ℋ ((r : ℂ) • X.toLinearMap)).re =
    r * (LinearMap.trace ℂ ℋ X.toLinearMap).re
  rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

end

end LiebAndoTrace

namespace LiebAndoTrace

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u''
variable {ℋ : Type u''} [Qudit ℋ]

lemma trace_re_convex_combo (θ : ℝ) (X₁ X₂ : B ℋ) :
    traceRe (ℋ := ℋ) ((1 - θ) • X₁ + θ • X₂) =
      (1 - θ) * traceRe (ℋ := ℋ) X₁ + θ * traceRe (ℋ := ℋ) X₂ := by
  have hadd : traceRe (ℋ := ℋ) ((1 - θ) • X₁ + θ • X₂) =
      traceRe (ℋ := ℋ) ((1 - θ) • X₁) + traceRe (ℋ := ℋ) (θ • X₂) := by
    change (LinearMap.trace ℂ ℋ
      (((1 - θ) • X₁).toLinearMap + (θ • X₂).toLinearMap)).re =
        (LinearMap.trace ℂ ℋ ((1 - θ) • X₁).toLinearMap).re +
          (LinearMap.trace ℂ ℋ (θ • X₂).toLinearMap).re
    rw [map_add, Complex.add_re]
  rw [hadd, traceRe_real_smul, traceRe_real_smul]

end

end LiebAndoTrace
