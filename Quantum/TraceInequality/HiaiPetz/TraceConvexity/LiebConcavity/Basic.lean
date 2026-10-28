/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Joint concavity of the support Lieb trace power at positive-definite endpoints

This module establishes the positive-definite case of the Lieb concavity used in
Hiai–Petz Theorem 6.4.

## Main results

* `matrixPosDef_convex_combo`: convex combinations of positive-definite matrices are
  positive-definite.
* `supportLiebTracePower_jointlyConcave_posDef`: for `p ∈ [0, 1]` and positive-definite
  `A1, A2, B1, B2`, the support Lieb trace power `supportLiebTracePower p A B X` is jointly
  concave in `(A, B)`, obtained from the joint concavity supplied by the
  provider-neutral `ProofNet` surface and the rewrite to `liebTracePower` on
  positive-definite inputs.

## References

* Hiai, Theorem 6.4.
-/

namespace HiaiPetz

namespace TraceConvexity

open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- A convex combination `t • A1 + (1 - t) • A2` (with `t ∈ [0, 1]`) of positive-definite
matrices is positive-definite. -/
theorem matrixPosDef_convex_combo {n : ℕ} {A1 A2 : Mₙ n} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hA1 : Matrix.PosDef A1) (hA2 : Matrix.PosDef A2) :
    Matrix.PosDef (t • A1 + (1 - t) • A2) := by
  by_cases htzero : t = 0
  · subst t
    have h : (0 : ℝ) • A1 + (1 - (0 : ℝ)) • A2 = A2 := by
      ext i j
      change (0 : ℂ) * A1 i j + (((1 - (0 : ℝ)) : ℝ) : ℂ) * A2 i j = A2 i j
      norm_num
    rwa [h]
  by_cases htone : t = 1
  · subst t
    have h : (1 : ℝ) • A1 + (1 - (1 : ℝ)) • A2 = A1 := by
      ext i j
      change (1 : ℂ) * A1 i j + (((1 - (1 : ℝ)) : ℝ) : ℂ) * A2 i j = A1 i j
      norm_num
    rwa [h]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have h1tpos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 htone)
  exact (hA1.smul htpos).add (hA2.smul h1tpos)

/-- Source: Hiai, Theorem 6.4. -/
theorem supportLiebTracePower_jointlyConcave_posDef :
  ∀ {n : ℕ} {p : ℝ} {X : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
      t ∈ Set.Icc (0 : ℝ) 1 →
      Matrix.PosDef A1 →
      Matrix.PosDef A2 →
      Matrix.PosDef B1 →
      Matrix.PosDef B2 →
      t * supportLiebTracePower p A1 B1 X +
          (1 - t) * supportLiebTracePower p A2 B2 X ≤
        supportLiebTracePower p (t • A1 + (1 - t) • A2)
          (t • B1 + (1 - t) • B2) X := by
  intro n p X hp A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  have hImat : ProofNet.MatrixMonotone (powerFn p) :=
    ProofNet.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi
      (TraceMonotonicity.powerFn_operatorMonotone_of_Icc hp)
  have hEquivalences := ProofNet.strictDPIEquivalences (f := powerFn p)
      (TraceMonotonicity.powerFn_continuousOn_Ioi p)
      (TraceMonotonicity.powerFn_pos_Ioi p)
  have hIII : ProofNet.StrictDirectDPI (powerFn p) :=
    hEquivalences.strictInverseDPI_iff_strictDirectDPI.mp
      (hEquivalences.matrixMonotone_iff_strictInverseDPI.mp hImat)
  have hIV : ProofNet.JointConcavity (powerFn p) :=
    hEquivalences.strictDirectDPI_iff_jointConcavity.mp hIII
  have hq := hIV ht.1 ht.2 hA1 hA2 hB1 hB2 (X := X)
  have hAt : Matrix.PosDef (t • A1 + (1 - t) • A2) :=
    matrixPosDef_convex_combo ht hA1 hA2
  have hBt : Matrix.PosDef (t • B1 + (1 - t) • B2) :=
    matrixPosDef_convex_combo ht hB1 hB2
  rw [quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := A1) (B := B1) (X := X) hB1,
    quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := A2) (B := B2) (X := X) hB2,
    quasiEntropy_powerFn_eq_jPowerTrace (p := p) (A := t • A1 + (1 - t) • A2)
      (B := t • B1 + (1 - t) • B2) (X := X) hBt] at hq
  rw [jPowerTrace_eq_liebTracePower_of_posDef (p := p) hA1 hB1,
    jPowerTrace_eq_liebTracePower_of_posDef (p := p) hA2 hB2,
    jPowerTrace_eq_liebTracePower_of_posDef (p := p) hAt hBt] at hq
  rw [supportLiebTracePower_eq_liebTracePower_of_posDef p hA1 hB1,
    supportLiebTracePower_eq_liebTracePower_of_posDef p hA2 hB2,
    supportLiebTracePower_eq_liebTracePower_of_posDef p hAt hBt]
  exact hq

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
