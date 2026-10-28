/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransportRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.ConcavityToMonotonicity
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.SharedStageCompatibility
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.ConvexityUpgrade

set_option linter.style.longLine false -- unbreakable long import lines

/-!
# HP62 Condition IV to I: convexity upgrade

This module contains the scalar midpoint-convexity gap, the upgrade to
all-H operator concavity, and the final wrappers for the Hiai--Petz 6.2
condition IV to condition I stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-! ### From Matrix Midpoint Concavity to All-H Concavity -/
/--
Matrix midpoint concavity of `f` on the positive ray is equivalent to midpoint
convexity of `-f` in the opposite order. This is the sign-change step in the
Hansen-Pedersen convexity transfer [hiaiyanagi2021].
-/
theorem matrixMidpointConcave_to_matrixMidpointConvex_neg_Ioi
    (f : ℝ → ℝ) :
    HansenPedersen.MatrixOperatorMidpointConcaveOnInterval (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.MatrixOperatorMidpointConvexOnInterval
        (Set.Ioi (0 : ℝ)) (fun x : ℝ => -f x) := by
  intro hmid
  let g : ℝ → ℝ := fun x => -f x
  intro n A B hA hB hσA hσB
  have hmid_f :=
    hmid (n := n) (A := A) (B := B) hA hB hσA hσB
  have hdiff_psd :
      (HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
          (1 / 2 : ℝ) •
            (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)).PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hmid_f)
  have hdiff_eq :
      (1 / 2 : ℝ) •
          (HansenPedersen.matrixCfcR g A + HansenPedersen.matrixCfcR g B) -
        HansenPedersen.matrixCfcR g ((1 / 2 : ℝ) • (A + B)) =
      HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
        (1 / 2 : ℝ) •
          (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) := by
    calc
      (1 / 2 : ℝ) •
            (HansenPedersen.matrixCfcR g A + HansenPedersen.matrixCfcR g B) -
          HansenPedersen.matrixCfcR g ((1 / 2 : ℝ) • (A + B))
          =
        (1 / 2 : ℝ) •
            (-HansenPedersen.matrixCfcR f A + -HansenPedersen.matrixCfcR f B) -
          (-HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))) := by
            simp [HansenPedersen.matrixCfcR, g, cfc_neg]
      _ = HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
            (1 / 2 : ℝ) •
              (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) := by
            ext i j
            simp [sub_eq_add_neg, add_comm]
            ring
  refine sub_nonneg.mp ?_
  rw [hdiff_eq]
  exact (Matrix.nonneg_iff_posSemidef).2 hdiff_psd

/--
Hansen--Pedersen [hiaiyanagi2021]: matrix midpoint concavity on `(0,∞)`
upgrades to all-H operator concavity.
-/
theorem matrixMidpointConcave_to_allHOperatorConcave_Ioi
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.MatrixOperatorMidpointConcaveOnInterval (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  intro hmid
  exact allHOperatorConvex_neg_to_allHOperatorConcave_Ioi f
    (allHOperatorMidpointConvex_to_allHOperatorConvex_Ioi (fun x : ℝ => -f x) hf.neg
      (HansenPedersen.matrixConvexImpliesAllHOperatorMidpointConvex
        (J := Set.Ioi (0 : ℝ)) (convex_Ioi 0) hf.neg
        (matrixMidpointConcave_to_matrixMidpointConvex_neg_Ioi f hmid)))

end

end Quantum.TraceInequality.Loewner.HiaiPetz
