/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
Data-bearing bridge instances for endomorphism algebras `L ℋ`.

This file isolates the data-bearing instance.  Possible instance diamonds with Mathlib's
instances have not been checked systematically.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition
/-! ### Bridge instances for L H -/
section ContinuousLinearMapsAreCStarAlgebras

noncomputable instance continuous_instance {ℋ : Type u} [Qudit ℋ] : CStarAlgebra (B ℋ)
  := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : Norm (L ℋ) where
  norm := fun X => ‖X.toContinuousLinearMap‖

noncomputable instance (ℋ : Type u) [Qudit ℋ] : MetricSpace (L ℋ) :=
  MetricSpace.induced LinearMap.toContinuousLinearMap
    LinearMap.toContinuousLinearMap.injective inferInstance

noncomputable instance c_algebra_instance {ℋ : Type u} [Qudit ℋ] : Algebra ℂ (L ℋ) := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : CStarAlgebra (L ℋ) :=
  let operatorNorm : Norm (L ℋ) := instNormL ℋ
  letI : Norm (L ℋ) := operatorNorm
  let operatorMetric : MetricSpace (L ℋ) := instMetricSpaceL ℋ
  letI : MetricSpace (L ℋ) := operatorMetric
  let operatorNormedRing : NormedRing (L ℋ) :=
    @NormedRing.mk (L ℋ) operatorNorm Module.End.instRing operatorMetric
      (fun x y => continuous_instance.dist_eq x.toContinuousLinearMap y.toContinuousLinearMap)
      (fun x y => continuous_instance.norm_mul_le x.toContinuousLinearMap y.toContinuousLinearMap)
  letI : NormedRing (L ℋ) := operatorNormedRing
  let operatorCompleteSpace : CompleteSpace (L ℋ) :=
    (MetricSpace.isometry_induced LinearMap.toContinuousLinearMap
      LinearMap.toContinuousLinearMap.injective).isUniformInducing.completeSpace_congr
        (fun X => ⟨(X : L ℋ), rfl⟩) |>.mpr continuous_instance.toCompleteSpace
  letI : CompleteSpace (L ℋ) := operatorCompleteSpace
  let operatorCStarRing : CStarRing (L ℋ) :=
    ⟨fun x => continuous_instance.norm_mul_self_le x.toContinuousLinearMap⟩
  letI : CStarRing (L ℋ) := operatorCStarRing
  let operatorNormedAlgebra : NormedAlgebra ℂ (L ℋ) :=
    @NormedAlgebra.mk ℂ (L ℋ) inferInstance operatorNormedRing.toSeminormedRing
      (Module.End.instAlgebra ℂ ℂ ℋ)
      (fun r x => continuous_instance.norm_smul_le r x.toContinuousLinearMap)
  @CStarAlgebra.mk (L ℋ) operatorNormedRing LinearMap.instStarRingId
    operatorCompleteSpace operatorCStarRing operatorNormedAlgebra LinearMap.instStarModuleId

noncomputable instance continuous_sor_instance {ℋ : Type u} [Qudit ℋ] : StarOrderedRing (B ℋ)
  := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : StarOrderedRing (L ℋ) where
  le_iff x y := by
    letI : Ring (L ℋ) := Module.End.instRing
    letI : AddCommGroup (L ℋ) := Module.End.instRing.toAddCommGroup
    letI : AddMonoid (L ℋ) := Module.End.instRing.toAddMonoid
    letI : Mul (L ℋ) := Module.End.instRing.toMul
    have closure_clm_of_closure_lm : ∀ {p : L ℋ},
        p ∈ AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s) →
          p.toContinuousLinearMap ∈
            AddSubmonoid.closure (Set.range fun s : B ℋ ↦ star s * s) := by
      intro p hp
      induction hp using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨s, hs⟩ := hx
        exact AddSubmonoid.subset_closure ⟨s.toContinuousLinearMap, by subst hs; rfl⟩
      | zero => exact AddSubmonoid.zero_mem _
      | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy
    have closure_lm_of_closure_clm : ∀ {p : B ℋ},
        p ∈ AddSubmonoid.closure (Set.range fun s : B ℋ ↦ star s * s) →
          (p : L ℋ) ∈
            AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s) := by
      intro p hp
      induction hp using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨s, hs⟩ := hx
        exact AddSubmonoid.subset_closure ⟨(s : L ℋ), by subst hs; rfl⟩
      | zero => exact AddSubmonoid.zero_mem _
      | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy
    constructor
    · intro h
      obtain ⟨p, hp, hy⟩ :=
        (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mp h
      use (p : L ℋ)
      exact ⟨closure_lm_of_closure_clm hp, LinearMap.toContinuousLinearMap.injective (hy.trans rfl)⟩
    · rintro ⟨p, hp, hy⟩
      apply (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mpr
      exact ⟨p.toContinuousLinearMap, closure_clm_of_closure_lm hp,
        congrArg LinearMap.toContinuousLinearMap hy⟩

end ContinuousLinearMapsAreCStarAlgebras

end Definition

end QuantumChannel
