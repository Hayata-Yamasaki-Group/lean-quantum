/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Finite operational measurement statistics

This file packages normalized OPT states (`NormalizedState`) and the probability mass function
produced by a finite observation test (`observationPMF`), including the deterministic one-outcome
observation.
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- A physical state together with normalization against the deterministic effect. -/
abbrev NormalizedState (A : Sys) :=
  {rho : State (Sys := Sys) A // IsNormalizedState (Sys := Sys) rho}

/-- The PMF obtained by running an operationally allowed finite observation
test on a normalized state. -/
noncomputable def observationPMF {A : Sys}
    (M : Test (Sys := Sys) A (𝟙_ Sys))
    (rho : NormalizedState (Sys := Sys) A) : PMF M.ι :=
  PMF.ofFintype
    (fun i => ENNReal.ofReal
      (prob (Sys := Sys) (M.outcome i) rho.1))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · have htotal : Finset.univ.sum M.outcome =
            detEffect (Sys := Sys) A :=
          CausalOperationalProbabilisticTheory.detEffect_unique
            (Sys := Sys)
            (CausalOperationalProbabilisticTheory.test_total_channel
              (Sys := Sys) M.outcome M.isTest)
        have hsum :
            Finset.univ.sum
                (fun i : M.ι => prob (Sys := Sys) (M.outcome i) rho.1) =
              prob (Sys := Sys) (Finset.univ.sum M.outcome) rho.1 := by
          change Finset.univ.sum
              (fun i : M.ι =>
                (effectEvalLinearMap (Sys := Sys) (A := A) rho.1) (M.outcome i)) =
            (effectEvalLinearMap (Sys := Sys) (A := A) rho.1)
              (Finset.univ.sum M.outcome)
          exact (map_sum
            (effectEvalLinearMap (Sys := Sys) (A := A) rho.1)
            M.outcome Finset.univ).symm
        rw [hsum, htotal, rho.2.2]
        exact ENNReal.ofReal_one
      · intro i _hi
        exact prob_nonneg_of_isState_isEffect (Sys := Sys) rho.2.1
          (by
            simpa [IsEffect] using
              (OperationalProbabilisticTheory.test_transformation
                (Sys := Sys) M.isTest i)))

@[simp]
theorem observationPMF_apply {A : Sys}
    (M : Test (Sys := Sys) A (𝟙_ Sys))
    (rho : NormalizedState (Sys := Sys) A) (i : M.ι) :
    observationPMF M rho i =
      ENNReal.ofReal (prob (Sys := Sys) (M.outcome i) rho.1) :=
  rfl

/-- The singleton observation consisting of the deterministic effect. -/
noncomputable def Test.deterministicObservation (A : Sys) :
    Test (Sys := Sys) A (𝟙_ Sys) where
  ι := PUnit
  outcome := fun _ => detEffect (Sys := Sys) A
  isTest :=
    OperationalProbabilisticTheory.channel_singleton_test
      (Sys := Sys)
      (CausalOperationalProbabilisticTheory.detEffect_channel
        (Sys := Sys) A)

end

end OPT
