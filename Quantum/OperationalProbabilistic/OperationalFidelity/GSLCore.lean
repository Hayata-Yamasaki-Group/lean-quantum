/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Operational root fidelity

The quantity in this file is the infimum of classical root overlaps over the
finite observation tests allowed by the operational theory.  It is therefore
an allowed-measurement **root fidelity** (not the squared fidelity).
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- Classical root overlap (Bhattacharyya coefficient) of two finite PMFs. -/
noncomputable def classicalRootFidelity {iota : Type} [Fintype iota]
    (p q : PMF iota) : ℝ≥0∞ :=
  ∑ i, (p i * q i).rpow (1 / 2 : ℝ)

theorem classicalRootFidelity_le_one {iota : Type} [Fintype iota]
    (p q : PMF iota) :
    classicalRootFidelity p q ≤ 1 := by
  have hp : ∑ i, p i = (1 : ℝ≥0∞) := by
    simpa using p.tsum_coe
  have hq : ∑ i, q i = (1 : ℝ≥0∞) := by
    simpa using q.tsum_coe
  have hrpow (x : ℝ≥0∞) :
      (x.rpow (1 / 2 : ℝ)).rpow (2 : ℝ) = x := by
    change (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x
    rw [← ENNReal.rpow_mul]
    norm_num
  calc
    classicalRootFidelity p q =
        ∑ i, (p i).rpow (1 / 2 : ℝ) * (q i).rpow (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤
        (∑ i, ((p i).rpow (1 / 2 : ℝ)).rpow (2 : ℝ)).rpow (1 / 2 : ℝ) *
          (∑ i, ((q i).rpow (1 / 2 : ℝ)).rpow (2 : ℝ)).rpow
            (1 / 2 : ℝ) := by
      exact ENNReal.inner_le_Lp_mul_Lq Finset.univ
        (fun i => (p i).rpow (1 / 2 : ℝ))
        (fun i => (q i).rpow (1 / 2 : ℝ))
        (by
          rw [Real.holderConjugate_iff]
          norm_num)
    _ = 1 := by
      simp_rw [hrpow]
      rw [hp, hq]
      norm_num

theorem classicalRootFidelity_ne_top {iota : Type} [Fintype iota]
    (p q : PMF iota) :
    classicalRootFidelity p q ≠ ⊤ :=
  (lt_of_le_of_lt (classicalRootFidelity_le_one p q) ENNReal.one_lt_top).ne

/-- Root fidelity obtained by minimizing the classical root overlap over all
operationally allowed finite observation tests.  This is not the infimum over
all affine effects unless a separate no-restriction bridge is supplied. -/
noncomputable def allowedOperationalRootFidelityENNReal {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) : ℝ≥0∞ :=
  ⨅ M : Test (Sys := Sys) A (𝟙_ Sys),
    classicalRootFidelity
      (observationPMF M rho) (observationPMF M sigma)

/-- Real-valued allowed operational root fidelity. -/
noncomputable def allowedOperationalRootFidelity {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) : ℝ :=
  (allowedOperationalRootFidelityENNReal rho sigma).toReal

theorem allowedOperationalRootFidelityENNReal_le_one {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    allowedOperationalRootFidelityENNReal rho sigma ≤ 1 := by
  calc
    allowedOperationalRootFidelityENNReal rho sigma ≤
        classicalRootFidelity
          (observationPMF (Test.deterministicObservation (Sys := Sys) A) rho)
          (observationPMF (Test.deterministicObservation (Sys := Sys) A) sigma) :=
      iInf_le _ (Test.deterministicObservation (Sys := Sys) A)
    _ ≤ 1 := classicalRootFidelity_le_one _ _

theorem allowedOperationalRootFidelityENNReal_ne_top {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    allowedOperationalRootFidelityENNReal rho sigma ≠ ⊤ :=
  (lt_of_le_of_lt
    (allowedOperationalRootFidelityENNReal_le_one rho sigma)
    ENNReal.one_lt_top).ne

theorem allowedOperationalRootFidelity_nonneg {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    0 ≤ allowedOperationalRootFidelity rho sigma :=
  ENNReal.toReal_nonneg

theorem allowedOperationalRootFidelity_le_one {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    allowedOperationalRootFidelity rho sigma ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    (allowedOperationalRootFidelityENNReal_le_one rho sigma)

end

end OPT
