/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegKWExtra.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore

/-!
# Khatri--Wilde Stein protocols and rates

This file defines binary testing protocols and the predicates for achievable
and strong-converse rates used by the quantum Stein lemma in Khatri--Wilde,
arXiv:2011.04672v2, `entropies.tex:7178--7387`. Tensor copies use `systemPow`
and `densityTensorPow`. The remaining lemmas establish Petz and sandwiched
Rényi divergence identities on the tensor unit, tensor-power additivity,
and convergence to Umegaki relative entropy as the order tends to one.
-/

noncomputable section

open QuantumState
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology

namespace QuantumModel
namespace NativeStein

open NativeHypothesisTesting
open Filter

local instance operatorSelfAdjointUnitalCFCStein (A : Sys) :
    ContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance operatorNonnegSpectrumStein (A : Sys) :
    NonnegSpectrumClass ℝ (Operator A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- A binary test on `n` tensor copies with upper bounds on its type-II and
type-I errors.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7178--7199`. -/
structure HypothesisTestingProtocol
    {A : Sys} (n : ℕ) (rho sigma : DensityMatrix A)
    (epsilonII epsilonI : ℝ≥0) where
  test : Effect (systemPow A n)
  typeII_le :
    Real.toNNReal
      (testValue test (densityTensorPow sigma n).operator) ≤
      epsilonII
  typeI_le :
    Real.toNNReal
      (1 - testValue test (densityTensorPow rho n).operator) ≤
      epsilonI

/-- A nonnegative real exponent achievable with every fixed positive type-I
error allowance and every positive rate slack.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7201--7213`. -/
def IsAchievableRate {A : Sys}
    (rho sigma : DensityMatrix A) (R : ℝ) : Prop :=
  0 ≤ R ∧
    ∀ epsilon : OPT.ProbabilityLevel, 0 < epsilon.1 →
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ n in atTop,
          Nonempty
            (HypothesisTestingProtocol n rho sigma
              (OPT.binaryExponentProbability
                ((n : ℝ) * (R - delta)))
              ⟨epsilon.1, epsilon.2.1⟩)

/-- A nonnegative real rate above which exponentially small type-II error is
eventually incompatible with every fixed type-I allowance below one.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7214--7226`. -/
def IsStrongConverseRate {A : Sys}
    (rho sigma : DensityMatrix A) (R : ℝ) : Prop :=
  0 ≤ R ∧
    ∀ epsilon : OPT.ProbabilityLevel, epsilon.1 < 1 →
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ n in atTop,
          ¬ Nonempty
            (HypothesisTestingProtocol n rho sigma
              (OPT.binaryExponentProbability
                ((n : ℝ) * (R + delta)))
              ⟨epsilon.1, epsilon.2.1⟩)

/-- Density-pair sandwiched Rényi divergence converges from above to Umegaki
relative entropy.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:2174--2257,7311--7315` (`prop-sand_ren_ent_lim`,
`eq:QEI:sandwiched-Renyi-to-Umegaki`), whose order-one limit is invoked in
the strong-converse half of Stein's lemma. -/
theorem sandwichedRenyiDivBits_tendsto_umegaki
    {A : Sys} (rho sigma : DensityMatrix A) :
    Tendsto (fun alpha : ℝ => sandwichedRenyiDivBits alpha rho sigma.operator)
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiRelEntropyBits rho sigma.operator)) :=
  sandwichedRenyiDivBits_tendsto_umegaki_of_nonneg rho sigma.operator sigma.nonneg

end NativeStein
end QuantumModel
