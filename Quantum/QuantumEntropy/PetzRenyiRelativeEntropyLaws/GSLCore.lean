/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiFiniteAdditivity.GSLCore

open QuantumState TensorProduct

/-!
# Matrix relative-entropy laws for the Petz Rényi divergence

This file defines the structure `PetzMatrixRelativeEntropyLaws`, which records
data processing, tensor additivity, and binary normalization for the Petz
quantum Rényi divergence at an order in the closed interval from zero to two.
-/

namespace OPT

universe u v

/-- The concrete density-matrix laws required of the Petz quantum Rényi
divergence at a fixed order. -/
structure PetzMatrixRelativeEntropyLaws (alpha : PetzRenyiOrder) : Prop where
  dataProcessing :
    ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
      (E : QuantumChannel.CPTP H K)
      (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma),
      petzQuantumRenyiDivergence alpha (E.toFun rho) (E.toFun sigma)
          (quantumFMapDensity E rho hrho) (quantumFMapDensity E sigma hsigma) ≤
        petzQuantumRenyiDivergence alpha rho sigma hrho hsigma
  tensorAdditivity :
    ∀ {H : Type u} {K : Type v} [Qudit H] [Qudit K]
      [Nontrivial H] [Nontrivial K] [Nontrivial (H ⊗[ℂ] K)]
      (rho₁ sigma₁ : L H) (rho₂ sigma₂ : L K)
      (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
      (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂),
      petzQuantumRenyiDivergence alpha
          (TensorProduct.map rho₁ rho₂ : L (H ⊗[ℂ] K))
          (TensorProduct.map sigma₁ sigma₂)
          (isDensity_tensorProduct rho₁ rho₂ hrho₁ hrho₂)
          (isDensity_tensorProduct sigma₁ sigma₂ hsigma₁ hsigma₂) =
        petzQuantumRenyiDivergence alpha rho₁ sigma₁ hrho₁ hsigma₁ +
          petzQuantumRenyiDivergence alpha rho₂ sigma₂ hrho₂ hsigma₂
  binaryNormalization :
    ∀ {H : Type u} [Qudit H] [Nontrivial H] (pair : PetzBinaryPurePair H),
      petzQuantumRenyiDivergence alpha pair.pure₀ pair.uniform
        pair.pure₀_density pair.uniform_density = 1

end OPT
