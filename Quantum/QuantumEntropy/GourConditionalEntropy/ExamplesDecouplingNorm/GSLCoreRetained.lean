/-
Trace norm and Hilbert--Schmidt norm of Hermitian operators: for a Hermitian `M`,
`T₁(M) = Σ_i |λ_i(M)|`, the maximum of `Re Tr (K M)` over Hermitian contractions
`−I ≤ K ≤ I` is `T₁(M)`, attained at `K = sign(M)`, and `T₁`, `H₂` are finite and continuous
(cf. Gour §7.7).
-/

import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCore

namespace GourConditionalEntropy

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

theorem w40_hermitian_norm_dictionary : ∀ {H : Type u} [Qudit.{u} H]
    [Nontrivial H] (M : L H) (hM : IsSelfAdjoint M),
    let hsym := (LinearMap.isSymmetric_iff_isSelfAdjoint M).mpr hM
    w40T₁ M = ∑ i, |hsym.eigenvalues (rfl : Module.finrank ℂ H = Module.finrank ℂ H) i| ∧
    ((w40H₂ M) ^ 2 : ℝ) = w40Q M ∧
    IsGreatest {r : ℝ | ∃ K : L H, IsSelfAdjoint K ∧ -(1 : L H) ≤ K ∧ K ≤ 1 ∧
      r = (Tr (K * M)).re} (w40T₁ M) ∧
    Continuous (fun M : {X : L H // IsSelfAdjoint X} => w40T₁ M.1) ∧
    Continuous (fun M : {X : L H // IsSelfAdjoint X} => w40H₂ M.1) := by
  intro H _ _ M hM
  obtain ⟨hspec, hbound, hsign⟩ := (GourConditionalEntropy.w40_trace_norm_spectral_variational.{u})
    M hM
  refine ⟨hspec, ?_, ?_, (GourConditionalEntropy.w40_trace_norm_continuity.{u})⟩
  · have htrace :
        inner ℂ (HilbertSchmidtOperatorSpace.ofOp M.toContinuousLinearMap)
          (HilbertSchmidtOperatorSpace.ofOp M.toContinuousLinearMap) = Tr (star M * M) := by
      rw [HilbertSchmidtOperatorSpace.hsInner_eq_trace]
      rfl
    have hnonneg : 0 ≤ (Tr (star M * M)).re := by
      rw [← htrace]
      exact inner_self_nonneg (𝕜 := ℂ)
    rw [w40H₂, Real.sq_sqrt hnonneg, w40Q]
    have hreal := inner_self_ofReal_re (𝕜 := ℂ)
      (HilbertSchmidtOperatorSpace.ofOp M.toContinuousLinearMap)
    rw [htrace] at hreal
    simpa only [hM.star_eq, pow_two] using hreal
  · refine ⟨?_, ?_⟩
    · exact ⟨cfc (fun x : ℝ => if x = 0 then 0 else if x < 0 then -1 else 1) M,
        hsign.1, hsign.2.1, hsign.2.2.1, hsign.2.2.2.symm⟩
    · rintro r ⟨K, hK, hlo, hhi, rfl⟩
      exact hbound K hK hlo hhi

end

end GourConditionalEntropy
