/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.SpectralBounds

/-!
# From contraction Jensen to the two-variable Jensen inequality

This file proves the `(ii) → (iii)` implication in the Hansen–Pedersen
characterization.  The proof applies the contraction inequality to a block
diagonal operator and a contractive column, then reads off the first diagonal
entry of the resulting block order.

## Main results

* `conditionII_implies_conditionIII`: global `ConditionII → ConditionIII`
  wrapper.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section ContractionToTwoVariable

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

/-- Fixed-Hilbert-space form of `(ii) → (iii)` in Theorem 5.1.7.  It applies
the contraction inequality to `diag(A, B)` and the column block `(C, D)`.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
private theorem conditionII_implies_conditionIII_fixed {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hII : ConditionII.{u} α f)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    {A B C D : L H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hσB : spectrum ℝ B ⊆ halfOpenRay α)
    (hCD : star C * C + star D * D ≤ (1 : L H)) :
    cfcR (ℋ := H) f (star C * A * C + star D * B * D) ≤
      star C * cfcR (ℋ := H) f A * C + star D * cfcR (ℋ := H) f B * D := by
  haveI : Nontrivial H := HansenPedersen.nontrivial_of_nontrivial_L
  haveI : Nontrivial (WithLp 2 (H × H)) := inferInstance
  let X := HansenPedersen.Internal.diagMapCLM A B
  let Y := blockCLM C 0 D 0
  let M := star C * A * C + star D * B * D
  let N := star C * cfcR (ℋ := H) f A * C + star D * cfcR (ℋ := H) f B * D
  have hXself : IsSelfAdjoint X := HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hA hB
  have hσX : spectrum ℝ X ⊆ halfOpenRay α :=
    spectrum_diagMapCLM_subset_halfOpenRay hA hB hσA hσB
  have hYnorm : ‖Y‖ ≤ 1 := blockCLM_col_norm_le_one hCD
  have hmain := hII (K := WithLp 2 (H × H)) (A := X) (C := Y) hXself hσX hYnorm
  have hXY :
      star Y * X * Y = HansenPedersen.Internal.diagMapCLM M 0 := by
    dsimp [X, Y, M]
    rw [blockCLM_col_star]
    calc
      blockCLM (star C) (star D) 0 0 * HansenPedersen.Internal.diagMapCLM A B * blockCLM C 0 D 0
          = blockCLM (star C) (star D) 0 0 * blockCLM A 0 0 B * blockCLM C 0 D 0 := by
              simp [blockCLM_zero_zero]
      _ = blockCLM (star C * A) (star D * B) 0 0 * blockCLM C 0 D 0 := by
            rw [blockCLM_mul]
            simp
      _ = blockCLM (star C * A * C + star D * B * D) 0 0 0 := by
            rw [blockCLM_mul]
            simp [mul_assoc]
      _ = HansenPedersen.Internal.diagMapCLM M 0 := by
            simp [blockCLM_zero_zero, M]
  have hcfX :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f B) := by
    simpa [X] using cfcR_diagMapCLM (K := H) hf hA hB hσA hσB
  have hright :
      star Y * cfcR (ℋ := WithLp 2 (H × H)) f X * Y =
        HansenPedersen.Internal.diagMapCLM N 0 := by
    dsimp [Y, N]
    rw [hcfX, blockCLM_col_star]
    calc
      blockCLM (star C) (star D) 0 0 *
          HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f B) *
          blockCLM C 0 D 0
          = blockCLM (star C) (star D) 0 0 *
              blockCLM (cfcR (ℋ := H) f A) 0 0 (cfcR (ℋ := H) f B) *
              blockCLM C 0 D 0 := by
                simp [blockCLM_zero_zero]
      _ = blockCLM (star C * cfcR (ℋ := H) f A)
            (star D * cfcR (ℋ := H) f B) 0 0 * blockCLM C 0 D 0 := by
            rw [blockCLM_mul]
            simp
      _ = blockCLM N 0 0 0 := by
            rw [blockCLM_mul]
            simp [N, mul_assoc]
      _ = HansenPedersen.Internal.diagMapCLM N 0 := by
            simp [blockCLM_zero_zero, N]
  have hσM :
      spectrum ℝ M ⊆ halfOpenRay α :=
    compressed_sum_spectrum_subset_halfOpenRay (K := H) hα hA hB hσA hσB hCD
  have hMself : IsSelfAdjoint M := by
    dsimp [M]
    exact (star_mul_selfAdjoint_mul hA).add (star_mul_selfAdjoint_mul hB)
  have hcfAself : IsSelfAdjoint (cfcR (ℋ := H) f A) := by
    simp [cfcR]
  have hcfBself : IsSelfAdjoint (cfcR (ℋ := H) f B) := by
    simp [cfcR]
  have hNself : IsSelfAdjoint N := by
    dsimp [N]
    exact (star_mul_selfAdjoint_mul hcfAself).add (star_mul_selfAdjoint_mul hcfBself)
  have hcfMself : IsSelfAdjoint (cfcR (ℋ := H) f M) := by
    simp [cfcR]
  have hcfM :
      cfcR (ℋ := WithLp 2 (H × H)) f (HansenPedersen.Internal.diagMapCLM M 0) =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f 0) := by
    simpa using cfcR_diagMapCLM (K := H) hf
      hMself (IsSelfAdjoint.zero _) hσM (spectrum_zero_subset_halfOpenRay (K := H) hα)
  have hdiag :
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f 0) ≤
        HansenPedersen.Internal.diagMapCLM N 0 := by
    simpa [hXY, hcfM, hright] using hmain
  exact diagMapCLM_fst_le_of_le hcfMself hNself hdiag

/-- Global `ConditionII → ConditionIII` implication in Theorem 5.1.7, obtained
by applying the fixed-Hilbert-space block argument uniformly in `H`.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
theorem conditionII_implies_conditionIII {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hII : ConditionII.{u} α f) :
    ConditionIII.{u} α f := by
  intro H _ _ _ _ _ A B C D hA hB hσA hσB hCD
  exact conditionII_implies_conditionIII_fixed hf hα hII hA hB hσA hσB hCD

end ContractionToTwoVariable

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
