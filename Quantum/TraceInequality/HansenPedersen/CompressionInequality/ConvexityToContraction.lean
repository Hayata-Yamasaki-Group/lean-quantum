/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ContractionInstances
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.RotatedBlockCompression
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.JuliaUnitary

/-!
# From operator convexity to the contraction inequality

This file proves the `(i) → (ii)` implication in Hiai–Yanagi Theorem 5.1.7.
The proof dilates a contraction to Julia block unitaries, applies midpoint
operator convexity on the two-by-two block space, identifies the diagonal CFC
blocks, and then drops the nonpositive `f 0` contribution.

## Main results

* `ConvexityCharacterization.compressed_spectrum_subset_halfOpenRay`: spectral
  control for a single contraction compression.
* `ConvexityCharacterization.conditionI_implies_conditionII_fixed`: fixed
  Hilbert-space form of `(i) → (ii)`.
* `ConvexityCharacterization.conditionI_implies_conditionII`: global `AllH`
  form of the same implication.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u v

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

open scoped ComplexOrder

section ConditionItoII

open scoped ComplexOrder

/-- Spectral control for a single contraction compression.  If a self-adjoint
operator has spectrum in `halfOpenRay α`, then so does `C* A C` for
`‖C‖ ≤ 1`. -/
lemma compressed_spectrum_subset_halfOpenRay {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {α : WithTop ℝ} {A C : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hC : ‖C‖ ≤ 1) :
    spectrum ℝ (star C * A * C) ⊆ halfOpenRay α := by
  have hA0 : 0 ≤ A := by
    exact HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA (by
      intro x hx
      exact (hσA hx).1)
  have hA_norm_mem : ‖A‖ ∈ spectrum ℝ A := CStarAlgebra.norm_mem_spectrum_of_nonneg hA0
  have hA_norm_lt : ((‖A‖ : ℝ) : WithTop ℝ) < α := (hσA hA_norm_mem).2
  have hA_le : A ≤ (‖A‖ : ℝ) • (1 : L K) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
  have hM0 : (0 : L K) ≤ star C * A * C := star_left_conjugate_nonneg hA0 C
  have hMself : IsSelfAdjoint (star C * A * C) := IsSelfAdjoint.of_nonneg hM0
  have hCA : star C * A * C ≤ (‖A‖ : ℝ) • (star C * C) := by
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc] using
      star_left_conjugate_le_conjugate hA_le C
  have hMβ : star C * A * C ≤ (‖A‖ : ℝ) • (1 : L K) := by
    calc
      star C * A * C ≤ (‖A‖ : ℝ) • (star C * C) := hCA
      _ ≤ (‖A‖ : ℝ) • (1 : L K) := by
          exact smul_le_smul_of_nonneg_left
            (HansenPedersen.ConvexityCharacterization.star_mul_self_le_one_of_norm_le_one
              (K := K) hC)
            (norm_nonneg _)
  intro x hx
  have hxIcc := HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := star C * A * C) (α := 0) (β := ‖A‖) hMself
    (by simpa [Algebra.algebraMap_eq_smul_one] using hM0)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hMβ) hx
  refine ⟨hxIcc.1, ?_⟩
  exact lt_of_le_of_lt (by exact_mod_cast hxIcc.2) hA_norm_lt

private theorem convex_half_apply {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {α : WithTop ℝ} {f : ℝ → ℝ}
    (hConv : HOperatorConvexOnInterval K (halfOpenRay α) f)
    {A B : L K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hσB : spectrum ℝ B ⊆ halfOpenRay α) :
    cfcR (ℋ := K) f ((1 / 2 : ℝ) • (A + B)) ≤
      (1 / 2 : ℝ) • (cfcR (ℋ := K) f A + cfcR (ℋ := K) f B) := by
  have h :=
    hConv (A := A) (B := B) (t := (1 / 2 : ℝ))
      hA hB (by positivity) (by norm_num) hσA hσB
  have hlhs :
      (1 - (1 / 2 : ℝ)) • A + (1 / 2 : ℝ) • B = (1 / 2 : ℝ) • (A + B) := by
    calc
      (1 - (1 / 2 : ℝ)) • A + (1 / 2 : ℝ) • B
          = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by norm_num
      _ = (1 / 2 : ℝ) • (A + B) := by rw [smul_add]
  have hrhs :
      (1 - (1 / 2 : ℝ)) • cfcR (ℋ := K) f A + (1 / 2 : ℝ) • cfcR (ℋ := K) f B =
        (1 / 2 : ℝ) • (cfcR (ℋ := K) f A + cfcR (ℋ := K) f B) := by
    calc
      (1 - (1 / 2 : ℝ)) • cfcR (ℋ := K) f A + (1 / 2 : ℝ) • cfcR (ℋ := K) f B
          = (1 / 2 : ℝ) • cfcR (ℋ := K) f A + (1 / 2 : ℝ) • cfcR (ℋ := K) f B := by
              norm_num
      _ = (1 / 2 : ℝ) • (cfcR (ℋ := K) f A + cfcR (ℋ := K) f B) := by rw [smul_add]
  rw [hlhs, hrhs] at h
  exact h

open scoped HansenPedersen.ConvexityCharacterization.ContractionInstances

/-- Julia-block conjugation of a diagonal block operator, computed once over
atom operators (`U₀ = blockCLM C (-E) D (star C)` shape).  Extracted from
`conditionI_implies_conditionII_fixed`, where the same block normalization was
previously repeated four times inside one declaration. -/
private lemma star_juliaBlock_mul_diag_mul_juliaBlock
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C E D W Z : L K) (hE : star E = E) (hD : star D = D) :
    star (blockCLM C (-E) D (star C)) * blockCLM W 0 0 Z * blockCLM C (-E) D (star C) =
      blockCLM (star C * W * C + D * Z * D)
        (-(star C * W * E) + D * Z * star C)
        (-(E * W * C) + C * Z * D)
        (E * W * E + C * Z * star C) := by
  rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
  simp [hE, hD, mul_assoc, add_comm]

/-- Sign-flipped Julia-block conjugation of a diagonal block operator
(`V = blockCLM C E D (-(star C))` shape), computed once over atom operators.
Extracted from `conditionI_implies_conditionII_fixed`. -/
private lemma star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C E D W Z : L K) (hE : star E = E) (hD : star D = D) :
    star (blockCLM C E D (-(star C))) * blockCLM W 0 0 Z * blockCLM C E D (-(star C)) =
      blockCLM (star C * W * C + D * Z * D)
        (star C * W * E - D * Z * star C)
        (E * W * C - C * Z * D)
        (E * W * E + C * Z * star C) := by
  rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
  simp [hE, hD, mul_assoc, sub_eq_add_neg, add_comm]

/-- Midpoint average of two block operators with equal diagonal and opposite
off-diagonal blocks: the off-diagonal parts cancel and the average collapses to
the block-diagonal operator.  Extracted from
`conditionI_implies_conditionII_fixed`, where the same block normalization was
previously repeated twice (once for the dilated operators, once for their CFC
images). -/
private lemma half_smul_add_blockCLM_of_neg
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a b b' c c' d : L K) (hb : b' = -b) (hc : c' = -c) :
    (1 / 2 : ℝ) • (blockCLM a b' c' d + blockCLM a b c d) =
      HansenPedersen.Internal.diagMapCLM a d := by
  subst hb hc
  rw [blockCLM_add, smul_blockCLM]
  have ha2 : (1 / 2 : ℝ) • (a + a) = a := by
    rw [smul_add, ← add_smul]
    norm_num
  have hd2 : (1 / 2 : ℝ) • (d + d) = d := by
    rw [smul_add, ← add_smul]
    norm_num
  rw [neg_add_cancel, neg_add_cancel, smul_zero, ha2, hd2, blockCLM_zero_zero]

/-- Two-sided compression of the real CFC of `0` reduces to a scalar multiple:
`cfcR f 0` is the constant `f 0` times the identity, so `D * cfcR f 0 * D`
collapses to `f 0 • (D * D)`.  Extracted from
`conditionI_implies_conditionII_fixed`, where this CFC normalization was the
heaviest single step of the sign-condition argument. -/
private lemma mul_cfcR_zero_mul {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint]
    (f : ℝ → ℝ) (D : L K) :
    D * cfcR (ℋ := K) f 0 * D = (f 0 : ℝ) • (D * D) := by
  simp [cfcR, Algebra.algebraMap_eq_smul_one]

/-- Discarding the `f 0` defect term: when `f 0 ≤ 0` and `D` is self-adjoint,
`X + D * cfcR f 0 * D ≤ X`. -/
private lemma add_mul_cfcR_zero_mul_le {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint]
    (f : ℝ → ℝ) (hf0 : f 0 ≤ 0) (X D : L K) (hD : star D = D) :
    X + D * cfcR (ℋ := K) f 0 * D ≤ X := by
  have hDD : 0 ≤ D * D := by
    have h := star_mul_self_nonneg D
    rwa [hD] at h
  have h : D * cfcR (ℋ := K) f 0 * D ≤ 0 := by
    rw [mul_cfcR_zero_mul]
    exact smul_nonpos_of_nonpos_of_nonneg hf0 hDD
  simpa using add_le_add_left h X

-- The proof below runs with the default heartbeat budget: `IsSelfAdjoint (0 : L H)` is
-- proved once (its inline elaboration re-ran a deep star-instance unification), and the
-- midpoint block-cancellation and `cfcR f 0` compression normalizations are done by the
-- atom-level private lemmas above.
/-- Fixed-Hilbert-space form of `(i) → (ii)` in Theorem 5.1.7.  It derives the
Jensen contraction inequality from operator convexity by Julia-block dilation,
midpoint convexity on the block space, and the sign condition `f 0 ≤ 0`.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
theorem conditionI_implies_conditionII_fixed {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hI : ConditionI.{u} α f)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    {A C : L H}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hC : ‖C‖ ≤ 1) :
    cfcR (ℋ := H) f (star C * A * C) ≤ star C * cfcR (ℋ := H) f A * C := by
  /- Step 1: Build the Julia dilation encoding the contraction as a midpoint problem. -/
  haveI : Nontrivial H := HansenPedersen.nontrivial_of_nontrivial_L
  haveI : Nontrivial (WithLp 2 (H × H)) := inferInstance
  let E : L H := defectLeft C
  let D : L H := defectRight C
  let A0 : L (WithLp 2 (H × H)) := HansenPedersen.Internal.diagMapCLM A 0
  let F0 : L (WithLp 2 (H × H)) :=
    HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0)
  let U0 : L (WithLp 2 (H × H)) := blockCLM C (-E) D (star C)
  let S0 : L (WithLp 2 (H × H)) := blockCLM (1 : L H) 0 0 (- (1 : L H))
  let U : unitary (L (WithLp 2 (H × H))) := ⟨U0, julia_block_mem_unitary (K := H) hC⟩
  let S : unitary (L (WithLp 2 (H × H))) := ⟨S0, signFlip_block_mem_unitary (K := H)⟩
  let V : unitary (L (WithLp 2 (H × H))) := U * S
  let X : L (WithLp 2 (H × H)) := star (↑U : L (WithLp 2 (H × H))) * A0 * (↑U : L _)
  let Y : L (WithLp 2 (H × H)) := star (↑V : L (WithLp 2 (H × H))) * A0 * (↑V : L _)
  let M : L H := star C * A * C
  let N : L H := E * A * E
  let R : L H := star C * cfcR (ℋ := H) f A * C + D * cfcR (ℋ := H) f 0 * D
  let T : L H := E * cfcR (ℋ := H) f A * E + C * cfcR (ℋ := H) f 0 * star C
  have hEstar : star E = E := (defectLeft_selfAdjoint (K := H) C).star_eq
  have hDstar : star D = D := (defectRight_selfAdjoint (K := H) C).star_eq
  have h0self : IsSelfAdjoint (0 : L H) := IsSelfAdjoint.zero _
  /- Step 2: Transfer self-adjointness and spectral control from A to the dilated conjugates. -/
  have hA0self : IsSelfAdjoint A0 := by
    simpa [A0] using HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hA h0self
  have hσA0 : spectrum ℝ A0 ⊆ halfOpenRay α := by
    simpa [A0] using spectrum_diagMapCLM_subset_halfOpenRay
      (K := H) hA h0self hσA (spectrum_zero_subset_halfOpenRay (K := H) hα)
  have hXself : IsSelfAdjoint X := by
    exact hA0self.conjugate' _
  have hYself : IsSelfAdjoint Y := by
    exact hA0self.conjugate' _
  have hσX : spectrum ℝ X ⊆ halfOpenRay α := by
    have hspec : spectrum ℝ X = spectrum ℝ A0 := by
      dsimp [X]
      exact Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A0) (U := U)
    rw [hspec]
    exact hσA0
  have hσY : spectrum ℝ Y ⊆ halfOpenRay α := by
    have hspec : spectrum ℝ Y = spectrum ℝ A0 := by
      dsimp [Y]
      exact Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A0) (U := V)
    rw [hspec]
    exact hσA0
  have hConv :
      HOperatorConvexOnInterval (WithLp 2 (H × H)) (halfOpenRay α) f :=
    hI.1 (WithLp 2 (H × H))
  have hA0block : A0 = blockCLM A 0 0 0 := by
    dsimp [A0]
    exact (blockCLM_zero_zero (K := H) A (0 : L H)).symm
  /- Step 3: Rewrite the conjugates so off-diagonal blocks cancel on averaging. -/
  have hXblock :
      X =
        blockCLM M (-(star C * A * E)) (-(E * A * C)) N := by
    dsimp only [X, U, U0]
    rw [hA0block]
    rw [star_juliaBlock_mul_diag_mul_juliaBlock (K := H) C E D A 0 hEstar hDstar]
    simp [M, N]
  have hVblock :
      (↑V : L (WithLp 2 (H × H))) = blockCLM C E D (- star C) := by
    dsimp [V, U, S, U0, S0]
    rw [blockCLM_mul]
    simp
  have hYblock :
      Y =
        blockCLM M (star C * A * E) (E * A * C) N := by
    dsimp only [Y]
    rw [hVblock]
    rw [hA0block]
    rw [star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock (K := H) C E D A 0 hEstar hDstar]
    simp [M, N]
  have havg :
      (1 / 2 : ℝ) • (X + Y) = HansenPedersen.Internal.diagMapCLM M N := by
    rw [hXblock, hYblock]
    exact half_smul_add_blockCLM_of_neg M _ _ _ _ N rfl rfl
  have hσM : spectrum ℝ M ⊆ halfOpenRay α := by
    simpa [M] using compressed_spectrum_subset_halfOpenRay
      (K := H) hA hσA hC
  have hσN : spectrum ℝ N ⊆ halfOpenRay α := by
    have hEnorm : ‖E‖ ≤ 1 := defectLeft_norm_le_one (K := H) hC
    simpa [N, E, hEstar] using compressed_spectrum_subset_halfOpenRay
      (K := H) hA hσA hEnorm
  have hMself : IsSelfAdjoint M := by
    simpa [M] using star_mul_selfAdjoint_mul (K := H) (T := A) (C := C) hA
  have hNself : IsSelfAdjoint N := by
    simpa [N, E, hEstar] using star_mul_selfAdjoint_mul (K := H) (T := A) (C := E) hA
  /- Step 4: Identify the averaged CFC and the two conjugate CFCs in diagonal form. -/
  have hcfavg :
      cfcR (ℋ := WithLp 2 (H × H)) f ((1 / 2 : ℝ) • (X + Y)) =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f N) := by
    rw [havg]
    simpa using cfcR_diagMapCLM (K := H) hf hMself hNself hσM hσN
  have hcfA0 :
      cfcR (ℋ := WithLp 2 (H × H)) f A0 = F0 := by
    simpa [A0, F0] using cfcR_diagMapCLM (K := H) hf hA h0self
      hσA (spectrum_zero_subset_halfOpenRay (K := H) hα)
  have hcfX :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        star (↑U : L (WithLp 2 (H × H))) * F0 * (↑U : L _) := by
    rw [← hcfA0]
    exact cfcR_unitary_conj (K := WithLp 2 (H × H)) hf hA0self hσA0 U
  have hcfY :
      cfcR (ℋ := WithLp 2 (H × H)) f Y =
        star (↑V : L (WithLp 2 (H × H))) * F0 * (↑V : L _) := by
    rw [← hcfA0]
    exact cfcR_unitary_conj (K := WithLp 2 (H × H)) hf hA0self hσA0 V
  have hcfXblock :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        blockCLM R
          (-(star C * cfcR (ℋ := H) f A * E) + D * cfcR (ℋ := H) f 0 * star C)
          (-(E * cfcR (ℋ := H) f A * C) + C * cfcR (ℋ := H) f 0 * D)
          T := by
    rw [hcfX]
    dsimp only [F0, U, U0]
    rw [← blockCLM_zero_zero]
    rw [star_juliaBlock_mul_diag_mul_juliaBlock (K := H) C E D
      (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) hEstar hDstar]
  have hcfYblock :
      cfcR (ℋ := WithLp 2 (H × H)) f Y =
        blockCLM R
          (star C * cfcR (ℋ := H) f A * E - D * cfcR (ℋ := H) f 0 * star C)
          (E * cfcR (ℋ := H) f A * C - C * cfcR (ℋ := H) f 0 * D)
          T := by
    rw [hcfY, hVblock]
    dsimp only [F0]
    rw [← blockCLM_zero_zero]
    rw [star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock (K := H) C E D
      (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) hEstar hDstar]
  have hrhs :
      (1 / 2 : ℝ) •
          (cfcR (ℋ := WithLp 2 (H × H)) f X + cfcR (ℋ := WithLp 2 (H × H)) f Y) =
        HansenPedersen.Internal.diagMapCLM R T := by
    rw [hcfXblock, hcfYblock]
    exact half_smul_add_blockCLM_of_neg R _ _ _ _ T
      (by rw [neg_sub, sub_eq_neg_add]) (by rw [neg_sub, sub_eq_neg_add])
  /- Step 5: Apply midpoint convexity on the dilation to obtain a diagonal block inequality. -/
  have hconv :
      cfcR (ℋ := WithLp 2 (H × H)) f ((1 / 2 : ℝ) • (X + Y)) ≤
        (1 / 2 : ℝ) •
          (cfcR (ℋ := WithLp 2 (H × H)) f X + cfcR (ℋ := WithLp 2 (H × H)) f Y) := by
    exact convex_half_apply (K := WithLp 2 (H × H)) hConv hXself hYself hσX hσY
  have hdiag :
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f N) ≤
        HansenPedersen.Internal.diagMapCLM R T := by
    rw [hcfavg, hrhs] at hconv
    exact hconv
  /- Step 6: Read the first diagonal block and discard the f 0 defect term. -/
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    refine (star_mul_selfAdjoint_mul
      (K := H)
      (T := cfcR (ℋ := H) f A)
      (C := C)
      (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := A))).add ?_
    simpa [D, hDstar] using
      (star_mul_selfAdjoint_mul
        (K := H)
        (T := cfcR (ℋ := H) f 0)
        (C := D)
        (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := 0)))
  have hcfM_le : cfcR (ℋ := H) f M ≤ R := by
    exact diagMapCLM_fst_le_of_le
      (K := H)
      (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := M))
      hRself
      hdiag
  exact le_trans hcfM_le (add_mul_cfcR_zero_mul_le f hI.2 _ D hDstar)

/-- Global `AllH` form of `(i) → (ii)` in Theorem 5.1.7.  It applies the
fixed-space contraction inequality on each Hilbert space.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
theorem conditionI_implies_conditionII {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hI : ConditionI.{u} α f) :
    ConditionII.{u} α f := by
  intro H _ _ _ _ _ A C hA hσA hC
  exact conditionI_implies_conditionII_fixed hf hα hI hA hσA hC

end ConditionItoII

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
