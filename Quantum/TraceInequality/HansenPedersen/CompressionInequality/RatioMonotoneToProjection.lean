/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ProjectionInstances
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ConvexityToContraction
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ContractionToTwoVariable
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ContractionToRatioMonotone

/-!
# Ratio monotonicity implies projection compression

This module proves the regularization step from condition V, monotonicity of
`t ↦ f t / t`, to condition IV, the projection compression inequality.  The
argument first handles strictly positive spectra using square-root
intertwining identities, then regularizes projections by positive contractions
and passes to the limit.

## Main results

* `conditionV_implies_conditionIV`: condition V implies the projection
  compression inequality.
* Scoped reducible instance caches for the real scalar and order
  structure on `L K`, used to keep the regularization proof elaboration stable.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u v

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section RatioMonotoneToProjection

open scoped ComplexOrder
open Internal

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

open scoped HansenPedersen.ConvexityCharacterization.ProjectionInstances

omit [Nontrivial (L K)] in
private theorem cfcR_diagMapCLM_union {g : ℝ → ℝ} {a b : L K}
    (hg : ContinuousOn g (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfcR (ℋ := WithLp 2 (K × K)) g (HansenPedersen.Internal.diagMapCLM a b) =
      HansenPedersen.Internal.diagMapCLM
        (cfcR (ℋ := K) g a)
        (cfcR (ℋ := K) g b) := by
  simpa [cfcR] using
    (HansenPedersen.cfcR_diagMapCLM_union (ℋ := K) (f := g) (a := a) (b := b)
      (hf := hg) (ha := ha) (hb := hb))

omit [Nontrivial (L K)] in
-- Local spectral-set version of Lemma 5.1.6(2), for functions only continuous on the spectra
-- of `A* A` and `A A*`.
private theorem intertwining_cfcR_of_union {A : L K} {g : ℝ → ℝ}
    (hg : ContinuousOn g (spectrum ℝ ((star A) * A) ∪ spectrum ℝ (A * star A))) :
    A * cfcR (ℋ := K) g ((star A) * A) = cfcR (ℋ := K) g (A * star A) * A := by
  let T : L (WithLp 2 (K × K)) := Internal.offDiagCLM (star A) A
  have hT2 : T ^ 2 =
      HansenPedersen.Internal.diagMapCLM ((star A) * A) (A * star A) := by
    simpa [T, pow_two] using
      Internal.offDiagCLM_mul_offDiagCLM (star A) A (star A) A
  have hdiag :
      cfcR (ℋ := WithLp 2 (K × K)) g (T ^ 2) =
        HansenPedersen.Internal.diagMapCLM
          (cfcR (ℋ := K) g ((star A) * A))
          (cfcR (ℋ := K) g (A * star A)) := by
    rw [hT2]
    exact cfcR_diagMapCLM_union (K := K) (g := g) (hg := hg)
      (ha := IsSelfAdjoint.star_mul_self A) (hb := IsSelfAdjoint.mul_star_self A)
  have hT2T : Commute (T ^ 2) T := (Commute.refl T).pow_left 2
  have hcomm : Commute (cfcR (ℋ := WithLp 2 (K × K)) g (T ^ 2)) T := hT2T.cfc_real g
  have hEq :
      cfcR (ℋ := WithLp 2 (K × K)) g (T ^ 2) * T =
        T * cfcR (ℋ := WithLp 2 (K × K)) g (T ^ 2) := hcomm.eq
  have hOff :
      Internal.offDiagCLM
          (cfcR (ℋ := K) g ((star A) * A) * star A)
          (cfcR (ℋ := K) g (A * star A) * A) =
        Internal.offDiagCLM
          (star A * cfcR (ℋ := K) g (A * star A))
          (A * cfcR (ℋ := K) g ((star A) * A)) := by
    simpa [T, hdiag, Internal.diagMapCLM_mul_offDiagCLM,
      Internal.offDiagCLM_mul_diagMapCLM] using hEq
  rcases Internal.offDiagCLM_inj (K := K) hOff with ⟨_, hsnd⟩
  simpa [cfcR] using hsnd.symm

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
@[fun_prop] private lemma continuousOn_ratio_of_positiveSpectrum
    {α : WithTop ℝ} {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay α))
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    ContinuousOn (fun t : ℝ ↦ f t / t) (spectrum ℝ A) := by
  have hcont_f : ContinuousOn f (spectrum ℝ A) :=
    hf.mono (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA)
  exact hcont_f.div continuousOn_id <| by
    intro x hx
    exact ne_of_gt ((hσA hx).1)

private lemma spectrum_subset_positiveOpenRay_of_lower_bound
    {α : WithTop ℝ} {m : ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hm : 0 < m)
    (hAlo : (m : ℝ) • (1 : L K) ≤ A)
    (hσAhi : spectrum ℝ A ⊆ halfOpenRay α) :
    spectrum ℝ A ⊆ positiveOpenRay α := by
  intro x hx
  have hxIcc := HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := A) (α := m) (β := ‖A‖) hA
    (by simpa [Algebra.algebraMap_eq_smul_one] using hAlo)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self) hx
  exact ⟨lt_of_lt_of_le hm hxIcc.1, (hσAhi hx).2⟩

private lemma spectrum_subset_Icc_of_pos_contraction {m : ℝ} {C : L K}
    (hC : IsSelfAdjoint C) (_hm : 0 ≤ m)
    (hClo : (m : ℝ) • (1 : L K) ≤ C)
    (hChi : C ≤ (1 : L K)) :
    spectrum ℝ C ⊆ Set.Icc m 1 := by
  intro x hx
  exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := C) (α := m) (β := 1) hC
    (by simpa [Algebra.algebraMap_eq_smul_one] using hClo)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hChi) hx

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma norm_le_one_of_nonneg_le_one {C : L K}
    (hC0 : 0 ≤ C) (hC1 : C ≤ (1 : L K)) :
    ‖C‖ ≤ 1 := by
  simpa [one_smul] using (CStarAlgebra.norm_le_one_iff_of_nonneg _ hC0).2 hC1

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma self_mul_le_one_of_nonneg_le_one {C : L K}
    (hC : IsSelfAdjoint C) (hC0 : 0 ≤ C) (hC1 : C ≤ (1 : L K)) :
    C * C ≤ (1 : L K) := by
  have hnorm : ‖C‖ ≤ 1 := norm_le_one_of_nonneg_le_one hC0 hC1
  simpa [hC.star_eq] using
    HansenPedersen.ConvexityCharacterization.mul_star_self_le_one_of_norm_le_one (K := K) hnorm

omit [Nontrivial (L K)] in
private lemma self_mul_lower_bound_of_pos_contraction {m : ℝ} {C : L K}
    (hC : IsSelfAdjoint C) (hm : 0 ≤ m)
    (hσC : spectrum ℝ C ⊆ Set.Icc m 1) :
    (m ^ 2 : ℝ) • (1 : L K) ≤ C * C := by
  have hsquare :
      cfcR (ℋ := K) (fun x : ℝ ↦ x * x) C = C * C := by
    calc
      cfcR (ℋ := K) (fun x : ℝ ↦ x * x) C
          = cfcR (ℋ := K) (fun x : ℝ ↦ x) C * cfcR (ℋ := K) (fun x : ℝ ↦ x) C := by
              dsimp [cfcR]
              rw [← cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) C
                continuousOn_id continuousOn_id]
      _ = C * C := by
            simp [cfcR, cfc_id' (R := ℝ) (a := C) (ha := hC)]
  have hle :
      algebraMap ℝ (L K) (m ^ 2) ≤ cfcR (ℋ := K) (fun x : ℝ ↦ x * x) C := by
    refine
      (algebraMap_le_cfc_iff (R := ℝ) (A := L K) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x * x) (r := m ^ 2) (a := C)
        (hf := continuousOn_id.mul continuousOn_id) (ha := hC)).2 ?_
    intro x hx
    have hxIcc := hσC hx
    nlinarith [hxIcc.1, hxIcc.2, hm]
  rw [hsquare] at hle
  simpa [Algebra.algebraMap_eq_smul_one] using hle

private lemma sqrtPos_mul_ratio_mul_sqrtPos_eq_cfcR {α : WithTop ℝ} {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay α))
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    sqrtPos A * cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A * sqrtPos A =
      cfcR (ℋ := K) f A := by
  have hratio := ratio_cfc_eq_invSqrtPos_mul_cfcR_mul_invSqrtPos
    (K := K) hf hσA
  calc
    sqrtPos A * cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A * sqrtPos A
        = sqrtPos A * (invSqrtPos A * cfcR (ℋ := K) f A * invSqrtPos A) * sqrtPos A := by
            rw [hratio]
    _ = (sqrtPos A * invSqrtPos A) * cfcR (ℋ := K) f A * (invSqrtPos A * sqrtPos A) := by
          simp [mul_assoc]
    _ = cfcR (ℋ := K) f A := by
          rw [sqrtPos_mul_invSqrtPos (K := K) hA hσA, invSqrtPos_mul_sqrtPos (K := K) hA hσA]
          simp

private lemma spectrum_subset_halfOpenRay_of_nonneg_le {α : WithTop ℝ} {M A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hM0 : 0 ≤ M)
    (hMA : M ≤ A) :
    spectrum ℝ M ⊆ halfOpenRay α := by
  have hA0 : 0 ≤ A := by
    exact HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA (by
      intro x hx
      exact (hσA hx).1)
  have hA_norm_mem : ‖A‖ ∈ spectrum ℝ A := CStarAlgebra.norm_mem_spectrum_of_nonneg hA0
  have hA_norm_lt : ((‖A‖ : ℝ) : WithTop ℝ) < α := (hσA hA_norm_mem).2
  have hMself : IsSelfAdjoint M := IsSelfAdjoint.of_nonneg hM0
  have hMβ : M ≤ (‖A‖ : ℝ) • (1 : L K) := by
    exact le_trans hMA (by
      simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self)
  intro x hx
  have hxIcc := HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := M) (α := 0) (β := ‖A‖) hMself
    (by simpa [Algebra.algebraMap_eq_smul_one] using hM0)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hMβ) hx
  exact ⟨hxIcc.1, lt_of_le_of_lt (by exact_mod_cast hxIcc.2) hA_norm_lt⟩

private theorem conditionV_implies_conditionII_posSpectrum_fixed
    {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hV : ConditionV.{u} α f)
    {A C : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α)
    (hC : IsSelfAdjoint C)
    {m : ℝ} (hm : 0 < m)
    (hCm : (m : ℝ) • (1 : L K) ≤ C)
    (hC1 : C ≤ (1 : L K)) :
    cfcR (ℋ := K) f (C * A * C) ≤ C * cfcR (ℋ := K) f A * C := by
  /- Step 1: Use g(t)=f(t)/t on the positive spectral range. -/
  let g : ℝ → ℝ := fun t ↦ f t / t
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_positiveOpenRay (K := K) hA hσA
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L K) (a := A) (ha := hA)).2
      (by
        intro x hx
        exact (hσA hx).1) with ⟨r, hr, hAr⟩
  have hσC : spectrum ℝ C ⊆ Set.Icc m 1 :=
    spectrum_subset_Icc_of_pos_contraction (K := K) hC hm.le hCm hC1
  have hC0 : 0 ≤ C := by
    exact HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hC (by
      intro x hx
      exact le_trans hm.le (hσC hx).1)
  have hCnorm : ‖C‖ ≤ 1 := norm_le_one_of_nonneg_le_one (K := K) hC0 hC1
  have hC2lo : (m ^ 2 : ℝ) • (1 : L K) ≤ C * C :=
    self_mul_lower_bound_of_pos_contraction (K := K) hC hm.le hσC
  have hC2hi : C * C ≤ (1 : L K) :=
    self_mul_le_one_of_nonneg_le_one (K := K) hC hC0 hC1
  /- Step 2: Factor A through sqrtPos so the B-products match the compression problem. -/
  let S : L K := sqrtPos A
  let B : L K := C * S
  have hS : IsSelfAdjoint S := by
    simpa [S] using sqrtPos_selfAdjoint (K := K) (A := A)
  have hSsq : S * S = A := by
    simpa [S] using sqrtPos_sq (K := K) hA hσA
  have hBstarB :
      star B * B = S * (C * C) * S := by
    dsimp [B]
    rw [show star (C * S) = S * C by simp [hC.star_eq, hS.star_eq]]
    simp [mul_assoc]
  have hBBstar : B * star B = C * A * C := by
    dsimp [B]
    calc
      (C * S) * star (C * S) = (C * S) * (S * C) := by
        simp [hC.star_eq, hS.star_eq]
      _ = C * (S * S) * C := by
        simp [mul_assoc]
      _ = C * A * C := by
        simp [hSsq]
  have hBstarB0 : 0 ≤ star B * B := by
    simp
  have hBBstar0 : 0 ≤ B * star B := by
    simpa [hBBstar, hC.star_eq] using star_left_conjugate_nonneg hA0 C
  have hBstarB_le_A : star B * B ≤ A := by
    rw [hBstarB]
    calc
      S * (C * C) * S ≤ S * (1 : L K) * S := by
        simpa [hS.star_eq, mul_assoc] using star_left_conjugate_le_conjugate hC2hi S
      _ = A := by simp [hSsq]
  /- Step 3: Keep both B-products in the positive interval for ratio CFC identities. -/
  have hBBstar_half : spectrum ℝ (B * star B) ⊆ halfOpenRay α := by
    simpa [hBBstar, hC.star_eq] using
      compressed_spectrum_subset_halfOpenRay (K := K) hA
        (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA) hCnorm
  have hBstarB_half : spectrum ℝ (star B * B) ⊆ halfOpenRay α :=
    spectrum_subset_halfOpenRay_of_nonneg_le (K := K) hA
      (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA) hBstarB0 hBstarB_le_A
  have hBstarB_self : IsSelfAdjoint (star B * B) := IsSelfAdjoint.of_nonneg hBstarB0
  have hBBstar_self : IsSelfAdjoint (B * star B) := IsSelfAdjoint.of_nonneg hBBstar0
  have hBstarB_lo :
      ((r * m ^ 2 : ℝ) • (1 : L K)) ≤ star B * B := by
    rw [hBstarB]
    calc
      (r * m ^ 2 : ℝ) • (1 : L K) = (m ^ 2 : ℝ) • ((r : ℝ) • (1 : L K)) := by
        simp [smul_smul, mul_comm]
      _ ≤ (m ^ 2 : ℝ) • A := by
        exact smul_le_smul_of_nonneg_left hAr (pow_nonneg hm.le 2)
      _ = S * ((m ^ 2 : ℝ) • (1 : L K)) * S := by
        simp [hSsq]
      _ ≤ S * (C * C) * S := by
        simpa [hS.star_eq, mul_assoc] using star_left_conjugate_le_conjugate hC2lo S
  have hBBstar_lo :
      ((r * m ^ 2 : ℝ) • (1 : L K)) ≤ B * star B := by
    rw [hBBstar]
    calc
      (r * m ^ 2 : ℝ) • (1 : L K) = (r : ℝ) • ((m ^ 2 : ℝ) • (1 : L K)) := by
        simp [smul_smul]
      _ ≤ (r : ℝ) • (C * C) := by
        exact smul_le_smul_of_nonneg_left hC2lo hr.le
      _ = C * ((r : ℝ) • (1 : L K)) * C := by
        simp
      _ ≤ C * A * C := by
        simpa [hC.star_eq, mul_assoc, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, mul_smul_comm]
          using star_left_conjugate_le_conjugate hAr C
  have hrm : 0 < r * m ^ 2 := by positivity
  have hσBstarB :
      spectrum ℝ (star B * B) ⊆ positiveOpenRay α :=
    spectrum_subset_positiveOpenRay_of_lower_bound
      (K := K) hBstarB_self hrm hBstarB_lo hBstarB_half
  have hσBBstar :
      spectrum ℝ (B * star B) ⊆ positiveOpenRay α :=
    spectrum_subset_positiveOpenRay_of_lower_bound
      (K := K) hBBstar_self hrm hBBstar_lo hBBstar_half
  /- Step 4: Apply monotonicity of the ratio to star B * B <= A before conjugating by B. -/
  have hmono :
      cfcR (ℋ := K) g (star B * B) ≤ cfcR (ℋ := K) g A := by
    exact hV (K := K) (A := star B * B) (B := A) hBstarB_self hA
      hσBstarB hσA hBstarB_le_A
  have hg_union :
      ContinuousOn g (spectrum ℝ (star B * B) ∪ spectrum ℝ (B * star B)) := by
    exact
      (continuousOn_ratio_of_positiveSpectrum
        (K := K) (hf := hf) (hσA := hσBstarB)).union_of_isClosed
        (continuousOn_ratio_of_positiveSpectrum
          (K := K) (hf := hf) (hσA := hσBBstar))
        (spectrum.isClosed (𝕜 := ℝ) (star B * B))
        (spectrum.isClosed (𝕜 := ℝ) (B * star B))
  have hinter :
      B * cfcR (ℋ := K) g (star B * B) =
        cfcR (ℋ := K) g (B * star B) * B :=
    intertwining_cfcR_of_union (K := K) (A := B) (g := g) hg_union
  have hconj :
      B * cfcR (ℋ := K) g (star B * B) * star B ≤
        B * cfcR (ℋ := K) g A * star B := by
    simpa [mul_assoc] using star_right_conjugate_le_conjugate hmono B
  /- Step 5: Convert the conjugated ratio inequality back to the f-CFC inequality. -/
  have hleft :
      B * cfcR (ℋ := K) g (star B * B) * star B =
        cfcR (ℋ := K) f (B * star B) := by
    calc
      B * cfcR (ℋ := K) g (star B * B) * star B
          = cfcR (ℋ := K) g (B * star B) * (B * star B) := by
              simpa [mul_assoc] using congrArg (fun T => T * star B) hinter
      _ = cfcR (ℋ := K) f (B * star B) := by
            exact ratio_cfcR_mul_self_eq_cfcR (K := K) hf hBBstar_self hσBBstar
  have hright :
      B * cfcR (ℋ := K) g A * star B = C * cfcR (ℋ := K) f A * C := by
    rw [show star B = S * C by
      dsimp [B]
      simp [hC.star_eq, hS.star_eq]]
    calc
      B * cfcR (ℋ := K) g A * (S * C)
          = C * (S * cfcR (ℋ := K) g A * S) * C := by
              dsimp [B]
              simp [mul_assoc]
      _ = C * cfcR (ℋ := K) f A * C := by
            rw [sqrtPos_mul_ratio_mul_sqrtPos_eq_cfcR (K := K) hf hA hσA]
  rw [hleft, hright, hBBstar] at hconj
  exact hconj

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma projection_nonneg {P : L K}
    (hP : IsSelfAdjoint P) (hPP : P * P = P) :
    (0 : L K) ≤ P := by
  simpa [hP.star_eq, hPP] using star_mul_self_nonneg P

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma projection_le_one {P : L K}
    (hP : IsSelfAdjoint P) (hPP : P * P = P) :
    P ≤ (1 : L K) := by
  have hdiff : (0 : L K) ≤ (1 : L K) - P := by
    simpa [sub_eq_add_neg, hP.star_eq, hPP, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
      using star_mul_self_nonneg ((1 : L K) - P)
  simpa [sub_eq_add_neg] using hdiff

private noncomputable def regularizedProjection (P : L K) (ε : ℝ) : L K :=
  ((1 + ε)⁻¹ : ℝ) • (P + ε • (1 : L K))

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma regularizedProjection_selfAdjoint {P : L K} {ε : ℝ}
    (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (regularizedProjection (K := K) P ε) := by
  dsimp [regularizedProjection]
  simpa [add_comm, add_left_comm, add_assoc] using
    (IsSelfAdjoint.all ((1 + ε)⁻¹)).smul
      (hP.add ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one _)))

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma regularizedProjection_lower {P : L K} {ε : ℝ}
    (hP : IsSelfAdjoint P) (hPP : P * P = P) (hε : 0 < ε) :
    ((ε / (1 + ε) : ℝ) • (1 : L K)) ≤ regularizedProjection (K := K) P ε := by
  have hP0 : (0 : L K) ≤ P := projection_nonneg (K := K) hP hPP
  have h0 :
      (ε : ℝ) • (1 : L K) ≤ P + ε • (1 : L K) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hP0 ((ε : ℝ) • (1 : L K))
  have hcoeff : 0 ≤ ((1 + ε)⁻¹ : ℝ) := by positivity
  calc
    ((ε / (1 + ε) : ℝ) • (1 : L K))
        = ((1 + ε)⁻¹ : ℝ) • ((ε : ℝ) • (1 : L K)) := by
            simp [div_eq_mul_inv, smul_smul, mul_comm]
    _ ≤ ((1 + ε)⁻¹ : ℝ) • (P + ε • (1 : L K)) := by
          exact smul_le_smul_of_nonneg_left h0 hcoeff
    _ = regularizedProjection (K := K) P ε := by
          simp [regularizedProjection]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma regularizedProjection_le_one {P : L K} {ε : ℝ}
    (hP : IsSelfAdjoint P) (hPP : P * P = P) (hε : 0 < ε) :
    regularizedProjection (K := K) P ε ≤ (1 : L K) := by
  have hP1 : P ≤ (1 : L K) := projection_le_one (K := K) hP hPP
  have h0 :
      P + ε • (1 : L K) ≤ (1 + ε : ℝ) • (1 : L K) := by
    calc
      P + ε • (1 : L K) ≤ ε • (1 : L K) + (1 : L K) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hP1 ((ε : ℝ) • (1 : L K))
      _ = (1 + ε : ℝ) • (1 : L K) := by
        simp [add_comm, add_smul]
  have hcoeff : 0 ≤ ((1 + ε)⁻¹ : ℝ) := by positivity
  calc
    regularizedProjection (K := K) P ε
        = ((1 + ε)⁻¹ : ℝ) • (P + ε • (1 : L K)) := by
            simp [regularizedProjection]
    _ ≤ ((1 + ε)⁻¹ : ℝ) • ((1 + ε : ℝ) • (1 : L K)) := by
          exact smul_le_smul_of_nonneg_left h0 hcoeff
    _ = (1 : L K) := by
          have hne : (1 + ε : ℝ) ≠ 0 := by linarith
          simp [smul_smul, hne]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma tendsto_regularizedProjection {P : L K} :
    Tendsto (fun ε : ℝ => regularizedProjection (K := K) P ε)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 P) := by
  have hcoeff_tendsto :
      Tendsto (fun ε : ℝ => ((1 + ε)⁻¹ : ℝ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun ε : ℝ => ((1 + ε)⁻¹ : ℝ)) 0 := by
      refine ContinuousAt.inv₀ ?_ ?_
      · exact (continuous_const.add continuous_id).continuousAt
      · norm_num
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hε_tendsto : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall_tendsto :
      Tendsto (fun ε : ℝ => ε * ((1 + ε)⁻¹ : ℝ))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) := by
    simpa using hε_tendsto.mul hcoeff_tendsto
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          ((1 + ε)⁻¹ : ℝ) • P + (ε * ((1 + ε)⁻¹ : ℝ)) • (1 : L K))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 ((1 : ℝ) • P + (0 : ℝ) • (1 : L K))) := by
    exact (hcoeff_tendsto.smul_const P).add (hsmall_tendsto.smul_const (1 : L K))
  simpa [regularizedProjection, div_eq_mul_inv, smul_add, smul_smul, mul_assoc,
    mul_left_comm, mul_comm]
    using hsum

private noncomputable def regularizationPoint (α : WithTop ℝ) : ℝ :=
  if htop : α = ⊤ then 1 else α.untop htop / 2

private lemma regularizationPoint_pos {α : WithTop ℝ}
    (hα : (0 : WithTop ℝ) < α) :
    0 < regularizationPoint α := by
  by_cases htop : α = ⊤
  · simp [regularizationPoint, htop]
  · have hα' : 0 < α.untop htop := by
      have : (0 : WithTop ℝ) < ((α.untop htop : ℝ) : WithTop ℝ) := by
        simpa [WithTop.coe_untop, htop] using hα
      simpa using this
    have hhalf : 0 < α.untop htop / 2 := by linarith
    simpa [regularizationPoint, htop] using hhalf

private lemma regularizationPoint_lt {α : WithTop ℝ}
    (hα : (0 : WithTop ℝ) < α) :
    ((regularizationPoint α : ℝ) : WithTop ℝ) < α := by
  by_cases htop : α = ⊤
  · simp [regularizationPoint, htop]
  · have hα' : 0 < α.untop htop := by
      have : (0 : WithTop ℝ) < ((α.untop htop : ℝ) : WithTop ℝ) := by
        simpa [WithTop.coe_untop, htop] using hα
      simpa using this
    have hhalf : α.untop htop / 2 < α.untop htop := by linarith
    simpa [regularizationPoint, htop, WithTop.coe_untop] using hhalf

omit [Nontrivial (L K)] in
private lemma spectrum_regularizationPoint_subset_halfOpenRay {α : WithTop ℝ}
    (hα : (0 : WithTop ℝ) < α) :
    spectrum ℝ ((regularizationPoint α : ℝ) • (1 : L K)) ⊆ halfOpenRay α := by
  intro x hx
  have hx' :
      x = regularizationPoint α := by
    have hxsingleton :
        x ∈ ({regularizationPoint α} : Set ℝ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (CFC.spectrum_algebraMap_subset (R := ℝ) (A := L K) (regularizationPoint α) hx)
    simpa using hxsingleton
  subst x
  exact ⟨(regularizationPoint_pos hα).le, regularizationPoint_lt hα⟩

private theorem conditionV_implies_conditionIV_posSpectrum_fixed
    {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hV : ConditionV.{u} α f)
    {A P : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α)
    (hP : IsSelfAdjoint P)
    (hPP : P * P = P) :
    cfcR (ℋ := K) f (P * A * P) ≤ P * cfcR (ℋ := K) f A * P := by
  /- Step 1: Regularize the projection into strictly positive contractions approaching P. -/
  let Cε : ℝ → L K := fun ε => regularizedProjection (K := K) P ε
  let T : ℝ → L K := fun ε => Cε ε * A * Cε ε
  let R : ℝ → L K := fun ε => Cε ε * cfcR (ℋ := K) f A * Cε ε
  /- Step 2: Choose a compact spectral window for the limiting compression and CFC continuity. -/
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_positiveOpenRay (K := K) hA hσA
  have hP0 : (0 : L K) ≤ P := projection_nonneg (K := K) hP hPP
  have hP1 : P ≤ (1 : L K) := projection_le_one (K := K) hP hPP
  have hPnorm : ‖P‖ ≤ 1 := norm_le_one_of_nonneg_le_one (K := K) hP0 hP1
  have hA_norm_mem : ‖A‖ ∈ spectrum ℝ A :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg hA0
  have hA_norm_lt : ((‖A‖ : ℝ) : WithTop ℝ) < α := by
    exact
      (spectrum_subset_halfOpenRay_of_positiveOpenRay
        (A := A) hσA hA_norm_mem).2
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) ‖A‖) := by
    refine hf.mono ?_
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt (by exact_mod_cast hx.2) hA_norm_lt⟩
  have hPAPself : IsSelfAdjoint (P * A * P) := by
    simpa [hP.star_eq, mul_assoc] using
      IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg hA0 P)
  have hσPAP_Icc : spectrum ℝ (P * A * P) ⊆ Set.Icc (0 : ℝ) ‖A‖ := by
    simpa [hP.star_eq] using
      compressed_spectrum_subset_Icc_zero_norm (K := K) hA hA0 hPnorm
  /- Step 3: Pass the regularized contractions through multiplication to get the operator limits. -/
  have hCε_tendsto : Tendsto Cε (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 P) :=
    tendsto_regularizedProjection (K := K)
  have hT_tendsto : Tendsto T (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (P * A * P)) := by
    dsimp [T]
    simpa [Cε, mul_assoc] using (hCε_tendsto.mul_const A).mul hCε_tendsto
  have hR_tendsto :
      Tendsto R (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (P * cfcR (ℋ := K) f A * P)) := by
    dsimp [R]
    simpa [Cε, mul_assoc] using
      ((hCε_tendsto.mul_const (cfcR (ℋ := K) f A)).mul hCε_tendsto)
  /- Step 4: Use CFC continuity on the compact window to identify the limit of the left side. -/
  have hL :
      Tendsto (fun ε : ℝ => cfcR (ℋ := K) f (T ε))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f (P * A * P))) := by
    simpa [cfcR, T] using
      Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f)
        hT_tendsto
        (by
          refine Filter.mem_of_superset self_mem_nhdsWithin ?_
          intro ε hε
          have hCεself : IsSelfAdjoint (Cε ε) :=
            regularizedProjection_selfAdjoint (K := K) (P := P) hP
          have hCεlo :
              ((ε / (1 + ε) : ℝ) • (1 : L K)) ≤ Cε ε :=
            regularizedProjection_lower (K := K) (P := P) hP hPP hε
          have hCε0 : (0 : L K) ≤ Cε ε := by
            have hεpos : 0 < ε := hε
            have hden : 0 < 1 + ε := by linarith
            have hscalar_nonneg : 0 ≤ ε / (1 + ε) := by
              exact div_nonneg hεpos.le hden.le
            have hnonneg :
                (0 : L K) ≤ ((ε / (1 + ε) : ℝ) • (1 : L K)) := by
              simpa [Algebra.algebraMap_eq_smul_one] using
                smul_nonneg hscalar_nonneg
                  (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
            exact le_trans hnonneg hCεlo
          have hCε1 : Cε ε ≤ (1 : L K) :=
            regularizedProjection_le_one (K := K) (P := P) hP hPP hε
          have hCεnorm : ‖Cε ε‖ ≤ 1 :=
            norm_le_one_of_nonneg_le_one (K := K) hCε0 hCε1
          simpa [T, Cε, hCεself.star_eq] using
            compressed_spectrum_subset_Icc_zero_norm (K := K) hA hA0 hCεnorm)
        (by
          refine Filter.mem_of_superset self_mem_nhdsWithin ?_
          intro ε hε
          have hCεlo :
              ((ε / (1 + ε) : ℝ) • (1 : L K)) ≤ Cε ε :=
            regularizedProjection_lower (K := K) (P := P) hP hPP hε
          have hCε0 : (0 : L K) ≤ Cε ε := by
            have hεpos : 0 < ε := hε
            have hden : 0 < 1 + ε := by linarith
            have hscalar_nonneg : 0 ≤ ε / (1 + ε) := by
              exact div_nonneg hεpos.le hden.le
            have hnonneg :
                (0 : L K) ≤ ((ε / (1 + ε) : ℝ) • (1 : L K)) := by
              simpa [Algebra.algebraMap_eq_smul_one] using
                smul_nonneg hscalar_nonneg
                  (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
            exact le_trans hnonneg hCεlo
          have hCεself : IsSelfAdjoint (Cε ε) :=
            regularizedProjection_selfAdjoint (K := K) (P := P) hP
          simpa [T, Cε, hCεself.star_eq, mul_assoc] using
            IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg hA0 (Cε ε)))
        hσPAP_Icc hPAPself hfIcc
  /- Step 5: Apply the strict contraction theorem and close by order convergence. -/
  have hEventually :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        cfcR (ℋ := K) f (T ε) ≤ R ε := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro ε hε
    have hCεself : IsSelfAdjoint (Cε ε) :=
      regularizedProjection_selfAdjoint (K := K) (P := P) hP
    have hCεlo :
        ((ε / (1 + ε) : ℝ) • (1 : L K)) ≤ Cε ε :=
      regularizedProjection_lower (K := K) (P := P) hP hPP hε
    have hCε1 : Cε ε ≤ (1 : L K) :=
      regularizedProjection_le_one (K := K) (P := P) hP hPP hε
    have hεratio : 0 < ε / (1 + ε) := by
      have hεpos : 0 < ε := hε
      have hden : 0 < 1 + ε := by linarith
      exact div_pos hεpos hden
    simpa [T, R, Cε] using
      conditionV_implies_conditionII_posSpectrum_fixed (K := K) hf hV
        (A := A) (C := Cε ε) hA hσA hCεself hεratio hCεlo hCε1
  exact le_of_tendsto_of_tendsto hL hR_tendsto hEventually

/-- Condition V, monotonicity of `t ↦ f t / t` on positive spectra, implies
the projection compression inequality.  The proof regularizes a projection to
strictly positive contractions and passes the strict-spectrum inequality to the
limit.
Source: Hiai--Yanagi, Theorem 5.1.7. -/
theorem conditionV_implies_conditionIV {α : WithTop ℝ} {f : ℝ → ℝ}
    (hα : (0 : WithTop ℝ) < α)
    (hf : ContinuousOn f (halfOpenRay α))
    (hV : ConditionV.{u} α f) :
    ConditionIV.{u} α f := by
  intro K _ _ _ _ _ A P hA hP hPP hσA
  /- Step 1: Push A into the positive-spectrum regime by mixing it with an interior scalar point. -/
  let c : ℝ := regularizationPoint α
  let B : L K := c • (1 : L K)
  let Aε : ℝ → L K := fun ε ↦ (1 - ε) • A + ε • B
  have hc_pos : 0 < c := regularizationPoint_pos hα
  have hc_lt : ((c : ℝ) : WithTop ℝ) < α := regularizationPoint_lt hα
  have hσB : spectrum ℝ B ⊆ halfOpenRay α := by
    simpa [B] using spectrum_regularizationPoint_subset_halfOpenRay (K := K) hα
  have hA0 : 0 ≤ A :=
    HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA <| by
      intro x hx
      exact (hσA hx).1
  have hBself : IsSelfAdjoint B := by
    dsimp [B]
    simpa using (IsSelfAdjoint.all c).smul (IsSelfAdjoint.one _)
  have hA_norm_mem : ‖A‖ ∈ spectrum ℝ A :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg hA0
  have hA_norm_lt : ((‖A‖ : ℝ) : WithTop ℝ) < α := (hσA hA_norm_mem).2
  let β : ℝ := max ‖A‖ c
  have hβ_lt : ((β : ℝ) : WithTop ℝ) < α := by
    dsimp [β]
    exact max_lt_iff.mpr ⟨hA_norm_lt, hc_lt⟩
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) β) := by
    refine hf.mono ?_
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt (by exact_mod_cast hx.2) hβ_lt⟩
  /- Step 2: Put A, the perturbations, and their P-compressions in one compact spectral window. -/
  have hP0 : (0 : L K) ≤ P := projection_nonneg (K := K) hP hPP
  have hP1 : P ≤ (1 : L K) := projection_le_one (K := K) hP hPP
  have hPAPself : IsSelfAdjoint (P * A * P) := by
    simpa [hP.star_eq, mul_assoc] using
      IsSelfAdjoint.of_nonneg (star_left_conjugate_nonneg hA0 P)
  have hAβ : A ≤ (β : ℝ) • (1 : L K) := by
    calc
      A ≤ (‖A‖ : ℝ) • (1 : L K) := by
        simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
      _ ≤ (β : ℝ) • (1 : L K) := by
        exact smul_le_smul_of_nonneg_right (le_max_left ‖A‖ c) zero_le_one
  have hσA_Icc : spectrum ℝ A ⊆ Set.Icc (0 : ℝ) β := by
    exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
      (K := K) (T := A) (α := 0) (β := β) hA
      (by simpa [Algebra.algebraMap_eq_smul_one] using hA0)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hAβ)
  have hsmall :
      Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  have hAεself : ∀ ε : ℝ, IsSelfAdjoint (Aε ε) := by
    intro ε
    dsimp [Aε, B]
    exact ((IsSelfAdjoint.all (1 - ε)).smul hA).add ((IsSelfAdjoint.all ε).smul hBself)
  have hAε_half :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → spectrum ℝ (Aε ε) ⊆ halfOpenRay α := by
    intro ε hεpos hεlt1
    simpa [Aε] using
      HansenPedersen.ConvexityCharacterization.convex_combination_spectrum_subset_halfOpenRay
        (K := K) hα hA hBself hεpos.le hεlt1.le hσA hσB
  have hAεlo :
      ∀ {ε : ℝ}, ε < 1 → ((ε * c : ℝ) • (1 : L K)) ≤ Aε ε := by
    intro ε hεlt1
    have hfirst_nonneg : (0 : L K) ≤ (1 - ε) • A := by
      exact smul_nonneg (sub_nonneg.mpr hεlt1.le) hA0
    calc
      ((ε * c : ℝ) • (1 : L K)) = ε • B := by
        simp [B, smul_smul]
      _ ≤ (1 - ε) • A + ε • B := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfirst_nonneg (ε • B)
      _ = Aε ε := by
        simp [Aε, B]
  have hAεβ :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → Aε ε ≤ (β : ℝ) • (1 : L K) := by
    intro ε hεpos hεlt1
    have hBβ : B ≤ (β : ℝ) • (1 : L K) := by
      dsimp [B, β]
      exact smul_le_smul_of_nonneg_right (le_max_right ‖A‖ c) zero_le_one
    calc
      Aε ε = (1 - ε) • A + ε • B := by rfl
      _ ≤ (1 - ε) • ((β : ℝ) • (1 : L K)) + ε • ((β : ℝ) • (1 : L K)) := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left hAβ (sub_nonneg.mpr hεlt1.le))
          (smul_le_smul_of_nonneg_left hBβ hεpos.le)
      _ = (β : ℝ) • (1 : L K) := by
        rw [← add_smul]
        have hsum : (1 - ε) + ε = 1 := by ring
        simp [hsum]
  have hAε_Icc :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → spectrum ℝ (Aε ε) ⊆ Set.Icc (0 : ℝ) β := by
    intro ε hεpos hεlt1
    exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
      (K := K) (T := Aε ε) (α := 0) (β := β) (hAεself ε)
      (by
        have hεc_pos : 0 < ε * c := by positivity
        have hnonneg : (0 : L K) ≤ ((ε * c : ℝ) • (1 : L K)) := by
          simpa [Algebra.algebraMap_eq_smul_one] using
            smul_nonneg hεc_pos.le (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
        have hAε0 : (0 : L K) ≤ Aε ε := le_trans hnonneg (hAεlo hεlt1)
        simpa [Algebra.algebraMap_eq_smul_one] using hAε0)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hAεβ hεpos hεlt1)
  have hPAεP0 :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → (0 : L K) ≤ P * Aε ε * P := by
    intro ε hεpos hεlt1
    have hεc_pos : 0 < ε * c := by positivity
    have hnonneg : (0 : L K) ≤ ((ε * c : ℝ) • (1 : L K)) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        smul_nonneg hεc_pos.le (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
    have hAε0 : (0 : L K) ≤ Aε ε := le_trans hnonneg (hAεlo hεlt1)
    simpa [hP.star_eq] using star_left_conjugate_nonneg hAε0 P
  have hPAεPself :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → IsSelfAdjoint (P * Aε ε * P) := by
    intro ε hεpos hεlt1
    simpa [hP.star_eq, mul_assoc] using IsSelfAdjoint.of_nonneg (hPAεP0 hεpos hεlt1)
  have hPAεPβ :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 → P * Aε ε * P ≤ (β : ℝ) • (1 : L K) := by
    intro ε hεpos hεlt1
    calc
      P * Aε ε * P ≤ P * ((β : ℝ) • (1 : L K)) * P := by
        simpa [hP.star_eq, mul_assoc] using
          star_left_conjugate_le_conjugate (hAεβ hεpos hεlt1) P
      _ = (β : ℝ) • P := by
        simp [hPP]
      _ ≤ (β : ℝ) • (1 : L K) := by
        exact smul_le_smul_of_nonneg_left hP1 (le_trans (norm_nonneg _) (le_max_left ‖A‖ c))
  have hPAεP_Icc :
      ∀ {ε : ℝ}, 0 < ε → ε < 1 →
        spectrum ℝ (P * Aε ε * P) ⊆ Set.Icc (0 : ℝ) β := by
    intro ε hεpos hεlt1
    exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
      (K := K) (T := P * Aε ε * P) (α := 0) (β := β) (hPAεPself hεpos hεlt1)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hPAεP0 hεpos hεlt1)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hPAεPβ hεpos hεlt1)
  /- Step 3: Show the perturbed operators and their P-compressions converge to the original ones. -/
  have hAε_tendsto : Tendsto Aε (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 A) := by
    have hε_tendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1m_tendsto : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hε_tendsto
    simpa [Aε, B, c, smul_add, add_comm, add_left_comm, add_assoc] using
      (h1m_tendsto.smul_const A).add (hε_tendsto.smul_const B)
  have hPAεP_tendsto :
      Tendsto (fun ε : ℝ ↦ P * Aε ε * P) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (P * A * P)) := by
    simpa [Aε, mul_assoc] using ((tendsto_const_nhds.mul hAε_tendsto).mul tendsto_const_nhds)
  have hσPAP_Icc : spectrum ℝ (P * A * P) ⊆ Set.Icc (0 : ℝ) β := by
    have hPAP0 : (0 : L K) ≤ P * A * P := by
      simpa [hP.star_eq] using star_left_conjugate_nonneg hA0 P
    have hAβ : A ≤ (β : ℝ) • (1 : L K) := by
      calc
        A ≤ (‖A‖ : ℝ) • (1 : L K) := by
          simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
        _ ≤ (β : ℝ) • (1 : L K) := by
          exact smul_le_smul_of_nonneg_right (le_max_left ‖A‖ c) zero_le_one
    have hPAPβ : P * A * P ≤ (β : ℝ) • (1 : L K) := by
      calc
        P * A * P ≤ P * ((β : ℝ) • (1 : L K)) * P := by
          simpa [hP.star_eq, mul_assoc] using star_left_conjugate_le_conjugate hAβ P
        _ = (β : ℝ) • P := by
          simp [hPP]
        _ ≤ (β : ℝ) • (1 : L K) := by
          exact smul_le_smul_of_nonneg_left hP1 (le_trans (norm_nonneg _) (le_max_left ‖A‖ c))
    exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
      (K := K) (T := P * A * P) (α := 0) (β := β) hPAPself
      (by simpa [Algebra.algebraMap_eq_smul_one] using hPAP0)
      (by simpa [Algebra.algebraMap_eq_smul_one] using hPAPβ)
  /- Step 4: Convert those operator limits into CFC limits using the compact spectral window. -/
  have hcfAε_tendsto :
      Tendsto (fun ε : ℝ ↦ cfcR (ℋ := K) f (Aε ε))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f A)) := by
    simpa [cfcR, Aε] using
      Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f)
        hAε_tendsto
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          exact hAε_Icc hεpos hεlt1)
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          exact hAεself ε)
        hσA_Icc hA hfIcc
  have hR_tendsto :
      Tendsto (fun ε : ℝ ↦ P * cfcR (ℋ := K) f (Aε ε) * P)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (P * cfcR (ℋ := K) f A * P)) := by
    simpa [mul_assoc] using ((tendsto_const_nhds.mul hcfAε_tendsto).mul tendsto_const_nhds)
  have hL_tendsto :
      Tendsto (fun ε : ℝ ↦ cfcR (ℋ := K) f (P * Aε ε * P))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f (P * A * P))) := by
    simpa [cfcR, mul_assoc] using
      Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f)
        hPAεP_tendsto
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          exact hPAεP_Icc hεpos hεlt1)
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          exact hPAεPself hεpos hεlt1)
        hσPAP_Icc hPAPself hfIcc
  /- Step 5: Apply the positive-spectrum projection inequality and take the limit. -/
  have hEventually :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        cfcR (ℋ := K) f (P * Aε ε * P) ≤ P * cfcR (ℋ := K) f (Aε ε) * P := by
    refine Filter.mem_of_superset hsmall ?_
    intro ε hε
    rcases hε with ⟨hεpos, hεlt1⟩
    have hAεself' : IsSelfAdjoint (Aε ε) := hAεself ε
    have hεc_pos : 0 < ε * c := mul_pos hεpos hc_pos
    have hAε_pos : spectrum ℝ (Aε ε) ⊆ positiveOpenRay α :=
      spectrum_subset_positiveOpenRay_of_lower_bound
        (K := K) hAεself' hεc_pos (hAεlo hεlt1) (hAε_half hεpos hεlt1)
    simpa [Aε, mul_assoc] using
      conditionV_implies_conditionIV_posSpectrum_fixed (K := K) hf hV
        (A := Aε ε) (P := P) hAεself' hAε_pos hP hPP
  exact le_of_tendsto_of_tendsto hL_tendsto hR_tendsto hEventually

end RatioMonotoneToProjection

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
