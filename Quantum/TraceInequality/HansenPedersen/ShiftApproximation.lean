/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Shift approximation for the continuous functional calculus

This file collects the shift-approximation machinery used to transport
operator convexity, concavity, and monotonicity statements between the open
half-line `(0,∞)` and the closed half-line `[0,∞)`.  The mechanism combines
two ingredients:

1. the *shift* `A ↦ A + ε • 1` on operators, matched on the CFC side by the
   function shift `f ↦ f (· + ε)` (`cfc_shift_eq_Ici`), which moves a spectrum
   contained in `[0,∞)` into `(0,∞)`; and
2. the *CFC limit transfer principle* (`cfc_add_const_tendsto_Ioi`,
   `shifted_cfc_tendsto_Ioi`, and the `*_of_tendsto_Ioi` lemmas), which passes
   operator convexity / monotonicity / concavity from the shifted
   approximants back to the limit function as `ε → 0⁺`.

This is a mechanism file: it corresponds to no single statement in the book
and carries no `Source:` anchors.  Its lemmas are the shared infrastructure
behind the Hiai--Yanagi Lemma 5.1.10 book route and Corollary 5.1.11 in
`LaterConsequences.lean`, and behind the quasi-entropy condition conversions in
`HansenPedersen/QuasiEntropyDataProcessing/Conditions.lean`.

## Main results

* `cfc_shift_eq_Ici`: shift compatibility
  `cfcR (f (· + ε)) A = cfcR f (A + ε • 1)` for spectra in `[0,∞)`.
* `shifted_cfc_tendsto_Ioi`: convergence `cfcR (f (· + p)) A → cfcR f A` as
  `p → 0⁺` for spectra in `(0,∞)`.
* `operatorConvexOn_of_tendsto_Ioi`, `operatorMonotoneOn_of_tendsto_Ioi`,
  `operatorConcaveOn_of_tendsto_Ioi`: operator convexity / monotonicity /
  concavity on `(0,∞)` pass to CFC limits.
* `allHOperatorMonotone_shift_Ici`, `allHOperatorConcave_shift_Ici`:
  transport of the all-Hilbert-space predicates from `(0,∞)` to the shifted
  function on `[0,∞)`.
* `spectrum_convexCombo_Ioi`, `spectrum_add_pos_scalar_subset_Ioi`,
  `spectrum_cfc_subset_Ioi_of_continuous_pos`: positivity of spectra along
  the constructions above.
-/

namespace HansenPedersen

universe u

open CFC
open scoped Topology

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section ShiftApproximation

omit [Nontrivial (L ℋ)] in
/-- A self-adjoint operator with spectrum in `(0,∞)` is strictly positive. -/
lemma isStrictlyPositive_of_isSelfAdjoint_of_spectrum_subset_Ioi {A : L ℋ}
    (hA : IsSelfAdjoint A)
    (hAs : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    IsStrictlyPositive A := by
  rw [CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos]
  refine ⟨hA, ?_⟩
  intro x hx
  simpa [Set.mem_Ioi] using hAs hx

omit [Nontrivial (L ℋ)] in
/-- For spectrum in `(0,∞)`, `cfcR (·⁻¹) A = Ring.inverse A`. -/
lemma cfcR_inv_eq_inverse {A : L ℋ} (hA : IsSelfAdjoint A)
    (hAs : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (ℋ := ℋ) (fun x : ℝ ↦ x⁻¹) A = Ring.inverse A := by
  dsimp [cfcR]
  simpa [cfc_id' (R := ℝ) (a := A) (ha := hA)] using
    (cfc_inv (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
      (a := A) (fun x hx ↦ ne_of_gt (by simpa [Set.mem_Ioi] using hAs hx)) (ha := hA))

/-- A convex combination `(1 - t) • A + t • B` of self-adjoint operators with
spectra in `(0,∞)` again has spectrum in `(0,∞)`. -/
lemma spectrum_convexCombo_Ioi {A B : L ℋ} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      exact add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add
          (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

/-- Operator convexity on `(0,∞)` passes to CFC limits: if
`cfcR (F p) A → cfcR f A` as `p → 0⁺` for every self-adjoint `A` with spectrum
in `(0,∞)`, and `F p` is eventually operator convex, then `f` is operator
convex. -/
lemma operatorConvexOn_of_tendsto_Ioi
    {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hlim :
      ∀ {A : L ℋ}, IsSelfAdjoint A →
        spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
        Filter.Tendsto (fun p : ℝ => cfcR (ℋ := ℋ) (F p) A)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds (cfcR (ℋ := ℋ) f A)))
    (hconv :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (F p)) :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B t hA hB ht0 ht1 As Bs
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have Cs : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using spectrum_convexCombo_Ioi (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  have hEventually :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := ℋ) (F p) C ≤
          (1 - t) • cfcR (ℋ := ℋ) (F p) A + t • cfcR (ℋ := ℋ) (F p) B := by
    filter_upwards [hconv] with p hp
    simpa [C] using hp hA hB ht0 ht1 As Bs
  have hL :
      Filter.Tendsto (fun p : ℝ => cfcR (ℋ := ℋ) (F p) C)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := ℋ) f C)) :=
    hlim hC Cs
  have hA' :
      Filter.Tendsto (fun p : ℝ => cfcR (ℋ := ℋ) (F p) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := ℋ) f A)) :=
    hlim hA As
  have hB' :
      Filter.Tendsto (fun p : ℝ => cfcR (ℋ := ℋ) (F p) B)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := ℋ) f B)) :=
    hlim hB Bs
  have hR :
      Filter.Tendsto
        (fun p : ℝ =>
          (1 - t) • cfcR (ℋ := ℋ) (F p) A + t • cfcR (ℋ := ℋ) (F p) B)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds ((1 - t) • cfcR (ℋ := ℋ) f A + t • cfcR (ℋ := ℋ) f B)) := by
    exact (tendsto_const_nhds.smul hA').add (tendsto_const_nhds.smul hB')
  simpa [C] using le_of_tendsto_of_tendsto hL hR hEventually

/-- If `f` is continuous on `(0,∞)`, the shift `t ↦ f (t + ε)` (`ε > 0`) is
continuous on `[0,∞)`. -/
lemma continuousOn_shift_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ ↦ f (t + ε)) (halfOpenRay ⊤) := by
  refine hf.comp (continuousOn_id.add continuousOn_const) ?_
  intro x hx
  simpa [halfOpenRay_top, Set.mem_Ioi] using add_pos_of_nonneg_of_pos hx.1 hε

section FixedK

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

/-- Adding `ε • 1` (`ε > 0`) to a self-adjoint operator with spectrum in
`[0,∞)` yields spectrum in `(0,∞)`. -/
lemma spectrum_add_pos_scalar_subset_Ioi {A : L K} (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ halfOpenRay ⊤) {ε : ℝ} (hε : 0 < ε) :
    spectrum ℝ (A + (ε : ℝ) • (1 : L K)) ⊆ Set.Ioi (0 : ℝ) := by
  have hA0 : 0 ≤ A := by
    exact nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici (ℋ := K) hA (by
      simpa [halfOpenRay_top] using hσA)
  have hAε : IsSelfAdjoint (A + (ε : ℝ) • (1 : L K)) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hA.add
      (IsSelfAdjoint.algebraMap (A := L K) (r := ε) (hr := IsSelfAdjoint.all ε))
  have hlow : (ε : ℂ) • (1 : L K) ≤ A + (ε : ℝ) • (1 : L K) := by
    have htmp : (ε : ℝ) • (1 : L K) ≤ (ε : ℝ) • (1 : L K) + A := by
      exact le_add_of_nonneg_right hA0
    simpa [Algebra.algebraMap_eq_smul_one, add_comm, add_left_comm, add_assoc] using htmp
  exact (CFC.exists_pos_algebraMap_le_iff (A := L K) (a := A + (ε : ℝ) • (1 : L K))
      (ha := hAε)).1 ⟨ε, hε, hlow⟩

omit [Nontrivial (L K)] in
/-- Shift compatibility of the CFC: `cfcR (f (· + ε)) A = cfcR f (A + ε • 1)`
for spectrum in `[0,∞)`. -/
lemma cfc_shift_eq_Ici {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ halfOpenRay ⊤)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    cfcR (ℋ := K) (fun x : ℝ ↦ f (x + ε)) A =
      cfcR (ℋ := K) f (A + (ε : ℝ) • (1 : L K)) := by
  have hcont_shift : ContinuousOn (fun x : ℝ ↦ x + ε) (spectrum ℝ A) :=
    continuousOn_id.add continuousOn_const
  have himage_Ioi :
      ((fun x : ℝ ↦ x + ε) '' spectrum ℝ A) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [halfOpenRay_top, Set.mem_Ici] using hσA hy
    simpa [Set.mem_Ioi] using add_pos_of_nonneg_of_pos hy0 hε
  have hcont_f :
      ContinuousOn f ((fun x : ℝ ↦ x + ε) '' spectrum ℝ A) := by
    intro x hx
    exact (hf x (himage_Ioi hx)).mono (by
      intro y hy
      exact himage_Ioi hy)
  have hadd :
      cfcR (ℋ := K) (fun x : ℝ ↦ x + ε) A = A + (ε : ℝ) • (1 : L K) := by
    have hfun : (fun x : ℝ ↦ x + ε) = fun x : ℝ ↦ ε + x := by
      funext x
      ring
    have hadd' :
        cfcR (ℋ := K) (fun x : ℝ ↦ ε + x) A = (ε : ℝ) • (1 : L K) + A := by
      simpa [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA), Algebra.algebraMap_eq_smul_one,
        add_comm, add_left_comm, add_assoc] using
        (cfc_add_const (R := ℝ) (A := L K) (p := IsSelfAdjoint)
          (r := ε) (f := fun x : ℝ ↦ x) (a := A)
          (hf := continuousOn_id) (ha := hA))
    rw [hfun, hadd']
    simp [add_comm]
  calc
    cfcR (ℋ := K) (fun x : ℝ ↦ f (x + ε)) A
        = cfcR (ℋ := K) f (cfcR (ℋ := K) (fun x : ℝ ↦ x + ε) A) := by
            simpa [cfcR] using
              (cfc_comp' (R := ℝ) (A := L K) (p := IsSelfAdjoint)
                (g := f) (f := fun x : ℝ ↦ x + ε) (a := A)
                (hg := hcont_f) (hf := hcont_shift) (ha := hA))
    _ = cfcR (ℋ := K) f (A + (ε : ℝ) • (1 : L K)) := by rw [hadd]

/-- A uniform spectral window for the regularization path `A + p • 1`, `0 ≤ p ≤ 1`. -/
private lemma spectrum_add_smul_one_subset_Icc {A : L K} (hA : IsSelfAdjoint A) {α : ℝ}
    (hαA : algebraMap ℝ (L K) α ≤ A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    spectrum ℝ (A + (p : ℝ) • (1 : L K)) ⊆ Set.Icc α (‖A‖ + 1) := by
  have hAp_sa : IsSelfAdjoint (A + (p : ℝ) • (1 : L K)) := by
    have hscalar : IsSelfAdjoint ((p : ℝ) • (1 : L K)) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (IsSelfAdjoint.algebraMap (A := L K) (r := p) (hr := IsSelfAdjoint.all p))
    exact hA.add hscalar
  have hlow : (α : ℂ) • (1 : L K) ≤ A + (p : ℝ) • (1 : L K) := by
    have hp_nonneg : (0 : L K) ≤ (p : ℝ) • (1 : L K) := by
      exact smul_nonneg hp0 (zero_le_one : (0 : L K) ≤ (1 : L K))
    simpa using le_add_of_nonneg_right hp_nonneg |> fun h => le_trans hαA h
  have hupp : A + (p : ℝ) • (1 : L K) ≤ ((‖A‖ + 1 : ℝ) : ℂ) • (1 : L K) := by
    have hpupper : (p : ℝ) • (1 : L K) ≤ (1 : ℝ) • (1 : L K) := by
      exact smul_le_smul_of_nonneg_right hp1
        (zero_le_one : (0 : L K) ≤ (1 : L K))
    calc
      A + (p : ℝ) • (1 : L K) ≤ (‖A‖ : ℝ) • (1 : L K) + (1 : ℝ) • (1 : L K) := by
            have hAupper' : A ≤ (‖A‖ : ℝ) • (1 : L K) := by
              simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
            exact add_le_add hAupper' hpupper
      _ = (‖A‖ + 1 : ℝ) • (1 : L K) := by simp [add_smul]
  exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) hAp_sa hlow hupp

/-- Continuity of the CFC along the regularization path:
`cfcR f (A + p • 1) → cfcR f A` as `p → 0⁺`. -/
lemma cfc_add_const_tendsto_Ioi {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto
      (fun p : ℝ ↦ cfcR (ℋ := K) f (A + (p : ℝ) • (1 : L K)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (cfcR (ℋ := K) f A)) := by
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L K) (a := A) (ha := hA)).2
      (by intro x hx; exact hσA hx) with ⟨α, hαpos, hαA⟩
  let Ap : ℝ → L K := fun p => A + (p : ℝ) • (1 : L K)
  have hσA_Icc : spectrum ℝ A ⊆ Set.Icc α (‖A‖ + 1) := by
    simpa using spectrum_add_smul_one_subset_Icc (K := K) hA hαA le_rfl zero_le_one
  have hsmall :
      Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  have hAp_tendsto : Filter.Tendsto Ap (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds A) := by
    have hptendsto :
        Filter.Tendsto (fun p : ℝ => p) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds 0) :=
      nhdsWithin_le_nhds
    simpa [Ap] using tendsto_const_nhds.add (hptendsto.smul_const (1 : L K))
  simpa [Ap, cfcR] using
    Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f) hAp_tendsto
      (by
        refine Filter.mem_of_superset hsmall ?_
        intro p hp
        exact spectrum_add_smul_one_subset_Icc (K := K) hA hαA hp.1.le hp.2.le)
      (by
        filter_upwards [self_mem_nhdsWithin] with p hp
        have hscalar : IsSelfAdjoint ((p : ℝ) • (1 : L K)) := by
          simpa [Algebra.algebraMap_eq_smul_one] using
            (IsSelfAdjoint.algebraMap (A := L K) (r := p) (hr := IsSelfAdjoint.all p))
        exact hA.add hscalar)
      hσA_Icc hA (hf.mono <| by
        intro x hx
        exact lt_of_lt_of_le hαpos hx.1)

omit [Nontrivial (L K)] in
/-- Operator monotonicity on `(0,∞)` passes to CFC limits (the same
approximation principle as `operatorConvexOn_of_tendsto_Ioi`). -/
lemma operatorMonotoneOn_of_tendsto_Ioi
    {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hlim :
      ∀ {A : L K}, IsSelfAdjoint A →
        spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
        Filter.Tendsto (fun p : ℝ => cfcR (ℋ := K) (F p) A)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds (cfcR (ℋ := K) f A)))
    (hmono :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) (F p)) :
    OperatorMonotoneOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) f := by
  intro A B hA hB hσA hσB hAB
  have hEventually :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := K) (F p) A ≤ cfcR (ℋ := K) (F p) B := by
    filter_upwards [hmono] with p hp
    exact hp hA hB hσA hσB hAB
  exact le_of_tendsto_of_tendsto (hlim hA hσA) (hlim hB hσB) hEventually

/-- Operator concavity on `(0,∞)` passes to CFC limits, by negation from
`operatorConvexOn_of_tendsto_Ioi`. -/
lemma operatorConcaveOn_of_tendsto_Ioi
    {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hlim :
      ∀ {A : L K}, IsSelfAdjoint A →
        spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
        Filter.Tendsto (fun p : ℝ => cfcR (ℋ := K) (F p) A)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds (cfcR (ℋ := K) f A)))
    (hconc :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        OperatorConcaveOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) (F p)) :
    OperatorConcaveOnInterval (ℋ := K) (Set.Ioi (0 : ℝ)) f := by
  simpa [OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn] using
    operatorConvexOn_of_tendsto_Ioi (ℋ := K)
      (F := fun p x => -(F p x)) (f := fun x => -f x)
      (by
        intro A hA hσA
        simpa [cfcR, cfc_neg] using (hlim (A := A) hA hσA).neg)
      (by
        filter_upwards [hconc] with p hp
        simpa [OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn] using hp)

end FixedK

/-- Combined form of `cfc_shift_eq_Ici` and `cfc_add_const_tendsto_Ioi`:
`cfcR (f (· + p)) A → cfcR f A` as `p → 0⁺`. -/
lemma shifted_cfc_tendsto_Ioi
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto (fun p : ℝ ↦ cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (cfcR (ℋ := K) f A)) := by
  have hσA_half : spectrum ℝ A ⊆ halfOpenRay ⊤ := by
    intro x hx
    have hx0 : 0 < x := by simpa [Set.mem_Ioi] using hσA hx
    simpa [halfOpenRay_top, Set.mem_Ici] using le_of_lt hx0
  have hrepl :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A =
          cfcR (ℋ := K) f (A + (p : ℝ) • (1 : L K)) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    simpa using cfc_shift_eq_Ici (K := K) (A := A) hA hσA_half hf hp
  exact (cfc_add_const_tendsto_Ioi (K := K) hA hσA hf).congr'
    (Filter.EventuallyEq.symm hrepl)

/-- Operator monotonicity on `(0,∞)` transports to the shifted function on
`[0,∞)`. -/
lemma allHOperatorMonotone_shift_Ici {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hmono : AllHOperatorMonotoneOnInterval.{u} (Set.Ioi (0 : ℝ)) f)
    {ε : ℝ} (hε : 0 < ε) :
    AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) (fun t : ℝ ↦ f (t + ε)) := by
  intro K _ _ _ _ _ A B hA hB hσA hσB hAB
  have hσA_half : spectrum ℝ A ⊆ halfOpenRay ⊤ := hσA
  have hσB_half : spectrum ℝ B ⊆ halfOpenRay ⊤ := hσB
  have hAε_sa : IsSelfAdjoint (A + (ε : ℝ) • (1 : L K)) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      hA.add (IsSelfAdjoint.algebraMap (A := L K) (r := ε) (hr := IsSelfAdjoint.all ε))
  have hBε_sa : IsSelfAdjoint (B + (ε : ℝ) • (1 : L K)) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      hB.add (IsSelfAdjoint.algebraMap (A := L K) (r := ε) (hr := IsSelfAdjoint.all ε))
  have hσAε : spectrum ℝ (A + (ε : ℝ) • (1 : L K)) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_add_pos_scalar_subset_Ioi (K := K) hA hσA_half hε
  have hσBε : spectrum ℝ (B + (ε : ℝ) • (1 : L K)) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_add_pos_scalar_subset_Ioi (K := K) hB hσB_half hε
  have hbase := hmono K hAε_sa hBε_sa hσAε hσBε
    (by simpa using add_le_add_right hAB ((ε : ℝ) • (1 : L K)))
  rw [cfc_shift_eq_Ici (K := K) (A := A) hA hσA_half hf hε,
    cfc_shift_eq_Ici (K := K) (A := B) hB hσB_half hf hε]
  exact hbase

/-- Operator concavity on `(0,∞)` transports to the shifted function on
`[0,∞)`. -/
lemma allHOperatorConcave_shift_Ici {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hconc : AllHOperatorConcaveOnInterval.{u} (Set.Ioi (0 : ℝ)) f)
    {p : ℝ} (hp0 : 0 < p) :
    AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) (fun t : ℝ ↦ f (t + p)) := by
  intro K' _ _ _ _ _ A B t hA hB ht0 ht1 hσA hσB
  let C : L K' := (1 - t) • A + t • B
  have hAε_sa : IsSelfAdjoint (A + (p : ℝ) • (1 : L K')) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      hA.add (IsSelfAdjoint.algebraMap (A := L K') (r := p) (hr := IsSelfAdjoint.all p))
  have hBε_sa : IsSelfAdjoint (B + (p : ℝ) • (1 : L K')) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      hB.add (IsSelfAdjoint.algebraMap (A := L K') (r := p) (hr := IsSelfAdjoint.all p))
  have hσAε : spectrum ℝ (A + (p : ℝ) • (1 : L K')) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_add_pos_scalar_subset_Ioi (K := K') hA hσA hp0
  have hσBε : spectrum ℝ (B + (p : ℝ) • (1 : L K')) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_add_pos_scalar_subset_Ioi (K := K') hB hσB hp0
  have hbase := hconc K' hAε_sa hBε_sa ht0 ht1 hσAε hσBε
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hA0 : 0 ≤ A := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici (ℋ := K') hA
      (by simpa [halfOpenRay_top] using hσA)
    have hB0 : 0 ≤ B := nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici (ℋ := K') hB
      (by simpa [halfOpenRay_top] using hσB)
    exact add_nonneg
      (smul_nonneg (sub_nonneg.mpr ht1) hA0)
      (smul_nonneg ht0 hB0)
  have hC_sa : IsSelfAdjoint C := IsSelfAdjoint.of_nonneg hC0
  have hσC : spectrum ℝ C ⊆ halfOpenRay ⊤ :=
    spectrum_subset_halfOpenRay_top_of_nonneg (ℋ := K') hC0
  have hσCε : spectrum ℝ (C + (p : ℝ) • (1 : L K')) ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_add_pos_scalar_subset_Ioi (K := K') hC_sa hσC hp0
  let fp : ℝ → ℝ := fun t : ℝ ↦ f (t + p)
  have hshiftA_neg :
      cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) A =
        cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (A + (p : ℝ) • (1 : L K')) := by
    simpa [fp] using cfc_shift_eq_Ici (K := K') (A := A) hA hσA hf.neg hp0
  have hshiftB_neg :
      cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) B =
        cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (B + (p : ℝ) • (1 : L K')) := by
    simpa [fp] using cfc_shift_eq_Ici (K := K') (A := B) hB hσB hf.neg hp0
  have hshiftC_neg :
      cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) C =
        cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (C + (p : ℝ) • (1 : L K')) := by
    simpa [fp, C] using cfc_shift_eq_Ici (K := K') (A := C) hC_sa hσC hf.neg hp0
  have hsum :
      C + (p : ℝ) • (1 : L K') =
        (1 - t) • (A + (p : ℝ) • (1 : L K')) + t • (B + (p : ℝ) • (1 : L K')) := by
    dsimp [C]
    calc
      (1 - t) • A + t • B + (p : ℝ) • (1 : L K')
          = (1 - t) • A + t • B + (((1 - t) * p + t * p) : ℝ) • (1 : L K') := by
              congr 2
              ring
      _ = (1 - t) • (A + (p : ℝ) • (1 : L K')) + t • (B + (p : ℝ) • (1 : L K')) := by
            simp [smul_add, smul_smul, add_smul, add_assoc, add_left_comm, add_comm,
              sub_eq_add_neg, mul_comm]
  have hbase' :
      cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) C ≤
        (1 - t) • cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) A +
          t • cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) B := by
    calc
      cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) C
          = cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (C + (p : ℝ) • (1 : L K')) := hshiftC_neg
      _ ≤ (1 - t) • cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (A + (p : ℝ) • (1 : L K')) +
            t • cfcR (ℋ := K') (fun x : ℝ ↦ -f x) (B + (p : ℝ) • (1 : L K')) := by
              simpa [hsum] using hbase
      _ = (1 - t) • cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) A +
            t • cfcR (ℋ := K') (fun x : ℝ ↦ -fp x) B := by
              rw [← hshiftA_neg, ← hshiftB_neg]
  simpa [OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn, C] using hbase'

/-- Positive spectral mapping: a positive continuous function of a positive
operator has spectrum in `(0,∞)`. -/
lemma spectrum_cfc_subset_Ioi_of_continuous_pos
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < f t) :
    spectrum ℝ (cfcR (ℋ := K) f A) ⊆ Set.Ioi (0 : ℝ) := by
  have hcont : ContinuousOn f (spectrum ℝ A) := by
    refine hf.mono ?_
    intro x hx
    exact hσA hx
  have hspec :
      spectrum ℝ (cfcR (ℋ := K) f A) = f '' spectrum ℝ A := by
    simpa [cfcR] using
      (cfc_map_spectrum (R := ℝ) (A := L K) (p := IsSelfAdjoint)
        (f := f) (a := A) (hf := hcont) (ha := hA))
  rw [hspec]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact hpos y (hσA hy)

-- Keep the inverse-composition bridge behind a declaration boundary: Lean 4.29
-- times out more easily when the same `cfc_comp'` proof is repeated inline.
/-- `cfcR (1/f) A = cfcR (1/·) (cfcR f A)` for `f` positive on the spectrum
(declaration-boundary form). -/
theorem cfc_inv_comp_of_pos_Ioi
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {f : ℝ → ℝ} {g : ℝ → ℝ} {A : L K}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hgdef : g = fun t : ℝ ↦ 1 / f t) :
    cfcR (ℋ := K) g A = cfcR (ℋ := K) (fun x : ℝ ↦ 1 / x) (cfcR (ℋ := K) f A) := by
  have hcont_fA : ContinuousOn (fun x : ℝ ↦ 1 / x) (f '' spectrum ℝ A) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa [one_div] using (continuousAt_inv₀ (hpos y (hσA hy)).ne').continuousWithinAt
  simpa [hgdef, cfcR, one_div] using
    (cfc_comp' (R := ℝ) (A := L K) (p := IsSelfAdjoint)
      (g := fun x : ℝ ↦ 1 / x) (f := f) (a := A)
      (hg := hcont_fA) (hf := hf.mono (by intro x hx; exact hσA hx)) (ha := hA))

end ShiftApproximation

end HansenPedersen
