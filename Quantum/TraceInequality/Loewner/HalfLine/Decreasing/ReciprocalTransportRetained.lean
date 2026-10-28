/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.Basic
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.BasicRetained
import Quantum.TraceInequality.Loewner.HalfLine.CayleyCFCInternal
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.ReciprocalTransport

/-!
# Positive-ray decreasing representations: reciprocal transport

This module is the Cayley and reciprocal-transport stage of the Simon-style
half-line decreasing-function theory, passing through unitization and CFC
transport to positive-ray monotonicity.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/--
The normalized positive-ray Cayley parameter reverses order on elements whose
quasispectra lie in `(-1,1)`.
-/
theorem positiveRayNormalizedCayleyParameter_antitone
    {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha_sa : IsSelfAdjoint a) (hb_sa : IsSelfAdjoint b)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) (hab : a ≤ b) :
    positiveRayNormalizedCayleyParameter b ≤
      positiveRayNormalizedCayleyParameter a := by
  let pa : Unitization ℂ A := cfc unitToPositiveCayley (a : Unitization ℂ A)
  let pb : Unitization ℂ A := cfc unitToPositiveCayley (b : Unitization ℂ A)
  have hpa_nonneg : 0 ≤ pa := by
    simpa [pa] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := a) ha_sa ha
  have hpb_nonneg : 0 ≤ pb := by
    simpa [pb] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := b) hb_sa hb
  have hp_le : pa ≤ pb := by
    simpa [pa, pb] using
      cfc_unitToPositiveCayley_mono_of_interval
        (A := A) ha_sa hb_sa ha hb hab
  have hpa_spec : spectrum ℝ pa ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pa] using spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
      (A := A) (a := a) ha_sa ha
  have hpb_spec : spectrum ℝ pb ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pb] using spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
      (A := A) (a := b) hb_sa hb
  have hanti :
      LownerHeinzCore.OperatorAntitoneOn
        (𝓐 := Unitization ℂ A) (Set.Ioi (0 : ℝ)) (fun x : ℝ => 1 / x) := by
    exact
      @LownerHeinzCore.one_div_operatorAntitoneOn_Ioi
        (Unitization ℂ A) inferInstance Unitization.instPartialOrder
        Unitization.instStarOrderedRing
  have hpb_sa : IsSelfAdjoint pb :=
    @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
      inferInstance Unitization.instStarOrderedRing pb hpb_nonneg
  have hpa_sa : IsSelfAdjoint pa :=
    @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
      inferInstance Unitization.instStarOrderedRing pa hpa_nonneg
  dsimp [LownerHeinzCore.OperatorAntitoneOn] at hanti
  simpa [positiveRayNormalizedCayleyParameter, pa, pb] using
    hanti hpb_sa hpa_sa hp_le hpb_spec hpa_spec

/-! ### Reciprocal CFC transport to positive monotonicity -/

/--
If the reciprocal `g = 1 / f` is CFC-antitone on `(0,∞)` and `f` is positive,
then `f` is positive-ray operator monotone.
-/
theorem operatorMonotoneOnPositive_of_reciprocal_operatorAntitoneOnAll
    {f g : ℝ → ℝ}
    (hfpos : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 < f x)
    (hgf : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = (f x)⁻¹)
    (hganti : LownerHeinzCore.OperatorAntitoneOnAll.{0} (Set.Ioi (0 : ℝ)) g) :
    OperatorMonotoneOnPositive.{u} f := by
  refine operatorMonotoneOnPositive_of_unitIntervalFiniteMatrixMonotone
    (unitIntervalMatrixMonotone_of_finiteMatrixMonotone ?_)
  refine ⟨?_⟩
  intro A _ _ _ _ a ha b hb hab
  let ua : Unitization ℂ A := (a : Unitization ℂ A)
  let ub : Unitization ℂ A := (b : Unitization ℂ A)
  let pa : Unitization ℂ A := cfc unitToPositiveCayley ua
  let pb : Unitization ℂ A := cfc unitToPositiveCayley ub
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  have hpa_nonneg : 0 ≤ pa := by
    simpa [pa, ua] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := a) ha.1 ha.2
  have hpb_nonneg : 0 ≤ pb := by
    simpa [pb, ub] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := b) hb.1 hb.2
  have hp_le : pa ≤ pb := by
    simpa [pa, pb, ua, ub] using
      cfc_unitToPositiveCayley_mono_of_interval
        (A := A) ha.1 hb.1 ha.2 hb.2 hab
  have hpa_spec : spectrum ℝ pa ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pa, ua] using spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
      (A := A) (a := a) ha.1 ha.2
  have hpb_spec : spectrum ℝ pb ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pb, ub] using spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
      (A := A) (a := b) hb.1 hb.2
  have hg_le : LownerHeinzCore.cfcR g pb ≤ LownerHeinzCore.cfcR g pa := by
    have hanti :
        LownerHeinzCore.OperatorAntitoneOn
          (𝓐 := Unitization ℂ A) (Set.Ioi (0 : ℝ)) g := by
      exact
        @hganti (Unitization ℂ A) inferInstance Unitization.instPartialOrder
          Unitization.instStarOrderedRing inferInstance
    have hpb_sa : IsSelfAdjoint pb :=
      @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
        inferInstance Unitization.instStarOrderedRing pb hpb_nonneg
    have hpa_sa : IsSelfAdjoint pa :=
      @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
        inferInstance Unitization.instStarOrderedRing pa hpa_nonneg
    dsimp [LownerHeinzCore.OperatorAntitoneOn] at hanti
    exact hanti hpb_sa hpa_sa hp_le hpb_spec hpa_spec
  have hfin_pa : (spectrum ℝ pa).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex (B := Unitization ℂ A) pa
  have hfin_pb : (spectrum ℝ pb).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex (B := Unitization ℂ A) pb
  have hpa_ne : ∀ x ∈ spectrum ℝ pa, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hfpos x (hpa_spec hx))
  have hpb_ne : ∀ x ∈ spectrum ℝ pb, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hfpos x (hpb_spec hx))
  let ufa : (Unitization ℂ A)ˣ :=
    cfcUnits (R := ℝ) (A := Unitization ℂ A)
      (p := IsSelfAdjoint) f pa hpa_ne
      (hf := hfin_pa.continuousOn _) (ha := cfc_predicate unitToPositiveCayley ua)
  let ufb : (Unitization ℂ A)ˣ :=
    cfcUnits (R := ℝ) (A := Unitization ℂ A)
      (p := IsSelfAdjoint) f pb hpb_ne
      (hf := hfin_pb.continuousOn _) (ha := cfc_predicate unitToPositiveCayley ub)
  have hga_eq :
      LownerHeinzCore.cfcR g pa = (↑ufa⁻¹ : Unitization ℂ A) := by
    have hg_cfc :
        LownerHeinzCore.cfcR g pa =
          cfc (fun x : ℝ => (f x)⁻¹) pa := by
      dsimp [LownerHeinzCore.cfcR]
      apply cfc_congr
      intro x hx
      exact hgf x (hpa_spec hx)
    have hfinv :
        cfc (fun x : ℝ => (f x)⁻¹) pa =
          Ring.inverse (cfc f pa) := by
      exact cfc_inv (R := ℝ) (A := Unitization ℂ A)
        (p := IsSelfAdjoint) (f := f) (a := pa) hpa_ne
        (hf := hfin_pa.continuousOn _) (ha := cfc_predicate unitToPositiveCayley ua)
    have hufa : (ufa : Unitization ℂ A) = cfc f pa := by
      rfl
    rw [hg_cfc, hfinv]
    simpa [hufa] using (Ring.inverse_unit ufa)
  have hgb_eq :
      LownerHeinzCore.cfcR g pb = (↑ufb⁻¹ : Unitization ℂ A) := by
    have hg_cfc :
        LownerHeinzCore.cfcR g pb =
          cfc (fun x : ℝ => (f x)⁻¹) pb := by
      dsimp [LownerHeinzCore.cfcR]
      apply cfc_congr
      intro x hx
      exact hgf x (hpb_spec hx)
    have hfinv :
        cfc (fun x : ℝ => (f x)⁻¹) pb =
          Ring.inverse (cfc f pb) := by
      exact cfc_inv (R := ℝ) (A := Unitization ℂ A)
        (p := IsSelfAdjoint) (f := f) (a := pb) hpb_ne
        (hf := hfin_pb.continuousOn _) (ha := cfc_predicate unitToPositiveCayley ub)
    have hufb : (ufb : Unitization ℂ A) = cfc f pb := by
      rfl
    rw [hg_cfc, hfinv]
    simpa [hufb] using (Ring.inverse_unit ufb)
  have hufb_inv_nonneg : 0 ≤ (↑ufb⁻¹ : Unitization ℂ A) := by
    have hnonneg :
        0 ≤ cfc (fun x : ℝ => (f x)⁻¹) pb := by
      refine @cfc_nonneg ℝ (Unitization ℂ A) IsSelfAdjoint
        _ _ _ _ _ _ _ _ _ _ _ Unitization.instPartialOrder
        Unitization.instStarOrderedRing _ _
        (f := fun x : ℝ => (f x)⁻¹) (a := pb) ?_
      intro x hx
      exact le_of_lt (inv_pos.mpr (hfpos x (hpb_spec hx)))
    simpa [ufb] using hnonneg
  have hinv_le : (↑ufb⁻¹ : Unitization ℂ A) ≤ (↑ufa⁻¹ : Unitization ℂ A) := by
    rw [← hga_eq, ← hgb_eq]
    exact hg_le
  have huf_le : (ufa : Unitization ℂ A) ≤ (ufb : Unitization ℂ A) := by
    haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
    have h :=
      @CStarAlgebra.inv_le_inv (Unitization ℂ A) inferInstance
        Unitization.instPartialOrder Unitization.instStarOrderedRing
        (a := ufb⁻¹) (b := ufa⁻¹) hufb_inv_nonneg hinv_le
    simpa using h
  have htarget_unit :
      cfc (fun y : ℝ =>
          positiveCayleyPullback f y - positiveCayleyPullback f 0) ua ≤
        cfc (fun y : ℝ =>
          positiveCayleyPullback f y - positiveCayleyPullback f 0) ub := by
    have heqa :=
      cfc_pullback_eq_cfc_halfline_add_const
        (h := f) (A := A) (a := a) ha.1 ha.2
    have heqb :=
      cfc_pullback_eq_cfc_halfline_add_const
        (h := f) (A := A) (a := b) hb.1 hb.2
    have hpa_shift :
        cfc (fun x : ℝ => f x - f 0) pa +
            algebraMap ℝ (Unitization ℂ A) (f 0) =
          cfc f pa := by
      have hcont : ContinuousOn (fun x : ℝ => f x - f 0) (spectrum ℝ pa) :=
        hfin_pa.continuousOn _
      calc
        cfc (fun x : ℝ => f x - f 0) pa +
            algebraMap ℝ (Unitization ℂ A) (f 0) =
            cfc (fun x : ℝ => (f x - f 0) + f 0) pa := by
              exact (cfc_add_const (r := f 0)
                (f := fun x : ℝ => f x - f 0) (a := pa)
                (hf := hcont) (ha := cfc_predicate unitToPositiveCayley ua)).symm
        _ = cfc f pa := by
              apply cfc_congr
              intro x hx
              ring
    have hpb_shift :
        cfc (fun x : ℝ => f x - f 0) pb +
            algebraMap ℝ (Unitization ℂ A) (f 0) =
          cfc f pb := by
      have hcont : ContinuousOn (fun x : ℝ => f x - f 0) (spectrum ℝ pb) :=
        hfin_pb.continuousOn _
      calc
        cfc (fun x : ℝ => f x - f 0) pb +
            algebraMap ℝ (Unitization ℂ A) (f 0) =
            cfc (fun x : ℝ => (f x - f 0) + f 0) pb := by
              exact (cfc_add_const (r := f 0)
                (f := fun x : ℝ => f x - f 0) (a := pb)
                (hf := hcont) (ha := cfc_predicate unitToPositiveCayley ub)).symm
        _ = cfc f pb := by
              apply cfc_congr
              intro x hx
              ring
    have huf_shift :
        cfc (fun x : ℝ => f x - f 0) pa ≤
          cfc (fun x : ℝ => f x - f 0) pb := by
      have hwith_const :
          cfc (fun x : ℝ => f x - f 0) pa +
              algebraMap ℝ (Unitization ℂ A) (f 0) ≤
            cfc (fun x : ℝ => f x - f 0) pb +
              algebraMap ℝ (Unitization ℂ A) (f 0) := by
        rw [hpa_shift, hpb_shift]
        simpa [pa, pb, ufa, ufb] using huf_le
      exact (add_le_add_iff_right
        (algebraMap ℝ (Unitization ℂ A) (f 0))).1 hwith_const
    have hmono_with_const :
        cfc (fun y : ℝ =>
            positiveCayleyPullback f y - positiveCayleyPullback f 0) ua +
            algebraMap ℝ (Unitization ℂ A) (f 1 - f 0) ≤
          cfc (fun y : ℝ =>
            positiveCayleyPullback f y - positiveCayleyPullback f 0) ub +
            algebraMap ℝ (Unitization ℂ A) (f 1 - f 0) := by
      rw [heqa, heqb]
      simpa [pa, pb, ua, ub] using huf_shift
    exact (add_le_add_iff_right
      (algebraMap ℝ (Unitization ℂ A) (f 1 - f 0))).1 hmono_with_const
  rw [← Unitization.inr_le_iff
    (cfcₙ
      (fun y : ℝ =>
        positiveCayleyPullback f y - positiveCayleyPullback f 0) a)
    (cfcₙ
      (fun y : ℝ =>
        positiveCayleyPullback f y - positiveCayleyPullback f 0) b)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveCayleyPullback f y - positiveCayleyPullback f 0) a)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveCayleyPullback f y - positiveCayleyPullback f 0) b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
    (fun y : ℝ =>
      positiveCayleyPullback f y - positiveCayleyPullback f 0) (by simp),
    Unitization.real_cfcₙ_eq_cfc_inr b
    (fun y : ℝ =>
      positiveCayleyPullback f y - positiveCayleyPullback f 0) (by simp)]
  exact htarget_unit

end

end Quantum.TraceInequality.Loewner
