import Quantum.Analysis.CStar.CayleySpectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo

/-!
# Shared Cayley and finite-spectrum CFC infrastructure

This internal module collects the Cayley-transform, unitization, and finite-spectrum
lemmas used by the direct, decreasing, and endpoint half-line bridges.
-/

namespace Quantum.TraceInequality.Loewner

open Set Filter

open scoped Topology

noncomputable section

theorem quasispectrum_finite_of_finiteDimensional_complex
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] (a : A) :
    (quasispectrum ℝ a).Finite := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a]
  exact spectrum_real_finite_of_finiteDimensional_complex (B := Unitization ℂ A)
    (a : Unitization ℂ A)

theorem spectrum_unitization_inr_subset_of_quasispectrum_subset
    {A : Type*} [NonUnitalCStarAlgebra A] {a : A} {s : Set ℝ}
    (ha : quasispectrum ℝ a ⊆ s) :
    spectrum ℝ (a : Unitization ℂ A) ⊆ s := by
  intro x hx
  have hxq : x ∈ quasispectrum ℝ a := by
    simpa [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a] using hx
  exact ha hxq

theorem cfc_unitToPositiveCayley_eq_one_add_two_kernel
    {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfc unitToPositiveCayley (a : Unitization ℂ A) =
      1 + (2 : ℝ) •
        ((cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a : A) :
          Unitization ℂ A) := by
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs :
      spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hphi :
      ContinuousOn unitToPositiveCayley (spectrum ℝ (a : Unitization ℂ A)) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  have hker :
      ContinuousOn (unitIntervalOperatorKernel (-1 : ℝ))
        (spectrum ℝ (a : Unitization ℂ A)) := by
    intro x hx
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hs hx
    have hden : 1 + (-1 : ℝ) * x ≠ 0 := by
      have : 1 - x ≠ 0 := by linarith [hxI.2]
      simpa [sub_eq_add_neg, mul_comm] using this
    unfold unitIntervalOperatorKernel
    exact continuousAt_id.div
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden
      |>.continuousWithinAt
  calc
    cfc unitToPositiveCayley (a : Unitization ℂ A) =
        cfc (fun y : ℝ => 1 + 2 * unitIntervalOperatorKernel (-1 : ℝ) y)
          (a : Unitization ℂ A) := by
          apply cfc_congr
          intro y hy
          exact unitToPositiveCayley_eq_one_add_two_kernel (hs hy)
    _ =
        1 + (2 : ℝ) • cfc (unitIntervalOperatorKernel (-1 : ℝ))
          (a : Unitization ℂ A) := by
          rw [cfc_add (f := fun _ : ℝ => 1)
            (g := fun y : ℝ => 2 * unitIntervalOperatorKernel (-1 : ℝ) y)
            (a := (a : Unitization ℂ A))
            (hf := continuousOn_const) (hg := continuousOn_const.mul hker)]
          rw [cfc_const_one ℝ (a := (a : Unitization ℂ A)) (ha := ha_inr)]
          rw [cfc_const_mul (r := (2 : ℝ))
            (f := unitIntervalOperatorKernel (-1 : ℝ))
            (a := (a : Unitization ℂ A)) (hf := hker)]
          rfl
    _ =
        1 + (2 : ℝ) •
          ((cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a : A) :
            Unitization ℂ A) := by
          have hcfc :
              cfc (unitIntervalOperatorKernel (-1 : ℝ))
                  (a : Unitization ℂ A) =
                ((cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a : A) :
                  Unitization ℂ A) :=
            (Unitization.real_cfcₙ_eq_cfc_inr a
              (unitIntervalOperatorKernel (-1 : ℝ))
              (unitIntervalOperatorKernel_map_zero (-1 : ℝ))).symm
          rw [hcfc]

theorem cfc_unitToPositiveCayley_nonneg_of_interval
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ cfc unitToPositiveCayley (a : Unitization ℂ A) := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs :
      spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hnonneg :
      @LE.le (Unitization ℂ A) Unitization.instPartialOrder.toLE 0
        (cfc unitToPositiveCayley (a : Unitization ℂ A)) := by
    exact @cfc_nonneg ℝ (Unitization ℂ A) IsSelfAdjoint
      _ _ _ _ _ _ _ _ _ _ _ Unitization.instPartialOrder
      Unitization.instStarOrderedRing _ _
      (f := unitToPositiveCayley) (a := (a : Unitization ℂ A)) fun x hx =>
        (unitToPositiveCayley_mem_Ioi (hs hx)).le
  exact hnonneg

theorem cfc_unitToPositiveCayley_mono_of_interval
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha_sa : IsSelfAdjoint a) (hb_sa : IsSelfAdjoint b)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) (hab : a ≤ b) :
    cfc unitToPositiveCayley (a : Unitization ℂ A) ≤
      cfc unitToPositiveCayley (b : Unitization ℂ A) := by
  have hker :
      cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a ≤
        cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) b := by
    exact unitIntervalOperatorKernel_cfcₙ_le_of_neg
      (A := A) (lambda := (-1 : ℝ))
      (by norm_num) (by constructor <;> norm_num)
      ha_sa hb_sa ha hb hab
  have hker_unit :
      ((cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) a : A) :
          Unitization ℂ A) ≤
        ((cfcₙ (unitIntervalOperatorKernel (-1 : ℝ)) b : A) :
          Unitization ℂ A) := by
    exact (Unitization.inr_le_iff _ _
      (cfcₙ_predicate (unitIntervalOperatorKernel (-1 : ℝ)) a)
      (cfcₙ_predicate (unitIntervalOperatorKernel (-1 : ℝ)) b)).mpr hker
  rw [cfc_unitToPositiveCayley_eq_one_add_two_kernel (A := A) ha_sa ha,
    cfc_unitToPositiveCayley_eq_one_add_two_kernel (A := A) hb_sa hb]
  simpa [add_comm] using
    add_le_add_left
      (smul_le_smul_of_nonneg_left hker_unit (by norm_num : (0 : ℝ) ≤ 2))
      1

theorem cfc_pullback_eq_cfc_halfline_add_const
    {h : ℝ → ℝ}
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfc (fun y : ℝ =>
        positiveCayleyPullback h y - positiveCayleyPullback h 0)
        (a : Unitization ℂ A) +
      algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) =
      cfc (fun x : ℝ => h x - h 0)
        (cfc unitToPositiveCayley (a : Unitization ℂ A) :
          Unitization ℂ A) := by
  let g : ℝ → ℝ := positiveCayleyPullback h
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs :
      spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hfinite :
      (spectrum ℝ (a : Unitization ℂ A)).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex (B := Unitization ℂ A)
      (a : Unitization ℂ A)
  have hgCont :
      ContinuousOn (fun y : ℝ => g y - g 0)
        (spectrum ℝ (a : Unitization ℂ A)) :=
    hfinite.continuousOn _
  have hphiCont :
      ContinuousOn unitToPositiveCayley (spectrum ℝ (a : Unitization ℂ A)) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  have hhImageCont :
      ContinuousOn (fun x : ℝ => h x - h 0)
        (unitToPositiveCayley '' spectrum ℝ (a : Unitization ℂ A)) :=
    hfinite.image unitToPositiveCayley |>.continuousOn _
  calc
    cfc (fun y : ℝ => g y - g 0) (a : Unitization ℂ A) +
        algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) =
        cfc (fun y : ℝ => (g y - g 0) + (h 1 - h 0))
          (a : Unitization ℂ A) := by
          exact (cfc_add_const (r := h 1 - h 0)
            (f := fun y : ℝ => g y - g 0) (a := (a : Unitization ℂ A))
            (hf := hgCont) (ha := ha_inr)).symm
    _ =
        cfc (fun y : ℝ => h (unitToPositiveCayley y) - h 0)
          (a : Unitization ℂ A) := by
          apply cfc_congr
          intro y hy
          simp [g, positiveCayleyPullback, unitToPositiveCayley_zero]
    _ =
        cfc (fun x : ℝ => h x - h 0)
          (cfc unitToPositiveCayley (a : Unitization ℂ A) :
            Unitization ℂ A) := by
          rw [cfc_comp' (fun x : ℝ => h x - h 0) unitToPositiveCayley
            (a := (a : Unitization ℂ A))
            (hg := hhImageCont) (hf := hphiCont) (ha := ha_inr)]

end

end Quantum.TraceInequality.Loewner
