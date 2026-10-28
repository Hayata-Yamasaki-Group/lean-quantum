import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.ConditionICompat
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.HalfLine.AH1

import Quantum.TraceInequality.HiaiPetz.ConditionICompatCore
import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFCReverse

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

noncomputable section

attribute [local instance]
  instConditionICompatCLMCStar
  instConditionICompatCLMRealCFC
  instConditionICompatMatrixRealAlgebra

noncomputable local instance instConditionICompatCStarMatrixRealAlgebra {n : ℕ} :
    Algebra ℝ (CStarMatrix (Fin n) (Fin n) ℂ) := Algebra.complexToReal

/-- Nonnegative complex matrices have nonnegative real spectrum. -/
noncomputable local instance instConditionICompatMatrixNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.instNonnegSpectrumClass

/-- The C⋆-matrix algebra `CStarMatrix (Fin n) (Fin n) ℂ` is a C⋆-algebra. -/
noncomputable local instance instConditionICompatCStarMatrixCStar {n : ℕ} :
    CStarAlgebra (CStarMatrix (Fin n) (Fin n) ℂ) :=
  CStarMatrix.instCStarAlgebra

/-- The C⋆-matrix algebra `CStarMatrix (Fin n) (Fin n) ℂ` is a star-ordered ring. -/
noncomputable local instance instConditionICompatCStarMatrixStarOrderedRing {n : ℕ} :
    StarOrderedRing (CStarMatrix (Fin n) (Fin n) ℂ) :=
  CStarMatrix.instStarOrderedRing

/-- The C⋆-matrix algebra has a real continuous functional calculus for self-adjoint
elements. -/
local instance instConditionICompatCStarMatrixRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The C⋆-matrix algebra `CStarMatrix (Fin n) (Fin n) ℂ` is finite-dimensional over `ℂ`. -/
noncomputable local instance instConditionICompatCStarMatrixFiniteDimensional {n : ℕ} :
    FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) := by
  let e := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  exact e.toAlgEquiv.toLinearEquiv.finiteDimensional

private theorem conditionICompat_quasispectrum_finite_of_finiteDimensional_complex
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] (a : A) :
    (quasispectrum ℝ a).Finite := by
  haveI : FiniteDimensional ℂ (Unitization ℂ A) := by
    change FiniteDimensional ℂ (ℂ × A)
    infer_instance
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a]
  exact spectrum_real_finite_of_finiteDimensional_complex (B := Unitization ℂ A)
    (a : Unitization ℂ A)

private instance conditionICompat_instUnitizationFiniteDimensional
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (Unitization ℂ A) := by
  change FiniteDimensional ℂ (ℂ × A)
  infer_instance

private instance conditionICompat_instUnitizationStarOrderedRing {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    StarOrderedRing (Unitization ℂ A) :=
  Unitization.instStarOrderedRing

private theorem conditionICompat_spectrum_unitization_inr_subset_of_quasispectrum_subset
    {A : Type*} [NonUnitalCStarAlgebra A] {a : A} {s : Set ℝ}
    (ha : quasispectrum ℝ a ⊆ s) :
    spectrum ℝ (a : Unitization ℂ A) ⊆ s := by
  intro x hx
  have hxq : x ∈ quasispectrum ℝ a := by
    simpa [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a] using hx
  exact ha hxq

private theorem conditionICompat_continuousOn_unitToPositiveCayley_of_subset_Ioo {s : Set ℝ}
    (hs : s ⊆ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn unitToPositiveCayley s := by
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hs hx
  have hden : 1 - x ≠ 0 := by linarith [hxI.2]
  unfold unitToPositiveCayley
  exact ((continuousAt_const.add continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) hden).continuousWithinAt

private theorem conditionICompat_unitToPositiveCayley_eq_one_add_two_kernel {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    unitToPositiveCayley y =
      1 + 2 * unitIntervalOperatorKernel (-1 : ℝ) y := by
  have hden : 1 - y ≠ 0 := by linarith [hy.2]
  unfold unitToPositiveCayley
  have hk : unitIntervalOperatorKernel (-1 : ℝ) y = y / (1 - y) := by
    unfold unitIntervalOperatorKernel
    ring_nf
  rw [hk]
  field_simp [hden]
  ring_nf

private theorem conditionICompat_cfc_unitToPositiveCayley_eq_one_add_two_kernel
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
    conditionICompat_spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hphi :
      ContinuousOn unitToPositiveCayley (spectrum ℝ (a : Unitization ℂ A)) :=
    conditionICompat_continuousOn_unitToPositiveCayley_of_subset_Ioo hs
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
          exact conditionICompat_unitToPositiveCayley_eq_one_add_two_kernel (hs hy)
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

private theorem conditionICompat_cfc_unitToPositiveCayley_mono_of_interval
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
  rw [conditionICompat_cfc_unitToPositiveCayley_eq_one_add_two_kernel (A := A) ha_sa ha,
    conditionICompat_cfc_unitToPositiveCayley_eq_one_add_two_kernel (A := A) hb_sa hb]
  simpa [add_comm] using
    add_le_add_left
      (smul_le_smul_of_nonneg_left hker_unit (by norm_num : (0 : ℝ) ≤ 2))
      1

private theorem conditionICompat_spectrum_cfc_unitToPositiveCayley_subset_Ioi
    {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) ⊆
      Set.Ioi (0 : ℝ) := by
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs :
      spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    conditionICompat_spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hcont :
      ContinuousOn unitToPositiveCayley (spectrum ℝ (a : Unitization ℂ A)) :=
    conditionICompat_continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  have hspec :
      spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) =
        unitToPositiveCayley '' spectrum ℝ (a : Unitization ℂ A) := by
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := Unitization ℂ A)
        (p := IsSelfAdjoint) (f := unitToPositiveCayley)
        (a := (a : Unitization ℂ A)) (ha := ha_inr) (hf := hcont))
  intro y hy
  rw [hspec] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact unitToPositiveCayley_mem_Ioi (hs hx)

private theorem conditionICompat_cfc_pullback_eq_cfc_halfline_add_const
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
    conditionICompat_spectrum_unitization_inr_subset_of_quasispectrum_subset ha
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
    conditionICompat_continuousOn_unitToPositiveCayley_of_subset_Ioo hs
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

private def conditionICompatStarAlgEquivToStarAlgHom {A B : Type*}
    [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring B] [Algebra ℂ B] [Star B]
    (e : A ≃⋆ₐ[ℂ] B) : A →⋆ₐ[ℂ] B :=
  { e.toAlgEquiv.toAlgHom with
    map_star' := by
      intro x
      exact map_star e x }

private def conditionICompatStarAlgEquivToNonUnitalStarAlgHom {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B] [Star B]
    (e : A ≃⋆ₐ[ℂ] B) : A →⋆ₙₐ[ℂ] B where
  toFun := e
  map_zero' := map_zero e
  map_add' := map_add e
  map_mul' := map_mul e
  map_smul' := map_smul e
  map_star' := map_star e

private lemma conditionICompat_starAlgEquiv_map_nonneg {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : 0 ≤ x) :
    0 ≤ e x := by
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hx ⊢
  rcases hx with ⟨y, hy⟩
  refine ⟨e y, ?_⟩
  calc
    e x = e (star y * y) := by rw [hy]
    _ = e (star y) * e y := by rw [map_mul]
    _ = star (e y) * e y := by rw [map_star]

private lemma conditionICompat_starAlgEquiv_map_le {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x y : A} (hxy : x ≤ y) :
    e x ≤ e y := by
  rw [← sub_nonneg] at hxy ⊢
  have hmap := conditionICompat_starAlgEquiv_map_nonneg (A := A) (B := B) e hxy
  simpa [map_sub] using hmap

private lemma conditionICompat_nonUnitalStarAlgEquiv_map_nonneg {A B : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : 0 ≤ x) :
    0 ≤ e x := by
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hx ⊢
  rcases hx with ⟨y, hy⟩
  refine ⟨e y, ?_⟩
  calc
    e x = e (star y * y) := by rw [hy]
    _ = e (star y) * e y := by rw [map_mul]
    _ = star (e y) * e y := by rw [map_star]

private lemma conditionICompat_nonUnitalStarAlgEquiv_map_le {A B : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x y : A} (hxy : x ≤ y) :
    e x ≤ e y := by
  rw [← sub_nonneg] at hxy ⊢
  have hmap := conditionICompat_nonUnitalStarAlgEquiv_map_nonneg (A := A) (B := B) e hxy
  simpa [map_sub] using hmap


-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
private theorem conditionICompat_cstarMatrix_cfc_eq_of_matrixCfcR {f : ℝ → ℝ} {n : ℕ}
    (A : CStarMatrix (Fin n) (Fin n) ℂ) (hA : IsSelfAdjoint A) :
    CStarMatrix.ofMatrix
        (HansenPedersen.matrixCfcR f
          ((CStarMatrix.ofMatrix (m := Fin n) (n := Fin n) (A := ℂ)).symm A)) =
      LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) f A := by
  let e := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) ℂ := conditionICompatStarAlgEquivToStarAlgHom e
  let ψ : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin n) (Fin n) ℂ := conditionICompatStarAlgEquivToStarAlgHom e.symm
  have hψA : IsSelfAdjoint (ψ A) := hA.map ψ
  have hφψA : IsSelfAdjoint (φ (ψ A)) := by
    simpa [φ, ψ, e] using hA
  have hfin : (spectrum ℝ (ψ A)).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex
      (B := Matrix (Fin n) (Fin n) ℂ) (ψ A)
  have hmap :
      φ (cfc f (ψ A)) = cfc f (φ (ψ A)) := by
    have hφcont : Continuous φ := by
      simpa [φ, conditionICompatStarAlgEquivToStarAlgHom] using (StarAlgEquiv.isometry e).continuous
    exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ f (ψ A)
      (hf := hfin.continuousOn f) (hφ := hφcont) (ha := hψA) (hφa := hφψA)
  have hmatrix :
      HansenPedersen.matrixCfcR f (ψ A) = cfc f (ψ A) :=
    conditionICompat_matrixCfcR_eq_cfc (f := f) (A := ψ A) hψA
  dsimp [LownerHeinzCore.cfcR]
  change φ (HansenPedersen.matrixCfcR f (ψ A)) = cfc f A
  rw [hmatrix, hmap]
  have hround : φ (ψ A) = A := by
    change e (e.symm A) = A
    exact e.apply_symm_apply A
  rw [hround]

-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
private theorem conditionICompat_cstarMatrix_conditionI_cfc_le_of_order {f : ℝ → ℝ} {n : ℕ}
    (hI : ConditionI f)
    {A B : CStarMatrix (Fin n) (Fin n) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAspec : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hBspec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hAB : A ≤ B) :
    LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) f A ≤
      LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) f B := by
  let e := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) ℂ := conditionICompatStarAlgEquivToStarAlgHom e
  let ψ : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin n) (Fin n) ℂ := conditionICompatStarAlgEquivToStarAlgHom e.symm
  have hψA : IsSelfAdjoint (ψ A) := hA.map ψ
  have hψB : IsSelfAdjoint (ψ B) := hB.map ψ
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    change e.symm x = e.symm y at hxy
    exact e.symm.injective hxy
  have hψAspec : spectrum ℝ (ψ A) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hA.map_spectrum_real ψ hψinj]
    exact hAspec
  have hψBspec : spectrum ℝ (ψ B) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hB.map_spectrum_real ψ hψinj]
    exact hBspec
  have hψAB : ψ A ≤ ψ B := by
    exact conditionICompat_starAlgEquiv_map_le
      (A := CStarMatrix (Fin n) (Fin n) ℂ)
      (B := Matrix (Fin n) (Fin n) ℂ) e.symm hAB
  have hmatrix :
      HansenPedersen.matrixCfcR f (ψ A) ≤ HansenPedersen.matrixCfcR f (ψ B) :=
    hI hψA hψB hψAspec hψBspec hψAB
  have hmapped :
      φ (HansenPedersen.matrixCfcR f (ψ A)) ≤
        φ (HansenPedersen.matrixCfcR f (ψ B)) := by
    exact conditionICompat_starAlgEquiv_map_le
      (A := Matrix (Fin n) (Fin n) ℂ)
      (B := CStarMatrix (Fin n) (Fin n) ℂ) e hmatrix
  have hAe := conditionICompat_cstarMatrix_cfc_eq_of_matrixCfcR
    (f := f) (A := A) hA
  have hBe := conditionICompat_cstarMatrix_cfc_eq_of_matrixCfcR
    (f := f) (A := B) hB
  change
    CStarMatrix.ofMatrix
      (HansenPedersen.matrixCfcR f
        ((CStarMatrix.ofMatrix (m := Fin n) (n := Fin n) (A := ℂ)).symm A)) ≤
      CStarMatrix.ofMatrix
        (HansenPedersen.matrixCfcR f
          ((CStarMatrix.ofMatrix (m := Fin n) (n := Fin n) (A := ℂ)).symm B)) at hmapped
  simpa [hAe, hBe] using hmapped

-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
private theorem conditionICompat_cstarMatrix_cfcₙ_sub_const_le {f : ℝ → ℝ} {n : ℕ}
    (hI : ConditionI f)
    {A B : CStarMatrix (Fin n) (Fin n) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAspec : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hBspec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hAB : A ≤ B) :
    cfcₙ (fun x : ℝ => f x - f 0) A ≤
      cfcₙ (fun x : ℝ => f x - f 0) B := by
  let g : ℝ → ℝ := fun x : ℝ => f x - f 0
  have hg0 : g 0 = 0 := by simp [g]
  have hmonoF :
      cfc f A ≤ cfc f B := by
    have hblock := conditionICompat_cstarMatrix_conditionI_cfc_le_of_order
      (f := f) (n := n) hI hA hB hAspec hBspec hAB
    simpa [LownerHeinzCore.cfcR] using hblock
  have hfd : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    instConditionICompatCStarMatrixFiniteDimensional
  letI : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) := hfd
  have hfinA : (spectrum ℝ A).Finite :=
    @spectrum_real_finite_of_finiteDimensional_complex
      (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance inferInstance inferInstance
      hfd A
  have hfinB : (spectrum ℝ B).Finite :=
    @spectrum_real_finite_of_finiteDimensional_complex
      (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance inferInstance inferInstance
      hfd B
  have hmonoG :
      cfc g A ≤ cfc g B := by
    have hAeq : cfc g A = cfc f A - algebraMap ℝ (CStarMatrix (Fin n) (Fin n) ℂ) (f 0) := by
      dsimp [g]
      rw [cfc_sub (f := f) (g := fun _ : ℝ => f 0) (a := A)
        (hf := hfinA.continuousOn f) (hg := continuousOn_const)]
      rw [cfc_const (R := ℝ) (A := CStarMatrix (Fin n) (Fin n) ℂ)
        (p := IsSelfAdjoint) (r := f 0) (a := A) (ha := hA)]
    have hBeq : cfc g B = cfc f B - algebraMap ℝ (CStarMatrix (Fin n) (Fin n) ℂ) (f 0) := by
      dsimp [g]
      rw [cfc_sub (f := f) (g := fun _ : ℝ => f 0) (a := B)
        (hf := hfinB.continuousOn f) (hg := continuousOn_const)]
      rw [cfc_const (R := ℝ) (A := CStarMatrix (Fin n) (Fin n) ℂ)
        (p := IsSelfAdjoint) (r := f 0) (a := B) (ha := hB)]
    rw [hAeq, hBeq]
    exact sub_le_sub_right hmonoF _
  have hqfinA : (quasispectrum ℝ A).Finite :=
    conditionICompat_quasispectrum_finite_of_finiteDimensional_complex A
  have hqfinB : (quasispectrum ℝ B).Finite :=
    conditionICompat_quasispectrum_finite_of_finiteDimensional_complex B
  change cfcₙ g A ≤ cfcₙ g B
  have hAeqₙ : cfcₙ g A = cfc g A :=
    cfcₙ_eq_cfc (hf := hqfinA.continuousOn g)
  have hBeqₙ : cfcₙ g B = cfc g B :=
    cfcₙ_eq_cfc (hf := hqfinB.continuousOn g)
  simpa [hAeqₙ, hBeqₙ] using hmonoG

/--
gcongr form of Hiai--Petz condition (i) transported to finite `CStarMatrix` CFC.
It delegates to `conditionICompat_cstarMatrix_conditionI_cfc_le_of_order`.
-/
@[gcongr]
theorem cfcR_le_cfcR_of_le_of_conditionI_cstarMatrix
    {f : ℝ → ℝ} (hf : ConditionI f) {n : ℕ}
    {A B : CStarMatrix (Fin n) (Fin n) ℂ} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) f A ≤
      LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) f B :=
  conditionICompat_cstarMatrix_conditionI_cfc_le_of_order
    (f := f) hf hA hB hσA hσB hAB

/--
gcongr form of Hiai--Petz condition (i) for finite `CStarMatrix` non-unital CFC.
It delegates to `conditionICompat_cstarMatrix_cfcₙ_sub_const_le`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_conditionI_cstarMatrix
    {f : ℝ → ℝ} (hf : ConditionI f) {n : ℕ}
    {A B : CStarMatrix (Fin n) (Fin n) ℂ} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcₙ (fun x : ℝ => f x - f 0) A ≤ cfcₙ (fun x : ℝ => f x - f 0) B :=
  conditionICompat_cstarMatrix_cfcₙ_sub_const_le
    (f := f) hf hA hB hσA hσB hAB

-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
private theorem conditionICompat_piCStarMatrix_conditionI_cfcₙ_sub_const_le_of_order {f : ℝ → ℝ}
    (hI : ConditionI f)
    {ι : Type} [Finite ι] {n : ι → ℕ}
    {A B : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAspec : ∀ i : ι, spectrum ℝ (A i) ⊆ Set.Ioi (0 : ℝ))
    (hBspec : ∀ i : ι, spectrum ℝ (B i) ⊆ Set.Ioi (0 : ℝ))
    (hAB : A ≤ B) :
    letI : Fintype ι := Fintype.ofFinite ι
    cfcₙ (fun x : ℝ => f x - f 0) A ≤
      cfcₙ (fun x : ℝ => f x - f 0) B := by
  letI : Fintype ι := Fintype.ofFinite ι
  let g : ℝ → ℝ := fun x : ℝ => f x - f 0
  have hg0 : g 0 = 0 := by simp [g]
  have hAcomp : ∀ i : ι, IsSelfAdjoint (A i) := by
    intro i
    change star (A i) = A i
    exact congrFun hA i
  have hBcomp : ∀ i : ι, IsSelfAdjoint (B i) := by
    intro i
    change star (B i) = B i
    exact congrFun hB i
  have hmono : ∀ i : ι, cfcₙ g (A i) ≤ cfcₙ g (B i) := by
    intro i
    have hABi : A i ≤ B i := hAB i
    exact conditionICompat_cstarMatrix_cfcₙ_sub_const_le
      (f := f) (n := n i) hI (hAcomp i) (hBcomp i)
      (hAspec i) (hBspec i) hABi
  have hmapA : cfcₙ g A = fun i : ι => cfcₙ g (A i) := by
    have hfin : (⋃ i, quasispectrum ℝ (A i)).Finite := by
      exact Set.finite_iUnion fun i =>
        conditionICompat_quasispectrum_finite_of_finiteDimensional_complex (A i)
    exact cfcₙ_map_pi (S := ℂ) g A (hf := hfin.continuousOn g)
      (ha := hA) (ha' := hAcomp)
  have hmapB : cfcₙ g B = fun i : ι => cfcₙ g (B i) := by
    have hfin : (⋃ i, quasispectrum ℝ (B i)).Finite := by
      exact Set.finite_iUnion fun i =>
        conditionICompat_quasispectrum_finite_of_finiteDimensional_complex (B i)
    exact cfcₙ_map_pi (S := ℂ) g B (hf := hfin.continuousOn g)
      (ha := hB) (ha' := hBcomp)
  rw [hmapA, hmapB]
  intro i
  exact hmono i

/--
gcongr form of Hiai--Petz condition (i) for finite products of `CStarMatrix`.
It delegates to `conditionICompat_piCStarMatrix_conditionI_cfcₙ_sub_const_le_of_order`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_conditionI_piCStarMatrix
    {f : ℝ → ℝ} (hf : ConditionI f)
    {ι : Type} [Finite ι] {n : ι → ℕ}
    {A B : ∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ} (hAB : A ≤ B)
    (hA : IsSelfAdjoint A) (hσA : ∀ i : ι, spectrum ℝ (A i) ⊆ Set.Ioi (0 : ℝ))
    (hB : IsSelfAdjoint B) (hσB : ∀ i : ι, spectrum ℝ (B i) ⊆ Set.Ioi (0 : ℝ)) :
    letI : Fintype ι := Fintype.ofFinite ι
    cfcₙ (fun x : ℝ => f x - f 0) A ≤ cfcₙ (fun x : ℝ => f x - f 0) B := by
  letI := Fintype.ofFinite ι
  exact conditionICompat_piCStarMatrix_conditionI_cfcₙ_sub_const_le_of_order
    (f := f) hf hA hB hσA hσB hAB

-- Finite-dimensional CFC transport triggers heavy CStarAlgebra instance search.
-- Matrix and unitization equivalence rewrites make the CFC proof expensive.
private theorem conditionICompat_unitization_conditionI_cfcₙ_sub_const_le_of_order {f : ℝ → ℝ}
    (hI : ConditionI f)
    {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {P Q : Unitization ℂ A}
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hPspec : spectrum ℝ P ⊆ Set.Ioi (0 : ℝ))
    (hQspec : spectrum ℝ Q ⊆ Set.Ioi (0 : ℝ))
    (hPQ : P ≤ Q) :
    cfcₙ (fun x : ℝ => f x - f 0) P ≤
      cfcₙ (fun x : ℝ => f x - f 0) Q := by
  classical
  let g : ℝ → ℝ := fun x : ℝ => f x - f 0
  have hg0 : g 0 = 0 := by simp [g]
  letI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  rcases unitizationStarAlgEquivProvider
      (A := A) with
    ⟨ι, instι, n, hn, ⟨e⟩⟩
  letI : Fintype ι := instι
  haveI : ∀ i : ι, Nontrivial (EuclideanSpace ℂ (Fin (n i))) := hn
  haveI : ∀ i : ι,
      StarOrderedRing (CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    fun _ => CStarMatrix.instStarOrderedRing
  let φ : Unitization ℂ A →⋆ₙₐ[ℂ]
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    conditionICompatStarAlgEquivToNonUnitalStarAlgHom e
  let ψ : (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) →⋆ₙₐ[ℂ]
      Unitization ℂ A :=
    conditionICompatStarAlgEquivToNonUnitalStarAlgHom e.symm
  have hφP : IsSelfAdjoint (φ P) := hP.map φ
  have hφQ : IsSelfAdjoint (φ Q) := hQ.map φ
  have hφPspec :
      ∀ i : ι, spectrum ℝ ((φ P) i) ⊆ Set.Ioi (0 : ℝ) := by
    intro i x hx
    have hxprod : x ∈ spectrum ℝ (e P) := by
      change x ∈ spectrum ℝ ((φ P))
      rw [Pi.spectrum_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hseq :
        spectrum ℝ (e P) = spectrum ℝ P := by
      simpa using
        (AlgEquiv.spectrum_eq
          (R := ℝ) (e.toAlgEquiv.restrictScalars ℝ) P)
    exact hPspec (by simpa [hseq] using hxprod)
  have hφQspec :
      ∀ i : ι, spectrum ℝ ((φ Q) i) ⊆ Set.Ioi (0 : ℝ) := by
    intro i x hx
    have hxprod : x ∈ spectrum ℝ (e Q) := by
      change x ∈ spectrum ℝ ((φ Q))
      rw [Pi.spectrum_eq]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hseq :
        spectrum ℝ (e Q) = spectrum ℝ Q := by
      simpa using
        (AlgEquiv.spectrum_eq
          (R := ℝ) (e.toAlgEquiv.restrictScalars ℝ) Q)
    exact hQspec (by simpa [hseq] using hxprod)
  have hφPQ : φ P ≤ φ Q := by
    exact @conditionICompat_nonUnitalStarAlgEquiv_map_le
      (Unitization ℂ A)
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      inferInstance inferInstance Unitization.instStarOrderedRing
      inferInstance inferInstance inferInstance e P Q hPQ
  have hblock :
      cfcₙ g (φ P) ≤ cfcₙ g (φ Q) := by
    simpa [g] using
      conditionICompat_piCStarMatrix_conditionI_cfcₙ_sub_const_le_of_order
        (f := f) hI hφP hφQ hφPspec hφQspec hφPQ
  have hback :
      ψ (cfcₙ g (φ P)) ≤ ψ (cfcₙ g (φ Q)) := by
    exact @conditionICompat_nonUnitalStarAlgEquiv_map_le
      (∀ i : ι, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ)
      (Unitization ℂ A)
      inferInstance inferInstance inferInstance
      inferInstance inferInstance Unitization.instStarOrderedRing e.symm
      (cfcₙ g (φ P)) (cfcₙ g (φ Q)) hblock
  have hfinφP : (quasispectrum ℝ (φ P)).Finite := by
    have hfin : (quasispectrum ℝ P).Finite :=
      conditionICompat_quasispectrum_finite_of_finiteDimensional_complex P
    have hsubset :
        quasispectrum ℝ (φ P) ⊆ quasispectrum ℝ P := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ φ P
    exact hfin.subset hsubset
  have hfinφQ : (quasispectrum ℝ (φ Q)).Finite := by
    have hfin : (quasispectrum ℝ Q).Finite :=
      conditionICompat_quasispectrum_finite_of_finiteDimensional_complex Q
    have hsubset :
        quasispectrum ℝ (φ Q) ⊆ quasispectrum ℝ Q := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ φ Q
    exact hfin.subset hsubset
  have hmapP :
      ψ (cfcₙ g (φ P)) = cfcₙ g P := by
    have hψφP : IsSelfAdjoint (ψ (φ P)) := by
      change IsSelfAdjoint (e.symm (e P))
      simpa using hP
    have hcf := ψ.map_cfcₙ g (φ P)
      (hf := hfinφP.continuousOn g) (hf₀ := hg0)
      (ha := hφP) (hφa := hψφP)
    have hround : ψ (φ P) = P := by
      change e.symm (e P) = P
      exact e.symm_apply_apply P
    exact hcf.trans (congrArg (fun x : Unitization ℂ A => cfcₙ g x) hround)
  have hmapQ :
      ψ (cfcₙ g (φ Q)) = cfcₙ g Q := by
    have hψφQ : IsSelfAdjoint (ψ (φ Q)) := by
      change IsSelfAdjoint (e.symm (e Q))
      simpa using hQ
    have hcf := ψ.map_cfcₙ g (φ Q)
      (hf := hfinφQ.continuousOn g) (hf₀ := hg0)
      (ha := hφQ) (hφa := hψφQ)
    have hround : ψ (φ Q) = Q := by
      change e.symm (e Q) = Q
      exact e.symm_apply_apply Q
    exact hcf.trans (congrArg (fun x : Unitization ℂ A => cfcₙ g x) hround)
  change cfcₙ g P ≤ cfcₙ g Q
  simpa [hmapP, hmapQ] using hback

/--
gcongr form of Hiai--Petz condition (i) for finite-dimensional unitizations.
It delegates to `conditionICompat_unitization_conditionI_cfcₙ_sub_const_le_of_order`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_conditionI_unitization
    {f : ℝ → ℝ} (hf : ConditionI f)
    {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ A]
    {P Q : Unitization ℂ A} (hPQ : P ≤ Q)
    (hP : IsSelfAdjoint P) (hσP : spectrum ℝ P ⊆ Set.Ioi (0 : ℝ))
    (hQ : IsSelfAdjoint Q) (hσQ : spectrum ℝ Q ⊆ Set.Ioi (0 : ℝ)) :
    cfcₙ (fun x : ℝ => f x - f 0) P ≤ cfcₙ (fun x : ℝ => f x - f 0) Q :=
  conditionICompat_unitization_conditionI_cfcₙ_sub_const_le_of_order
    (f := f) hf hP hQ hσP hσQ hPQ

/--
Hiai-Petz condition (i) gives finite-dimensional matrix monotonicity after the
positive-to-unit Cayley pullback. This is the Loewner entry step for the
positive-ray route [carlen2022].
-/
theorem conditionI_to_unitIntervalFiniteMatrixMonotone {f : ℝ → ℝ}
    (hI : ConditionI f) :
    UnitIntervalFiniteMatrixMonotone.{0} (positiveCayleyPullback f) := by
  refine ⟨?_⟩
  intro A _ _ _ hfd a ha b hb hab
  let ua : Unitization ℂ A := (a : Unitization ℂ A)
  let ub : Unitization ℂ A := (b : Unitization ℂ A)
  let pa : Unitization ℂ A := cfc unitToPositiveCayley ua
  let pb : Unitization ℂ A := cfc unitToPositiveCayley ub
  haveI : FiniteDimensional ℂ A := hfd
  letI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  have hpa_sa : IsSelfAdjoint pa := by
    dsimp [pa, ua]
    exact cfc_predicate unitToPositiveCayley (a : Unitization ℂ A)
  have hpb_sa : IsSelfAdjoint pb := by
    dsimp [pb, ub]
    exact cfc_predicate unitToPositiveCayley (b : Unitization ℂ A)
  have hpa_spec : spectrum ℝ pa ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pa, ua] using
      conditionICompat_spectrum_cfc_unitToPositiveCayley_subset_Ioi
        (A := A) (a := a) ha.1 ha.2
  have hpb_spec : spectrum ℝ pb ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pb, ub] using
      conditionICompat_spectrum_cfc_unitToPositiveCayley_subset_Ioi
        (A := A) (a := b) hb.1 hb.2
  have hp_le : pa ≤ pb := by
    simpa [pa, pb, ua, ub] using
      conditionICompat_cfc_unitToPositiveCayley_mono_of_interval
        (A := A) ha.1 hb.1 ha.2 hb.2 hab
  have hmonoₙ :
      cfcₙ (fun x : ℝ => f x - f 0) pa ≤
        cfcₙ (fun x : ℝ => f x - f 0) pb :=
    conditionICompat_unitization_conditionI_cfcₙ_sub_const_le_of_order
      (f := f) hI hpa_sa hpb_sa hpa_spec hpb_spec hp_le
  have hmono :
      cfc (fun x : ℝ => f x - f 0) pa ≤
        cfc (fun x : ℝ => f x - f 0) pb := by
    have hfin_pa : (quasispectrum ℝ pa).Finite :=
      conditionICompat_quasispectrum_finite_of_finiteDimensional_complex pa
    have hfin_pb : (quasispectrum ℝ pb).Finite :=
      conditionICompat_quasispectrum_finite_of_finiteDimensional_complex pb
    have hmono' := hmonoₙ
    rw [cfcₙ_eq_cfc (hf := hfin_pa.continuousOn _),
      cfcₙ_eq_cfc (hf := hfin_pb.continuousOn _)] at hmono'
    exact hmono'
  have htarget_unit :
      cfc (fun y : ℝ =>
          positiveCayleyPullback f y - positiveCayleyPullback f 0) ua ≤
        cfc (fun y : ℝ =>
          positiveCayleyPullback f y - positiveCayleyPullback f 0) ub := by
    have heqa := conditionICompat_cfc_pullback_eq_cfc_halfline_add_const
      (h := f) (A := A) (a := a) ha.1 ha.2
    have heqb := conditionICompat_cfc_pullback_eq_cfc_halfline_add_const
      (h := f) (A := A) (a := b) hb.1 hb.2
    have hwith_const :
        cfc (fun y : ℝ =>
            positiveCayleyPullback f y - positiveCayleyPullback f 0) ua +
            algebraMap ℝ (Unitization ℂ A) (f 1 - f 0) ≤
          cfc (fun y : ℝ =>
            positiveCayleyPullback f y - positiveCayleyPullback f 0) ub +
            algebraMap ℝ (Unitization ℂ A) (f 1 - f 0) := by
      rw [heqa, heqb]
      simpa [pa, pb, ua, ub] using hmono
    exact (add_le_add_iff_right
      (algebraMap ℝ (Unitization ℂ A) (f 1 - f 0))).1 hwith_const
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

/--
Hiai-Petz condition (i) implies operator monotonicity on the positive ray via
the Cayley reduction to finite-dimensional unit-interval monotonicity
[carlen2022].
-/
theorem conditionI_to_operatorMonotoneOnPositive {f : ℝ → ℝ}
    (hI : ConditionI f) :
    OperatorMonotoneOnPositive.{u} f :=
  operatorMonotoneOnPositive_of_unitIntervalFiniteMatrixMonotone
    (unitIntervalMatrixMonotone_of_finiteMatrixMonotone
      (conditionI_to_unitIntervalFiniteMatrixMonotone hI))

/--
gcongr form of strict-positive CFC monotonicity from Hiai--Petz condition (i).
It delegates through `conditionI_to_operatorMonotoneOnPositive`.
-/
@[gcongr]
theorem cfc_sub_le_cfc_sub_of_le_of_conditionI
    {f : ℝ → ℝ} (hf : ConditionI f)
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    cfc (fun x : ℝ => f x - f 0) a ≤ cfc (fun x : ℝ => f x - f 0) b :=
  cfc_sub_le_cfc_sub_of_le_of_operatorMonotoneOnPositive
    (conditionI_to_operatorMonotoneOnPositive.{0} hf) hab ha hb

/--
gcongr form of normalized Cayley CFC monotonicity from Hiai--Petz condition (i).
It delegates through `conditionI_to_operatorMonotoneOnPositive`.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_conditionI
    {f : ℝ → ℝ} (hf : ConditionI f)
    {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback f x - positiveCayleyPullback f 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback f x - positiveCayleyPullback f 0) b :=
  cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_operatorMonotoneOnPositive
    (conditionI_to_operatorMonotoneOnPositive.{0} hf) hab ha hqa hb hqb

/-- Carlen's positive-ray operator monotonicity condition recovers the
Hiai--Petz finite-dimensional Condition I surface. -/
theorem carlenCondition1_to_conditionI {f : ℝ → ℝ}
    (h1 : OperatorMonotoneOnPositive.{u} f) :
    ConditionI f := by
  let h10 : OperatorMonotoneOnPositive.{0} f :=
    ⟨operatorMonotoneOnUnitInterval_toZero h1.to_unitInterval⟩
  intro n A B hA hB hAspec hBspec hAB
  haveI : NonnegSpectrumClass ℝ (HansenPedersen.Mₙ n) :=
    Matrix.instNonnegSpectrumClass
  have hAstrict : IsStrictlyPositive A := by
    exact
      (@CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
        (HansenPedersen.Mₙ n) _ _ _ _ _ _ _ this _ _ (a := A)).2
        ⟨hA, fun x hx => hAspec hx⟩
  have hBstrict : IsStrictlyPositive B := by
    exact
      (@CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
        (HansenPedersen.Mₙ n) _ _ _ _ _ _ _ this _ _ (a := B)).2
        ⟨hB, fun x hx => hBspec hx⟩
  have hmonoSub :
      cfc (fun x : ℝ => f x - f 0) A ≤
        cfc (fun x : ℝ => f x - f 0) B :=
    positiveCayley_cfc_transport_of_strictPositive
      (A := Matrix (Fin n) (Fin n) ℂ) h10 hAstrict hBstrict hAB
  have hfinA : (spectrum ℝ A).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex
      (B := Matrix (Fin n) (Fin n) ℂ) A
  have hfinB : (spectrum ℝ B).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex
      (B := Matrix (Fin n) (Fin n) ℂ) B
  have hAeq :
      cfc (fun x : ℝ => f x - f 0) A =
        cfc f A - algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (f 0) := by
    rw [cfc_sub (f := f) (g := fun _ : ℝ => f 0) (a := A)
      (hf := hfinA.continuousOn f) (hg := continuousOn_const)]
    rw [cfc_const (R := ℝ) (A := Matrix (Fin n) (Fin n) ℂ)
      (p := IsSelfAdjoint) (r := f 0) (a := A) (ha := hA)]
  have hBeq :
      cfc (fun x : ℝ => f x - f 0) B =
        cfc f B - algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (f 0) := by
    rw [cfc_sub (f := f) (g := fun _ : ℝ => f 0) (a := B)
      (hf := hfinB.continuousOn f) (hg := continuousOn_const)]
    rw [cfc_const (R := ℝ) (A := Matrix (Fin n) (Fin n) ℂ)
      (p := IsSelfAdjoint) (r := f 0) (a := B) (ha := hB)]
  have hmonoCfc : cfc f A ≤ cfc f B := by
    have hsub :
        cfc f A - algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (f 0) ≤
          cfc f B - algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (f 0) := by
      simpa [hAeq, hBeq] using hmonoSub
    have hadd :=
      add_le_add_right hsub (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (f 0))
    simpa [sub_eq_add_neg, add_assoc] using hadd
  have hAmat := conditionICompat_matrixCfcR_eq_cfc (f := f) (A := A) hA
  have hBmat := conditionICompat_matrixCfcR_eq_cfc (f := f) (A := B) hB
  simpa [hAmat, hBmat] using hmonoCfc

theorem conditionI_to_loewnerConditionI {f : ℝ → ℝ}
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ f x)
    (hI : ConditionI f) :
    LoewnerConditionI.{u} f := by
  exact closedPositive_extension_of_operatorMonotoneOnPositive_nonneg
    (conditionI_to_operatorMonotoneOnPositive hI)
    hpos

end

end Quantum.TraceInequality.Loewner.HiaiPetz
