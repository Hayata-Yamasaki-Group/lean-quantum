import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Quantum.TraceInequality.Loewner.HalfLine.Basic
import Quantum.QuantumEntropy.Common.RealComplexOrder

/-!
# Closed-positive CFC bridge on the half-line

This module contains the unitization infrastructure and endpoint-to-direct-CFC
bridge for the closed positive half-line.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

universe u

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-- The real scalar action on `ℂ` is continuous. -/
local instance instHalfLineRealComplexContinuousSMul :
    ContinuousSMul ℝ ℂ where
  continuous_smul := by
    change Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * p.2
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

private instance instHalfLineUnitizationRealStarModule {A : Type*}
    [NonUnitalCStarAlgebra A] :
    StarModule ℝ (Unitization ℂ A) where
  star_smul r x := by
    apply Unitization.ext
    · simp [Unitization.fst_smul, Unitization.fst_star]
    · simp [Unitization.snd_smul, Unitization.snd_star]

private instance instHalfLineUnitizationRealSelfTower {A : Type*}
    [NonUnitalCStarAlgebra A] :
    IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) where
  smul_assoc r x y := by
    change (r • x) * y = r • (x * y)
    apply Unitization.ext
    · simp only [Unitization.fst_smul, Unitization.fst_mul, Complex.real_smul]
      rw [mul_assoc]
    · simp only [Unitization.snd_smul, Unitization.snd_mul, Unitization.fst_smul,
        Complex.real_smul]
      rw [smul_add, smul_add]
      have h1 : ((r : ℂ) * x.fst) • y.snd = r • x.fst • y.snd := by
        change ((r : ℂ) * x.fst) • y.snd = (r : ℂ) • x.fst • y.snd
        rw [mul_smul]
      have h2 : y.fst • r • x.snd = r • y.fst • x.snd := by
        exact (smul_comm r y.fst x.snd).symm
      rw [h1, h2]
      rw [smul_mul_assoc]

private instance instHalfLineUnitizationRealSMulComm {A : Type*}
    [NonUnitalCStarAlgebra A] :
    SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) where
  smul_comm r x y := by
    rw [smul_eq_mul x y, smul_eq_mul x (r • y)]
    apply Unitization.ext
    · simp only [Unitization.fst_smul, Unitization.fst_mul, Complex.real_smul]
      ring_nf
    · simp only [Unitization.snd_smul, Unitization.snd_mul, Unitization.fst_smul,
        Complex.real_smul, smul_add]
      have h1 : r • x.fst • y.snd = x.fst • r • y.snd := by
        exact smul_comm r x.fst y.snd
      have h2 : r • y.fst • x.snd = ((r : ℂ) * y.fst) • x.snd := by
        change (r : ℂ) • y.fst • x.snd = ((r : ℂ) * y.fst) • x.snd
        rw [mul_smul]
      rw [h1, h2]
      rw [← mul_smul_comm r x.snd y.snd]

private noncomputable instance instHalfLineUnitizationRealNonnegSpectrumClass {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    NonnegSpectrumClass ℝ (Unitization ℂ A) := by
  exact @CStarAlgebra.instNonnegSpectrumClass (Unitization ℂ A) inferInstance
    Unitization.instPartialOrder Unitization.instStarOrderedRing

private theorem halfLine_unitization_real_smul_add {A : Type*} [NonUnitalCStarAlgebra A]
    (r : ℝ) (x y : Unitization ℂ A) : r • (x + y) = r • x + r • y := by
  apply Unitization.ext
  · simp only [Unitization.fst_smul, Unitization.fst_add, Complex.real_smul]
    rw [mul_add]
  · simp [Unitization.snd_smul, Unitization.snd_add, smul_add]

private theorem halfLine_unitization_real_add_smul {A : Type*} [NonUnitalCStarAlgebra A]
    (r s : ℝ) (x : Unitization ℂ A) : (r + s) • x = r • x + s • x := by
  apply Unitization.ext
  · simp only [Unitization.fst_smul, Complex.real_smul, Complex.ofReal_add,
      Unitization.fst_add]
    rw [add_mul]
  · simp [Unitization.snd_smul, Unitization.snd_add, add_smul]

private instance instHalfLineUnitizationRealOrderedModule {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    IsOrderedModule ℝ (Unitization ℂ A) where
  smul_le_smul_of_nonneg_left r hr a b hab := by
    haveI : StarModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealStarModule
    haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instHalfLineUnitizationRealSelfTower
    haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instHalfLineUnitizationRealSMulComm
    rw [StarOrderedRing.nonneg_iff] at hr
    rw [StarOrderedRing.le_iff] at hab ⊢
    obtain ⟨p, hp, rfl⟩ := hab
    have hmem : r • p ∈ AddSubmonoid.closure
        (Set.range fun s : Unitization ℂ A => star s * s) :=
      @smul_mem_closure_star_mul ℝ (Unitization ℂ A) inferInstance inferInstance
        inferInstance inferInstance inferInstance instHalfLineUnitizationRealStarModule
        instHalfLineUnitizationRealSelfTower instHalfLineUnitizationRealSMulComm
        (r := r) hr (a := p) hp
    exact ⟨r • p, hmem, halfLine_unitization_real_smul_add r a p⟩
  smul_le_smul_of_nonneg_right a ha r s hrs := by
    haveI : StarModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealStarModule
    haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instHalfLineUnitizationRealSelfTower
    haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instHalfLineUnitizationRealSMulComm
    rw [StarOrderedRing.nonneg_iff] at ha
    rw [StarOrderedRing.le_iff] at hrs ⊢
    obtain ⟨p, hp, rfl⟩ := hrs
    have hmem : p • a ∈ AddSubmonoid.closure
        (Set.range fun s : Unitization ℂ A => star s * s) :=
      @smul_mem_closure_star_mul ℝ (Unitization ℂ A) inferInstance inferInstance
        inferInstance inferInstance inferInstance instHalfLineUnitizationRealStarModule
        instHalfLineUnitizationRealSelfTower instHalfLineUnitizationRealSMulComm
        (r := p) hp (a := a) ha
    exact ⟨p • a, hmem, halfLine_unitization_real_add_smul r p a⟩

private instance instHalfLineUnitizationRealPosSMulMono {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    PosSMulMono ℝ (Unitization ℂ A) where
  smul_le_smul_of_nonneg_left r hr a b hab :=
    instHalfLineUnitizationRealOrderedModule.smul_le_smul_of_nonneg_left
      (a := r) hr (b₁ := a) (b₂ := b) hab

private instance instHalfLineUnitizationRealNormSMulClass {A : Type*}
    [NonUnitalCStarAlgebra A] :
    NormSMulClass ℝ (Unitization ℂ A) :=
  NormedSpace.toNormSMulClass

private instance instHalfLineUnitizationRealContinuousSMul {A : Type*}
    [NonUnitalCStarAlgebra A] :
    ContinuousSMul ℝ (Unitization ℂ A) :=
  IsScalarTower.continuousSMul ℂ

private instance instHalfLineUnitizationStarOrderedRing {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    StarOrderedRing (Unitization ℂ A) :=
  Unitization.instStarOrderedRing

private instance instHalfLineUnitizationOrderClosedTopology {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    OrderClosedTopology (Unitization ℂ A) := by
  exact @CStarAlgebra.instOrderClosedTopology (Unitization ℂ A) inferInstance
    Unitization.instPartialOrder Unitization.instStarOrderedRing

private theorem continuousAt_positiveToUnitCayley_of_pos {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt positiveToUnitCayley x := by
  have hx0 : 0 < x := by simpa using hx
  have hden : x + 1 ≠ 0 := by linarith
  unfold positiveToUnitCayley
  exact (continuousAt_id.sub continuousAt_const).div
    (continuousAt_id.add continuousAt_const) hden

private theorem operatorMonotoneOnPositive_pullback_continuousOn {h : ℝ → ℝ}
    (hh : OperatorMonotoneOnPositive.{u} h) :
    ContinuousOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) := by
  have hpos : LoewnerPosOnUnitInterval (positiveCayleyPullback h) :=
    loewnerPosOnUnitInterval_of_operatorMonotone
      (operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval)
  exact (publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval 1 hpos).continuousOn

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_01
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_01
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    ContinuousOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) := by
  apply @operatorMonotoneOnPositive_pullback_continuousOn
  all_goals assumption
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_01

private theorem operatorMonotoneOnPositive_continuousAt {h : ℝ → ℝ}
    (hh : OperatorMonotoneOnPositive.{u} h) {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt h x := by
  have hgCont := operatorMonotoneOnPositive_pullback_continuousOn hh
  have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hgAt :
      ContinuousAt (positiveCayleyPullback h) (positiveToUnitCayley x) :=
    hgCont.continuousAt (isOpen_Ioo.mem_nhds hy)
  have hcomp :
      ContinuousAt
        (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) x := by
    simpa [Function.comp_def] using
      hgAt.comp' (continuousAt_positiveToUnitCayley_of_pos hx)
  have heq :
      (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) =ᶠ[𝓝 x] h := by
    have hx0 : 0 < x := by simpa using hx
    filter_upwards [Ioi_mem_nhds hx0] with z hz
    simp [positiveCayleyPullback,
      unitToPositiveCayley_positiveToUnitCayley (by simpa using hz)]
  exact hcomp.congr heq

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_02
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_02
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt h x := by
  apply @operatorMonotoneOnPositive_continuousAt
  all_goals assumption
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_02

private theorem OperatorMonotoneOnClosedPositive.continuousWithinAt_zero {h : ℝ → ℝ}
    (hh : OperatorMonotoneOnClosedPositive.{u} h) :
    ContinuousWithinAt h (Set.Ici (0 : ℝ)) 0 :=
  (continuousWithinAt_Ioi_iff_Ici (a := (0 : ℝ)) (f := h)).1
    hh.right_continuous_at_zero

theorem _root_.LW2.Fixtures.DUni.chk_d_trans_02
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive.{u} h) :
    ContinuousWithinAt h (Set.Ici (0 : ℝ)) 0 := by
  apply @OperatorMonotoneOnClosedPositive.continuousWithinAt_zero
  all_goals assumption

/-- Closed-positive operator monotone functions are continuous on `[0,∞)`. -/
theorem operatorMonotoneOnClosedPositive_continuousOn_Ici {h : ℝ → ℝ}
    (hh : OperatorMonotoneOnClosedPositive h) :
    ContinuousOn h (Set.Ici (0 : ℝ)) := by
  intro x hx
  have hxnonneg : 0 ≤ x := by simpa using hx
  rcases eq_or_lt_of_le hxnonneg with rfl | hxpos
  · exact hh.continuousWithinAt_zero
  · exact
      (operatorMonotoneOnPositive_continuousAt hh.to_open
        (by simpa using hxpos)).continuousWithinAt

private theorem spectrum_strictPositive_subset_Ioi
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    spectrum ℝ a ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a).1 ha x hx

private theorem continuousOn_positiveToUnitCayley_of_subset_Ioi {s : Set ℝ}
    (hs : s ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn positiveToUnitCayley s := by
  intro x hx
  exact (continuousAt_positiveToUnitCayley_of_pos (hs hx)).continuousWithinAt

private theorem spectrum_cfc_positiveToUnitCayley_subset_Ioo
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    spectrum ℝ (cfc positiveToUnitCayley a : A) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  have hspos : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_strictPositive_subset_Ioi ha
  intro y hy
  rw [cfc_map_spectrum (R := ℝ) (a := a) (f := positiveToUnitCayley)
    (hf := continuousOn_positiveToUnitCayley_of_subset_Ioi hspos)] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact positiveToUnitCayley_mem_Ioo (hspos hx)

private theorem quasispectrum_cfc_positiveToUnitCayley_subset_Ioo
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    quasispectrum ℝ (cfc positiveToUnitCayley a : A) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro y hy
  rw [quasispectrum_eq_spectrum_union_zero] at hy
  rcases hy with hy | rfl
  · exact spectrum_cfc_positiveToUnitCayley_subset_Ioo ha hy
  · norm_num

private def positiveCayleyAux (x : ℝ) : ℝ :=
  1 - (1 + x)⁻¹

private theorem continuousOn_positiveCayleyAux_of_quasispectrum_nonneg
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) :
    ContinuousOn positiveCayleyAux (quasispectrum ℝ a) := by
  intro x hx
  have hx0 : 0 ≤ x := quasispectrum_nonneg_of_nonneg a ha x hx
  have hden : 1 + x ≠ 0 := by linarith
  unfold positiveCayleyAux
  exact (continuousAt_const.sub
    ((continuousAt_const.add continuousAt_id).inv₀ hden)).continuousWithinAt

private theorem continuousOn_positiveCayleyAux_of_spectrum_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) :
    ContinuousOn positiveCayleyAux (spectrum ℝ a) :=
  (continuousOn_positiveCayleyAux_of_quasispectrum_nonneg (A := A) ha).mono
    (spectrum_subset_quasispectrum ℝ a)

/-- Nonunital CFC monotonicity for the Cayley auxiliary function, isolated from the
unital bridge so the Unitization normalization elaborates in its own declaration. -/
private theorem cfcₙ_positiveCayleyAux_mono_of_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    cfcₙ positiveCayleyAux a ≤ cfcₙ positiveCayleyAux b := by
  simpa [positiveCayleyAux] using
    CFC.monotoneOn_one_sub_one_add_inv_real ha hb hab

/-- One-sided nonunital-to-unital CFC bridge for `positiveCayleyAux`, kept separate
from monotonicity so each Unitization normalization is paid for once. -/
private theorem cfcₙ_positiveCayleyAux_eq_cfc_of_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) :
    cfcₙ positiveCayleyAux a = cfc positiveCayleyAux a := by
  exact
    cfcₙ_eq_cfc (R := ℝ) (A := A) (p := IsSelfAdjoint)
      (f := positiveCayleyAux) (a := a)
      (hf := continuousOn_positiveCayleyAux_of_quasispectrum_nonneg ha)
      (hf0 := by norm_num [positiveCayleyAux])

private theorem cfc_positiveCayleyAux_mono_of_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    cfc positiveCayleyAux a ≤ cfc positiveCayleyAux b := by
  have hauxₙ : cfcₙ positiveCayleyAux a ≤ cfcₙ positiveCayleyAux b :=
    cfcₙ_positiveCayleyAux_mono_of_nonneg ha hb hab
  rw [cfcₙ_positiveCayleyAux_eq_cfc_of_nonneg ha,
    cfcₙ_positiveCayleyAux_eq_cfc_of_nonneg hb] at hauxₙ
  exact hauxₙ

private theorem cfc_positiveToUnitCayley_eq_aux
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    cfc positiveToUnitCayley a = (2 : ℝ) • cfc positiveCayleyAux a - 1 := by
  have hspos : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_strictPositive_subset_Ioi ha
  have hauxCont : ContinuousOn positiveCayleyAux (spectrum ℝ a) :=
    continuousOn_positiveCayleyAux_of_spectrum_nonneg ha.nonneg
  calc
    cfc positiveToUnitCayley a =
        cfc (fun x : ℝ => 2 * positiveCayleyAux x - 1) a := by
          apply cfc_congr
          intro x hx
          have hxpos : 0 < x := hspos hx
          have hden : x + 1 ≠ 0 := by linarith
          unfold positiveToUnitCayley positiveCayleyAux
          field_simp [hden]
          ring_nf
    _ = (2 : ℝ) • cfc positiveCayleyAux a - 1 := by
          rw [cfc_sub
            (f := fun x : ℝ => 2 * positiveCayleyAux x)
            (g := fun _ : ℝ => 1)
            (hf := continuousOn_const.mul hauxCont) (hg := continuousOn_const)]
          rw [cfc_const_mul (r := (2 : ℝ)) (f := positiveCayleyAux) (a := a)
            (hf := hauxCont)]
          rw [cfc_const (r := (1 : ℝ)) (a := a) (ha := ha.isSelfAdjoint)]
          simp

private theorem cfc_positiveToUnitCayley_mono_of_strictPositive
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : a ≤ b) :
    cfc positiveToUnitCayley a ≤ cfc positiveToUnitCayley b := by
  rw [cfc_positiveToUnitCayley_eq_aux ha, cfc_positiveToUnitCayley_eq_aux hb]
  exact sub_le_sub_right
    (smul_le_smul_of_nonneg_left
      (cfc_positiveCayleyAux_mono_of_nonneg ha.nonneg hb.nonneg hab)
      (by norm_num : (0 : ℝ) ≤ 2))
    1

private theorem cfc_positiveCayleyPullback_sub_zero_eq
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    cfc (fun x : ℝ => h x - h 0) a =
      cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0)
          (cfc positiveToUnitCayley a : A) +
        algebraMap ℝ A (h 1 - h 0) := by
  let g : ℝ → ℝ := positiveCayleyPullback h
  have hspos : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_strictPositive_subset_Ioi ha
  have hphiCont : ContinuousOn positiveToUnitCayley (spectrum ℝ a) :=
    continuousOn_positiveToUnitCayley_of_subset_Ioi hspos
  have hgCont := operatorMonotoneOnPositive_pullback_continuousOn hh
  have hcompCont :
      ContinuousOn (fun x : ℝ => g (positiveToUnitCayley x) - g 0)
        (spectrum ℝ a) := by
    intro x hx
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := hspos hx
    have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
      positiveToUnitCayley_mem_Ioo hxpos
    have hgy :
        ContinuousAt g (positiveToUnitCayley x) := by
      simpa [g] using hgCont.continuousAt (isOpen_Ioo.mem_nhds hy)
    exact ((hgy.comp' (continuousAt_positiveToUnitCayley_of_pos hxpos)).sub
      continuousAt_const).continuousWithinAt
  have hgImageCont :
      ContinuousOn (fun y : ℝ => g y - g 0)
        (positiveToUnitCayley '' spectrum ℝ a) := by
    rintro y ⟨x, hx, rfl⟩
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := hspos hx
    have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
      positiveToUnitCayley_mem_Ioo hxpos
    have hgy :
        ContinuousAt g (positiveToUnitCayley x) := by
      simpa [g] using hgCont.continuousAt (isOpen_Ioo.mem_nhds hy)
    exact (hgy.sub continuousAt_const).continuousWithinAt
  calc
    cfc (fun x : ℝ => h x - h 0) a =
        cfc (fun x : ℝ =>
          (g (positiveToUnitCayley x) - g 0) + (h 1 - h 0)) a := by
          apply cfc_congr
          intro x hx
          have hxpos : x ∈ Set.Ioi (0 : ℝ) := hspos hx
          simp [g, positiveCayleyPullback,
            unitToPositiveCayley_positiveToUnitCayley hxpos]
    _ =
        cfc (fun x : ℝ => g (positiveToUnitCayley x) - g 0) a +
          algebraMap ℝ A (h 1 - h 0) := by
          rw [cfc_add_const (r := h 1 - h 0)
            (f := fun x : ℝ => g (positiveToUnitCayley x) - g 0)
            (a := a) (hf := hcompCont) (ha := ha.isSelfAdjoint)]
    _ =
        cfc (fun y : ℝ => g y - g 0) (cfc positiveToUnitCayley a : A) +
          algebraMap ℝ A (h 1 - h 0) := by
          rw [cfc_comp' (fun y : ℝ => g y - g 0) positiveToUnitCayley a
            (hg := hgImageCont) (hf := hphiCont) (ha := ha.isSelfAdjoint)]
    _ =
        cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0)
            (cfc positiveToUnitCayley a : A) +
          algebraMap ℝ A (h 1 - h 0) := by
          rfl

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_03
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_03
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : IsStrictlyPositive a) :
    cfc (fun x : ℝ => h x - h 0) a =
      cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0)
          (cfc positiveToUnitCayley a : A) +
        algebraMap ℝ A (h 1 - h 0) := by
  apply @cfc_positiveCayleyPullback_sub_zero_eq
  all_goals assumption
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_03

/--
Positive-ray operator monotonicity gives direct CFC monotonicity on strictly
positive elements after undoing the Cayley transform.
-/
theorem positiveCayley_cfc_transport_of_strictPositive
    {h : ℝ → ℝ} {A : Type u} (hh : OperatorMonotoneOnPositive.{u} h)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : a ≤ b) :
    cfc (fun x : ℝ => h x - h 0) a ≤
      cfc (fun x : ℝ => h x - h 0) b := by
  let g : ℝ → ℝ := positiveCayleyPullback h
  let ya : A := cfc positiveToUnitCayley a
  let yb : A := cfc positiveToUnitCayley b
  have hya_mem :
      ya ∈ {y : A | IsSelfAdjoint y ∧ quasispectrum ℝ y ⊆ Set.Ioo (-1 : ℝ) 1} := by
    refine ⟨by cfc_tac, ?_⟩
    simpa [ya] using quasispectrum_cfc_positiveToUnitCayley_subset_Ioo ha
  have hyb_mem :
      yb ∈ {y : A | IsSelfAdjoint y ∧ quasispectrum ℝ y ⊆ Set.Ioo (-1 : ℝ) 1} := by
    refine ⟨by cfc_tac, ?_⟩
    simpa [yb] using quasispectrum_cfc_positiveToUnitCayley_subset_Ioo hb
  have hy_le : ya ≤ yb := by
    simpa [ya, yb] using cfc_positiveToUnitCayley_mono_of_strictPositive ha hb hab
  have hmono :=
    (hh.to_unitInterval.cfc_monotone (A := A)) hya_mem hyb_mem hy_le
  have hmono_cfc :
      cfc (fun y : ℝ => g y - g 0) ya ≤
        cfc (fun y : ℝ => g y - g 0) yb := by
    have hgCont := operatorMonotoneOnPositive_pullback_continuousOn hh
    have hcont_a :
        ContinuousOn (fun y : ℝ => g y - g 0) (quasispectrum ℝ ya) := by
      intro y hy
      have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := hya_mem.2 hy
      have hgy :
          ContinuousAt g y := by
        simpa [g] using hgCont.continuousAt (isOpen_Ioo.mem_nhds hyI)
      exact (hgy.sub continuousAt_const).continuousWithinAt
    have hcont_b :
        ContinuousOn (fun y : ℝ => g y - g 0) (quasispectrum ℝ yb) := by
      intro y hy
      have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := hyb_mem.2 hy
      have hgy :
          ContinuousAt g y := by
        simpa [g] using hgCont.continuousAt (isOpen_Ioo.mem_nhds hyI)
      exact (hgy.sub continuousAt_const).continuousWithinAt
    have hmono' :
        cfcₙ (fun y : ℝ => g y - g 0) ya ≤
          cfcₙ (fun y : ℝ => g y - g 0) yb := by
      simpa [g] using hmono
    rw [cfcₙ_eq_cfc (hf := hcont_a), cfcₙ_eq_cfc (hf := hcont_b)] at hmono'
    exact hmono'
  have haeq := cfc_positiveCayleyPullback_sub_zero_eq (h := h) hh ha
  have hbeq := cfc_positiveCayleyPullback_sub_zero_eq (h := h) hh hb
  rw [haeq, hbeq]
  simpa [g, ya, yb, add_comm] using
    add_le_add_right hmono_cfc (algebraMap ℝ A (h 1 - h 0))

/--
gcongr form of the strict-positive CFC transport for positive-ray monotone functions.
It delegates to `positiveCayley_cfc_transport_of_strictPositive`.
-/
@[gcongr]
theorem cfc_sub_le_cfc_sub_of_le_of_operatorMonotoneOnPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    cfc (fun x : ℝ => h x - h 0) a ≤ cfc (fun x : ℝ => h x - h 0) b :=
  positiveCayley_cfc_transport_of_strictPositive hh ha hb hab

/--
gcongr form of strict-positive CFC transport from the closed-positive predicate.
It delegates through `OperatorMonotoneOnClosedPositive.to_open`.
-/
@[gcongr]
theorem cfc_sub_le_cfc_sub_of_le_of_operatorMonotoneOnClosedPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive.{u} h)
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    cfc (fun x : ℝ => h x - h 0) a ≤ cfc (fun x : ℝ => h x - h 0) b :=
  positiveCayley_cfc_transport_of_strictPositive hh.to_open ha hb hab

private def unitizationPushup
    {A : Type*} [NonUnitalCStarAlgebra A] (a : A) (ε : ℝ) :
    Unitization ℂ A :=
  (a : Unitization ℂ A) + ε • (1 : Unitization ℂ A)

private theorem unitizationPushup_tendsto
    {A : Type*} [NonUnitalCStarAlgebra A] (a : A) :
    Tendsto (fun ε : ℝ => unitizationPushup a ε) (𝓝[>] (0 : ℝ))
      (𝓝 (a : Unitization ℂ A)) := by
  have hconst :
      Tendsto (fun _ : ℝ => (a : Unitization ℂ A)) (𝓝[>] (0 : ℝ))
        (𝓝 (a : Unitization ℂ A)) :=
    tendsto_const_nhds
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hsmul :
      Tendsto (fun ε : ℝ => ε • (1 : Unitization ℂ A)) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) • (1 : Unitization ℂ A))) :=
    hid.smul tendsto_const_nhds
  have hadd := hconst.add hsmul
  have hzero : (0 : ℝ) • (1 : Unitization ℂ A) = 0 :=
    zero_smul ℝ (1 : Unitization ℂ A)
  rw [hzero, add_zero] at hadd
  simpa [unitizationPushup] using hadd

private theorem unitizationPushup_nonneg
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ unitizationPushup a ε := by
  haveI : StarModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealStarModule
  haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSelfTower
  haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSMulComm
  haveI : IsOrderedModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealOrderedModule
  haveI : PosSMulMono ℝ (Unitization ℂ A) := instHalfLineUnitizationRealPosSMulMono
  have hpos : PosSMulMono ℝ (Unitization ℂ A) := instHalfLineUnitizationRealPosSMulMono
  have hε_one : 0 ≤ ε • (1 : Unitization ℂ A) :=
    @smul_nonneg ℝ (Unitization ℂ A) ε (1 : Unitization ℂ A)
      inferInstance inferInstance inferInstance inferInstance inferInstance hpos hε
      (zero_le_one : (0 : Unitization ℂ A) ≤ 1)
  unfold unitizationPushup
  exact add_nonneg (Unitization.inr_nonneg_iff.mpr ha) hε_one

private theorem unitizationInr_spectrum_subset_Icc
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) :
    spectrum ℝ (a : Unitization ℂ A) ⊆
      Set.Icc (0 : ℝ) (‖(a : Unitization ℂ A)‖ + 1) := by
  intro x hx
  have hnonneg : 0 ≤ (a : Unitization ℂ A) :=
    Unitization.inr_nonneg_iff.mpr ha
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hnonneg hx
  constructor
  · exact hx0
  · calc
      x = ‖x‖ := (Real.norm_of_nonneg hx0).symm
      _ ≤ ‖(a : Unitization ℂ A)‖ := spectrum.norm_le_norm_of_mem hx
      _ ≤ ‖(a : Unitization ℂ A)‖ + 1 := by linarith

private theorem unitizationPushup_spectrum_subset_Icc
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    spectrum ℝ (unitizationPushup a ε) ⊆
      Set.Icc (0 : ℝ) (‖(a : Unitization ℂ A)‖ + 1) := by
  intro x hx
  have hpush_nonneg : 0 ≤ unitizationPushup a ε :=
    unitizationPushup_nonneg ha hε.1.le
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hpush_nonneg hx
  have hsmul_norm : ‖ε • (1 : Unitization ℂ A)‖ ≤ (1 : ℝ) := by
    rw [norm_smul, norm_one, mul_one, Real.norm_of_nonneg hε.1.le]
    exact hε.2
  constructor
  · exact hx0
  · calc
      x = ‖x‖ := (Real.norm_of_nonneg hx0).symm
      _ ≤ ‖unitizationPushup a ε‖ := spectrum.norm_le_norm_of_mem hx
      _ ≤ ‖(a : Unitization ℂ A)‖ + ‖ε • (1 : Unitization ℂ A)‖ := by
        simpa [unitizationPushup] using
          norm_add_le (a : Unitization ℂ A) (ε • (1 : Unitization ℂ A))
      _ ≤ ‖(a : Unitization ℂ A)‖ + 1 := by
        exact add_le_add_right hsmul_norm _

private theorem closedPositive_cfc_pushup_tendsto
    {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici (0 : ℝ)))
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) :
    Tendsto
      (fun ε : ℝ =>
        cfc (fun x : ℝ => h x - h 0) (unitizationPushup a ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (cfc (fun x : ℝ => h x - h 0) (a : Unitization ℂ A))) := by
  let M : ℝ := ‖(a : Unitization ℂ A)‖ + 1
  have hfcont :
      ContinuousOn (fun x : ℝ => h x - h 0) (Set.Icc (0 : ℝ) M) := by
    exact (hcont.mono (by intro x hx; exact hx.1)).sub continuousOn_const
  have hspec_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (unitizationPushup a ε) ⊆ Set.Icc (0 : ℝ) M := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    simpa [M] using unitizationPushup_spectrum_subset_Icc (A := A) ha hε
  have hpred_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsSelfAdjoint (unitizationPushup a ε) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    exact @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance
      Unitization.instPartialOrder inferInstance Unitization.instStarOrderedRing
      (unitizationPushup a ε) (unitizationPushup_nonneg (A := A) ha hε.1.le)
  exact (unitizationPushup_tendsto (A := A) a).cfc
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M))
    (fun x : ℝ => h x - h 0)
    hspec_eventually hpred_eventually
    (by simpa [M] using unitizationInr_spectrum_subset_Icc (A := A) ha)
    (by
      exact @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance
        Unitization.instPartialOrder inferInstance Unitization.instStarOrderedRing
        (a : Unitization ℂ A) (Unitization.inr_nonneg_iff.mpr ha))
    hfcont

/--
If every positive epsilon pushup is ordered in the unitization, then the
closed-positive non-unital CFC values are ordered.
-/
theorem closedPositiveCFC_le_of_epsilon_pushup
    {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici (0 : ℝ)))
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpush :
      ∀ ⦃ε : ℝ⦄, 0 < ε →
        cfc (fun x : ℝ => h x - h 0)
            ((a : Unitization ℂ A) + ε • (1 : Unitization ℂ A))
          ≤
        cfc (fun x : ℝ => h x - h 0)
            ((b : Unitization ℂ A) + ε • (1 : Unitization ℂ A))) :
    cfcₙ (fun x : ℝ => h x - h 0) a ≤
      cfcₙ (fun x : ℝ => h x - h 0) b := by
  have hle_unit :
      cfc (fun x : ℝ => h x - h 0) (a : Unitization ℂ A) ≤
        cfc (fun x : ℝ => h x - h 0) (b : Unitization ℂ A) := by
    apply le_of_tendsto_of_tendsto
      (closedPositive_cfc_pushup_tendsto (A := A) hcont ha)
      (closedPositive_cfc_pushup_tendsto (A := A) hcont hb)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [unitizationPushup] using hpush (by simpa using hε)
  rw [← Unitization.inr_le_iff
    (cfcₙ (fun x : ℝ => h x - h 0) a)
    (cfcₙ (fun x : ℝ => h x - h 0) b)
    (cfcₙ_predicate (fun x : ℝ => h x - h 0) a)
    (cfcₙ_predicate (fun x : ℝ => h x - h 0) b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a (fun x : ℝ => h x - h 0) (by simp),
    Unitization.real_cfcₙ_eq_cfc_inr b (fun x : ℝ => h x - h 0) (by simp)]
  exact hle_unit

private theorem unitizationPushup_strictPositive
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive ((a : Unitization ℂ A) + ε • (1 : Unitization ℂ A)) := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  haveI : StarModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealStarModule
  haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSelfTower
  haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSMulComm
  haveI : IsOrderedModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealOrderedModule
  haveI : PosSMulMono ℝ (Unitization ℂ A) := instHalfLineUnitizationRealPosSMulMono
  have hpos : PosSMulMono ℝ (Unitization ℂ A) := instHalfLineUnitizationRealPosSMulMono
  have ha_unit : 0 ≤ (a : Unitization ℂ A) :=
    Unitization.inr_nonneg_iff.mpr ha
  have hε_unit :
      IsStrictlyPositive (ε • (1 : Unitization ℂ A)) := by
    exact @IsStrictlyPositive.smul (Unitization ℂ A) ℝ
      inferInstance Unitization.instPartialOrder inferInstance inferInstance inferInstance hpos
      ε hε (1 : Unitization ℂ A) isStrictlyPositive_one
  exact @IsStrictlyPositive.nonneg_add (Unitization ℂ A)
    inferInstance Unitization.instPartialOrder Unitization.instStarOrderedRing
    _ _ ha_unit hε_unit

/--
Endpoint-continuous closed-positive monotonicity implies the direct
closed-positive CFC monotonicity predicate.
-/
theorem operatorMonotoneOnClosedPositiveCFC_of_endpoint
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive.{u} h) :
    OperatorMonotoneOnClosedPositiveCFC.{u} h := by
  refine ⟨?_⟩
  intro A _ _ _ a ha b hb hab
  refine closedPositiveCFC_le_of_epsilon_pushup
    (A := A) (operatorMonotoneOnClosedPositive_continuousOn_Ici hh)
    ha hb ?_
  intro ε hε
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  haveI : StarModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealStarModule
  haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSelfTower
  haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instHalfLineUnitizationRealSMulComm
  haveI : IsOrderedModule ℝ (Unitization ℂ A) := instHalfLineUnitizationRealOrderedModule
  haveI : PosSMulMono ℝ (Unitization ℂ A) := instHalfLineUnitizationRealPosSMulMono
  have haε :
      IsStrictlyPositive
        ((a : Unitization ℂ A) + ε • (1 : Unitization ℂ A)) :=
    unitizationPushup_strictPositive (A := A) ha hε
  have hbε :
      IsStrictlyPositive
        ((b : Unitization ℂ A) + ε • (1 : Unitization ℂ A)) :=
    unitizationPushup_strictPositive (A := A) hb hε
  have hab_unit : (a : Unitization ℂ A) ≤ (b : Unitization ℂ A) := by
    exact (Unitization.inr_le_iff a b
      (IsSelfAdjoint.of_nonneg ha) (IsSelfAdjoint.of_nonneg hb)).mpr hab
  have habε :
      (a : Unitization ℂ A) + ε • (1 : Unitization ℂ A) ≤
        (b : Unitization ℂ A) + ε • (1 : Unitization ℂ A) :=
    by
      simpa [add_comm] using
        add_le_add_right hab_unit (ε • (1 : Unitization ℂ A))
  exact @positiveCayley_cfc_transport_of_strictPositive h (Unitization ℂ A)
    hh.to_open inferInstance Unitization.instPartialOrder Unitization.instStarOrderedRing
    _ _ haε hbε habε

end

end Loewner
end TraceInequality
end Quantum
