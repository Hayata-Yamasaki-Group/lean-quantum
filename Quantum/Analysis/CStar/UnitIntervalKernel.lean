import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Quantum.QuantumEntropy.Common.RealComplexOrder

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open MeasureTheory

private instance instUnitizationRealStarModule {A : Type*} [NonUnitalCStarAlgebra A] :
    StarModule ℝ (Unitization ℂ A) where
  star_smul r x := by
    apply Unitization.ext
    · simp [Unitization.fst_smul, Unitization.fst_star]
    · simp [Unitization.snd_smul, Unitization.snd_star]

private instance instUnitizationRealSelfTower {A : Type*} [NonUnitalCStarAlgebra A] :
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

private instance instUnitizationRealSMulComm {A : Type*} [NonUnitalCStarAlgebra A] :
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

private noncomputable instance instUnitizationRealNonnegSpectrumClass {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    NonnegSpectrumClass ℝ (Unitization ℂ A) := by
  exact @CStarAlgebra.instNonnegSpectrumClass (Unitization ℂ A) inferInstance
    Unitization.instPartialOrder Unitization.instStarOrderedRing

private theorem unitization_real_smul_add {A : Type*} [NonUnitalCStarAlgebra A]
    (r : ℝ) (x y : Unitization ℂ A) : r • (x + y) = r • x + r • y := by
  apply Unitization.ext
  · simp only [Unitization.fst_smul, Unitization.fst_add, Complex.real_smul]
    rw [mul_add]
  · simp [Unitization.snd_smul, Unitization.snd_add, smul_add]

private theorem unitization_real_add_smul {A : Type*} [NonUnitalCStarAlgebra A]
    (r s : ℝ) (x : Unitization ℂ A) : (r + s) • x = r • x + s • x := by
  apply Unitization.ext
  · simp only [Unitization.fst_smul, Complex.real_smul, Complex.ofReal_add,
      Unitization.fst_add]
    rw [add_mul]
  · simp [Unitization.snd_smul, Unitization.snd_add, add_smul]

private instance instUnitizationRealOrderedModule {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    IsOrderedModule ℝ (Unitization ℂ A) where
  smul_le_smul_of_nonneg_left r hr a b hab := by
    haveI : StarModule ℝ (Unitization ℂ A) := instUnitizationRealStarModule
    haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instUnitizationRealSelfTower
    haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instUnitizationRealSMulComm
    rw [StarOrderedRing.nonneg_iff] at hr
    rw [StarOrderedRing.le_iff] at hab ⊢
    obtain ⟨p, hp, rfl⟩ := hab
    have hmem : r • p ∈ AddSubmonoid.closure
        (Set.range fun s : Unitization ℂ A => star s * s) :=
      @smul_mem_closure_star_mul ℝ (Unitization ℂ A) inferInstance inferInstance
        inferInstance inferInstance inferInstance instUnitizationRealStarModule
        instUnitizationRealSelfTower instUnitizationRealSMulComm
        (r := r) hr (a := p) hp
    exact ⟨r • p, hmem, unitization_real_smul_add r a p⟩
  smul_le_smul_of_nonneg_right a ha r s hrs := by
    haveI : StarModule ℝ (Unitization ℂ A) := instUnitizationRealStarModule
    haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instUnitizationRealSelfTower
    haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
      instUnitizationRealSMulComm
    rw [StarOrderedRing.nonneg_iff] at ha
    rw [StarOrderedRing.le_iff] at hrs ⊢
    obtain ⟨p, hp, rfl⟩ := hrs
    have hmem : p • a ∈ AddSubmonoid.closure
        (Set.range fun s : Unitization ℂ A => star s * s) :=
      @smul_mem_closure_star_mul ℝ (Unitization ℂ A) inferInstance inferInstance
        inferInstance inferInstance inferInstance instUnitizationRealStarModule
        instUnitizationRealSelfTower instUnitizationRealSMulComm
        (r := p) hp (a := a) ha
    exact ⟨p • a, hmem, unitization_real_add_smul r p a⟩

/-- The normalized interval kernel used in the book integral representation. -/
def unitIntervalOperatorKernel (lambda x : ℝ) : ℝ :=
  x / (1 + lambda * x)

/-- The interval kernel vanishes at the origin. -/
@[simp]
theorem unitIntervalOperatorKernel_zero (lambda : ℝ) :
    unitIntervalOperatorKernel lambda 0 = 0 := by
  simp [unitIntervalOperatorKernel]

/-- The interval kernel maps the origin to the origin, as required by `cfcₙ`. -/
theorem unitIntervalOperatorKernel_map_zero (lambda : ℝ) :
    (fun x : ℝ => unitIntervalOperatorKernel lambda x) 0 = 0 :=
  unitIntervalOperatorKernel_zero lambda

/-- Complex coercion rewrites the real interval kernel as the same fractional expression. -/
@[simp]
theorem unitIntervalOperatorKernel_complex_eq (lambda x : ℝ) :
    ((unitIntervalOperatorKernel lambda x : ℝ) : ℂ) =
      (x : ℂ) / (1 + (lambda : ℂ) * x) := by
  simp [unitIntervalOperatorKernel]

/-- The denominator in the interval kernel is positive on the book domain. -/
theorem unitIntervalOperatorKernel_denominator_pos {lambda x : ℝ}
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < 1 + lambda * x := by
  have hlambda_abs : |lambda| ≤ 1 := abs_le.mpr hlambda
  have hx_abs : |x| < 1 := by
    rw [abs_lt]
    exact hx
  have hmul_abs : |lambda * x| < 1 := by
    rw [abs_mul]
    calc
      |lambda| * |x| ≤ 1 * |x| := by
        exact mul_le_mul_of_nonneg_right hlambda_abs (abs_nonneg x)
      _ < 1 := by simpa using hx_abs
  have hneg : -1 < lambda * x := (abs_lt.mp hmul_abs).1
  linarith

/-- Joint continuity of the interval kernel on parameters and quasispectrum. -/
theorem unitIntervalOperatorKernel_joint_continuousOn_Icc_quasispectrum
    {A : Type*} [NonUnitalCStarAlgebra A] {a : A}
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn (Function.uncurry unitIntervalOperatorKernel)
      (Set.Icc (-1 : ℝ) 1 ×ˢ quasispectrum ℝ a) := by
  intro p hp
  rcases hp with ⟨hlambda, hz⟩
  have hden : 1 + p.1 * p.2 ≠ 0 :=
    (unitIntervalOperatorKernel_denominator_pos hlambda (hspec hz)).ne'
  change ContinuousWithinAt
    (fun p : ℝ × ℝ => p.2 / (1 + p.1 * p.2))
    (Set.Icc (-1 : ℝ) 1 ×ˢ quasispectrum ℝ a) p
  have hden_cont : ContinuousAt (fun p : ℝ × ℝ => 1 + p.1 * p.2) p :=
    continuous_const.continuousAt.add
      (continuous_fst.continuousAt.mul continuous_snd.continuousAt)
  exact (continuous_snd.continuousAt.div hden_cont hden).continuousWithinAt

/-- Continuity of the interval kernel on the book domain. -/
theorem unitIntervalOperatorKernel_continuousOn_Ioo {lambda : ℝ}
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1) :
    ContinuousOn (unitIntervalOperatorKernel lambda) (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  have hden : 1 + lambda * x ≠ 0 :=
    (unitIntervalOperatorKernel_denominator_pos hlambda hx).ne'
  change ContinuousWithinAt (fun x : ℝ => x / (1 + lambda * x)) (Set.Ioo (-1 : ℝ) 1) x
  exact continuousAt_id.div
    ((continuousAt_const.add (continuousAt_const.mul continuousAt_id))) hden |>.continuousWithinAt

/-- Fractional-linear rewrite for positive `lambda`. -/
theorem unitIntervalOperatorKernel_fractional_linear_pos {lambda x : ℝ}
    (hlambda : 0 < lambda) (hden : 1 + lambda * x ≠ 0) :
    unitIntervalOperatorKernel lambda x =
      lambda⁻¹ * (1 - (1 + lambda * x)⁻¹) := by
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hden' : 1 + x * lambda ≠ 0 := by
    simpa [mul_comm] using hden
  rw [unitIntervalOperatorKernel]
  field_simp [hlambda_ne, hden, hden']
  ring_nf

/-- Fractional-linear rewrite for negative `lambda`. -/
theorem unitIntervalOperatorKernel_fractional_linear_neg {lambda x : ℝ}
    (hlambda : lambda < 0) (hden : 1 + lambda * x ≠ 0) :
    unitIntervalOperatorKernel lambda x =
      (-lambda)⁻¹ * ((1 + lambda * x)⁻¹ - 1) := by
  have hlambda_ne : lambda ≠ 0 := ne_of_lt hlambda
  have hneg_ne : -lambda ≠ 0 := neg_ne_zero.mpr hlambda_ne
  have hden' : 1 + x * lambda ≠ 0 := by
    simpa [mul_comm] using hden
  rw [unitIntervalOperatorKernel]
  field_simp [hlambda_ne, hneg_ne, hden, hden']
  ring_nf

/-- The unitized denominator `1 + λa` is strictly positive for interval-spectrum `a`. -/
theorem unitIntervalOperatorKernel_denominator_strictlyPositive
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a : A} (ha : IsSelfAdjoint a)
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    IsStrictlyPositive (1 + lambda • (a : Unitization ℂ A)) := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  let ua : Unitization ℂ A := a
  have hua : IsSelfAdjoint ua := IsSelfAdjoint.inr (R := ℂ) ha
  have hspec_ua : spectrum ℝ ua ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact hspec (by rwa [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a])
  have hpos : IsStrictlyPositive (cfc (fun x : ℝ => 1 + lambda * x) ua) := by
    have hiff := @cfc_isStrictlyPositive_iff ℝ (Unitization ℂ A) IsSelfAdjoint
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      Unitization.instPartialOrder Unitization.instStarOrderedRing inferInstance inferInstance
      instUnitizationRealNonnegSpectrumClass
      (fun x : ℝ => 1 + lambda * x) ua (by fun_prop) hua
    rw [hiff]
    intro x hx
    exact unitIntervalOperatorKernel_denominator_pos hlambda (hspec_ua hx)
  have hcalc : cfc (fun x : ℝ => 1 + lambda * x) ua = 1 + lambda • ua := by
    rw [cfc_add (f := fun _ : ℝ => 1) (g := fun x : ℝ => lambda * x) (a := ua)
      (hf := by fun_prop) (hg := by fun_prop), cfc_const_one ℝ ua]
    rw [cfc_const_mul_id (R := ℝ) lambda ua]
    rfl
  rwa [hcalc] at hpos

private theorem unitIntervalOperatorKernel_denominator_ne_on_unitization_spectrum
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a : A} (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    ∀ x ∈ spectrum ℝ (a : Unitization ℂ A), 1 + lambda * x ≠ 0 := by
  intro x hx
  have hxq : x ∈ quasispectrum ℝ a := by
    rwa [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a]
  exact (unitIntervalOperatorKernel_denominator_pos hlambda (hspec hxq)).ne'

/-- Unitized CFC form of the positive-parameter fractional-linear identity. -/
theorem unitIntervalOperatorKernel_cfc_unitization_fractional_linear_pos
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda_pos : 0 < lambda)
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a : A} (ha : IsSelfAdjoint a)
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfc (unitIntervalOperatorKernel lambda) (a : Unitization ℂ A) =
      lambda⁻¹ • (1 - Ring.inverse (1 + lambda • (a : Unitization ℂ A))) := by
  let ua : Unitization ℂ A := a
  have hua : IsSelfAdjoint ua := IsSelfAdjoint.inr (R := ℂ) ha
  have hden_ne : ∀ x ∈ spectrum ℝ ua, 1 + lambda * x ≠ 0 := by
    intro x hx
    exact unitIntervalOperatorKernel_denominator_ne_on_unitization_spectrum
      hlambda hspec x (by simpa [ua] using hx)
  have hginv_cont : ContinuousOn (fun x : ℝ => (1 + lambda * x)⁻¹) (spectrum ℝ ua) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀ hden_ne
  have hfun : (spectrum ℝ ua).EqOn (unitIntervalOperatorKernel lambda)
      (fun x : ℝ => lambda⁻¹ * (1 - (1 + lambda * x)⁻¹)) := by
    intro x hx
    exact unitIntervalOperatorKernel_fractional_linear_pos hlambda_pos (hden_ne x hx)
  rw [cfc_congr hfun]
  rw [cfc_const_mul (r := lambda⁻¹) (f := fun x : ℝ => 1 - (1 + lambda * x)⁻¹) (a := ua)
    (hf := (continuousOn_const.sub hginv_cont))]
  rw [cfc_sub (f := fun _ : ℝ => 1) (g := fun x : ℝ => (1 + lambda * x)⁻¹) (a := ua)
    (hf := by fun_prop) (hg := hginv_cont)]
  rw [cfc_const_one ℝ ua]
  rw [cfc_inv (f := fun x : ℝ => 1 + lambda * x) (a := ua)
    (hf := by fun_prop) (ha := hua)]
  · rw [cfc_add (f := fun _ : ℝ => 1) (g := fun x : ℝ => lambda * x) (a := ua)
      (hf := by fun_prop) (hg := by fun_prop), cfc_const_one ℝ ua]
    rw [cfc_const_mul_id (R := ℝ) lambda ua]
    rfl
  · exact hden_ne

/-- Unitized CFC form of the negative-parameter fractional-linear identity. -/
theorem unitIntervalOperatorKernel_cfc_unitization_fractional_linear_neg
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda_neg : lambda < 0)
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a : A} (ha : IsSelfAdjoint a)
    (hspec : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfc (unitIntervalOperatorKernel lambda) (a : Unitization ℂ A) =
      (-lambda)⁻¹ • (Ring.inverse (1 + lambda • (a : Unitization ℂ A)) - 1) := by
  let ua : Unitization ℂ A := a
  have hua : IsSelfAdjoint ua := IsSelfAdjoint.inr (R := ℂ) ha
  have hden_ne : ∀ x ∈ spectrum ℝ ua, 1 + lambda * x ≠ 0 := by
    intro x hx
    exact unitIntervalOperatorKernel_denominator_ne_on_unitization_spectrum
      hlambda hspec x (by simpa [ua] using hx)
  have hginv_cont : ContinuousOn (fun x : ℝ => (1 + lambda * x)⁻¹) (spectrum ℝ ua) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀ hden_ne
  have hfun : (spectrum ℝ ua).EqOn (unitIntervalOperatorKernel lambda)
      (fun x : ℝ => (-lambda)⁻¹ * ((1 + lambda * x)⁻¹ - 1)) := by
    intro x hx
    exact unitIntervalOperatorKernel_fractional_linear_neg hlambda_neg (hden_ne x hx)
  rw [cfc_congr hfun]
  rw [cfc_const_mul (r := (-lambda)⁻¹) (f := fun x : ℝ => (1 + lambda * x)⁻¹ - 1) (a := ua)
    (hf := (hginv_cont.sub continuousOn_const))]
  rw [cfc_sub (f := fun x : ℝ => (1 + lambda * x)⁻¹) (g := fun _ : ℝ => 1) (a := ua)
    (hf := hginv_cont) (hg := by fun_prop)]
  rw [cfc_const_one ℝ ua]
  rw [cfc_inv (f := fun x : ℝ => 1 + lambda * x) (a := ua)
    (hf := by fun_prop) (ha := hua)]
  · rw [cfc_add (f := fun _ : ℝ => 1) (g := fun x : ℝ => lambda * x) (a := ua)
      (hf := by fun_prop) (hg := by fun_prop), cfc_const_one ℝ ua]
    rw [cfc_const_mul_id (R := ℝ) lambda ua]
    rfl
  · exact hden_ne

/-- CFC monotonicity of the interval kernel in the positive-parameter case. -/
theorem unitIntervalOperatorKernel_cfcₙ_le_of_pos
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda_pos : 0 < lambda)
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hspeca : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hspecb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ (unitIntervalOperatorKernel lambda) a ≤
      cfcₙ (unitIntervalOperatorKernel lambda) b := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  haveI : StarModule ℝ (Unitization ℂ A) := instUnitizationRealStarModule
  haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instUnitizationRealSelfTower
  haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instUnitizationRealSMulComm
  haveI : IsOrderedModule ℝ (Unitization ℂ A) := inferInstance
  haveI : IsOrderedAddMonoid (Unitization ℂ A) :=
    StarOrderedRing.toIsOrderedAddMonoid
  let ua : Unitization ℂ A := a
  let ub : Unitization ℂ A := b
  let da : Unitization ℂ A := 1 + lambda • ua
  let db : Unitization ℂ A := 1 + lambda • ub
  have hdena : IsStrictlyPositive da := by
    simpa [da, ua] using
      unitIntervalOperatorKernel_denominator_strictlyPositive hlambda ha hspeca
  have hdenb : IsStrictlyPositive db := by
    simpa [db, ub] using
      unitIntervalOperatorKernel_denominator_strictlyPositive hlambda hb hspecb
  have hle_inr : ua ≤ ub := by
    exact (Unitization.inr_le_iff a b ha hb).mpr hab
  have hden_le : da ≤ db := by
    simpa [da, db, add_comm, add_left_comm, add_assoc] using
      add_le_add_left (smul_le_smul_of_nonneg_left hle_inr (le_of_lt hlambda_pos))
        (1 : Unitization ℂ A)
  have hinv : Ring.inverse db ≤ Ring.inverse da := by
    obtain ⟨dbu, hdbu⟩ := hdenb.isUnit
    obtain ⟨dau, hdau⟩ := hdena.isUnit
    rw [← hdbu, ← hdau, Ring.inverse_unit, Ring.inverse_unit]
    exact @CStarAlgebra.inv_le_inv (Unitization ℂ A) inferInstance
      Unitization.instPartialOrder Unitization.instStarOrderedRing dau dbu
      (by simpa [hdau] using hdena.nonneg)
      (by simpa [hdau, hdbu] using hden_le)
  have hsub : 1 - Ring.inverse da ≤ 1 - Ring.inverse db := by
    exact sub_le_sub_left hinv 1
  have hsmul :
      lambda⁻¹ • (1 - Ring.inverse da) ≤ lambda⁻¹ • (1 - Ring.inverse db) := by
    exact smul_le_smul_of_nonneg_left hsub (inv_nonneg.mpr (le_of_lt hlambda_pos))
  rw [← Unitization.inr_le_iff
    (cfcₙ (unitIntervalOperatorKernel lambda) a)
    (cfcₙ (unitIntervalOperatorKernel lambda) b)
    (cfcₙ_predicate (unitIntervalOperatorKernel lambda) a)
    (cfcₙ_predicate (unitIntervalOperatorKernel lambda) b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
      (unitIntervalOperatorKernel lambda) (unitIntervalOperatorKernel_zero lambda),
    Unitization.real_cfcₙ_eq_cfc_inr b
      (unitIntervalOperatorKernel lambda) (unitIntervalOperatorKernel_zero lambda)]
  calc
    cfc (unitIntervalOperatorKernel lambda) (a : Unitization ℂ A) =
        lambda⁻¹ • (1 - Ring.inverse da) := by
      simpa [da, ua] using
        unitIntervalOperatorKernel_cfc_unitization_fractional_linear_pos
          hlambda_pos hlambda ha hspeca
    _ ≤ lambda⁻¹ • (1 - Ring.inverse db) := by
      simpa [da, db, ua, ub] using hsmul
    _ = cfc (unitIntervalOperatorKernel lambda) (b : Unitization ℂ A) := by
      simpa [db, ub] using
        (unitIntervalOperatorKernel_cfc_unitization_fractional_linear_pos
          hlambda_pos hlambda hb hspecb).symm

/-- CFC monotonicity of the interval kernel in the negative-parameter case. -/
theorem unitIntervalOperatorKernel_cfcₙ_le_of_neg
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {lambda : ℝ} (hlambda_neg : lambda < 0)
    (hlambda : lambda ∈ Set.Icc (-1 : ℝ) 1)
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hspeca : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hspecb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1)
    (hab : a ≤ b) :
    cfcₙ (unitIntervalOperatorKernel lambda) a ≤
      cfcₙ (unitIntervalOperatorKernel lambda) b := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  haveI : StarModule ℝ (Unitization ℂ A) := instUnitizationRealStarModule
  haveI : IsScalarTower ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instUnitizationRealSelfTower
  haveI : SMulCommClass ℝ (Unitization ℂ A) (Unitization ℂ A) :=
    instUnitizationRealSMulComm
  haveI : IsOrderedModule ℝ (Unitization ℂ A) := inferInstance
  haveI : IsOrderedAddMonoid (Unitization ℂ A) :=
    StarOrderedRing.toIsOrderedAddMonoid
  let ua : Unitization ℂ A := a
  let ub : Unitization ℂ A := b
  let da : Unitization ℂ A := 1 + lambda • ua
  let db : Unitization ℂ A := 1 + lambda • ub
  have hdena : IsStrictlyPositive da := by
    simpa [da, ua] using
      unitIntervalOperatorKernel_denominator_strictlyPositive hlambda ha hspeca
  have hdenb : IsStrictlyPositive db := by
    simpa [db, ub] using
      unitIntervalOperatorKernel_denominator_strictlyPositive hlambda hb hspecb
  have hle_inr : ua ≤ ub := by
    exact (Unitization.inr_le_iff a b ha hb).mpr hab
  have hmul_neg : lambda • ub ≤ lambda • ua := by
    exact @smul_le_smul_of_nonpos_left ℝ (Unitization ℂ A) lambda ua ub
      inferInstance inferInstance inferInstance inferInstance Unitization.instPartialOrder
      (StarOrderedRing.toIsOrderedAddMonoid (R := Unitization ℂ A))
      inferInstance
      (instUnitizationRealOrderedModule.toPosSMulMono :
        PosSMulMono ℝ (Unitization ℂ A))
      hle_inr (le_of_lt hlambda_neg)
  have hden_le : db ≤ da := by
    simpa [da, db, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hmul_neg (1 : Unitization ℂ A)
  have hinv : Ring.inverse da ≤ Ring.inverse db := by
    obtain ⟨dau, hdau⟩ := hdena.isUnit
    obtain ⟨dbu, hdbu⟩ := hdenb.isUnit
    rw [← hdau, ← hdbu, Ring.inverse_unit, Ring.inverse_unit]
    exact @CStarAlgebra.inv_le_inv (Unitization ℂ A) inferInstance
      Unitization.instPartialOrder Unitization.instStarOrderedRing dbu dau
      (by simpa [hdbu] using hdenb.nonneg)
      (by simpa [hdbu, hdau] using hden_le)
  have hsub : Ring.inverse da - 1 ≤ Ring.inverse db - 1 := by
    exact sub_le_sub_right hinv 1
  have hsmul :
      (-lambda)⁻¹ • (Ring.inverse da - 1) ≤
        (-lambda)⁻¹ • (Ring.inverse db - 1) := by
    exact smul_le_smul_of_nonneg_left hsub (inv_nonneg.mpr (le_of_lt (neg_pos.mpr hlambda_neg)))
  rw [← Unitization.inr_le_iff
    (cfcₙ (unitIntervalOperatorKernel lambda) a)
    (cfcₙ (unitIntervalOperatorKernel lambda) b)
    (cfcₙ_predicate (unitIntervalOperatorKernel lambda) a)
    (cfcₙ_predicate (unitIntervalOperatorKernel lambda) b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
      (unitIntervalOperatorKernel lambda) (unitIntervalOperatorKernel_zero lambda),
    Unitization.real_cfcₙ_eq_cfc_inr b
      (unitIntervalOperatorKernel lambda) (unitIntervalOperatorKernel_zero lambda)]
  calc
    cfc (unitIntervalOperatorKernel lambda) (a : Unitization ℂ A) =
        (-lambda)⁻¹ • (Ring.inverse da - 1) := by
      simpa [da, ua] using
        unitIntervalOperatorKernel_cfc_unitization_fractional_linear_neg
          hlambda_neg hlambda ha hspeca
    _ ≤ (-lambda)⁻¹ • (Ring.inverse db - 1) := by
      simpa [da, db, ua, ub] using hsmul
    _ = cfc (unitIntervalOperatorKernel lambda) (b : Unitization ℂ A) := by
      simpa [db, ub] using
        (unitIntervalOperatorKernel_cfc_unitization_fractional_linear_neg
          hlambda_neg hlambda hb hspecb).symm

/-- CFC monotonicity of the interval kernel for `lambda = 0`. -/
theorem unitIntervalOperatorKernel_cfcₙ_le_of_zero
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a ≤ b) :
    cfcₙ (unitIntervalOperatorKernel 0) a ≤ cfcₙ (unitIntervalOperatorKernel 0) b := by
  have hka : cfcₙ (unitIntervalOperatorKernel 0) a = a := by
    rw [cfcₙ_congr (a := a) (f := unitIntervalOperatorKernel 0) (g := fun x : ℝ => x)]
    · exact cfcₙ_id' ℝ a ha
    · intro x _hx
      simp [unitIntervalOperatorKernel]
  have hkb : cfcₙ (unitIntervalOperatorKernel 0) b = b := by
    rw [cfcₙ_congr (a := b) (f := unitIntervalOperatorKernel 0) (g := fun x : ℝ => x)]
    · exact cfcₙ_id' ℝ b hb
    · intro x _hx
      simp [unitIntervalOperatorKernel]
  simpa [hka, hkb] using hab

end

end Quantum.TraceInequality.Loewner
