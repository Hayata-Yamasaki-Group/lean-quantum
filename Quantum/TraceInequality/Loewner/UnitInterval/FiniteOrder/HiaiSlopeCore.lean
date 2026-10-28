import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ForwardCoefficientSource
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 20 Hiai four-point slope core diagnostics

This file contains the four-point kernel-core diagnostics and the Hiai slope
core estimates retained as conditional diagnostics around the public C1
regularity route.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution
open scoped fwdDiff

noncomputable section

/-- The four real nodes in the Hiai interlacing configuration `a < c < b < d`. -/
def hiaiFourPointNodes (a c b d : ℝ) : Fin 4 → ℝ
  | 0 => a
  | 1 => c
  | 2 => b
  | 3 => d

/-- Each Hiai four-point node lies in `(-1,1)` when the four inputs do. -/
lemma hiaiFourPointNodes_mem_Ioo
    {a c b d : ℝ}
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ i, hiaiFourPointNodes a c b d i ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro i
  fin_cases i <;> simp [hiaiFourPointNodes, ha, hb, hc, hd]

/-- Strict interlacing `a < c < b < d` makes the Hiai four-point node map injective. -/
lemma hiaiFourPointNodes_injective
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    Function.Injective (hiaiFourPointNodes a c b d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hiaiFourPointNodes] at hij ⊢ <;> try linarith

/--
The public Löwner kernel matrix is positive on the Hiai four-point
interlacing nodes, for every test vector.

The remaining kernel-core frontier is the scalar simplification of this
quadratic test for the correct Hiai vector.
-/
theorem hiaiFourPoint_loewnerKernel_quadratic_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f)
    {a c b d : ℝ}
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (v : Fin 4 → ℂ) :
    0 ≤
      star v ⬝ᵥ
        (Matrix.of
          (fun i j : Fin 4 =>
            (loewnerKernel f
              (hiaiFourPointNodes a c b d i)
              (hiaiFourPointNodes a c b d j) : ℂ))).mulVec v := by
  exact
    loewnerKernel_quadratic_nonneg_of_loewnerPosOnUnitInterval h
      (hiaiFourPointNodes_mem_Ioo ha hb hc hd)
      (hiaiFourPointNodes_injective hac hcb hbd) v

/--
The Hiai four-point slope-core inequality, expressed with public Löwner kernel
entries.  This is the precise scalar frontier extracted from finite Löwner
kernel positivity in the first public regularity step.
-/
def hiaiLoewnerKernelCoreOnUnitInterval (f : ℝ → ℝ) : Prop :=
  ∀ {a c b d : ℝ},
    a ∈ Set.Ioo (-1 : ℝ) 1 →
    b ∈ Set.Ioo (-1 : ℝ) 1 →
    c ∈ Set.Ioo (-1 : ℝ) 1 →
    d ∈ Set.Ioo (-1 : ℝ) 1 →
    a < c →
    c < b →
    b < d →
      0 ≤
        (((d - a) / (b - a)) * loewnerKernel f c a * loewnerKernel f c d -
          loewnerKernel f c a * loewnerKernel f c b -
          ((d - b) / (b - a)) * loewnerKernel f c b * loewnerKernel f c d)

/--
The scalar expression that has to be extracted from the Hiai four-point public
kernel quadratic test.  It is named separately so the remaining PSD-extraction
frontier is an exact algebraic target rather than an informal formula.
-/
def hiaiFourPointKernelCoreExpression
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  ((d - a) / (b - a)) * loewnerKernel f c a * loewnerKernel f c d -
    loewnerKernel f c a * loewnerKernel f c b -
    ((d - b) / (b - a)) * loewnerKernel f c b * loewnerKernel f c d

/--
The named four-point expression is exactly the kernel-form Hiai slope-core
integrand.
-/
theorem hiaiFourPointKernelCoreExpression_eq
    (f : ℝ → ℝ) (a c b d : ℝ) :
    hiaiFourPointKernelCoreExpression f a c b d =
      ((d - a) / (b - a)) * loewnerKernel f c a * loewnerKernel f c d -
        loewnerKernel f c a * loewnerKernel f c b -
        ((d - b) / (b - a)) * loewnerKernel f c b * loewnerKernel f c d := by
  rfl

/--
Once the four-point kernel-core expression is nonnegative in every Hiai
interlacing configuration, the public kernel-form core interface follows.
-/
theorem hiaiLoewnerKernelCoreOnUnitInterval_of_kernelCoreExpression_nonneg
    {f : ℝ → ℝ}
    (hcore :
      ∀ {a c b d : ℝ},
        a ∈ Set.Ioo (-1 : ℝ) 1 →
        b ∈ Set.Ioo (-1 : ℝ) 1 →
        c ∈ Set.Ioo (-1 : ℝ) 1 →
        d ∈ Set.Ioo (-1 : ℝ) 1 →
        a < c →
        c < b →
        b < d →
          0 ≤ hiaiFourPointKernelCoreExpression f a c b d) :
    hiaiLoewnerKernelCoreOnUnitInterval f := by
  intro a c b d ha hb hc hd hac hcb hbd
  simpa [hiaiFourPointKernelCoreExpression] using
    hcore ha hb hc hd hac hcb hbd

/--
The non-principal `2 × 2` minor behind the Hiai four-point kernel-core
expression.  The rows are the interlacing nodes `c,d` and the columns are
`a,b`.
-/
def hiaiFourPointKernelCoreMinor
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  loewnerKernel f c a * loewnerKernel f b d -
    loewnerKernel f c b * loewnerKernel f a d

/--
The `2 × 2` cross-block matrix whose determinant is the Hiai non-principal
minor.  The first row uses the center node `c`, and the second row uses the
opposite endpoint pair as it appears in the kernel-core algebra.
-/
def hiaiFourPointKernelCoreMinorMatrix
    (f : ℝ → ℝ) (a c b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ
  | 0, 0 => loewnerKernel f c a
  | 0, 1 => loewnerKernel f c b
  | 1, 0 => loewnerKernel f a d
  | 1, 1 => loewnerKernel f b d

/--
The determinant form of the Hiai non-principal minor.  This is the exact
scalar target for the remaining Schur/test-vector extraction from the public
four-point kernel PSD statement.
-/
theorem hiaiFourPointKernelCoreMinorMatrix_det
    (f : ℝ → ℝ) (a c b d : ℝ) :
    (hiaiFourPointKernelCoreMinorMatrix f a c b d).det =
      hiaiFourPointKernelCoreMinor f a c b d := by
  rw [Matrix.det_fin_two]
  rfl

/--
Nonnegativity of the cross-block determinant is exactly nonnegativity of the
Hiai non-principal minor.  The remaining public PSD frontier is therefore the
extraction of this determinant sign, not another algebraic normalization.
-/
theorem hiaiFourPointKernelCoreMinor_nonneg_of_crossBlock_det_nonneg
    {f : ℝ → ℝ} {a c b d : ℝ}
    (hdet : 0 ≤ (hiaiFourPointKernelCoreMinorMatrix f a c b d).det) :
    0 ≤ hiaiFourPointKernelCoreMinor f a c b d := by
  simpa [hiaiFourPointKernelCoreMinorMatrix_det] using hdet

/--
The named kernel-core expression is a positive scalar multiple of the Hiai
non-principal minor.  Thus the remaining public PSD extraction frontier is
equivalently the positivity of this minor.
-/
theorem hiaiFourPointKernelCoreExpression_eq_minor
    (f : ℝ → ℝ) {a c b d : ℝ}
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiFourPointKernelCoreExpression f a c b d =
      ((d - b) * (d - a) / ((d - c) * (b - a))) *
        hiaiFourPointKernelCoreMinor f a c b d := by
  have hca : c ≠ a := ne_of_gt hac
  have hcb_ne : c ≠ b := ne_of_lt hcb
  have hcd : c ≠ d := ne_of_lt (lt_trans hcb hbd)
  have hbd_ne : b ≠ d := ne_of_lt hbd
  have had : a ≠ d := ne_of_lt (lt_trans hac (lt_trans hcb hbd))
  have hba_sub : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
  have hdc_sub : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hcb hbd))
  have hdb_sub : d - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbd)
  have hda_sub : d - a ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (lt_trans hac (lt_trans hcb hbd)))
  rw [hiaiFourPointKernelCoreExpression,
    hiaiFourPointKernelCoreMinor,
    loewnerKernel_eq_div (f := f) (x := c) (y := a) hca,
    loewnerKernel_eq_div (f := f) (x := c) (y := b) hcb_ne,
    loewnerKernel_eq_div (f := f) (x := c) (y := d) hcd,
    loewnerKernel_eq_div (f := f) (x := b) (y := d) hbd_ne,
    loewnerKernel_eq_div (f := f) (x := a) (y := d) had]
  field_simp [hba_sub, hdc_sub, hdb_sub, hda_sub, sub_ne_zero.mpr hca,
    sub_ne_zero.mpr hcb_ne, sub_ne_zero.mpr hcd, sub_ne_zero.mpr hbd_ne,
    sub_ne_zero.mpr had]
  ring

/--
Nonnegativity of the Hiai non-principal minor is enough to prove the named
kernel-core expression, since the scalar factor in the interlacing
configuration is positive.
-/
theorem hiaiFourPointKernelCoreExpression_nonneg_of_minor_nonneg
    {f : ℝ → ℝ} {a c b d : ℝ}
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hminor : 0 ≤ hiaiFourPointKernelCoreMinor f a c b d) :
    0 ≤ hiaiFourPointKernelCoreExpression f a c b d := by
  rw [hiaiFourPointKernelCoreExpression_eq_minor f hac hcb hbd]
  have hfactor :
      0 ≤ (d - b) * (d - a) / ((d - c) * (b - a)) := by
    have hdb : 0 ≤ d - b := sub_nonneg.mpr hbd.le
    have hda : 0 ≤ d - a :=
      sub_nonneg.mpr (le_of_lt (lt_trans hac (lt_trans hcb hbd)))
    have hdc : 0 ≤ d - c := sub_nonneg.mpr (le_of_lt (lt_trans hcb hbd))
    have hba : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt (lt_trans hac hcb))
    exact div_nonneg (mul_nonneg hdb hda) (mul_nonneg hdc hba)
  exact mul_nonneg hfactor hminor

/--
If the Hiai non-principal minor is nonnegative in every interlacing
configuration, then the public kernel-form Hiai core follows.
-/
theorem hiaiLoewnerKernelCoreOnUnitInterval_of_kernelCoreMinor_nonneg
    {f : ℝ → ℝ}
    (hminor :
      ∀ {a c b d : ℝ},
        a ∈ Set.Ioo (-1 : ℝ) 1 →
        b ∈ Set.Ioo (-1 : ℝ) 1 →
        c ∈ Set.Ioo (-1 : ℝ) 1 →
        d ∈ Set.Ioo (-1 : ℝ) 1 →
        a < c →
        c < b →
        b < d →
          0 ≤ hiaiFourPointKernelCoreMinor f a c b d) :
    hiaiLoewnerKernelCoreOnUnitInterval f := by
  refine hiaiLoewnerKernelCoreOnUnitInterval_of_kernelCoreExpression_nonneg ?_
  intro a c b d ha hb hc hd hac hcb hbd
  exact hiaiFourPointKernelCoreExpression_nonneg_of_minor_nonneg
    hac hcb hbd (hminor ha hb hc hd hac hcb hbd)

/--
If the Hiai cross-block determinant is nonnegative in every interlacing
configuration, then the public kernel-form Hiai core follows.
-/
theorem hiaiLoewnerKernelCoreOnUnitInterval_of_crossBlock_det_nonneg
    {f : ℝ → ℝ}
    (hdet :
      ∀ {a c b d : ℝ},
        a ∈ Set.Ioo (-1 : ℝ) 1 →
        b ∈ Set.Ioo (-1 : ℝ) 1 →
        c ∈ Set.Ioo (-1 : ℝ) 1 →
        d ∈ Set.Ioo (-1 : ℝ) 1 →
        a < c →
        c < b →
        b < d →
          0 ≤ (hiaiFourPointKernelCoreMinorMatrix f a c b d).det) :
    hiaiLoewnerKernelCoreOnUnitInterval f := by
  refine hiaiLoewnerKernelCoreOnUnitInterval_of_kernelCoreMinor_nonneg ?_
  intro a c b d ha hb hc hd hac hcb hbd
  exact hiaiFourPointKernelCoreMinor_nonneg_of_crossBlock_det_nonneg
    (hdet ha hb hc hd hac hcb hbd)

/--
The kernel-form Hiai core gives the slope-form Hiai core by rewriting each
off-diagonal kernel entry as the corresponding secant slope.
-/
theorem hiaiSlopeCoreOnUnitInterval_of_kernelCore
    {f : ℝ → ℝ}
    (hcore : hiaiLoewnerKernelCoreOnUnitInterval f) :
    hiaiSlopeCoreOnUnitInterval f := by
  intro a c b d ha hb hc hd hac hcb hbd
  have hca : a ≠ c := ne_of_lt hac
  have hcb_ne : b ≠ c := ne_of_gt hcb
  have hdc : d ≠ c := ne_of_gt (lt_trans hcb hbd)
  simpa [slope_eq_loewnerKernel_of_ne (f := f) hca,
    slope_eq_loewnerKernel_of_ne (f := f) hcb_ne,
    slope_eq_loewnerKernel_of_ne (f := f) hdc] using
    hcore ha hb hc hd hac hcb hbd

/--
Minor nonnegativity is the remaining PSD-extraction target; once it is
available, the slope-form Hiai core follows immediately.
-/
theorem hiaiSlopeCoreOnUnitInterval_of_kernelCoreMinor_nonneg
    {f : ℝ → ℝ}
    (hminor :
      ∀ {a c b d : ℝ},
        a ∈ Set.Ioo (-1 : ℝ) 1 →
        b ∈ Set.Ioo (-1 : ℝ) 1 →
        c ∈ Set.Ioo (-1 : ℝ) 1 →
        d ∈ Set.Ioo (-1 : ℝ) 1 →
        a < c →
        c < b →
        b < d →
          0 ≤ hiaiFourPointKernelCoreMinor f a c b d) :
    hiaiSlopeCoreOnUnitInterval f :=
  hiaiSlopeCoreOnUnitInterval_of_kernelCore
    (hiaiLoewnerKernelCoreOnUnitInterval_of_kernelCoreMinor_nonneg hminor)

/--
The cross-block determinant sign is an equivalent remaining extraction target
for the slope-form Hiai core.
-/
theorem hiaiSlopeCoreOnUnitInterval_of_crossBlock_det_nonneg
    {f : ℝ → ℝ}
    (hdet :
      ∀ {a c b d : ℝ},
        a ∈ Set.Ioo (-1 : ℝ) 1 →
        b ∈ Set.Ioo (-1 : ℝ) 1 →
        c ∈ Set.Ioo (-1 : ℝ) 1 →
        d ∈ Set.Ioo (-1 : ℝ) 1 →
        a < c →
        c < b →
        b < d →
          0 ≤ (hiaiFourPointKernelCoreMinorMatrix f a c b d).det) :
    hiaiSlopeCoreOnUnitInterval f :=
  hiaiSlopeCoreOnUnitInterval_of_kernelCore
    (hiaiLoewnerKernelCoreOnUnitInterval_of_crossBlock_det_nonneg hdet)

/-!
### Scalar Hiai squeeze algebra

The lemmas in this block do not use Chapter 3 CFC order comparison.  They are
the one-variable scalar part of the Hiai regularity argument, phrased for the
public Chapter 20 slope-core contract above.
-/

/-- Additive-error form of the `q → ∞` Hiai estimate. -/
theorem hiaiSlopeCore_rightSecant_le_left_add_of_invQ_le
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {a c b d η : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (herror : slope f c a / ((d - b) / (b - a)) ≤ η) :
    slope f c b ≤ slope f c a + η := by
  have h :=
    hiaiSlopeCore_rightSecant_le_left_add_invQ
      hmono hcore ha hb hc hd hac hcb hbd
  linarith

/-- Additive-error form of the `q → 0` Hiai estimate. -/
theorem hiaiSlopeCore_rightSecant_le_far_add_of_qMul_le
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {a c b d η : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (herror : ((d - b) / (b - a)) * slope f c d ≤ η) :
    slope f c b ≤ slope f c d + η := by
  have h :=
    hiaiSlopeCore_rightSecant_le_far_addQ
      hmono hcore ha hb hc hd hac hcb hbd
  linarith

/-!
### Hiai slope-core to cross-secant control

The next lemmas are purely one-variable scalar consequences of
`hiaiSlopeCoreOnUnitInterval`.  They do not use CFC order comparison,
the normalized main theorem, or an integral representation.
-/

end

end Quantum.TraceInequality.Loewner
