import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizationKernelPSD
import Quantum.TraceInequality.Loewner.RealComplexOrder

/-!
# Chapter 20 affine pullback PSD transport

This file contains the affine pullback of Hiai regularization to the normalized
unit interval and the associated Löwner-kernel PSD transport.
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

noncomputable section

/--
Affine pullback of the Hiai regularization to the normalized unit interval
around the center `x` with radius `r`.
-/
noncomputable def hiaiRegularizationAffinePullback
    (φ : ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ) (x r u : ℝ) : ℝ :=
  hiaiRegularization φ ε f (x + r * u)

/--
Normalized points in `(-1, 1)` map into the regularized interior when the
ambient closed interval is contained there.
-/
theorem hiaiRegularization_affinePullback_mem_interior
    {ε x r u : ℝ} (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    x + r * u ∈ hiaiRegularizedInterior ε := by
  apply hsub
  constructor
  · have hmul : -r < r * u := by
      simpa using (mul_lt_mul_of_pos_left hu.1 hr)
    linarith
  · have hmul : r * u < r := by
      simpa using (mul_lt_mul_of_pos_left hu.2 hr)
    linarith

/--
An affine change of variables with nonzero radius preserves injectivity of the
node family.
-/
theorem hiaiRegularization_affinePullback_nodes_injective
    {ι : Type*} {x r : ℝ} (hr : r ≠ 0) {u : ι → ℝ}
    (hu : Function.Injective u) :
    Function.Injective (fun i : ι => x + r * u i) := by
  intro i j hij
  apply hu
  have hmul : r * u i = r * u j := by
    linarith
  exact mul_left_cancel₀ hr hmul

/--
The Löwner kernel of an affine pullback is the original kernel multiplied by
the positive scale factor.
-/
theorem loewnerKernel_affinePullback_eq
    {g : ℝ → ℝ} {x r u v : ℝ} (hr : 0 < r)
    (hgu : DifferentiableAt ℝ g (x + r * u)) :
    loewnerKernel (fun w : ℝ => g (x + r * w)) u v =
      r * loewnerKernel g (x + r * u) (x + r * v) := by
  by_cases huv : u = v
  · subst v
    have hlin : HasDerivAt (fun w : ℝ => x + r * w) r u := by
      simpa [mul_comm] using ((hasDerivAt_id u).const_mul r).const_add x
    have hcomp : HasDerivAt (fun w : ℝ => g (x + r * w))
        (r * deriv g (x + r * u)) u := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
        hgu.hasDerivAt.comp u hlin
    simp [loewnerKernel_self, hcomp.deriv]
  · have hscaled : x + r * u ≠ x + r * v := by
      intro h
      apply huv
      have hmul : r * u = r * v := by
        linarith
      exact mul_left_cancel₀ hr.ne' hmul
    have hsub : u - v ≠ 0 := sub_ne_zero.mpr huv
    have hscaled_sub : x + r * u - (x + r * v) ≠ 0 := sub_ne_zero.mpr hscaled
    rw [loewnerKernel_eq_div (f := fun w : ℝ => g (x + r * w)) huv,
      loewnerKernel_eq_div (f := g) hscaled]
    field_simp [hsub, hscaled_sub, hr.ne']
    ring

/--
The affine pullback of a Hiai regularization is differentiable on the normalized
unit interval.
-/
theorem hiaiRegularization_affinePullback_differentiableOn
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    DifferentiableOn ℝ
      (hiaiRegularizationAffinePullback φ ε f x r)
      (Set.Ioo (-1 : ℝ) 1) := by
  intro u hu
  have huReg :
      x + r * u ∈ hiaiRegularizedInterior ε :=
    hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u) hr hsub hu
  have hg :=
    regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
      (φ := φ) (f := f) hφ hε huReg hpos
  have hlin : HasDerivAt (fun w : ℝ => x + r * w) r u := by
    simpa [mul_comm] using ((hasDerivAt_id u).const_mul r).const_add x
  exact ((hg.comp u hlin).differentiableAt).differentiableWithinAt

/--
The affine pullback of a regularized Löwner-positive function has positive
semidefinite Löwner matrices on normalized nodes.
-/
theorem hiaiRegularization_affinePullback_posSemidef
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    {n : ℕ} {u : Fin n → ℝ}
    (hu : ∀ i, u i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective u) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel
        (hiaiRegularizationAffinePullback φ ε f x r)
        (u i) (u j) : ℂ)).PosSemidef := by
  let z : Fin n → ℝ := fun i => x + r * u i
  have hz : ∀ i, z i ∈ hiaiRegularizedInterior ε := by
    intro i
    exact hiaiRegularization_affinePullback_mem_interior
      (ε := ε) (x := x) (r := r) (u := u i) hr hsub (hu i)
  have hzinj : Function.Injective z :=
    hiaiRegularization_affinePullback_nodes_injective
      (x := x) (r := r) hr.ne' hinj
  have hbase :
      (Matrix.of fun i j : Fin n =>
        (loewnerKernel (hiaiRegularization φ ε f) (z i) (z j) : ℂ)).PosSemidef :=
    regularization_loewnerKernelPSD
      (φ := φ) (f := f) hφ hε hz hzinj hpos
  have hmat :
      (Matrix.of fun i j : Fin n =>
        (loewnerKernel
          (hiaiRegularizationAffinePullback φ ε f x r)
          (u i) (u j) : ℂ)) =
        (r : ℝ) •
          (Matrix.of fun i j : Fin n =>
            (loewnerKernel (hiaiRegularization φ ε f) (z i) (z j) : ℂ)) := by
    ext i j
    have hdiff :
        DifferentiableAt ℝ (hiaiRegularization φ ε f) (x + r * u i) :=
      (regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
        (φ := φ) (f := f) hφ hε (hz i) hpos).differentiableAt
    have hk :=
      loewnerKernel_affinePullback_eq
        (g := hiaiRegularization φ ε f)
        (x := x) (r := r) (u := u i) (v := u j) hr hdiff
    change
      ((loewnerKernel
          (fun w : ℝ => hiaiRegularization φ ε f (x + r * w))
          (u i) (u j) : ℝ) : ℂ) =
        (r : ℝ) •
          ((loewnerKernel (hiaiRegularization φ ε f) (z i) (z j) : ℝ) : ℂ)
    rw [hk]
    simp [z]
  rw [hmat]
  exact hbase.smul (α := ℝ) hr.le

/--
The regularized PSD theorem, restricted to a small interval and pulled back
affinely, supplies the standard unit-interval Löwner positivity input.
-/
theorem hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval
      (hiaiRegularizationAffinePullback φ ε f x r) where
  differentiable :=
    hiaiRegularization_affinePullback_differentiableOn
      (φ := φ) (f := f) hφ hε hr hsub hpos
  posSemidef := by
    intro n u hu hinj
    exact hiaiRegularization_affinePullback_posSemidef
      (φ := φ) (f := f) hφ hε hr hsub hpos hu hinj

end

end Quantum.TraceInequality.Loewner
