import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel

/-!
# Affine transport to arbitrary open intervals

This file transports the normalized interval theorem to arbitrary open intervals
using affine maps and the corresponding public predicates.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology

noncomputable section

universe u

/-- The affine map sending the open interval `(a, b)` to `(-1, 1)`. -/
def openIntervalToUnitInterval (a b x : ℝ) : ℝ :=
  (2 * x - (a + b)) / (b - a)

/-- The inverse affine map sending `(-1, 1)` to `(a, b)`. -/
def unitIntervalToOpenInterval (a b u : ℝ) : ℝ :=
  ((b - a) * u + (a + b)) / 2

/-- Pull a real function on `(a, b)` back to the normalized interval. -/
def openIntervalPullback (a b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => f (unitIntervalToOpenInterval a b u)

/-- The affine map onto `(a, b)` in center-plus-radius form:
`(a + b)/2 + ((b - a)/2) · u`. -/
theorem unitIntervalToOpenInterval_eq_center_add_radius_mul
    (a b u : ℝ) :
    unitIntervalToOpenInterval a b u =
      (a + b) / 2 + ((b - a) / 2) * u := by
  unfold unitIntervalToOpenInterval
  ring

/-- The map `(a, b) → (-1, 1)` is a left inverse of `(-1, 1) → (a, b)`. -/
theorem openIntervalToUnitInterval_unitIntervalToOpenInterval
    {a b : ℝ} (hab : a < b) (u : ℝ) :
    openIntervalToUnitInterval a b (unitIntervalToOpenInterval a b u) = u := by
  unfold openIntervalToUnitInterval unitIntervalToOpenInterval
  have hba : b - a ≠ 0 := by linarith
  field_simp [hba]
  ring

/-- The map `(-1, 1) → (a, b)` is a left inverse of `(a, b) → (-1, 1)`. -/
theorem unitIntervalToOpenInterval_openIntervalToUnitInterval
    {a b : ℝ} (hab : a < b) (x : ℝ) :
    unitIntervalToOpenInterval a b (openIntervalToUnitInterval a b x) = x := by
  unfold openIntervalToUnitInterval unitIntervalToOpenInterval
  have hba : b - a ≠ 0 := by linarith
  field_simp [hba]
  ring

/-- The affine map sends the normalized interval `(-1, 1)` into `(a, b)`. -/
theorem unitIntervalToOpenInterval_mem_Ioo
    {a b u : ℝ} (hab : a < b) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    unitIntervalToOpenInterval a b u ∈ Set.Ioo a b := by
  unfold unitIntervalToOpenInterval
  constructor <;> nlinarith [hab, hu.1, hu.2]

/-- The affine map sends `(a, b)` into the normalized interval `(-1, 1)`. -/
theorem openIntervalToUnitInterval_mem_Ioo
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Ioo a b) :
    openIntervalToUnitInterval a b x ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold openIntervalToUnitInterval
  have hba_pos : 0 < b - a := by linarith
  constructor
  · have hnum : -(b - a) < 2 * x - (a + b) := by nlinarith [hx.1]
    have hdiv := div_lt_div_of_pos_right hnum hba_pos
    calc
      (-1 : ℝ) = -(b - a) / (b - a) := by
        field_simp [(ne_of_gt hba_pos)]
      _ < (2 * x - (a + b)) / (b - a) := hdiv
  · have hnum : 2 * x - (a + b) < b - a := by nlinarith [hx.2]
    have hdiv := div_lt_div_of_pos_right hnum hba_pos
    calc
      (2 * x - (a + b)) / (b - a) < (b - a) / (b - a) := hdiv
      _ = (1 : ℝ) := by
        field_simp [(ne_of_gt hba_pos)]

/-- The image `unitIntervalToOpenInterval a b u` lies in `(a, b)` iff `u ∈ (-1, 1)`. -/
theorem unitIntervalToOpenInterval_mem_Ioo_iff
    {a b u : ℝ} (hab : a < b) :
    unitIntervalToOpenInterval a b u ∈ Set.Ioo a b ↔
      u ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hu
    have hunit :
        openIntervalToUnitInterval a b
            (unitIntervalToOpenInterval a b u) ∈ Set.Ioo (-1 : ℝ) 1 :=
      openIntervalToUnitInterval_mem_Ioo hab hu
    simpa [openIntervalToUnitInterval_unitIntervalToOpenInterval hab u] using hunit
  · exact unitIntervalToOpenInterval_mem_Ioo hab

/-- The image `openIntervalToUnitInterval a b x` lies in `(-1, 1)` iff `x ∈ (a, b)`. -/
theorem openIntervalToUnitInterval_mem_Ioo_iff
    {a b x : ℝ} (hab : a < b) :
    openIntervalToUnitInterval a b x ∈ Set.Ioo (-1 : ℝ) 1 ↔
      x ∈ Set.Ioo a b := by
  constructor
  · intro hx
    have hopen :
        unitIntervalToOpenInterval a b
            (openIntervalToUnitInterval a b x) ∈ Set.Ioo a b :=
      unitIntervalToOpenInterval_mem_Ioo hab hx
    simpa [unitIntervalToOpenInterval_openIntervalToUnitInterval hab x] using hopen
  · exact openIntervalToUnitInterval_mem_Ioo hab

/--
Public operator-monotonicity predicate on an arbitrary open interval `(a, b)`.

This is the theorem-facing affine-transported predicate: a function is
operator monotone on `(a, b)` when its pullback to the normalized interval is
operator monotone there.  This mirrors the half-line API, where the public
open-domain predicate is transported to the already established normalized
interval statement.
-/
structure OperatorMonotoneOnOpenInterval (a b : ℝ) (f : ℝ → ℝ) : Prop where
  to_unitInterval :
    OperatorMonotoneOnUnitInterval.{u} (openIntervalPullback a b f)

/--
Public finite Löwner-matrix positivity condition on an arbitrary open interval.
-/
structure LoewnerPosOnOpenInterval (a b : ℝ) (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo a b)
  posSemidef :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo a b) →
        Function.Injective x →
          (Matrix.of
            (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef

/--
General-interval integral representation, encoded by affine transport to the
normalized interval. An explicit pushforward formula would require a separate
equivalence theorem.
-/
structure IntegralRepOnOpenInterval (a b : ℝ) (f : ℝ → ℝ) where
  pullback_rep : IntegralRepOnUnitInterval (openIntervalPullback a b f)

/-- Package a normalized-interval integral representation of the pullback as an integral
representation of `f` on `(a, b)`. -/
def integralRepOnOpenInterval_of_integralRepOnUnitInterval
    {a b : ℝ} {f : ℝ → ℝ}
    (rep : IntegralRepOnUnitInterval (openIntervalPullback a b f)) :
    IntegralRepOnOpenInterval a b f :=
  ⟨rep⟩

/-- Extract the underlying normalized-interval integral representation of the pullback from an
integral representation of `f` on `(a, b)`. -/
def IntegralRepOnOpenInterval.toUnitInterval
    {a b : ℝ} {f : ℝ → ℝ}
    (rep : IntegralRepOnOpenInterval a b f) :
    IntegralRepOnUnitInterval (openIntervalPullback a b f) :=
  rep.pullback_rep

/-- Löwner-matrix positivity of `f` on `(a, b)` transports to Löwner-matrix positivity of its
pullback on `(-1, 1)`; under the affine change of variables the Löwner kernel rescales by the
positive radius `(b - a)/2`. [simon2019] -/
theorem loewnerPosOnUnitInterval_of_loewnerPosOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hpos : LoewnerPosOnOpenInterval a b f) :
    LoewnerPosOnUnitInterval (openIntervalPullback a b f) := by
  let c : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  refine ⟨?_, ?_⟩
  · have hlin :
        DifferentiableOn ℝ (unitIntervalToOpenInterval a b)
          (Set.Ioo (-1 : ℝ) 1) := by
      unfold unitIntervalToOpenInterval
      fun_prop
    have hmap :
        Set.MapsTo (unitIntervalToOpenInterval a b)
          (Set.Ioo (-1 : ℝ) 1) (Set.Ioo a b) :=
      fun _ hu => unitIntervalToOpenInterval_mem_Ioo hab hu
    simpa [openIntervalPullback, Function.comp_def] using
      hpos.differentiable.comp hlin hmap
  · intro n u hu hinj
    let z : Fin n → ℝ := fun i => c + r * u i
    have hz : ∀ i, z i ∈ Set.Ioo a b := by
      intro i
      have hmem := unitIntervalToOpenInterval_mem_Ioo hab (hu i)
      simpa [z, c, r, unitIntervalToOpenInterval_eq_center_add_radius_mul] using hmem
    have hzinj : Function.Injective z := by
      intro i j hij
      apply hinj
      have hmul : r * u i = r * u j := by
        dsimp [z] at hij
        linarith
      exact mul_left_cancel₀ hr.ne' hmul
    have hbase :
        (Matrix.of fun i j : Fin n =>
          (loewnerKernel f (z i) (z j) : ℂ)).PosSemidef :=
      hpos.posSemidef n z hz hzinj
    have hmat :
        (Matrix.of fun i j : Fin n =>
          (loewnerKernel (openIntervalPullback a b f) (u i) (u j) : ℂ)) =
          (r : ℝ) •
            (Matrix.of fun i j : Fin n =>
              (loewnerKernel f (z i) (z j) : ℂ)) := by
      ext i j
      have hdiff : DifferentiableAt ℝ f (c + r * u i) :=
        hpos.differentiable.differentiableAt (isOpen_Ioo.mem_nhds (hz i))
      have hk :=
        loewnerKernel_affinePullback_eq
          (g := f) (x := c) (r := r) (u := u i) (v := u j) hr hdiff
      have hkC :
          ((loewnerKernel (fun w : ℝ => f (c + r * w))
              (u i) (u j) : ℝ) : ℂ) =
            (r : ℝ) • ((loewnerKernel f (z i) (z j) : ℝ) : ℂ) := by
        rw [hk]
        simp [z]
      change
        ((loewnerKernel (fun w : ℝ => f (unitIntervalToOpenInterval a b w))
            (u i) (u j) : ℝ) : ℂ) =
          (r : ℝ) • ((loewnerKernel f (z i) (z j) : ℝ) : ℂ)
      simpa [unitIntervalToOpenInterval_eq_center_add_radius_mul, c, r] using hkC
    rw [hmat]
    exact hbase.smul (α := ℝ) hr.le

/-- Conversely, Löwner-matrix positivity of the pullback on `(-1, 1)` transports back to
Löwner-matrix positivity of `f` on `(a, b)`. [simon2019] -/
theorem loewnerPosOnOpenInterval_of_loewnerPosOnUnitInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hpos : LoewnerPosOnUnitInterval (openIntervalPullback a b f)) :
    LoewnerPosOnOpenInterval a b f := by
  let c : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hdiff_open : DifferentiableOn ℝ f (Set.Ioo a b) := by
    have hlin :
        DifferentiableOn ℝ (openIntervalToUnitInterval a b)
          (Set.Ioo a b) := by
      unfold openIntervalToUnitInterval
      fun_prop
    have hmap :
        Set.MapsTo (openIntervalToUnitInterval a b)
          (Set.Ioo a b) (Set.Ioo (-1 : ℝ) 1) :=
      fun _ hx => openIntervalToUnitInterval_mem_Ioo hab hx
    have hcomp := hpos.differentiable.comp hlin hmap
    exact hcomp.congr (by
      intro x hx
      simp [openIntervalPullback,
        unitIntervalToOpenInterval_openIntervalToUnitInterval hab x])
  refine ⟨hdiff_open, ?_⟩
  intro n x hx hinj
  let u : Fin n → ℝ := fun i => openIntervalToUnitInterval a b (x i)
  have hu : ∀ i, u i ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro i
    exact openIntervalToUnitInterval_mem_Ioo hab (hx i)
  have huinj : Function.Injective u := by
    intro i j hij
    apply hinj
    have hback :
        unitIntervalToOpenInterval a b (u i) =
          unitIntervalToOpenInterval a b (u j) := by
      rw [hij]
    simpa [u, unitIntervalToOpenInterval_openIntervalToUnitInterval hab] using hback
  have hbase :
      (Matrix.of fun i j : Fin n =>
        (loewnerKernel (openIntervalPullback a b f) (u i) (u j) : ℂ)).PosSemidef :=
    hpos.posSemidef n u hu huinj
  have hmat :
      (Matrix.of fun i j : Fin n =>
        (loewnerKernel (openIntervalPullback a b f) (u i) (u j) : ℂ)) =
        (r : ℝ) •
          (Matrix.of fun i j : Fin n =>
            (loewnerKernel f (x i) (x j) : ℂ)) := by
    ext i j
    have hxu : x i = c + r * u i := by
      simpa [u, c, r, unitIntervalToOpenInterval_eq_center_add_radius_mul] using
        (unitIntervalToOpenInterval_openIntervalToUnitInterval hab (x i)).symm
    have hxi : c + r * u i ∈ Set.Ioo a b := by
      simpa [hxu.symm] using hx i
    have hdiff : DifferentiableAt ℝ f (c + r * u i) :=
      hdiff_open.differentiableAt (isOpen_Ioo.mem_nhds hxi)
    have hk :=
      loewnerKernel_affinePullback_eq
        (g := f) (x := c) (r := r) (u := u i) (v := u j) hr hdiff
    have hxj : x j = c + r * u j := by
      simpa [u, c, r, unitIntervalToOpenInterval_eq_center_add_radius_mul] using
        (unitIntervalToOpenInterval_openIntervalToUnitInterval hab (x j)).symm
    have hkC :
        ((loewnerKernel (fun w : ℝ => f (c + r * w))
            (u i) (u j) : ℝ) : ℂ) =
          (r : ℝ) • ((loewnerKernel f (x i) (x j) : ℝ) : ℂ) := by
      rw [hk]
      simp [hxu, hxj]
    change
      ((loewnerKernel (fun w : ℝ => f (unitIntervalToOpenInterval a b w))
          (u i) (u j) : ℝ) : ℂ) =
        (r : ℝ) • ((loewnerKernel f (x i) (x j) : ℝ) : ℂ)
    simpa [unitIntervalToOpenInterval_eq_center_add_radius_mul, c, r] using hkC
  have hscaled :
      ((r : ℝ) •
        (Matrix.of fun i j : Fin n =>
          (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef := by
    simpa [hmat] using hbase
  have hinv_scaled := hscaled.smul (α := ℝ) (inv_nonneg.mpr hr.le)
  convert hinv_scaled using 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.of_apply, Complex.real_smul]
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hrC]
  simp

/-- Operator monotonicity of `f` on `(a, b)` unfolds, by definition, to operator monotonicity of
its pullback on `(-1, 1)`. -/
theorem operatorMonotoneOnUnitInterval_of_operatorMonotoneOnOpenInterval
    {a b : ℝ} {f : ℝ → ℝ}
    (hmono : OperatorMonotoneOnOpenInterval.{u} a b f) :
    OperatorMonotoneOnUnitInterval.{u} (openIntervalPullback a b f) := by
  exact hmono.to_unitInterval

/-- Operator monotonicity of the pullback on `(-1, 1)` repackages as operator monotonicity of `f`
on `(a, b)`. -/
theorem operatorMonotoneOnOpenInterval_of_operatorMonotoneOnUnitInterval
    {a b : ℝ} {f : ℝ → ℝ}
    (hmono : OperatorMonotoneOnUnitInterval.{u} (openIntervalPullback a b f)) :
    OperatorMonotoneOnOpenInterval.{u} a b f := by
  exact ⟨hmono⟩

/-- On `(a, b)`, operator monotonicity implies Löwner-matrix positivity, via transport to the
normalized interval. [simon2019] -/
theorem loewnerPosOnOpenInterval_of_operatorMonotoneOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hmono : OperatorMonotoneOnOpenInterval.{u} a b f) :
    LoewnerPosOnOpenInterval a b f := by
  exact loewnerPosOnOpenInterval_of_loewnerPosOnUnitInterval hab
    (loewnerPosOnUnitInterval_of_operatorMonotone
      (operatorMonotoneOnUnitInterval_toZero
        (operatorMonotoneOnUnitInterval_of_operatorMonotoneOnOpenInterval hmono)))

/-- On `(a, b)`, an integral representation of `f` implies Löwner-matrix positivity. [simon2019] -/
theorem loewnerPosOnOpenInterval_of_integralRepOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (rep : IntegralRepOnOpenInterval a b f) :
    LoewnerPosOnOpenInterval a b f := by
  exact loewnerPosOnOpenInterval_of_loewnerPosOnUnitInterval hab
    (loewnerPosOnUnitInterval_of_integralRep rep.toUnitInterval)

/-- On `(a, b)`, an integral representation of `f` implies operator monotonicity. [simon2019] -/
theorem operatorMonotoneOnOpenInterval_of_integralRepOnOpenInterval
    {a b : ℝ} (_hab : a < b) {f : ℝ → ℝ}
    (rep : IntegralRepOnOpenInterval a b f) :
    OperatorMonotoneOnOpenInterval.{u} a b f := by
  exact operatorMonotoneOnOpenInterval_of_operatorMonotoneOnUnitInterval
    (operatorMonotoneOnUnitInterval_of_integralRep rep.toUnitInterval)

/-- On `(a, b)`, Löwner-matrix positivity of `f` yields all three
equivalent conditions — Löwner positivity, an integral representation, and operator
monotonicity. [simon2019] -/
theorem openInterval_loewnerPos_has_all_three
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hpos : LoewnerPosOnOpenInterval a b f) :
    LoewnerPosOnOpenInterval a b f ∧
      Nonempty (IntegralRepOnOpenInterval a b f) ∧
        OperatorMonotoneOnOpenInterval.{u} a b f := by
  have hunit_pos :
      LoewnerPosOnUnitInterval (openIntervalPullback a b f) :=
    loewnerPosOnUnitInterval_of_loewnerPosOnOpenInterval hab hpos
  rcases unitInterval_loewnerPos_has_all_three hunit_pos with
    ⟨_, hrep, hmono⟩
  refine ⟨hpos, ?_, ?_⟩
  · rcases hrep with ⟨rep⟩
    exact ⟨integralRepOnOpenInterval_of_integralRepOnUnitInterval rep⟩
  · exact operatorMonotoneOnOpenInterval_of_operatorMonotoneOnUnitInterval hmono

/-- Löwner-matrix positivity of `f` on `(a, b)` yields an integral representation. [simon2019] -/
theorem integralRepOnOpenInterval_nonempty_of_loewnerPosOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hpos : LoewnerPosOnOpenInterval a b f) :
    Nonempty (IntegralRepOnOpenInterval a b f) :=
  (openInterval_loewnerPos_has_all_three.{0} hab hpos).2.1

/-- Löwner-matrix positivity of `f` on `(a, b)` yields operator monotonicity. [simon2019] -/
theorem operatorMonotoneOnOpenInterval_of_loewnerPosOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hpos : LoewnerPosOnOpenInterval a b f) :
    OperatorMonotoneOnOpenInterval.{u} a b f :=
  (openInterval_loewnerPos_has_all_three hab hpos).2.2

/-- On `(a, b)`, operator monotonicity of `f` is equivalent to Löwner-matrix positivity.
[simon2019] -/
theorem operatorMonotoneOnOpenInterval_iff_loewnerPosOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} :
    OperatorMonotoneOnOpenInterval.{u} a b f ↔ LoewnerPosOnOpenInterval a b f :=
  ⟨loewnerPosOnOpenInterval_of_operatorMonotoneOnOpenInterval hab,
    operatorMonotoneOnOpenInterval_of_loewnerPosOnOpenInterval hab⟩

/-- On `(a, b)`, the existence of an integral representation of `f` is equivalent to
Löwner-matrix positivity. [simon2019] -/
theorem integralRepOnOpenInterval_nonempty_iff_loewnerPosOnOpenInterval
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} :
    Nonempty (IntegralRepOnOpenInterval a b f) ↔ LoewnerPosOnOpenInterval a b f :=
  ⟨fun hrep => hrep.elim (loewnerPosOnOpenInterval_of_integralRepOnOpenInterval hab),
    integralRepOnOpenInterval_nonempty_of_loewnerPosOnOpenInterval hab⟩

/-- The two Löwner equivalences on `(a, b)`: operator monotonicity ↔ Löwner positivity, and the
existence of an integral representation ↔ Löwner positivity. [simon2019] -/
theorem openInterval_loewner_conditions_equiv
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} :
    (OperatorMonotoneOnOpenInterval.{u} a b f ↔ LoewnerPosOnOpenInterval a b f) ∧
      (Nonempty (IntegralRepOnOpenInterval a b f) ↔
        LoewnerPosOnOpenInterval a b f) :=
  ⟨operatorMonotoneOnOpenInterval_iff_loewnerPosOnOpenInterval hab,
    integralRepOnOpenInterval_nonempty_iff_loewnerPosOnOpenInterval hab⟩

end

end Quantum.TraceInequality.Loewner
