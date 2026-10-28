import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform

import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.WellFounded
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators
open scoped ComplexOrder
open scoped Topology
open scoped BoundedContinuousFunction
open scoped UpperHalfPlane

open MeasureTheory Set Filter

noncomputable section

/-!
Step 6: Normal family on compact rectangles `KmC m` in the upper half-plane, using
bounded continuous functions (`→ᵇ`) and Arzelà–Ascoli.

This file is intentionally set up so that the Ascoli engine is separate from the
specialization to Stieltjes transforms.
-/

/-- Lower imaginary-height cutoff for the compact rectangle `KmC m`. -/
def δ (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

/-- Compact rectangle in the upper half-plane with height bounded below by `δ m`. -/
def KmC (m : ℕ) : Set ℂ :=
  {z | |z.re| ≤ (m : ℝ) ∧ δ m ≤ z.im ∧ z.im ≤ (m : ℝ) + 1}

/-- Subtype of points of the compact rectangle `KmC m`. -/
abbrev Xm (m : ℕ) : Type :=
  {z : ℂ // z ∈ KmC m}

/-- The lower height cutoff `δ m` is positive. -/
lemma delta_pos (m : ℕ) : 0 < δ m := by
  dsimp [δ]
  have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  exact one_div_pos.2 this

/-- Every point of `KmC m` has positive imaginary part. -/
lemma im_pos_of_mem_KmC {m : ℕ} {z : ℂ} (hz : z ∈ KmC m) : 0 < z.im := by
  have hδ : 0 < δ m := delta_pos m
  exact lt_of_lt_of_le hδ hz.2.1

/-- Coerce a point of `KmC m` to the upper half-plane. -/
def toUHP (m : ℕ) : Xm m → ℍ :=
  fun z => ⟨(z : ℂ), im_pos_of_mem_KmC (m := m) z.property⟩

/-- The rectangle `KmC m` is compact. -/
lemma isCompact_KmC (m : ℕ) : IsCompact (KmC m) := by
  classical
  have hclosed : IsClosed (KmC m) := by
    -- `KmC` is an intersection of closed halfspaces defined by continuous functions.
    have h1 : IsClosed {z : ℂ | |z.re| ≤ (m : ℝ)} := by
      have hcont : Continuous fun z : ℂ => |z.re| :=
        (continuous_abs : Continuous fun r : ℝ => |r|).comp Complex.continuous_re
      simpa using isClosed_le hcont continuous_const
    have h2 : IsClosed {z : ℂ | δ m ≤ z.im} := by
      have hcont : Continuous fun z : ℂ => z.im := Complex.continuous_im
      simpa using isClosed_le continuous_const hcont
    have h3 : IsClosed {z : ℂ | z.im ≤ (m : ℝ) + 1} := by
      have hcont : Continuous fun z : ℂ => z.im := Complex.continuous_im
      simpa using isClosed_le hcont continuous_const
    -- Rewrite `KmC` as an intersection.
    have :
        KmC m =
          ({z : ℂ | |z.re| ≤ (m : ℝ)} ∩ {z : ℂ | δ m ≤ z.im}) ∩
            {z : ℂ | z.im ≤ (m : ℝ) + 1} := by
      ext z
      simp [KmC, and_left_comm, and_comm]
    simpa [this] using (h1.inter h2).inter h3
  have hbounded : Bornology.IsBounded (KmC m) := by
    refine (Metric.isBounded_iff_subset_closedBall (c := (0 : ℂ))).2 ?_
    refine ⟨(2 * (m : ℝ) + 1), ?_⟩
    intro z hz
    have hre : |z.re| ≤ (m : ℝ) := hz.1
    have him : z.im ≤ (m : ℝ) + 1 := hz.2.2
    have him0 : 0 ≤ z.im := le_trans (le_of_lt (delta_pos m)) hz.2.1
    have hnorm :
        ‖z‖ ≤ (m : ℝ) + ((m : ℝ) + 1) := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ (m : ℝ) + z.im := by
              calc
                |z.re| + |z.im| ≤ (m : ℝ) + |z.im| := add_le_add hre le_rfl
                _ = (m : ℝ) + z.im := by simp [abs_of_nonneg him0]
        _ ≤ (m : ℝ) + ((m : ℝ) + 1) := by gcongr
    have hdist : dist z (0 : ℂ) ≤ 2 * (m : ℝ) + 1 := by
      have : (m : ℝ) + ((m : ℝ) + 1) = 2 * (m : ℝ) + 1 := by ring
      simpa [dist_eq_norm, this] using hnorm
    simpa [Metric.mem_closedBall] using hdist
  exact (Metric.isCompact_iff_isClosed_bounded (s := KmC m)).2 ⟨hclosed, hbounded⟩

/-- The subtype `Xm m` is compact. -/
instance instCompactSpace_Xm (m : ℕ) : CompactSpace (Xm m) :=
  (isCompact_iff_compactSpace (s := KmC m)).1 (isCompact_KmC m)

/-! ### Kernel bounds -/

/-- Uniform bound for the Stieltjes kernel on the strip `δ m ≤ im z`. -/
lemma kernel_bound {m : ℕ} {z : ℂ} (hz : δ m ≤ z.im) (t : ℝ) :
    ‖(1 / ((t : ℂ) - z))‖ ≤ 1 / δ m := by
  have hδ : 0 < δ m := delta_pos m
  have hz0 : 0 ≤ z.im := le_trans (le_of_lt hδ) hz
  have him : δ m ≤ |((t : ℂ) - z).im| := by
    have : ((t : ℂ) - z).im = -z.im := by simp
    simpa [this, abs_neg, abs_of_nonneg hz0] using hz
  have hnorm : δ m ≤ ‖(t : ℂ) - z‖ := le_trans him (Complex.abs_im_le_norm _)
  calc
    ‖(1 / ((t : ℂ) - z))‖ = 1 / ‖(t : ℂ) - z‖ := by
          simp [one_div]
    _ ≤ 1 / (δ m) := by
          exact one_div_le_one_div_of_le hδ hnorm
    _ = 1 / δ m := rfl

/-- Lipschitz bound in the point variable for the Stieltjes kernel on `δ m ≤ im`. -/
lemma kernel_diff_bound {m : ℕ} {z w : ℂ} (hz : δ m ≤ z.im) (hw : δ m ≤ w.im) (t : ℝ) :
    ‖(1 / ((t : ℂ) - z)) - (1 / ((t : ℂ) - w))‖ ≤ ‖z - w‖ / (δ m) ^ 2 := by
  have hδ : 0 < δ m := delta_pos m
  set a : ℂ := (t : ℂ) - z
  set b : ℂ := (t : ℂ) - w
  have ha : δ m ≤ ‖a‖ := by
    have hz0 : 0 ≤ z.im := le_trans (le_of_lt hδ) hz
    have : a.im = -z.im := by simp [a]
    have him : δ m ≤ |a.im| := by simpa [this, abs_neg, abs_of_nonneg hz0] using hz
    exact le_trans him (Complex.abs_im_le_norm a)
  have hb : δ m ≤ ‖b‖ := by
    have hw0 : 0 ≤ w.im := le_trans (le_of_lt hδ) hw
    have : b.im = -w.im := by simp [b]
    have him : δ m ≤ |b.im| := by simpa [this, abs_neg, abs_of_nonneg hw0] using hw
    exact le_trans him (Complex.abs_im_le_norm b)
  have hne1 : a ≠ 0 := by
    have : 0 < ‖a‖ := lt_of_lt_of_le hδ ha
    exact (norm_pos_iff).1 this
  have hne2 : b ≠ 0 := by
    have : 0 < ‖b‖ := lt_of_lt_of_le hδ hb
    exact (norm_pos_iff).1 this
  have hfrac :
      (1 / a) - (1 / b) = (b - a) / (a * b) := by
    field_simp [hne1, hne2]
  have hinv : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    simpa [one_div] using hfrac
  have hba : b - a = z - w := by
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm]
  calc
    ‖(1 / ((t : ℂ) - z)) - (1 / ((t : ℂ) - w))‖ = ‖(1 / a) - (1 / b)‖ := by
          simp [a, b]
    _ = ‖a⁻¹ - b⁻¹‖ := by simp [one_div]
    _ = ‖(b - a) / (a * b)‖ := by simp [hinv]
    _ = ‖b - a‖ / ‖a * b‖ := by simp
    _ = ‖z - w‖ / (‖a‖ * ‖b‖) := by
          simp [hba]
    _ ≤ ‖z - w‖ / ((δ m) * (δ m)) := by
          have hden : (δ m) * (δ m) ≤ ‖a‖ * ‖b‖ := by
            have hδ0 : 0 ≤ δ m := (le_of_lt hδ)
            exact mul_le_mul ha hb hδ0 (le_trans hδ0 ha)
          -- convert to inverses
          have : 1 / (‖a‖ * ‖b‖) ≤ 1 / ((δ m) * (δ m)) :=
            one_div_le_one_div_of_le (by nlinarith [hδ]) hden
          have hnum0 : 0 ≤ ‖z - w‖ := by positivity
          have := mul_le_mul_of_nonneg_left this hnum0
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
    _ = ‖z - w‖ / (δ m) ^ 2 := by ring

/-! ### Ascoli engine on bounded continuous functions -/

/--
Arzelà-Ascoli extraction for uniformly bounded equi-Lipschitz bounded continuous functions.
-/
theorem subseq_tendstoUniformly_of_bounds {m : ℕ} (FnBC : ℕ → Xm m →ᵇ ℂ) (R L : ℝ)
    (in_ball : ∀ n x, ‖FnBC n x‖ ≤ R)
    (lip : ∀ n x y, dist (FnBC n x) (FnBC n y) ≤ L * dist x y) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∃ Gm : Xm m →ᵇ ℂ, TendstoUniformly (fun n => FnBC (φ n)) Gm atTop := by
  classical
  let A : Set (Xm m →ᵇ ℂ) := Set.range FnBC
  let s : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hs : IsCompact s := isCompact_closedBall (0 : ℂ) R
  have in_s : ∀ (f : Xm m →ᵇ ℂ) (x : Xm m), f ∈ A → f x ∈ s := by
    intro f x hf
    rcases hf with ⟨n, rfl⟩
    have h0 : dist (FnBC n x) (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using in_ball n x
    simpa [s, Metric.mem_closedBall] using h0
  have b_lim : Tendsto (fun r : ℝ => L * r) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_const.mul continuous_id).tendsto (0 : ℝ))
  have H : Equicontinuous ((↑) : A → Xm m → ℂ) := by
    refine Metric.equicontinuous_of_continuity_modulus (b := fun r : ℝ => L * r) b_lim
      ((↑) : A → Xm m → ℂ) ?_
    intro x y f
    rcases f with ⟨f, hf⟩
    rcases hf with ⟨n, rfl⟩
    simpa using lip n x y
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (s := s) hs (A := A) in_s H
  have hx : ∀ n, FnBC n ∈ closure A := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  rcases IsCompact.tendsto_subseq (s := closure A) hcomp hx with
    ⟨a, ha, φ, hφ, ht⟩
  refine ⟨φ, hφ, a, ?_⟩
  -- Convert `Tendsto` in `→ᵇ` into uniform convergence.
  have ht' : Tendsto (fun n => FnBC (φ n)) atTop (𝓝 a) := ht
  exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).1 ht'

/-! ### Specialization to Stieltjes transforms -/

section Stieltjes

/-- The Stieltjes kernel at a point of `KmC m` is integrable against any finite measure. -/
lemma integrable_kernel {m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] (z : Xm m) :
    Integrable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) μ := by
  -- measurability is enough for `AEStronglyMeasurable` in second countable spaces
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) μ := by
    have hmeas' : Measurable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) := by
      have h1 : Measurable (fun t : ℝ => (t : ℂ)) :=
        (Complex.continuous_ofReal.measurable : Measurable fun t : ℝ => (t : ℂ))
      exact measurable_const.div (h1.sub measurable_const)
    exact hmeas'.aestronglyMeasurable
  have hg : Integrable (fun _ : ℝ => (1 / δ m : ℝ)) μ := integrable_const (1 / δ m)
  refine Integrable.mono' hg hmeas ?_
  refine (Eventually.of_forall fun t => ?_)
  exact kernel_bound (m := m) (z := (z : ℂ)) z.property.2.1 t

/-- The Stieltjes transform on `KmC m` is bounded by total mass times `1 / δ m`. -/
lemma stieltjes_norm_le {m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] (z : Xm m) :
    ‖stieltjes μ (toUHP m z)‖ ≤ (1 / δ m) * μ.real univ := by
  have h :
      ∀ᵐ t : ℝ ∂μ, ‖(1 / ((t : ℂ) - (z : ℂ)))‖ ≤ (1 / δ m) :=
    (Eventually.of_forall fun t : ℝ =>
      kernel_bound (m := m) (z := (z : ℂ)) z.property.2.1 t)
  -- `toUHP m z` coerces back to `z : ℂ`
  simpa [stieltjes, toUHP] using
    (norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ))))
      (C := (1 / δ m)) h)

/-- The Stieltjes transform is Lipschitz on `KmC m` with constant `μ.real univ / δ m ^ 2`. -/
lemma stieltjes_dist_le {m : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] (z w : Xm m) :
    dist (stieltjes μ (toUHP m z)) (stieltjes μ (toUHP m w)) ≤
      (μ.real univ / (δ m) ^ 2) * dist z w := by
  have hz : δ m ≤ (z : ℂ).im := z.property.2.1
  have hw : δ m ≤ (w : ℂ).im := w.property.2.1
  have hIntZ :
      Integrable (fun t : ℝ => (1 / ((t : ℂ) - (z : ℂ)))) μ :=
    integrable_kernel (m := m) μ z
  have hIntW :
      Integrable (fun t : ℝ => (1 / ((t : ℂ) - (w : ℂ)))) μ :=
    integrable_kernel (m := m) μ w
  have hsub :
      stieltjes μ (toUHP m z) - stieltjes μ (toUHP m w) =
        ∫ t : ℝ, (1 / ((t : ℂ) - (z : ℂ)) - 1 / ((t : ℂ) - (w : ℂ))) ∂μ := by
    simpa [stieltjes, toUHP] using (integral_sub hIntZ hIntW).symm
  have hdiff :
      ∀ᵐ t : ℝ ∂μ,
        ‖(1 / ((t : ℂ) - (z : ℂ)) - 1 / ((t : ℂ) - (w : ℂ)))‖ ≤
          ‖(z : ℂ) - (w : ℂ)‖ / (δ m) ^ 2 :=
    (Eventually.of_forall fun t : ℝ =>
      kernel_diff_bound (m := m) (z := (z : ℂ)) (w := (w : ℂ)) hz hw t)
  have hnorm :
      ‖∫ t : ℝ, (1 / ((t : ℂ) - (z : ℂ)) - 1 / ((t : ℂ) - (w : ℂ))) ∂μ‖ ≤
        (‖(z : ℂ) - (w : ℂ)‖ / (δ m) ^ 2) * μ.real univ :=
    norm_integral_le_of_norm_le_const (μ := μ) (f := fun t : ℝ =>
      (1 / ((t : ℂ) - (z : ℂ)) - 1 / ((t : ℂ) - (w : ℂ))))
      (C := ‖(z : ℂ) - (w : ℂ)‖ / (δ m) ^ 2) hdiff
  have hdist : dist (stieltjes μ (toUHP m z)) (stieltjes μ (toUHP m w)) =
      ‖stieltjes μ (toUHP m z) - stieltjes μ (toUHP m w)‖ := by
    simp [dist_eq_norm]
  -- move to the integral bound
  have : dist (stieltjes μ (toUHP m z)) (stieltjes μ (toUHP m w)) ≤
      (‖(z : ℂ) - (w : ℂ)‖ / (δ m) ^ 2) * μ.real univ := by
    simpa [hdist, hsub] using hnorm
  -- rewrite the right hand side into `L * dist z w`
  have hwz : ‖(z : ℂ) - (w : ℂ)‖ = dist z w := by
    simp [Subtype.dist_eq, dist_eq_norm]
  -- finalize
  calc
    dist (stieltjes μ (toUHP m z)) (stieltjes μ (toUHP m w))
        ≤ (‖(z : ℂ) - (w : ℂ)‖ / (δ m) ^ 2) * μ.real univ := this
    _ = (μ.real univ / (δ m) ^ 2) * dist z w := by
          simp [hwz, mul_left_comm, mul_comm, div_eq_mul_inv]

/--
Uniform mass bounds give a uniformly convergent subsequence of Stieltjes transforms on `Xm m`.
-/
theorem subseq_tendstoUniformly_stieltjes_of_mass_bound (μn : ℕ → Measure ℝ)
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) (m : ℕ) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∃ Gm : Xm m →ᵇ ℂ,
          TendstoUniformly (fun n x => stieltjes (μn (φ n)) (toUHP m x)) Gm atTop := by
  classical
  rcases hmass with ⟨M0, hMfin, hμle⟩
  let M : ℝ := M0.toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hMne : M0 ≠ ⊤ := ne_of_lt hMfin
  have hμreal_le : ∀ n, (μn n).real univ ≤ M := by
    intro n
    have : (μn n univ).toReal ≤ M0.toReal := ENNReal.toReal_mono hMne (hμle n)
    simpa [Measure.real, M] using this
  let R : ℝ := (1 / δ m) * M
  let L : ℝ := M / (δ m) ^ 2
  have hδ : 0 < δ m := delta_pos m
  have hL0 : 0 ≤ L := by
    have : 0 < (δ m) ^ 2 := sq_pos_of_pos hδ
    have : 0 ≤ (δ m) ^ 2 := le_of_lt this
    exact div_nonneg hM0 this
  -- define the sequence in `→ᵇ` using `mkOfCompact`
  let Fn : ℕ → Xm m → ℂ := fun n x => stieltjes (μn n) (toUHP m x)
  have hLip : ∀ n, LipschitzWith ⟨L, hL0⟩ (Fn n) := by
    intro n
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hnfin : μn n univ < ⊤ := lt_of_le_of_lt (hμle n) hMfin
    letI : IsFiniteMeasure (μn n) := ⟨hnfin⟩
    have hdist' :
        dist (Fn n x) (Fn n y) ≤ ((μn n).real univ / (δ m) ^ 2) * dist x y :=
      stieltjes_dist_le (m := m) (μ := μn n) x y
    have hμ' : (μn n).real univ / (δ m) ^ 2 ≤ L := by
      have hδ2 : 0 < (δ m) ^ 2 := sq_pos_of_pos hδ
      have hδ2' : 0 ≤ (δ m) ^ 2 := le_of_lt hδ2
      have : (μn n).real univ ≤ M := hμreal_le n
      have : (μn n).real univ / (δ m) ^ 2 ≤ M / (δ m) ^ 2 :=
        div_le_div_of_nonneg_right this hδ2'
      simpa [L] using this
    have hx : 0 ≤ dist x y := dist_nonneg
    have := mul_le_mul_of_nonneg_right hμ' hx
    exact le_trans hdist' (by simpa [mul_assoc] using this)
  let FnC : ℕ → C(Xm m, ℂ) := fun n => ⟨Fn n, (hLip n).continuous⟩
  let FnBC : ℕ → Xm m →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact (FnC n)
  have in_ball : ∀ n x, ‖FnBC n x‖ ≤ R := by
    intro n x
    have hnfin : μn n univ < ⊤ := lt_of_le_of_lt (hμle n) hMfin
    letI : IsFiniteMeasure (μn n) := ⟨hnfin⟩
    have h0 : ‖Fn n x‖ ≤ (1 / δ m) * (μn n).real univ :=
      stieltjes_norm_le (m := m) (μ := μn n) x
    have hμ' : (μn n).real univ ≤ M := hμreal_le n
    have hδ0 : 0 ≤ (1 / δ m) := by exact le_of_lt (one_div_pos.2 hδ)
    have : (1 / δ m) * (μn n).real univ ≤ (1 / δ m) * M := by
      exact mul_le_mul_of_nonneg_left hμ' hδ0
    simpa [FnBC, FnC, Fn, R, mul_assoc] using le_trans h0 this
  have lip : ∀ n x y, dist (FnBC n x) (FnBC n y) ≤ L * dist x y := by
    intro n x y
    have hnfin : μn n univ < ⊤ := lt_of_le_of_lt (hμle n) hMfin
    letI : IsFiniteMeasure (μn n) := ⟨hnfin⟩
    -- start from the `μn n`-dependent Lipschitz bound and push it to `L`
    have hdist' :
        dist (Fn n x) (Fn n y) ≤ ((μn n).real univ / (δ m) ^ 2) * dist x y :=
      stieltjes_dist_le (m := m) (μ := μn n) x y
    have hμ' : (μn n).real univ / (δ m) ^ 2 ≤ L := by
      have hδ2 : 0 < (δ m) ^ 2 := sq_pos_of_pos hδ
      have hδ2' : 0 ≤ (δ m) ^ 2 := le_of_lt hδ2
      have : (μn n).real univ ≤ M := hμreal_le n
      have : (μn n).real univ / (δ m) ^ 2 ≤ M / (δ m) ^ 2 :=
        (div_le_div_of_nonneg_right this hδ2')
      simpa [L] using this
    have hx : 0 ≤ dist x y := dist_nonneg
    have := mul_le_mul_of_nonneg_right hμ' hx
    have : ((μn n).real univ / (δ m) ^ 2) * dist x y ≤ L * dist x y := by
      simpa [mul_assoc] using this
    have htotal : dist (Fn n x) (Fn n y) ≤ L * dist x y := le_trans hdist' this
    simpa [FnBC, FnC, Fn] using htotal
  rcases
      subseq_tendstoUniformly_of_bounds (m := m) FnBC R L in_ball lip with
    ⟨φ, hφ, Gm, hconv⟩
  refine ⟨φ, hφ, Gm, ?_⟩
  simpa [FnBC, FnC, Fn] using hconv

end Stieltjes

end

end Quantum.TraceInequality.Loewner
