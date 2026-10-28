import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.IocUniformStepCore

/-!
# Chapter 20 uniform Ioc step exact volume-pairing handoff

This file contains the exact cover, left-endpoint representative volume
integral, domination, and a.e. convergence pieces completing the uniform
Ioc step Stieltjes/BV pairing argument.
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

/-- The uniform half-open atoms cover exactly the regularization window. -/
theorem hiaiIocUniformStep_atoms_iUnion_eq_window
    {ε x : ℝ} (hε : 0 < ε) (n : ℕ) :
    (⋃ k ∈ Finset.range (n + 1),
        Set.Ioc
          (hiaiIocUniformStepLeft ε x n k)
          (hiaiIocUniformStepRight ε x n k)) =
      Set.Ioc (x - ε) (x + ε) := by
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨k, hyk⟩
    rcases Set.mem_iUnion.mp hyk with ⟨hk, hyatom⟩
    exact hiaiIocUniformStep_mem_window_of_mem_atom
      (ε := ε) (x := x) hε.le (n := n) (k := k) hk hyatom
  · intro hy
    rcases hiaiIocUniformStep_exists_atom_of_mem_window
        (ε := ε) (x := x) hε (n := n) hy with ⟨k, hk, hyatom⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hyatom⟩⟩

/--
On a single atom, the left-endpoint representative is constant, so the atom
integral is the usual interval integral with that constant value.
-/
theorem hiaiIocUniformStep_leftRep_atom_intervalIntegral_eq
    {φ G : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) (n k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) :
    (∫ y in Set.Ioc
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k),
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hiaiIocUniformStepLeftRep G ε x n y) =
      ∫ y in
        hiaiIocUniformStepLeft ε x n k..
        hiaiIocUniformStepRight ε x n k,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          G (hiaiIocUniformStepLeft ε x n k) := by
  have hle :
      hiaiIocUniformStepLeft ε x n k ≤
        hiaiIocUniformStepRight ε x n k :=
    hiaiIocUniformStep_left_le_right
      (ε := ε) (x := x) hε (n := n) (k := k)
  rw [intervalIntegral.integral_of_le hle]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  rw [hiaiIocUniformStepLeftRep_eq_value_of_mem_atom
    (G := G) (ε := ε) (x := x) hε (n := n) (k := k) hk hy]

/--
The left-endpoint representative volume integral over the window is the finite
sum of the corresponding atom interval integrals.
-/
theorem hiaiIocUniformStep_leftRep_volumeIntegral_eq_sum
    {φ G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hiaiIocUniformStepLeftRep G ε x n y) =
      ∑ k ∈ Finset.range (n + 1),
        ∫ y in
          hiaiIocUniformStepLeft ε x n k..
          hiaiIocUniformStepRight ε x n k,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            G (hiaiIocUniformStepLeft ε x n k) := by
  let atom : ℕ → Set ℝ := fun k =>
    Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)
  let f : ℝ → ℝ := fun y =>
    (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
      hiaiIocUniformStepLeftRep G ε x n y
  have hwin_le : x - ε ≤ x + ε := by linarith
  have hcover : (⋃ k ∈ Finset.range (n + 1), atom k) =
      Set.Ioc (x - ε) (x + ε) := by
    simpa [atom] using
      hiaiIocUniformStep_atoms_iUnion_eq_window
        (ε := ε) (x := x) hε n
  have hpair :
      Set.Pairwise (↑(Finset.range (n + 1)))
        (fun j k => Disjoint (atom j) (atom k)) := by
    intro j hj k hk hjk
    exact hiaiIocUniformStep_atoms_disjoint
      (ε := ε) (x := x) hε.le (n := n) hjk
  have hf_int :
      ∀ k ∈ Finset.range (n + 1), IntegrableOn f (atom k) volume := by
    intro k hk
    have hle :
        hiaiIocUniformStepLeft ε x n k ≤
          hiaiIocUniformStepRight ε x n k :=
      hiaiIocUniformStep_left_le_right
        (ε := ε) (x := x) hε.le (n := n) (k := k)
    have hcont :
        Continuous
          (fun y : ℝ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              G (hiaiIocUniformStepLeft ε x n k)) :=
      (hiaiScaledMollifierWeight_deriv_y_continuous
        (φ := φ) (ε := ε) (x := x) hφ).neg.mul continuous_const
    have hint :
        IntegrableOn
          (fun y : ℝ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              G (hiaiIocUniformStepLeft ε x n k))
          (atom k) volume := by
      rw [show atom k =
          Set.Ioc
            (hiaiIocUniformStepLeft ε x n k)
            (hiaiIocUniformStepRight ε x n k) by rfl]
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact hcont.intervalIntegrable _ _
    refine hint.congr_fun ?_ (by simp [atom])
    intro y hy
    simp only [f, atom] at hy ⊢
    rw [hiaiIocUniformStepLeftRep_eq_value_of_mem_atom
      (G := G) (ε := ε) (x := x) hε.le (n := n) (k := k) hk hy]
  calc
    (∫ y in x - ε..x + ε, f y) =
        ∫ y in Set.Ioc (x - ε) (x + ε), f y := by
          rw [intervalIntegral.integral_of_le hwin_le]
    _ = ∫ y in ⋃ k ∈ Finset.range (n + 1), atom k, f y := by
          rw [hcover]
    _ = ∑ k ∈ Finset.range (n + 1), ∫ y in atom k, f y := by
          exact integral_biUnion_finset
            (Finset.range (n + 1))
            (fun k _hk => by simp [atom])
            hpair hf_int
    _ = ∑ k ∈ Finset.range (n + 1),
        ∫ y in
          hiaiIocUniformStepLeft ε x n k..
          hiaiIocUniformStepRight ε x n k,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            G (hiaiIocUniformStepLeft ε x n k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa [atom, f] using
            hiaiIocUniformStep_leftRep_atom_intervalIntegral_eq
              (φ := φ) (G := G) (ε := ε) (x := x) hε.le n k hk

/--
Concrete exact input for the finite-increment / volume-pairing handoff: the
uniform increment sum is exactly the left-endpoint representative volume
integral.
-/
theorem hiaiIocUniformStep_increment_sum_eq_leftRep_volumeIntegral
    {φ G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      hiaiIocUniformStepWeight φ ε x n k *
        (G (hiaiIocUniformStepRight ε x n k) -
          G (hiaiIocUniformStepLeft ε x n k))) =
      ∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hiaiIocUniformStepLeftRep G ε x n y := by
  rw [hiaiIocUniformStep_increment_sum_summationByParts
    (φ := φ) (G := G) hφ hε n]
  rw [hiaiIocUniformStep_leftRep_volumeIntegral_eq_sum
    (φ := φ) (G := G) hφ hε n]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [hiaiIocUniformStep_weight_increment_eq_deriv_integral
    (φ := φ) hφ (ε := ε) (x := x) n k]
  rw [intervalIntegral.integral_mul_const
    (r := G (hiaiIocUniformStepLeft ε x n k))
    (f := fun y : ℝ =>
      -deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y)]
  rw [intervalIntegral.integral_neg]
  ring

/--
Uniform-mesh finite-increment convergence with the exact Abel algebra supplied.
The only analytic input is convergence of the left-endpoint representative
volume integrals, which is `hiaiIocUniformStep_leftRep_volumeIntegral_tendsto`
below.
-/
theorem hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_leftRep_exact
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hLeft :
      Tendsto
        (fun n : ℕ =>
          ∫ y in x - ε..x + ε,
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y))) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          hiaiIocUniformStepWeight φ ε x n k *
            (hg.stieltjesFunction
                (hiaiIocUniformStepRight ε x n k) -
              hg.stieltjesFunction
                (hiaiIocUniformStepLeft ε x n k)))
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  exact
    hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_leftRep
      (φ := φ) (g := g) (ε := ε) (x := x) hg
      (Eventually.of_forall fun n =>
        hiaiIocUniformStep_increment_sum_eq_leftRep_volumeIntegral
          (φ := φ) (G := hg.stieltjesFunction) hφ hε n)
      hLeft

/-- The left-endpoint representative is a finite measurable step function. -/
theorem hiaiIocUniformStepLeftRep_aestronglyMeasurable
    {G : ℝ → ℝ} {ε x : ℝ} (n : ℕ) (μ : Measure ℝ) :
    AEStronglyMeasurable
      (fun y : ℝ => hiaiIocUniformStepLeftRep G ε x n y) μ := by
  unfold hiaiIocUniformStepLeftRep
  measurability

/--
The leftRep integrand in the dominated-convergence handoff is strongly
measurable.  The genuinely analytic inputs left for the next step are the
uniform bound and a.e. convergence, not measurability.
-/
theorem hiaiIocUniformStepLeftRep_integrand_aestronglyMeasurable
    {φ G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (n : ℕ) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hiaiIocUniformStepLeftRep G ε x n y)
      (volume.restrict (Set.Ioc (x - ε) (x + ε))) := by
  have hderiv_meas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          -deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y)
        (volume.restrict (Set.Ioc (x - ε) (x + ε))) :=
    (hiaiScaledMollifierWeight_deriv_y_continuous
      (φ := φ) (ε := ε) (x := x) hφ).neg.aestronglyMeasurable
  exact hderiv_meas.mul
    (hiaiIocUniformStepLeftRep_aestronglyMeasurable
      (G := G) (ε := ε) (x := x) n
      (volume.restrict (Set.Ioc (x - ε) (x + ε))))

/--
The right-continuous Stieltjes representative of a monotone function is bounded
on the compact regularization window by its endpoint values.
-/
theorem hiaiStieltjesFunction_abs_bound_on_window
    {g : ℝ → ℝ} (hg : Monotone g) {ε x y : ℝ}
    (hy : y ∈ Set.Icc (x - ε) (x + ε)) :
    |hg.stieltjesFunction y| ≤
      max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)| := by
  exact abs_le_max_abs_abs (hg.stieltjesFunction.mono hy.1)
    (hg.stieltjesFunction.mono hy.2)

/-- The left endpoint of a valid uniform atom lies in the compact window. -/
theorem hiaiIocUniformStep_left_mem_window
    {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ}
    (hk : k ∈ Finset.range (n + 1)) :
    hiaiIocUniformStepLeft ε x n k ∈
      Set.Icc (x - ε) (x + ε) := by
  have hwidth_nonneg : 0 ≤ hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_nonneg (ε := ε) hε n
  have hleft_ge :
      x - ε ≤ hiaiIocUniformStepLeft ε x n k := by
    unfold hiaiIocUniformStepLeft
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hwidth_nonneg)
  have hk_le : k ≤ n + 1 := by
    exact Nat.le_of_lt (Finset.mem_range.mp hk)
  have hk_cast : ((k : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hk_le
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hquot_nonneg : 0 ≤ (2 * ε) / ((n + 1 : ℕ) : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hε) hden_pos.le
  have hmul_le :
      ((k : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) ≤
        ((n + 1 : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hk_cast hquot_nonneg
  have hden_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hmul_eval :
      ((n + 1 : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) = 2 * ε := by
    field_simp [hden_ne]
  have hleft_le : hiaiIocUniformStepLeft ε x n k ≤ x + ε := by
    unfold hiaiIocUniformStepLeft hiaiIocUniformStepWidth
    rw [hmul_eval] at hmul_le
    nlinarith
  exact ⟨hleft_ge, hleft_le⟩

/--
Every left endpoint used by the uniform half-open representative lies in the
regularization window, so the monotone endpoint bound controls the representative
pointwise on the window.
-/
theorem hiaiIocUniformStepLeftRep_abs_bound_on_window
    {g : ℝ → ℝ} (hg : Monotone g) {ε x y : ℝ} (hε : 0 < ε)
    (n : ℕ) (hy : y ∈ Set.Ioc (x - ε) (x + ε)) :
    |hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y| ≤
      max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)| := by
  rcases hiaiIocUniformStep_exists_atom_of_mem_window
      (ε := ε) (x := x) hε (n := n) hy with ⟨k, hk, hyatom⟩
  rw [hiaiIocUniformStepLeftRep_eq_value_of_mem_atom
    (G := hg.stieltjesFunction) (ε := ε) (x := x) hε.le (n := n) (k := k) hk hyatom]
  have hleft_mem :
      hiaiIocUniformStepLeft ε x n k ∈
        Set.Icc (x - ε) (x + ε) := by
    exact hiaiIocUniformStep_left_mem_window
      (ε := ε) (x := x) hε.le (n := n) (k := k) hk
  exact hiaiStieltjesFunction_abs_bound_on_window
    (g := g) hg hleft_mem

/--
The leftRep integrands are uniformly dominated by the absolute derivative of
the scaled weight times the endpoint bound of the Stieltjes representative.
-/
theorem hiaiIocUniformStepLeftRep_integrand_bound_on_window
    {φ g : ℝ → ℝ} (hg : Monotone g) {ε x : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
      ‖(-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y‖ ≤
        |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
          max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)| := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have hrep :=
    hiaiIocUniformStepLeftRep_abs_bound_on_window
      (g := g) hg hε n hy
  calc
    ‖(-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
        hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y‖
        = |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
            |hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y| := by
          simp [Real.norm_eq_abs]
    _ ≤ |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
          max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)| := by
          exact mul_le_mul_of_nonneg_left hrep (abs_nonneg _)

/-- The natural domination function for the leftRep volume integrals is integrable. -/
theorem hiaiIocUniformStepLeftRep_bound_integrable_on_window
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ) (hg : Monotone g)
    {ε x : ℝ} :
    Integrable
      (fun y : ℝ =>
        |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
          max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)|)
      (volume.restrict (Set.Ioc (x - ε) (x + ε))) := by
  have hcont :
      Continuous
        (fun y : ℝ =>
          |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
            max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)|) :=
    (hiaiScaledMollifierWeight_deriv_y_continuous
      (φ := φ) (ε := ε) (x := x) hφ).abs.mul continuous_const
  exact hcont.integrableOn_Ioc

/--
LeftRep volume-integral convergence after all domination data have been supplied
from monotonicity and smoothness.  The sole analytic input is the pointwise
a.e. convergence of the left-endpoint representatives, which is
`hiaiIocUniformStepLeftRep_integrand_tendsto_ae_stieltjesFunction` below; the
combined statement is `hiaiIocUniformStep_leftRep_volumeIntegral_tendsto`.
-/
theorem hiaiIocUniformStep_leftRep_volumeIntegral_tendsto_of_ae_tendsto
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (h_lim :
      ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
        Tendsto
          (fun n : ℕ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
          atTop
          (𝓝
            ((-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hg.stieltjesFunction y))) :
    Tendsto
      (fun n : ℕ =>
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  have hle : x - ε ≤ x + ε := by linarith
  simpa [intervalIntegral.integral_of_le hle] using
    hiaiIocUniformStep_leftRep_volumeIntegral_tendsto_of_dominated
      (φ := φ) (G := hg.stieltjesFunction) (ε := ε) (x := x)
      (bound := fun y : ℝ =>
        |deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y| *
          max |hg.stieltjesFunction (x - ε)| |hg.stieltjesFunction (x + ε)|)
      (fun n =>
        hiaiIocUniformStepLeftRep_integrand_aestronglyMeasurable
          (φ := φ) (G := hg.stieltjesFunction) hφ (ε := ε) (x := x) n)
      (fun n =>
        hiaiIocUniformStepLeftRep_integrand_bound_on_window
          (φ := φ) (g := g) hg hε n)
      (hiaiIocUniformStepLeftRep_bound_integrable_on_window
        (φ := φ) (g := g) hφ hg (ε := ε) (x := x))
      h_lim

/--
Concrete `hPairing` input for the uniform-step Stieltjes IBP, reduced to the
a.e. convergence statement for the left-endpoint representatives
(`hiaiIocUniformStepLeftRep_integrand_tendsto_ae_stieltjesFunction` below).  The
version without this hypothesis is
`hiaiIocUniformStep_increment_sum_tendsto_volumePairing`.
-/
theorem hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_ae_tendsto
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (h_lim :
      ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
        Tendsto
          (fun n : ℕ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
          atTop
          (𝓝
            ((-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hg.stieltjesFunction y))) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          hiaiIocUniformStepWeight φ ε x n k *
            (hg.stieltjesFunction
                (hiaiIocUniformStepRight ε x n k) -
              hg.stieltjesFunction
                (hiaiIocUniformStepLeft ε x n k)))
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  exact
    hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_leftRep_exact
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStep_leftRep_volumeIntegral_tendsto_of_ae_tendsto
        (φ := φ) (g := g) hφ hε hg h_lim)

/--
Uniform-step Stieltjes integration-by-parts with all finite-step and domination
data supplied.  The input is exactly the leftRep a.e. convergence on the
regularization window; the version without it is
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed` below.
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_ae
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (h_lim :
      ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
        Tendsto
          (fun n : ℕ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
          atTop
          (𝓝
            ((-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hg.stieltjesFunction y))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_ae_tendsto
        (φ := φ) (g := g) hφ hε hg h_lim)

/--
At every continuity point of `G`, the uniform left-endpoint representative
converges pointwise to `G y` on the half-open regularization window.
-/
theorem hiaiIocUniformStepLeftRep_tendsto_of_continuousAt
    {G : ℝ → ℝ} {ε x y : ℝ} (hε : 0 < ε)
    (hy : y ∈ Set.Ioc (x - ε) (x + ε))
    (hcont : ContinuousAt G y) :
    Tendsto
      (fun n : ℕ => hiaiIocUniformStepLeftRep G ε x n y)
      atTop (𝓝 (G y)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  rcases (Metric.continuousAt_iff.mp hcont) δ hδ with ⟨η, hη, hG⟩
  have hwidth_eventually :
      ∀ᶠ n in atTop, hiaiIocUniformStepWidth ε n < η := by
    have hdist_eventually :=
      (Metric.tendsto_nhds.mp
        (hiaiIocUniformStepWidth_tendsto_zero ε)) η hη
    filter_upwards [hdist_eventually] with n hn
    have hwidth_nonneg :
        0 ≤ hiaiIocUniformStepWidth ε n :=
      hiaiIocUniformStepWidth_nonneg (ε := ε) hε.le n
    simpa [Real.dist_eq, abs_of_nonneg hwidth_nonneg] using hn
  filter_upwards [hwidth_eventually] with n hwidth_lt
  rcases hiaiIocUniformStep_exists_atom_of_mem_window
      (ε := ε) (x := x) hε (n := n) hy with ⟨k, hk, hyatom⟩
  rw [hiaiIocUniformStepLeftRep_eq_value_of_mem_atom
    (G := G) (ε := ε) (x := x) hε.le (n := n) (k := k) hk hyatom]
  have hdist_le :
      dist (hiaiIocUniformStepLeft ε x n k) y ≤
        hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStep_left_dist_le_width_of_mem_atom
      (ε := ε) (x := x) hε.le (n := n) (k := k) hyatom
  exact hG (lt_of_le_of_lt hdist_le hwidth_lt)

/--
For a monotone function, the uniform left-endpoint representative converges
a.e. on the regularization window to the right-continuous Stieltjes
representative.  The exceptional set is the countable discontinuity set of that
monotone representative.
-/
theorem hiaiIocUniformStepLeftRep_tendsto_ae_stieltjesFunction
    {g : ℝ → ℝ} (hg : Monotone g) {ε x : ℝ} (hε : 0 < ε) :
    ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
      Tendsto
        (fun n : ℕ =>
          hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
        atTop (𝓝 (hg.stieltjesFunction y)) := by
  have hcont_volume :
      ∀ᵐ y ∂volume, ContinuousAt (fun z : ℝ => hg.stieltjesFunction z) y := by
    filter_upwards
      [hg.stieltjesFunction.mono.countable_not_continuousAt.ae_notMem volume]
      with y hy
    simpa [Set.mem_setOf_eq] using hy
  have hcont_restrict :
      ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
        ContinuousAt (fun z : ℝ => hg.stieltjesFunction z) y :=
    MeasureTheory.ae_restrict_of_ae hcont_volume
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hcont_restrict] with y hywin hcont
  exact hiaiIocUniformStepLeftRep_tendsto_of_continuousAt
    (G := hg.stieltjesFunction) (ε := ε) (x := x) hε hywin hcont

/--
The integrands in the leftRep DCT handoff converge a.e. after multiplying by
the fixed smooth derivative factor.
-/
theorem hiaiIocUniformStepLeftRep_integrand_tendsto_ae_stieltjesFunction
    {φ g : ℝ → ℝ} (hg : Monotone g) {ε x : ℝ} (hε : 0 < ε) :
    ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
      Tendsto
        (fun n : ℕ =>
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
        atTop
        (𝓝
          ((-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y)) := by
  filter_upwards
    [hiaiIocUniformStepLeftRep_tendsto_ae_stieltjesFunction
      (g := g) hg (ε := ε) (x := x) hε]
    with y hy
  exact Filter.Tendsto.const_mul
    (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) hy

/--
Concrete convergence of the left-endpoint representative volume integrals,
with the a.e. convergence now supplied from the countable discontinuity set of
the Stieltjes representative.
-/
theorem hiaiIocUniformStep_leftRep_volumeIntegral_tendsto
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    Tendsto
      (fun n : ℕ =>
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  exact
    hiaiIocUniformStep_leftRep_volumeIntegral_tendsto_of_ae_tendsto
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStepLeftRep_integrand_tendsto_ae_stieltjesFunction
        (φ := φ) (g := g) hg (ε := ε) (x := x) hε)

/-- Concrete convergence of the uniform finite increment sums to the volume pairing. -/
theorem hiaiIocUniformStep_increment_sum_tendsto_volumePairing
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          hiaiIocUniformStepWeight φ ε x n k *
            (hg.stieltjesFunction
                (hiaiIocUniformStepRight ε x n k) -
              hg.stieltjesFunction
                (hiaiIocUniformStepLeft ε x n k)))
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  exact
    hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_leftRep_exact
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStep_leftRep_volumeIntegral_tendsto
        (φ := φ) (g := g) hφ hε hg)

/--
Uniform-step Stieltjes integration-by-parts with the leftRep a.e. convergence
closed.  This is the full `hibp` input produced by the finite `Ioc` step
approximation layer.
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStep_increment_sum_tendsto_volumePairing
        (φ := φ) (g := g) hφ hε hg)

/--
The same window-local diagnostic in the final `hibp` shape used by downstream
regularization handoffs.  The proof combines the support-window reduction with
the a.e. replacement of the right-continuous representative by the original
monotone function.
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_windowPairing
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hwindowPairing :
      (∫ y in Set.Icc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_rightContinuousRep
      (φ := φ) (g := g) (ε := ε) (x := x) hg
      (hiaiScaledMollifierWeight_BVPairing_rightContinuousRep_of_windowPairing
        (φ := φ) (g := g) hφ hε hg hwindowPairing)


end

end Quantum.TraceInequality.Loewner
