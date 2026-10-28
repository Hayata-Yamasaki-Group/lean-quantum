import Quantum.QuantumEntropy.SandwichedRenyiLMCompat.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Quantum.QuantumEntropy.GourSemiCausalMemory.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Jensen
import Mathlib
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
/-
One-sided compact minimax, approximate saddle points, and separation.
Source: Gour, Examples 7.24 and 7.25.
-/

open QuantumState QuantumChannel GourConditionalEntropy SandwichedRenyiRelativeEntropy
open scoped TensorProduct ComplexOrder BigOperators ENNReal Topology
universe u

namespace SandwichedRenyiRelativeEntropy

set_option autoImplicit false

-- Private auxiliary lemmas for the minimax argument below.
private theorem finite_separation_weights {F I : Type*} [AddCommGroup F] [Module ℝ F]
    [Fintype I] (T : Set F) (hT : Convex ℝ T) (hne : T.Nonempty)
    (q : I → F → ℝ) (hq : ∀ i, ConcaveOn ℝ T (q i)) (r : ℝ)
    (hno : ¬ ∃ y ∈ T, ∀ i, r < q i y) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ y ∈ T, (∑ i, w i * q i y) ≤ r := by
  classical
  let U : Set (I → ℝ) := {v | ∃ y ∈ T, ∀ i, v i < q i y}
  have hU : Convex ℝ U := by
    rintro v ⟨y, hy, hv⟩ z ⟨y', hy', hz⟩ a b ha hb hab
    refine ⟨a • y + b • y', hT hy hy' ha hb hab, fun i => ?_⟩
    have hc := (hq i).2 hy hy' ha hb hab
    change a * v i + b * z i < q i (a • y + b • y')
    change a * q i y + b * q i y' ≤ _ at hc
    rcases ha.eq_or_lt with rfl | ha
    · have hb1 : b = 1 := by linarith
      simpa only [hb1, zero_mul, one_mul, zero_smul, one_smul, zero_add] using hz i
    · have h1 := mul_lt_mul_of_pos_left (hv i) ha
      have h2 := mul_le_mul_of_nonneg_left (hz i).le hb
      linarith
  have hUo : IsOpen U := by
    have he : U = ⋃ y ∈ T, ⋂ i, {v : I → ℝ | v i < q i y} := by
      ext v
      simp only [U, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    rw [he]
    exact isOpen_iUnion fun y => isOpen_iUnion fun _ =>
      isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point hU hUo hno
  obtain ⟨y0, hy0⟩ := hne
  let v0 : I → ℝ := fun i => q i y0 - 1
  have hv0 : v0 ∈ U := ⟨y0, hy0, fun i => by dsimp [v0]; linarith⟩
  have hl0 := hl v0 hv0
  have hld : ∀ d : I → ℝ, (∀ i, d i ≤ 0) → l d ≤ 0 := by
    intro d hd
    by_contra! hpos
    let a := (l (fun _ => r) - l v0 + 1) / l d
    have ha : 0 ≤ a := le_of_lt (div_pos (by linarith) hpos)
    have hv : v0 + a • d ∈ U := by
      refine ⟨y0, hy0, fun i => ?_⟩
      have hh := mul_nonpos_of_nonneg_of_nonpos ha (hd i)
      change q i y0 - 1 + a * d i < q i y0
      linarith
    have hh := hl (v0 + a • d) hv
    rw [map_add, map_smul] at hh
    change l v0 + a * l d < l (fun _ => r) at hh
    dsimp only [a] at hh
    rw [div_mul_cancel₀ _ hpos.ne'] at hh
    linarith
  let c : I → ℝ := fun i => l (fun j => if i = j then 1 else 0)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    have hh := hld (-(fun j => if i = j then 1 else 0)) (by
      intro j
      simp only [Pi.neg_apply, neg_nonpos]
      split_ifs <;> norm_num)
    simpa only [map_neg, neg_nonpos, c] using hh
  have hlc (v : I → ℝ) : l v = ∑ i, c i * v i := by
    simpa only [c, smul_eq_mul, mul_comm] using
      LinearMap.pi_apply_eq_sum_univ l.toLinearMap v
  have hsum : 0 < ∑ i, c i := by
    have hn : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
    by_contra! hnp
    have hz : ∑ i, c i = 0 := le_antisymm hnp hn
    have hcz : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc j)).mp hz i (Finset.mem_univ i)
    simp only [hlc, hcz, zero_mul, Finset.sum_const_zero] at hl0
    exact lt_irrefl 0 hl0
  have hval : ∀ y ∈ T, l (fun i => q i y) ≤ l (fun _ => r) := by
    intro y hy
    by_contra! hgt
    let d := (l (fun i => q i y) - l (fun _ => r)) / (2 * ∑ i, c i)
    have hd : 0 < d := div_pos (sub_pos.mpr hgt) (mul_pos (by norm_num) hsum)
    have hv : (fun i => q i y - d) ∈ U := ⟨y, hy, fun i => by linarith⟩
    have hh := hl _ hv
    have he : l (fun i => q i y - d) = l (fun i => q i y) - d * ∑ i, c i := by
      simp only [hlc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_comm]
    rw [he] at hh
    have hdv : d * (2 * ∑ i, c i) = l (fun i => q i y) - l (fun _ => r) :=
      div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hsum))
    nlinarith
  refine ⟨fun i => c i / ∑ j, c j, fun i => div_nonneg (hc i) hsum.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hsum.ne']
  · intro y hy
    have hh := hval y hy
    rw [hlc, hlc, ← Finset.sum_mul] at hh
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_le_iff₀ hsum).mpr
    simpa only [mul_comm] using hh

private theorem finite_common_response {E F I : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [Finite I]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T) (hne : T.Nonempty)
    (f : E → F → ℝ) (hcv : ∀ y ∈ T, ConvexOn ℝ S (fun x => f x y))
    (hcc : ∀ x ∈ S, ConcaveOn ℝ T (f x)) (r : ℝ)
    (hr : ∀ x ∈ S, ∃ y ∈ T, r < f x y) (x : I → E) (hx : ∀ i, x i ∈ S) :
    ∃ y ∈ T, ∀ i, r < f (x i) y := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  by_contra hno
  obtain ⟨w, hw, hw1, hwy⟩ := finite_separation_weights T hT hne
    (fun i => f (x i)) (fun i => hcc (x i) (hx i)) r hno
  have hs : (∑ i, w i • x i) ∈ S :=
    hS.sum_mem (fun i _ => hw i) hw1 (fun i _ => hx i)
  obtain ⟨y, hy, hry⟩ := hr _ hs
  have hj := (hcv y hy).map_sum_le (fun i _ => hw i) hw1 (fun i _ => hx i)
  have hh := hwy y hy
  simp only [smul_eq_mul] at hj
  linarith

private theorem local_compact_common_response {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [T2Space F]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hcomp : IsCompact T) (hne : T.Nonempty) (f : E → F → ℝ)
    (hcv : ∀ y ∈ T, ConvexOn ℝ S (fun x => f x y))
    (hcc : ∀ x ∈ S, ConcaveOn ℝ T (f x))
    (hc : ∀ x ∈ S, ContinuousOn (f x) T) (r : ℝ)
    (hr : ∀ x ∈ S, ∃ y ∈ T, r < f x y) :
    ∃ y ∈ T, ∀ x ∈ S, r ≤ f x y := by
  classical
  let K : S → Set F := fun x => {y ∈ T | r ≤ f x.1 y}
  have hK : ∀ x, IsClosed (K x) := fun x =>
    hcomp.isClosed.isClosed_le continuousOn_const (hc x.1 x.2)
  have hfin : ∀ k : Finset S, (T ∩ ⋂ x ∈ k, K x).Nonempty := by
    intro k
    obtain ⟨y, hy, hxy⟩ := finite_common_response S T hS hT hne f hcv hcc r hr
      (fun i : k => i.1.1) (fun i => i.1.2)
    refine ⟨y, hy, ?_⟩
    simp only [Set.mem_iInter]
    intro x hx
    exact ⟨hy, (hxy ⟨x, hx⟩).le⟩
  obtain ⟨y, hy, hxy⟩ := hcomp.inter_iInter_nonempty K hK hfin
  exact ⟨y, hy, fun x hx => (Set.mem_iInter.mp hxy ⟨x, hx⟩).2⟩

-- A simultaneous approximate saddle point.
theorem compact_common_response :
  ∀ {E F : Type u} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T2Space F]
    (S : Set E) (T : Set F), S.Nonempty → Convex ℝ S →
    T.Nonempty → IsCompact T → Convex ℝ T →
  ∀ (f : E → F → ℝ),
    (∀ y ∈ T, ConvexOn ℝ S (fun x => f x y)) →
    (∀ x ∈ S, ConcaveOn ℝ T (f x)) →
    (∀ x ∈ S, ContinuousOn (f x) T) →
  ∀ r : ℝ, (∀ x ∈ S, ∃ y ∈ T, r < f x y) →
    ∃ y ∈ T, ∀ x ∈ S, r ≤ f x y := by
  intro E F _ _ _ _ _ _ S T _ hS hne hcomp hT f hcv hcc hc r hr
  exact local_compact_common_response S T hS hT hcomp hne f hcv hcc hc r hr

private def upperImage
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) : Set (F × ℝ) :=
  {z | ∃ y ∈ C, T y - z.1 ∈ D ∧ c y ≤ z.2}

private theorem upperImage_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ)
    {z w : F × ℝ} (hz : z ∈ upperImage C D T c)
    (hw : w ∈ upperImage C D T c) : z + w ∈ upperImage C D T c := by
  rcases hz with ⟨y, hy, hzy, hzn⟩
  rcases hw with ⟨v, hv, hwv, hwn⟩
  refine ⟨y + v, C.add_mem hy hv, ?_, ?_⟩
  · simpa only [map_add, Prod.fst_add, add_sub_add_comm] using D.add_mem hzy hwv
  · simpa only [map_add, Prod.snd_add] using add_le_add hzn hwn

private theorem upperImage_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ)
    {z : F × ℝ} (hz : z ∈ upperImage C D T c)
    {r : ℝ} (hr : 0 ≤ r) : r • z ∈ upperImage C D T c := by
  rcases hz with ⟨y, hy, hzy, hzn⟩
  refine ⟨r • y, C.smul_mem hr hy, ?_, ?_⟩
  · simpa only [map_smul, Prod.smul_fst, ← smul_sub] using D.smul_mem hr hzy
  · simpa only [map_smul, Prod.smul_snd, smul_eq_mul] using
      mul_le_mul_of_nonneg_left hzn hr

private theorem upperImage_convex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) : Convex ℝ (upperImage C D T c) := by
  intro z hz w hw a b ha hb _
  exact upperImage_add C D T c
    (upperImage_smul C D T c hz ha) (upperImage_smul C D T c hw hb)

private theorem upperImage_interior
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) (b : F)
    (hslater : ∃ y ∈ C, T y - b ∈ interior (D : Set F)) :
    (interior (upperImage C D T c)).Nonempty := by
  rcases hslater with ⟨y, hy, hslack⟩
  refine ⟨(b, c y + 1), mem_interior.mpr ?_⟩
  refine ⟨{z : F × ℝ | T y - z.1 ∈ interior (D : Set F) ∧ c y < z.2}, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨y, hy, interior_subset hz.1, hz.2.le⟩
  · exact (isOpen_interior.preimage (continuous_const.sub continuous_fst)).inter
      (isOpen_lt continuous_const continuous_snd)
  · exact ⟨hslack, by linarith⟩

private theorem upperImage_boundary
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) (b : F) (α : ℝ)
    (hminimal : ∀ t, (b, t) ∈ upperImage C D T c → α ≤ t) :
    (b, α) ∉ interior (upperImage C D T c) := by
  intro hint
  rcases Metric.isOpen_iff.1 isOpen_interior (b, α) hint with ⟨ε, hε, hball⟩
  have hzdist : dist (b, α - ε / 2) (b, α) < ε := by
    rw [Prod.dist_eq]
    simp only [dist_self, max_lt_iff, hε, true_and, Real.dist_eq,
      sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ε / 2)]
    linarith
  have hz := interior_subset (hball (by simpa only [Metric.mem_ball] using hzdist))
  have := hminimal (α - ε / 2) hz
  linarith

private theorem positive_functional_zero_at_interior
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Set F) (f : F →L[ℝ] ℝ) (hpos : ∀ z ∈ D, 0 ≤ f z)
    {x : F} (hx : x ∈ interior D) (hfx : f x = 0) : f = 0 := by
  rcases Metric.isOpen_iff.1 isOpen_interior x hx with ⟨ε, hε, hball⟩
  have hle (v : F) : f v ≤ 0 := by
    let r : ℝ := ε / (2 * (‖v‖ + 1))
    have hr : 0 < r := by dsimp [r]; positivity
    have hnorm : ‖r • v‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [r]
      apply (div_mul_eq_mul_div _ _ _).trans_lt
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).mpr
      nlinarith [norm_nonneg v]
    have hmem : x - r • v ∈ D := by
      apply interior_subset (hball ?_)
      simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hnorm
    have h := hpos _ hmem
    rw [map_sub, map_smul, hfx, smul_eq_mul, zero_sub, neg_nonneg] at h
    exact nonpos_of_mul_nonpos_right h hr
  ext v
  exact le_antisymm (hle v) (by simpa only [map_neg, neg_nonpos] using hle (-v))

private theorem functional_prod_decomposition
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : (F × ℝ) →L[ℝ] ℝ) (x : F) (t : ℝ) :
    G (x, t) = G (x, 0) + t * G (0, 1) := by
  have hp : (x, t) = (x, 0) + t • (0, 1) := by simp
  rw [hp, map_add, map_smul, smul_eq_mul]

private theorem linearMap_conicStrongDuality_attained_of_slater
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) (b : F) (yStar : E)
    (hyStar : yStar ∈ C) (hconstraint : T yStar - b ∈ D)
    (hminimal : ∀ y ∈ C, T y - b ∈ D → c yStar ≤ c y)
    (hslater : ∃ y ∈ C, T y - b ∈ interior (D : Set F)) :
    ∃ f : F →L[ℝ] ℝ,
      (∀ z ∈ D, 0 ≤ f z) ∧ (∀ y ∈ C, f (T y) ≤ c y) ∧ f b = c yStar := by
  let S := upperImage C D T c
  have hzero : (0 : F × ℝ) ∈ S := by
    exact ⟨0, C.zero_mem, by simp, by simp⟩
  have hstar : (b, c yStar) ∈ S := ⟨yStar, hyStar, hconstraint, le_rfl⟩
  have hbound : (b, c yStar) ∉ interior S := by
    apply upperImage_boundary C D T c
    rintro t ⟨y, hy, hcon, ht⟩
    exact (hminimal y hy hcon).trans ht
  obtain ⟨g, hgne, hsupport⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      (upperImage_convex C D T c) hbound (upperImage_interior C D T c b hslater)
  have hgstar : g (b, c yStar) = 0 := by
    have h0 := hsupport 0 hzero
    have h2 := hsupport ((2 : ℝ) • (b, c yStar))
      (upperImage_smul C D T c hstar (by norm_num))
    simp only [map_zero] at h0
    simp only [map_smul, smul_eq_mul] at h2
    linarith
  let G := -g
  have hGne : G ≠ 0 := neg_ne_zero.mpr hgne
  have hGpos (z : F × ℝ) (hz : z ∈ S) : 0 ≤ G z := by
    have := hsupport z hz
    change 0 ≤ -g z
    linarith
  have hGstar : G (b, c yStar) = 0 := by
    change -g (b, c yStar) = 0
    rw [hgstar, neg_zero]
  let f₀ : F →L[ℝ] ℝ := -(G.comp (ContinuousLinearMap.inl ℝ F ℝ))
  let β : ℝ := G (0, 1)
  have hdecomp (x : F) (t : ℝ) : G (x, t) = -f₀ x + t * β := by
    simpa only [f₀, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, neg_neg, β] using functional_prod_decomposition G x t
  have hβ : 0 ≤ β := by
    apply hGpos
    exact ⟨0, C.zero_mem, by simp, by simp⟩
  have hf₀ (z : F) (hz : z ∈ D) : 0 ≤ f₀ z := by
    have hmem : (-z, 0) ∈ S :=
      ⟨0, C.zero_mem, by simpa using hz, by simp⟩
    have := hGpos _ hmem
    simpa only [hdecomp, map_neg, neg_neg, zero_mul, add_zero] using this
  have hresidual (y : E) (hy : y ∈ C) : f₀ (T y) ≤ β * c y := by
    have hmem : (T y, c y) ∈ S :=
      ⟨y, hy, by simp, le_rfl⟩
    have := hGpos _ hmem
    rw [hdecomp] at this
    nlinarith
  have hobj : f₀ b = β * c yStar := by
    rw [hdecomp] at hGstar
    nlinarith
  have hβpos : 0 < β := by
    by_contra hn
    have hβzero : β = 0 := le_antisymm (le_of_not_gt hn) hβ
    have hfb : f₀ b = 0 := by rw [hobj, hβzero, zero_mul]
    rcases hslater with ⟨y, hy, hslack⟩
    have hfslack : f₀ (T y - b) = 0 := by
      have h1 := hresidual y hy
      rw [hβzero, zero_mul] at h1
      have h2 := hf₀ _ (interior_subset hslack)
      rw [map_sub, hfb, sub_zero] at h2 ⊢
      exact le_antisymm h1 h2
    have hfzero : f₀ = 0 :=
      positive_functional_zero_at_interior _ f₀ hf₀ hslack hfslack
    apply hGne
    apply ContinuousLinearMap.ext
    rintro ⟨x, t⟩
    simp only [hdecomp, hfzero, ContinuousLinearMap.zero_apply,
      hβzero, mul_zero, neg_zero, add_zero]
  refine ⟨β⁻¹ • f₀, ?_, ?_, ?_⟩
  · intro z hz
    exact mul_nonneg (inv_nonneg.mpr hβ) (hf₀ z hz)
  · intro y hy
    change β⁻¹ * f₀ (T y) ≤ c y
    have := mul_le_mul_of_nonneg_left (hresidual y hy) (inv_nonneg.mpr hβ)
    simpa only [← mul_assoc, inv_mul_cancel₀ hβpos.ne', one_mul] using this
  · change β⁻¹ * f₀ b = c yStar
    rw [hobj, ← mul_assoc, inv_mul_cancel₀ hβpos.ne', one_mul]


theorem linear_conic_dual_attained :
  ∀ {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : PointedCone ℝ E) (D : PointedCone ℝ F)
    (T : E →L[ℝ] F) (c : E →L[ℝ] ℝ) (b : F) (yStar : E),
    yStar ∈ C → T yStar - b ∈ D →
    (∀ y ∈ C, T y - b ∈ D → c yStar ≤ c y) →
    (∃ y ∈ C, T y - b ∈ interior (D : Set F)) →
    ∃ f : F →L[ℝ] ℝ, (∀ z ∈ D, 0 ≤ f z) ∧
      (∀ y ∈ C, f (T y) ≤ c y) ∧ f b = c yStar := by
  intro E F _ _ _ _ C D T c b yStar hy hc hm hs
  exact linearMap_conicStrongDuality_attained_of_slater C D T c b yStar hy hc hm hs

end SandwichedRenyiRelativeEntropy
