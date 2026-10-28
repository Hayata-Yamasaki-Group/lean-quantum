import Quantum.TraceInequality.Loewner.Koranyi.NormalFamily

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.WellFounded
import Mathlib.Topology.UniformSpace.UniformConvergence


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators
open scoped BoundedContinuousFunction
open scoped ComplexOrder
open scoped Topology
open scoped UpperHalfPlane

open MeasureTheory Set Filter

noncomputable section

/-!
Step 7: Diagonal extraction on the exhausting compact sets `KmH m` in the upper half-plane.

This file is the companion of `NormalFamily` and packages the diagonal limit
as a Pick function on `ℍ` (upper half-plane).
-/

/-- Upper-half-plane version of the compact rectangle `KmC m`. -/
def KmH (m : ℕ) : Set ℍ :=
  {z | ((z : ℂ)) ∈ KmC m}


/-- Every upper-half-plane point lies in some exhausting rectangle `KmH m`. -/
lemma mem_some_KmH (z : ℍ) : ∃ m : ℕ, z ∈ KmH m := by
  classical
  -- Choose `m` large enough to bound `|re z|`, `im z`, and `1 / im z`.
  let r : ℝ := |(z : ℂ).re|
  let i : ℝ := (z : ℂ).im
  have hi0 : 0 < i := by simpa using z.coe_im_pos
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℕ, r ≤ (m1 : ℝ) := exists_nat_ge r
  obtain ⟨m2, hm2⟩ : ∃ m2 : ℕ, i ≤ (m2 : ℝ) := exists_nat_ge i
  obtain ⟨m3, hm3⟩ : ∃ m3 : ℕ, (1 / i) ≤ (m3 : ℝ) := exists_nat_ge (1 / i)
  let m : ℕ := max m1 (max m2 m3)
  refine ⟨m, ?_⟩
  have hm1' : r ≤ (m : ℝ) := le_trans hm1 (by exact_mod_cast le_max_left m1 (max m2 m3))
  have hm2' : i ≤ (m : ℝ) := le_trans hm2 (by
    have : m2 ≤ max m2 m3 := le_max_left _ _
    exact_mod_cast le_trans this (le_trans (le_max_right m1 (max m2 m3)) (le_rfl)))
  have hm3' : (1 / i) ≤ (m : ℝ) := le_trans hm3 (by
    have : m3 ≤ max m2 m3 := le_max_right _ _
    exact_mod_cast le_trans this (le_max_right m1 (max m2 m3)))
  refine ⟨?_, ?_, ?_⟩
  · simpa [KmC, KmH, r] using hm1'
  · -- `δ m ≤ i` follows from `1 / i ≤ m` and monotonicity of `one_div`.
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have : 1 / ((m : ℝ) + 1) ≤ 1 / (1 / i) :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 / i)) (by nlinarith [hm3'])
    have : 1 / ((m : ℝ) + 1) ≤ i := by
      simpa [one_div, inv_inv] using this
    simpa [δ, i] using this
  · have : i ≤ (m : ℝ) + 1 := le_trans (le_trans (le_rfl : i ≤ i) hm2') (by nlinarith)
    simpa [KmC, KmH, i] using this

/-! ### Transport Step6 limits from `Xm m` to `KmH m` -/

/-- Subtype of upper-half-plane points lying in `KmH m`. -/
abbrev KmHT (m : ℕ) : Type :=
  {z : ℍ // z ∈ KmH m}

/-- Forget the upper-half-plane subtype to view `KmHT m` as `Xm m`. -/
def ιm (m : ℕ) : KmHT m → Xm m :=
  fun z => ⟨(z.1 : ℂ), z.2⟩

/-- `toUHP` after `ιm` leaves the Stieltjes transform unchanged. -/
lemma stieltjes_toUHP_ιm (μ : Measure ℝ) (m : ℕ) (z : KmHT m) :
    stieltjes μ (toUHP m (ιm m z)) = stieltjes μ z.1 := by
  simp [stieltjes, toUHP, ιm]

/-- Uniform convergence on `Xm m` transports to the upper-half-plane subtype `KmHT m`. -/
theorem tendstoUniformly_KmHT_of_tendstoUniformly_Xm
    {m : ℕ} {μn : ℕ → Measure ℝ} {φ : ℕ → ℕ}
    {Gm : Xm m →ᵇ ℂ}
    (h : TendstoUniformly (fun n x => stieltjes (μn (φ n)) (toUHP m x)) Gm atTop) :
    TendstoUniformly
      (fun (n : ℕ) (z : KmHT m) => stieltjes (μn (φ n)) z.1)
      (fun z => Gm (ιm m z)) atTop := by
  -- precompose by `ιm` and simplify `stieltjes` using coercions to `ℂ`
  have h' := h.comp (ιm m)
  simpa [Function.comp, stieltjes_toUHP_ιm] using h'

/-! ### Pick property is preserved under limits (pointwise) -/

/-- Nonnegative imaginary part is closed under sequential limits. -/
lemma im_nonneg_of_tendsto {u : ℕ → ℂ} {w : ℂ} (hu : ∀ n, 0 ≤ (u n).im)
    (ht : Tendsto u atTop (𝓝 w)) : 0 ≤ w.im := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := by
    have hcont : Continuous fun z : ℂ => z.im := Complex.continuous_im
    simpa using isClosed_le continuous_const hcont
  have : (∀ᶠ n in atTop, u n ∈ {z : ℂ | 0 ≤ z.im}) := by
    exact (Eventually.of_forall fun n => hu n)
  exact hclosed.mem_of_tendsto ht this

/-- Precompose the index of a uniformly convergent sequence by a map `g : ℕ → ℕ` tending to
`atTop`. -/
lemma _root_.Quantum.TraceInequality.Loewner.TendstoUniformly.comp_tendsto_atTop
    {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {g : ℕ → ℕ}
    (h : TendstoUniformly F f atTop) (hg : Tendsto g atTop atTop) :
    TendstoUniformly (fun n x => F (g n) x) f atTop := by
  intro u hu
  exact hg.eventually (h u hu)

/-! We currently only need a version of Step6 transported to the compact subtype `KmHT m`. -/

/-- Uniform mass bounds give a convergent Stieltjes subsequence on a fixed `KmHT m`. -/
theorem exists_subseq_tendstoUniformly_KmHT_of_mass_bound (μn : ℕ → Measure ℝ)
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) (m : ℕ) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∃ Gm : KmHT m → ℂ,
          TendstoUniformly (fun n z => stieltjes (μn (φ n)) z.1) Gm atTop := by
  classical
  rcases subseq_tendstoUniformly_stieltjes_of_mass_bound (μn := μn) (hmass := hmass) m with
    ⟨φ, hφ, Gm, hconv⟩
  refine ⟨φ, hφ, (fun z => Gm (ιm m z)), ?_⟩
  -- transport from `Xm m` to `KmHT m`
  simpa using
    tendstoUniformly_KmHT_of_tendstoUniformly_Xm (μn := μn) (φ := φ) (m := m) (Gm := Gm) hconv


/-! ### Step7: diagonal extraction on `KmHT m` -/

section Diagonal

variable (μn : ℕ → Measure ℝ)

/-- Dropping or adding a fixed finite prefix does not change uniform convergence at `atTop`. -/
private lemma tendstoUniformly_add_atTop_iff {α β : Type*} [UniformSpace β]
    (F : ℕ → α → β) (f : α → β) (k : ℕ) :
    TendstoUniformly (fun n x => F (n + k) x) f atTop ↔ TendstoUniformly F f atTop := by
  constructor
  · intro h u hu
    have h' : ∀ᶠ n in atTop, ∀ x : α, (f x, F (n + k) x) ∈ u := h u hu
    have : ∀ᶠ n in Filter.map (fun a => a + k) atTop, ∀ x : α, (f x, F n x) ∈ u := by
      simpa [Filter.eventually_map] using h'
    simpa [Filter.map_add_atTop_eq_nat] using this
  · intro h
    exact
      _root_.Quantum.TraceInequality.Loewner.TendstoUniformly.comp_tendsto_atTop
        (h := h) (hg := Filter.tendsto_add_atTop_nat k)

private lemma exists_strictMono_comp_of_range_subset {f g : ℕ → ℕ} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : Set.range f ⊆ Set.range g) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ f = g ∘ h := by
  classical
  have hex : ∀ n, ∃ k, f n = g k := by
    intro n
    have : f n ∈ Set.range g := hfg ⟨n, rfl⟩
    rcases this with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  let h : ℕ → ℕ := fun n => Classical.choose (hex n)
  have hh : ∀ n, f n = g (h n) := fun n => Classical.choose_spec (hex n)
  have hmono : StrictMono h := by
    intro a b hab
    have : g (h a) < g (h b) := by
      simpa [hh] using hf hab
    exact (hg.lt_iff_lt).1 this
  refine ⟨h, hmono, ?_⟩
  funext n
  simp [Function.comp, hh]

/-- Data for the diagonal construction up to `N`: a subsequence index `φ`, and for each `m < N`,
the corresponding limit function on `KmHT m`. -/
structure DiagUpto (μn : ℕ → Measure ℝ) (N : ℕ) where
  φ : ℕ → ℕ
  hφ : StrictMono φ
  /-- The previous subsequence index used to build `φ` (for `N = 0` this is `id`). -/
  prevφ : ℕ → ℕ
  hprevφ : StrictMono prevφ
  /-- The last extracted subsequence step (for `N = 0` this is `id`). -/
  step : ℕ → ℕ
  hstep : StrictMono step
  /-- The defining relation `φ = prevφ ∘ step`. -/
  hcomp : φ = prevφ ∘ step
  G : ∀ m : ℕ, m < N → KmHT m → ℂ
  hconv : ∀ m : ℕ, ∀ hm : m < N,
    TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (φ n)) z.1) (G m hm) atTop

namespace DiagUpto

/-- Initial diagonal data before any compact rectangles have been processed. -/
noncomputable def mk0 (μn : ℕ → Measure ℝ) : DiagUpto μn 0 :=
  { φ := id
    hφ := strictMono_id
    prevφ := id
    hprevφ := strictMono_id
    step := id
    hstep := strictMono_id
    hcomp := rfl
    G := fun _ hm => (False.elim (Nat.not_lt_zero _ hm))
    hconv := fun _ hm => (False.elim (Nat.not_lt_zero _ hm)) }

end DiagUpto

open DiagUpto

/-- Construct diagonal data by iterating the fixed-compact subsequence extraction. -/
noncomputable def diagUpto (μn : ℕ → Measure ℝ)
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) :
    (N : ℕ) → DiagUpto μn N
  := by
    classical
    refine Nat.rec (motive := fun N => DiagUpto μn N)
      (_root_.Quantum.TraceInequality.Loewner.DiagUpto.mk0 μn) ?_
    intro N prev
    let μn' : ℕ → Measure ℝ := fun n => μn (prev.φ n)
    have hmass' : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn' n univ ≤ M0 := by
      rcases hmass with ⟨M0, hM0, hμle⟩
      refine ⟨M0, hM0, ?_⟩
      intro n
      exact hμle (prev.φ n)
    -- extract convergence on `KmHT N` for the subsequence `μn'`
    let ex :=
      exists_subseq_tendstoUniformly_KmHT_of_mass_bound (μn := μn') (hmass := hmass') N
    let ψ : ℕ → ℕ := Classical.choose ex
    have hψ : StrictMono ψ := (Classical.choose_spec ex).1
    let GN : KmHT N → ℂ := Classical.choose ((Classical.choose_spec ex).2)
    have hconvN :
        TendstoUniformly (fun n (z : KmHT N) => stieltjes (μn' (ψ n)) z.1) GN atTop :=
      (Classical.choose_spec ((Classical.choose_spec ex).2))
    let φ : ℕ → ℕ := fun n => prev.φ (ψ n)
    have hφ : StrictMono φ := prev.hφ.comp hψ
    -- define `G` using a plain `if` so that `simp [hEq]` can discharge the cases
    let G : ∀ m : ℕ, m < N + 1 → KmHT m → ℂ :=
      fun m hm =>
        if hEq : m = N then
          (by
            subst hEq
            exact GN)
        else
          prev.G m (lt_of_le_of_ne (Nat.le_of_lt_succ hm) hEq)
    refine
      { φ := φ
        hφ := hφ
        prevφ := prev.φ
        hprevφ := prev.hφ
        step := ψ
        hstep := hψ
        hcomp := rfl
        G := G
        hconv := ?_ }
    intro m hm
    by_cases hEq : m = N
    · subst hEq
      -- this is exactly the extracted convergence on stage `N`
      simpa [G, φ, μn', Function.comp] using hconvN
    · have hlt : m < N := lt_of_le_of_ne (Nat.le_of_lt_succ hm) hEq
      -- inherit convergence from `prev` by precomposing with `ψ`
      have hprev :
          TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (prev.φ n)) z.1)
            (prev.G m hlt) atTop := prev.hconv m hlt
      have hψT : Tendsto ψ atTop atTop := hψ.tendsto_atTop
      have hcompT :=
        _root_.Quantum.TraceInequality.Loewner.TendstoUniformly.comp_tendsto_atTop
          (h := hprev) (hg := hψT)
      simpa [G, φ, μn', Function.comp, hEq] using hcompT

/-- Diagonal subsequence index selected from the stage `n + 1` construction. -/
noncomputable def diagIdx (μn : ℕ → Measure ℝ)
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) : ℕ → ℕ :=
  fun n => (diagUpto μn hmass (n + 1)).φ n

private lemma prevφ_succ
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) (N : ℕ) :
    (diagUpto μn hmass (N + 1)).prevφ = (diagUpto μn hmass N).φ := by
  cases N with
  | zero =>
      simp [diagUpto]
  | succ N =>
      simp [diagUpto]

/-- The diagonal subsequence index is strictly increasing. -/
lemma strictMono_diagIdx (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) :
    StrictMono (diagIdx (μn := μn) (hmass := hmass)) := by
  classical
  refine strictMono_nat_of_lt_succ ?_
  intro n
  let S1 : DiagUpto μn (n + 1) := diagUpto μn hmass (n + 1)
  let S2 : DiagUpto μn (n + 2) := diagUpto μn hmass (n + 2)
  have hlt : S1.φ n < S1.φ (n + 1) := S1.hφ (Nat.lt_succ_self _)
  have hstep_le : n + 1 ≤ S2.step (n + 1) := StrictMono.le_apply S2.hstep
  have hmono : Monotone S1.φ := S1.hφ.monotone
  have hle : S1.φ (n + 1) ≤ S1.φ (S2.step (n + 1)) := hmono hstep_le
  have hS2 :
      S2.φ (n + 1) = S1.φ (S2.step (n + 1)) := by
    -- `S2.φ = S2.prevφ ∘ S2.step` and `S2.prevφ = S1.φ`
    have hprev : S2.prevφ = S1.φ := by
      -- unfold one step of the recursion
      simp [S1, S2, prevφ_succ (μn := μn) hmass]
    -- finish
    simp [S2.hcomp, hprev]
  have : diagIdx μn hmass n < diagIdx μn hmass (n + 1) := by
    -- chain inequalities on `S1.φ`
    have : S1.φ n < S1.φ (S2.step (n + 1)) := lt_of_lt_of_le hlt hle
    simpa [diagIdx, S1, S2, hS2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  simpa [diagIdx] using this

private lemma range_phi_succ_subset
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0)
    (N : ℕ) :
    Set.range (diagUpto μn hmass (N + 1)).φ ⊆ Set.range (diagUpto μn hmass N).φ := by
  intro a ha
  rcases ha with ⟨n, rfl⟩
  let S := diagUpto μn hmass (N + 1)
  refine ⟨S.step n, ?_⟩
  have hcomp' : S.φ n = S.prevφ (S.step n) := by
    simpa [Function.comp] using congrArg (fun f => f n) S.hcomp
  -- unfold `prevφ` one step
  have hprev : S.prevφ = (diagUpto μn hmass N).φ := by
    simpa [S] using prevφ_succ (μn := μn) hmass N
  -- transport the range witness
  simpa [S, hprev] using hcomp'.symm

private lemma range_phi_le_subset (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0)
    {N N' : ℕ} (h : N ≤ N') :
    Set.range (diagUpto μn hmass N').φ ⊆ Set.range (diagUpto μn hmass N).φ := by
  classical
  induction h with
  | refl =>
      intro a ha
      simpa using ha
  | @step N' hle ih =>
      -- `N' ≤ N'+1`
      have hs :
          Set.range (diagUpto μn hmass (N' + 1)).φ ⊆ Set.range (diagUpto μn hmass N').φ :=
        range_phi_succ_subset (μn := μn) hmass N'
      exact hs.trans ih

private lemma range_diagIdx_add_subset
    (hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0)
    (m : ℕ) :
    Set.range (fun n => diagIdx (μn := μn) (hmass := hmass) (n + m)) ⊆
      Set.range (diagUpto μn hmass (m + 1)).φ := by
  intro a ha
  rcases ha with ⟨n, rfl⟩
  -- the value lies in the range of the later stage, and ranges are nested
  have hmem :
      diagIdx (μn := μn) (hmass := hmass) (n + m) ∈
        Set.range (diagUpto μn hmass (n + m + 1)).φ := by
    refine ⟨n + m, ?_⟩
    simp [diagIdx, Nat.add_comm]
  have hle : m + 1 ≤ n + m + 1 := by
    exact Nat.succ_le_succ (Nat.le_add_left m n)
  exact (range_phi_le_subset (μn := μn) hmass (N := m + 1) (N' := n + m + 1) hle)
    hmem

private lemma tendsto_of_tendstoUniformly {α β : Type*} [UniformSpace β] {F : ℕ → α → β}
    {f : α → β} (h : TendstoUniformly F f atTop) (x : α) :
    Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
  h.tendsto_at x

/-- Uniform mass bounds give a single subsequence converging uniformly on every `KmHT m`. -/
theorem exists_diagonal_tendstoUniformly_all_KmHT :
    (∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) →
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          ∀ m : ℕ, ∃ Gm : KmHT m → ℂ,
            TendstoUniformly (fun n z => stieltjes (μn (φ n)) z.1) Gm atTop := by
  classical
  intro hmass
  refine ⟨diagIdx (μn := μn) (hmass := hmass), strictMono_diagIdx (μn := μn) hmass, ?_⟩
  intro m
  let S : DiagUpto μn (m + 1) := diagUpto μn hmass (m + 1)
  let g : ℕ → ℕ := S.φ
  let Gm : KmHT m → ℂ := S.G m (Nat.lt_succ_self m)
  refine ⟨Gm, ?_⟩
  -- Use the convergence on stage `m+1`, and pass to the diagonal by subsequence + tail shift.
  have hS : TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (g n)) z.1) Gm atTop :=
    S.hconv m (Nat.lt_succ_self m)
  -- Consider the tail `n ↦ diagIdx (n+m)`; it lands in the range of `g`.
  let f : ℕ → ℕ := fun n => diagIdx (μn := μn) (hmass := hmass) (n + m)
  have hf : StrictMono f := by
    have hadd : StrictMono fun n : ℕ => n + m := by
      intro a b hab
      exact Nat.add_lt_add_right hab m
    exact (strictMono_diagIdx (μn := μn) hmass).comp hadd
  have hfg : Set.range f ⊆ Set.range g := by
    simpa [f, g, S] using range_diagIdx_add_subset (μn := μn) hmass m
  rcases exists_strictMono_comp_of_range_subset (f := f) (g := g) hf S.hφ hfg with
    ⟨h, hh, hf_eq⟩
  have hhT : Tendsto h atTop atTop := hh.tendsto_atTop
  have hsub : TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (g (h n))) z.1) Gm atTop :=
    _root_.Quantum.TraceInequality.Loewner.TendstoUniformly.comp_tendsto_atTop (h := hS) (hg := hhT)
  have htail :
      TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (f n)) z.1) Gm atTop := by
    simpa [hf_eq, Function.comp] using hsub
  -- Remove the finite prefix using the shift lemma.
  have :
      TendstoUniformly
        (fun n (z : KmHT m) =>
          stieltjes (μn (diagIdx (μn := μn) (hmass := hmass) n)) z.1)
        Gm atTop := by
    -- `f n = diagIdx (n+m)`
    have hshift :
        TendstoUniformly
            (fun n (z : KmHT m) =>
              stieltjes (μn (diagIdx (μn := μn) (hmass := hmass) (n + m))) z.1)
            Gm atTop := by
      simpa [f] using htail
    -- shift back
    exact (tendstoUniformly_add_atTop_iff
      (F := fun n (z : KmHT m) =>
        stieltjes (μn (diagIdx (μn := μn) (hmass := hmass) n)) z.1)
      (f := Gm) m).1 hshift
  simpa [diagIdx] using this

/-- Assemble the local compact limits into a global upper-half-plane function. -/
theorem exists_diagonal_limit_function :
    (∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) →
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          ∃ F : ℍ → ℂ,
            ∀ m : ℕ,
              TendstoUniformly
                (fun n (z : KmHT m) => stieltjes (μn (φ n)) z.1)
                (fun z => F z.1) atTop := by
  classical
  intro hmass
  rcases exists_diagonal_tendstoUniformly_all_KmHT (μn := μn) hmass with ⟨φ, hφ, hconv⟩
  -- Choose a local limit function `Gm` for each `m`.
  classical
  have hG : ∀ m : ℕ, ∃ Gm : KmHT m → ℂ,
      TendstoUniformly (fun n z => stieltjes (μn (φ n)) z.1) Gm atTop :=
    hconv
  let G : ∀ m : ℕ, KmHT m → ℂ := fun m => Classical.choose (hG m)
  have hGconv : ∀ m : ℕ,
      TendstoUniformly (fun n (z : KmHT m) => stieltjes (μn (φ n)) z.1) (G m) atTop := by
    intro m
    exact Classical.choose_spec (hG m)
  -- Define the global limit `F` by choosing an exhausting compact set for each `z`.
  let F : ℍ → ℂ := fun z =>
    let m := Classical.choose (mem_some_KmH z)
    have hz : z ∈ KmH m := Classical.choose_spec (mem_some_KmH z)
    G m ⟨z, hz⟩
  refine ⟨φ, hφ, F, ?_⟩
  intro m
  -- show `G m = F` on `KmHT m` by uniqueness of limits
  have hpt : ∀ z : KmHT m, F z.1 = G m z := by
    intro z
    -- `F z` is defined using some (chosen) `m0` with `z ∈ KmH m0`
    let m0 : ℕ := Classical.choose (mem_some_KmH z.1)
    have hz0 : z.1 ∈ KmH m0 := Classical.choose_spec (mem_some_KmH z.1)
    have ht0 :
        Tendsto (fun n => stieltjes (μn (φ n)) z.1) atTop (𝓝 (G m0 ⟨z.1, hz0⟩)) :=
      tendsto_of_tendstoUniformly (h := hGconv m0) ⟨z.1, hz0⟩
    have htm :
        Tendsto (fun n => stieltjes (μn (φ n)) z.1) atTop (𝓝 (G m z)) :=
      tendsto_of_tendstoUniformly (h := hGconv m) z
    have : G m0 ⟨z.1, hz0⟩ = G m z := tendsto_nhds_unique ht0 htm
    -- unfold `F` at `z.1`
    simp [F, m0, G, this]
  -- now rewrite the limit function pointwise
  have : (fun z : KmHT m => F z.1) = G m := by
    funext z
    simp [hpt z]
  simpa [this] using hGconv m

/-- The diagonal limit is a Pick function when each approximant has nonnegative imaginary part. -/
theorem exists_diagonal_pick_limit_function
    (hpick : ∀ n : ℕ, ∀ z : ℍ, 0 ≤ (stieltjes (μn n) z).im) :
    (∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n, μn n univ ≤ M0) →
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          ∃ F : ℍ → ℂ,
            (∀ m : ℕ,
              TendstoUniformly
                (fun n (z : KmHT m) => stieltjes (μn (φ n)) z.1)
                (fun z => F z.1) atTop) ∧
            (∀ z : ℍ, 0 ≤ (F z).im) := by
  classical
  intro hmass
  rcases exists_diagonal_limit_function (μn := μn) hmass with ⟨φ, hφ, F, hconvF⟩
  refine ⟨φ, hφ, F, hconvF, ?_⟩
  intro z
  rcases mem_some_KmH z with ⟨m, hz⟩
  let z' : KmHT m := ⟨z, hz⟩
  have ht :
      Tendsto (fun n => stieltjes (μn (φ n)) z) atTop (𝓝 (F z)) := by
    -- pointwise convergence from uniform convergence on `KmHT m`
    have := tendsto_of_tendstoUniformly (h := hconvF m) z'
    simpa [z'] using this
  have hu : ∀ n, 0 ≤ (stieltjes (μn (φ n)) z).im := by
    intro n
    exact hpick (φ n) z
  exact im_nonneg_of_tendsto hu ht

end Diagonal

end

end Quantum.TraceInequality.Loewner
