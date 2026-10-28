/-
For a commuting projection E below the complementary projection `I−P` of `P=testHi ρ σ a`, bounds the ρ-weighted log trace by a times the mass.
Source context: Gour, Theorem 11.4; Gour, Example 3.63; Hayashi–Yamasaki, Lemma 7.
-/
/-
Evaluates the ρ-weighted log trace on an arbitrary commuting projection from the global spectral cap of σ≥2^(−c)I.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.NestedProjections

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem eigen_real
    {A : Type u} [Qudit A] {X : L A} (hX : X.IsSymmetric)
    {v : A} (hv : v ≠ 0) {z : ℂ} (he : X v = z • v) :
    X v = (z.re : ℂ) • v := by
  have hz := hX.conj_eigenvalue_eq_self
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩)
  have hreal : (z.re : ℂ) = z := RCLike.conj_eq_iff_re.mp hz
  rwa [hreal]

private theorem eigen_nonneg
    {A : Type u} [Qudit A] {X : L A} (hX : X.IsPositive)
    {v : A} (hv : v ≠ 0) {r : ℝ} (he : X v = (r : ℂ) • v) : 0 ≤ r := by
  exact eigenvalue_nonneg_of_nonneg
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩) hX.re_inner_nonneg_right

private theorem log_eigen
    {A : Type u} [Qudit A] [Nontrivial A] {X : L A} (hX : X.IsPositive)
    {v : A} (hv : v ≠ 0) {r : ℝ} (he : X v = (r : ℂ) • v) :
    CFC.log X v = (Real.log r : ℂ) • v := by
  exact SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
    hX.isSelfAdjoint Real.log he
    (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm hv he)

private theorem posProj_zero
    {A : Type u} [Qudit A] {X : L A} (hX : X.IsSymmetric)
    {v : A} {r : ℝ} (he : X v = (r : ℂ) • v) (hr : r ≤ 0) :
    posProj X v = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff
    (⨆ (s : ℝ) (_ : 0 < s), Module.End.eigenspace X (s : ℂ))).2
  rw [← Submodule.iInf_orthogonal]
  apply (Submodule.mem_iInf _).mpr
  intro s
  by_cases hs : 0 < s
  · rw [iSup_pos hs]
    exact hX.orthogonalFamily_eigenspaces.isOrtho
      (by exact_mod_cast (ne_of_lt (lt_of_le_of_lt hr hs)))
      (Module.End.mem_eigenspace_iff.mpr he)
  · simp [hs]

private theorem eigen_pos
    {A : Type u} [Qudit A] {X : L A} (hX : IsPositiveDefinite X)
    {v : A} (hv : v ≠ 0) {r : ℝ} (he : X v = (r : ℂ) • v) : 0 < r := by
  apply lt_of_le_of_ne (eigen_nonneg hX.1 hv he)
  intro hr
  have hu : IsUnit X := (LinearMap.isUnit_iff_isUnit_det X).mpr
    (isUnit_iff_ne_zero.mpr hX.2)
  have hi : Function.Injective X := LinearMap.ker_eq_bot.mp
    ((LinearMap.isUnit_iff_ker_eq_bot X).mp hu)
  apply hv
  apply hi
  simpa [← hr] using he

private theorem inner_mul_eigen
    {A : Type u} [Qudit A] {X : L A} (hX : X.IsSymmetric)
    (E : L A) {v : A} {r : ℝ} (he : X v = (r : ℂ) • v) :
    (inner ℂ v ((X * E) v)).re = r * (inner ℂ v (E v)).re := by
  rw [Module.End.mul_apply, ← hX v (E v), he, inner_smul_left]
  simp

private theorem inner_log_eigen
    {A : Type u} [Qudit A] [Nontrivial A] {X S : L A}
    (hX : X.IsPositive) (hS : S.IsPositive) (E : L A)
    {v : A} (hv : v ≠ 0) {r s : ℝ}
    (heX : X v = (r : ℂ) • v) (heS : S v = (s : ℂ) • v) :
    (inner ℂ v ((X * E * (CFC.log X - CFC.log S)) v)).re =
      r * (inner ℂ v (E v)).re * (Real.log r - Real.log s) := by
  have hl : (CFC.log X - CFC.log S) v =
      ((Real.log r - Real.log s : ℝ) : ℂ) • v := by
    simp only [LinearMap.sub_apply, log_eigen hX hv heX, log_eigen hS hv heS,
      Complex.ofReal_sub, sub_smul]
  rw [Module.End.mul_apply, hl, map_smul, inner_smul_right, Complex.re_ofReal_mul,
    inner_mul_eigen hX.isSymmetric E heX]
  ring

private theorem scalar_weighted_log
    {r s w a : ℝ} (hr : 0 ≤ r) (hs : 0 < s) (hw : 0 ≤ w)
    (hcut : 0 < w → r ≤ Real.rpow 2 a * s) :
    r * w * (Real.log r - Real.log s) ≤ a * (r * w) * Real.log 2 := by
  by_cases hw0 : w = 0
  · simp [hw0]
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hlog := Real.log_le_log hrp (hcut (lt_of_le_of_ne hw (Ne.symm hw0)))
  change Real.log r ≤ Real.log ((2 : ℝ) ^ a * s) at hlog
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a)) hs.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have h := mul_le_mul_of_nonneg_left
    (show Real.log r - Real.log s ≤ a * Real.log 2 by linarith) (mul_nonneg hr hw)
  nlinarith only [h]

private theorem cutoff_eigen
    {A : Type u} [Qudit A] {X S E : L A}
    (hX : X.IsSymmetric) (hS : S.IsSymmetric) {a : ℝ}
    (hE : E ≤ 1 - testHi X S a) {v : A} {r s : ℝ}
    (heX : X v = (r : ℂ) • v) (heS : S v = (s : ℂ) • v)
    (hw : 0 < (inner ℂ v (E v)).re) : r ≤ Real.rpow 2 a * s := by
  by_contra hn
  have hd : Real.rpow 2 a * s - r ≤ 0 := by linarith
  have hS' : ((Real.rpow 2 a : ℝ) • S).IsSymmetric := by
    simpa only [Complex.coe_smul] using
      (LinearMap.IsSymmetric.smul
        (by simp : starRingEnd ℂ ((Real.rpow 2 a : ℝ) : ℂ) =
          ((Real.rpow 2 a : ℝ) : ℂ)) hS)
  have he : ((Real.rpow 2 a : ℝ) • S - X) v =
      ((Real.rpow 2 a * s - r : ℝ) : ℂ) • v := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, heX, heS,
      ← Complex.coe_smul, smul_smul, Complex.ofReal_sub, Complex.ofReal_mul, sub_smul]
  have hz := posProj_zero (hS'.sub hX) he hd
  have hp : (1 - testHi X S a) v = 0 := by
    simpa only [testHi, sub_sub_cancel] using hz
  have hpos := (LinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hE)
  have h : 0 ≤ (inner ℂ v (((1 - testHi X S a) - E) v)).re :=
    hpos.re_inner_nonneg_right v
  simp only [LinearMap.sub_apply, hp, zero_sub, inner_neg_right, Complex.neg_re] at h
  linarith

private theorem weighted_log_bound
    {A : Type u} [Qudit A] [Nontrivial A] (ρ σ : State A) (a : ℝ)
    (hσ : IsPositiveDefinite σ.1) (hc : Commute ρ.1 σ.1)
    (E : L A) (hE : E.IsPositive) (hb : E ≤ 1 - testHi ρ.1 σ.1 a) :
    logWeight ρ.1 σ.1 E ≤ a * pairing ρ.1 E := by
  classical
  let b := densityJointBasis ρ.1 σ.1 ρ.2 σ.2 hc
  let j := densityJointIndex ρ.1 σ.1 ρ.2 σ.2 hc
  let r : Fin (Module.finrank ℂ A) → ℝ := fun i => (j i).1.1.re
  let s : Fin (Module.finrank ℂ A) → ℝ := fun i => (j i).2.1.re
  let w : Fin (Module.finrank ℂ A) → ℝ := fun i => (inner ℂ (b i) (E (b i))).re
  have hr (i) : ρ.1 (b i) = (r i : ℂ) • b i :=
    eigen_real ρ.2.1.isSymmetric (b.orthonormal.ne_zero i)
      (Module.End.mem_eigenspace_iff.mp (densityJointBasis_mem ρ.1 σ.1 ρ.2 σ.2 hc i).1)
  have hs (i) : σ.1 (b i) = (s i : ℂ) • b i :=
    eigen_real σ.2.1.isSymmetric (b.orthonormal.ne_zero i)
      (Module.End.mem_eigenspace_iff.mp (densityJointBasis_mem ρ.1 σ.1 ρ.2 σ.2 hc i).2)
  have hterm (i) : r i * w i * (Real.log (r i) - Real.log (s i)) ≤
      a * (r i * w i) * Real.log 2 := by
    apply scalar_weighted_log
      (eigen_nonneg ρ.2.1 (b.orthonormal.ne_zero i) (hr i))
      (eigen_pos hσ (b.orthonormal.ne_zero i) (hs i))
      (hE.re_inner_nonneg_right (b i))
    exact cutoff_eigen ρ.2.1.isSymmetric σ.2.1.isSymmetric hb (hr i) (hs i)
  have htrace : (Tr (ρ.1 * E * (CFC.log ρ.1 - CFC.log σ.1))).re =
      ∑ i, r i * w i * (Real.log (r i) - Real.log (s i)) := by
    rw [Tr, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact inner_log_eigen ρ.2.1 σ.2.1 E (b.orthonormal.ne_zero i) (hr i) (hs i)
  have hmass : pairing ρ.1 E = ∑ i, r i * w i := by
    rw [pairing, Tr, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact inner_mul_eigen ρ.2.1.isSymmetric E (hr i)
  rw [logWeight, htrace, hmass]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [Finset.sum_mul, Finset.mul_sum] using
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i)

theorem gsl_y36 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (a : ℝ),
  IsPositiveDefinite.{u} σ.1 → Commute ρ.1 σ.1 →
  ∀ E : L.{u} A, E.IsPositive → E*E=E →
  Commute E ρ.1 → Commute E σ.1 →
  E ≤ 1-testHi.{u} ρ.1 σ.1 a →
    logWeight.{u} ρ.1 σ.1 E ≤ a * pairing.{u} ρ.1 E
:= by
  intro A _ _ ρ σ a hσ hc E hE _hEE _hEρ _hEσ hb
  have _nested := GourResource.gsl_y35.{u} ρ σ a a hc le_rfl
  exact weighted_log_bound ρ σ a hσ hc E hE hb

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem density_log_nonpos {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) : CFC.log ρ.1 ≤ 0 := by
  have hρ : 0 ≤ ρ.1 := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have hn : ‖ρ.1‖ ≤ 1 := by
    simpa only [ρ.2.2, Complex.one_re] using
      SandwichedRenyiRelativeEntropy.norm_le_re_trace_lm hρ
  apply cfc_nonpos
  intro x hx
  exact Real.log_nonpos
    ((StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) ρ.1).mp hρ x hx)
    ((Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hn))

private theorem spectral_log_lower {A : Type u} [Qudit A]
    (σ : State A) (c : ℝ)
    (hcap : (Real.rpow 2 (-c) : ℝ) • (1 : L A) ≤ σ.1) :
    (-c * Real.log 2) • (1 : L A) ≤ CFC.log σ.1 := by
  have hlower (x : ℝ) (hx : x ∈ spectrum ℝ σ.1) : Real.rpow 2 (-c) ≤ x := by
    apply (algebraMap_le_iff_le_spectrum σ.2.1.isSelfAdjoint).mp _ x hx
    simpa only [Algebra.algebraMap_eq_smul_one] using hcap
  have hp : 0 < Real.rpow 2 (-c) := Real.rpow_pos_of_pos (by norm_num) _
  rw [← Algebra.algebraMap_eq_smul_one]
  refine algebraMap_le_cfc Real.log (-c * Real.log 2) σ.1 ?_
    (continuousOn_id.log fun x hx => ne_of_gt (hp.trans_le (hlower x hx)))
    σ.2.1.isSelfAdjoint
  intro x hx
  have hbits : Real.log (Real.rpow 2 (-c)) = -c * Real.log 2 :=
    Real.log_rpow (by norm_num) (-c)
  exact hbits ▸ Real.log_le_log hp (hlower x hx)

private theorem trace_mul_mono {A : Type u} [Qudit A] [Nontrivial A]
    {W X Y : L A} (hW : 0 ≤ W) (hXY : X ≤ Y) :
    (Tr (W * X)).re ≤ (Tr (W * Y)).re := by
  have ht : 0 ≤ (Tr (W * (Y - X))).re := by
    by_cases hz : W * (Y - X) = 0
    · simp only [hz, map_zero, Complex.zero_re, le_refl]
    · exact (OPT.trace_re_pos_mul_of_nonneg_of_ne_zero hW (sub_nonneg.mpr hXY) hz).le
  rw [mul_sub, map_sub, Complex.sub_re] at ht
  exact sub_nonneg.mp ht

theorem gsl_y37 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (c : ℝ),
  IsPositiveDefinite.{u} σ.1 → Commute ρ.1 σ.1 →
  (Real.rpow 2 (-c) : ℝ) • (1 : L.{u} A) ≤ σ.1 →
  ∀ E : L.{u} A, E.IsPositive → E*E=E →
  Commute E ρ.1 → Commute E σ.1 →
    logWeight.{u} ρ.1 σ.1 E ≤ c * pairing.{u} ρ.1 E
:= by
  intro A _ _ ρ σ c _ _ hcap E hE _ hEρ _
  have hW : 0 ≤ ρ.1 * E := Commute.mul_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)
    ((LinearMap.nonneg_iff_isPositive _).mpr hE) hEρ.symm
  have hlog : CFC.log ρ.1 - CFC.log σ.1 ≤ (c * Real.log 2) • (1 : L A) := by
    have h := sub_le_sub (density_log_nonpos ρ) (spectral_log_lower σ c hcap)
    simpa only [zero_sub, neg_mul, neg_smul, neg_neg] using h
  have ht := trace_mul_mono hW hlog
  have hs : (Tr (ρ.1 * E * ((c * Real.log 2) • (1 : L A)))).re =
      (c * Real.log 2) * (Tr (ρ.1 * E)).re := by
    rw [mul_smul_comm, mul_one, ← Complex.coe_smul, map_smul,
      smul_eq_mul, Complex.re_ofReal_mul]
  rw [hs] at ht
  unfold logWeight pairing
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [mul_assoc, mul_comm (Real.log 2)] using ht

end GourResource

