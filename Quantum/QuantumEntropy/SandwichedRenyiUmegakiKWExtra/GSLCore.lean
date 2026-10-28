import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.Reduction
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.SandwichedRenyiNonNegKWExtra.GSLCore
import Quantum.QuantumEntropy.CFCDerivLMCompat.GSLCore
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.AlphaOne

namespace SandwichedRenyiRelativeEntropy
open QuantumState QuantumChannel MeasureTheory Filter
open scoped ComplexOrder Topology
universe u
section Umegaki
/-! ### Singular support order-one limit -/

private noncomputable def clampUnit (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem clampUnit_nonneg (t : ℝ) : 0 ≤ clampUnit t :=
  le_max_left _ _

private theorem clampUnit_le_one (t : ℝ) : clampUnit t ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

private theorem clampUnit_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    clampUnit t = t := by
  simp [clampUnit, ht0, ht1]

private noncomputable def entropySlopeExponent (p t : ℝ) : ℝ :=
  1 + clampUnit t * max p (-1 / 2)

private theorem entropySlopeExponent_pos (p t : ℝ) :
    0 < entropySlopeExponent p t := by
  have hc0 := clampUnit_nonneg t
  have hc1 := clampUnit_le_one t
  have hp : (-1 / 2 : ℝ) ≤ max p (-1 / 2) := le_max_right _ _
  unfold entropySlopeExponent
  by_cases hmax : 0 ≤ max p (-1 / 2)
  · positivity
  · have hmul : (-1 / 2 : ℝ) ≤ clampUnit t * max p (-1 / 2) := by
      nlinarith
    linarith

private noncomputable def entropySlopeIntegrand
    (p x t : ℝ) : ℝ :=
  let q := entropySlopeExponent p t
  q⁻¹ * ((x ^ q) * Real.log (x ^ q))

private noncomputable def entropySlope (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, entropySlopeIntegrand p x t

private theorem entropySlopeIntegrand_continuousOn :
    ContinuousOn (fun z : (ℝ × Set.Ici (0 : ℝ)) × ℝ =>
      entropySlopeIntegrand z.1.1 z.1.2.1 z.2) Set.univ := by
  rw [continuousOn_univ]
  unfold entropySlopeIntegrand
  apply Continuous.mul
  · apply Continuous.inv₀
    · unfold entropySlopeExponent clampUnit
      fun_prop
    · intro z
      exact ne_of_gt (entropySlopeExponent_pos z.1.1 z.2)
  · exact Real.continuous_mul_log.comp
      (by
        apply Continuous.rpow
        · exact continuous_subtype_val.comp continuous_fst.snd
        · unfold entropySlopeExponent clampUnit
          fun_prop
        · intro z
          exact Or.inr (entropySlopeExponent_pos z.1.1 z.2))

private theorem entropySlope_continuous_uncurry_nonneg :
    Continuous (Function.uncurry (fun p : ℝ =>
      fun x : Set.Ici (0 : ℝ) => entropySlope p x.1)) := by
  unfold entropySlope
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  simpa only [Function.uncurry_apply_pair] using
    (continuousOn_univ.mp entropySlopeIntegrand_continuousOn)

private theorem entropySlope_zero (x : ℝ) (_hx : 0 ≤ x) :
    entropySlope 0 x = x * Real.log x := by
  unfold entropySlope entropySlopeIntegrand entropySlopeExponent
  simp only [max_eq_left (show (-1 / 2 : ℝ) ≤ 0 by norm_num), mul_zero,
    add_zero, inv_one, Real.rpow_one, one_mul]
  simp

private theorem entropySlopeIntegrand_eq
    {p x t : ℝ} (hp : 0 < p) (hx : 0 < x)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    entropySlopeIntegrand p x t = x ^ (1 + t * p) * Real.log x := by
  have hmax : max p (-1 / 2) = p := max_eq_left (by linarith)
  have hq : 1 + t * p ≠ 0 := ne_of_gt (by positivity)
  unfold entropySlopeIntegrand entropySlopeExponent
  rw [clampUnit_eq t ht0 ht1, hmax]
  change (1 + t * p)⁻¹ *
      (x ^ (1 + t * p) * Real.log (x ^ (1 + t * p))) = _
  rw [Real.log_rpow hx]
  field_simp

private theorem entropySlope_eq_div
    {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    entropySlope p x = (x ^ (1 + p) - x) / p := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hleft : entropySlope p 0 = 0 := by
      unfold entropySlope
      have hfun : (fun t : ℝ => entropySlopeIntegrand p 0 t) = 0 := by
        funext t
        have hq : entropySlopeExponent p t ≠ 0 :=
          ne_of_gt (entropySlopeExponent_pos p t)
        unfold entropySlopeIntegrand
        change (entropySlopeExponent p t)⁻¹ *
          (0 ^ entropySlopeExponent p t *
            Real.log (0 ^ entropySlopeExponent p t)) = 0
        rw [Real.zero_rpow hq]
        simp
      rw [hfun]
      exact intervalIntegral.integral_zero
    rw [hleft]
    simp [Real.zero_rpow (by positivity : (1 + p) ≠ 0)]
  · have hderiv : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 →
        HasDerivAt (fun s : ℝ => x ^ (1 + s * p))
          (p * (x ^ (1 + t * p) * Real.log x)) t := by
      intro t _ht
      have hexp : HasDerivAt (fun s : ℝ => 1 + s * p) p t := by
        convert (hasDerivAt_id t).mul_const p |>.const_add 1 using 1
        ring
      convert hexp.const_rpow hxpos using 1
      ring
    have hint : IntervalIntegrable
        (fun t : ℝ => p * (x ^ (1 + t * p) * Real.log x)) volume 0 1 :=
      (by fun_prop (disch := positivity) : Continuous
        (fun t : ℝ => p * (x ^ (1 + t * p) * Real.log x))).intervalIntegrable 0 1
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hintegrand :
        (∫ t in (0 : ℝ)..1, p * (x ^ (1 + t * p) * Real.log x)) =
          p * entropySlope p x := by
      rw [intervalIntegral.integral_const_mul]
      unfold entropySlope
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
      exact (entropySlopeIntegrand_eq hp hxpos ht'.1 ht'.2).symm
    rw [hintegrand] at hfund
    have hxone : x ^ (1 + (0 : ℝ) * p) = x := by simp [Real.rpow_one]
    rw [hxone] at hfund
    apply (eq_div_iff (ne_of_gt hp)).2
    simpa [mul_comm] using hfund

private theorem spectrum_real_finite_test
    {ℋ : Type*} [Qudit ℋ] (X : L ℋ) :
    (spectrum ℝ X).Finite := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum X).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem cfc_entropySlope_eq
    {ℋ : Type*} [Qudit ℋ] {K : L ℋ} (hK : 0 ≤ K)
    {p : ℝ} (hp : 0 < p) :
    cfc (entropySlope p) K =
      (p⁻¹ : ℝ) • (CFC.rpow K (1 + p) - K) := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ K) :=
    fun f => (spectrum_real_finite_test K).continuousOn f
  have hfun : (spectrum ℝ K).EqOn (entropySlope p)
      (fun x : ℝ => p⁻¹ * (x ^ (1 + p) - x)) := by
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hK hx
    rw [entropySlope_eq_div hp hx0, div_eq_inv_mul]
  rw [cfc_congr hfun]
  have hinner : cfc (fun x : ℝ => x ^ (1 + p) - x) K =
      CFC.rpow K (1 + p) - K := by
    rw [cfc_sub (hf := hcont _) (hg := hcont _),
      cfc_id' ℝ K]
    rw [show cfc (fun x : ℝ => x ^ (1 + p)) K = CFC.rpow K (1 + p) by
      exact (CFC.rpow_eq_cfc_real hK).symm]
  rw [← hinner, ← cfc_smul (R := ℝ) p⁻¹
      (fun x : ℝ => x ^ (1 + p) - x) K (hcont _)]
  simp only [smul_eq_mul]

private theorem cfc_entropySlope_zero_eq
    {ℋ : Type*} [Qudit ℋ] {K : L ℋ} (hK : 0 ≤ K) :
    cfc (entropySlope 0) K = K * CFC.log K := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ K) :=
    fun f => (spectrum_real_finite_test K).continuousOn f
  have hfun : (spectrum ℝ K).EqOn (entropySlope 0)
      (fun x : ℝ => x * Real.log x) := by
    intro x hx
    exact entropySlope_zero x (spectrum_nonneg_of_nonneg hK hx)
  rw [cfc_congr hfun, cfc_mul _ _ K (hcont _) (hcont _),
    cfc_id' ℝ K]
  rfl

private theorem entropySlope_cfc_tendsto
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {ι : Type*} {l : Filter ι} {p : ι → ℝ} {K : ι → L ℋ} {K₀ : L ℋ}
    (hp : Tendsto p l (𝓝 (0 : ℝ)))
    (hK : Tendsto K l (𝓝 K₀))
    (hKnn : ∀ᶠ i in l, 0 ≤ K i)
    (hK₀nn : 0 ≤ K₀) :
    Tendsto (fun i => cfc (entropySlope (p i)) (K i))
      l (𝓝 (K₀ * CFC.log K₀)) := by
  let M : ℝ := ‖K₀‖ + 1
  let s : Set ℝ := Set.Icc 0 M
  have hM : 0 < M := by dsimp [M]; positivity
  have hs : IsCompact s := isCompact_Icc
  have hnorm : ∀ᶠ i in l, ‖K i‖ < M := by
    exact hK.norm.eventually (Iio_mem_nhds (by dsimp [M]; linarith))
  have hspectrum : ∀ᶠ i in l, spectrum ℝ (K i) ⊆ s := by
    filter_upwards [hKnn, hnorm] with i hi hknorm x hx
    refine ⟨spectrum_nonneg_of_nonneg hi hx, ?_⟩
    have habs : |x| ≤ ‖K i‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (habs.trans hknorm.le)
  have hspectrum₀ : spectrum ℝ K₀ ⊆ s := by
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg hK₀nn hx, ?_⟩
    have habs : |x| ≤ ‖K₀‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (habs.trans (by dsimp [M]; linarith))
  let F : ℝ → ℝ → ℝ := fun p x => entropySlope p x
  have hFcont : Continuous (fun z : ℝ × s => F z.1 z.2.1) := by
    have hmap : Continuous (fun z : ℝ × s =>
        (z.1, (⟨z.2.1, z.2.2.1⟩ : Set.Ici (0 : ℝ)))) :=
      continuous_fst.prodMk
        (Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_snd) _)
    simpa only [F, Function.uncurry_apply_pair, Function.comp_apply] using
      entropySlope_continuous_uncurry_nonneg.comp hmap
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hFuniformNhds : TendstoUniformly
      (fun p (x : s) => F p x.1) (fun x : s => F 0 x.1) (𝓝 (0 : ℝ)) :=
    Continuous.tendstoUniformly (fun p (x : s) => F p x.1) hFcont 0
  have hFuniform : TendstoUniformlyOn F (F 0) (𝓝[>] (0 : ℝ)) s := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    intro u hu
    exact (hFuniformNhds u hu).filter_mono nhdsWithin_le_nhds
  have hFuniformFull : TendstoUniformlyOn F (F 0) (𝓝 (0 : ℝ)) s := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact hFuniformNhds
  let UF : ℝ → UniformOnFun ℝ ℝ {s} :=
    fun p => UniformOnFun.ofFun {s} (F p)
  have hUFbase : Tendsto UF (𝓝 (0 : ℝ)) (𝓝 (UF 0)) := by
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro t ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    simpa only [UF, UniformOnFun.toFun_ofFun, Function.comp_apply] using hFuniformFull
  have hUF : Tendsto (fun i => UF (p i)) l (𝓝 (UF 0)) := hUFbase.comp hp
  let G : ι → UniformOnFun ℝ ℝ {s} × L ℋ := fun i => (UF (p i), K i)
  let G₀ : UniformOnFun ℝ ℝ {s} × L ℋ := (UF 0, K₀)
  let carrier : Set (UniformOnFun ℝ ℝ {s} × L ℋ) :=
    {f | ContinuousOn (UniformOnFun.toFun {s} f) s} ×ˢ
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s}
  have hFcontinuous (p : ℝ) : ContinuousOn (F p) s := by
    rw [continuousOn_iff_continuous_restrict]
    exact hFcont.comp (continuous_const.prodMk continuous_id)
  have hGmem : ∀ᶠ i in l, G i ∈ carrier := by
    filter_upwards [hKnn, hspectrum] with i hi hsp
    refine ⟨?_, IsSelfAdjoint.of_nonneg hi, hsp⟩
    simpa only [G, UF, UniformOnFun.toFun_ofFun] using hFcontinuous (p i)
  have hG₀mem : G₀ ∈ carrier := by
    refine ⟨?_, IsSelfAdjoint.of_nonneg hK₀nn, hspectrum₀⟩
    simpa only [G₀, UF, UniformOnFun.toFun_ofFun] using hFcontinuous 0
  have hGtendsto : Tendsto G l (𝓝 G₀) := by
    exact Filter.Tendsto.prodMk_nhds hUF hK
  have hGwithin : Tendsto G l (𝓝[carrier] G₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hGtendsto, hGmem⟩
  have hcfc := (continuousOn_cfc_setProd (A := L ℋ) hs).continuousWithinAt hG₀mem
  have hresult := hcfc.tendsto.comp hGwithin
  change Tendsto (fun i => cfc (F (p i)) (K i))
      l (𝓝 (cfc (F 0) K₀)) at hresult
  rw [show cfc (F 0) K₀ = K₀ * CFC.log K₀ by
    exact cfc_entropySlope_zero_eq hK₀nn] at hresult
  exact hresult

private theorem rpow_eq_cfc_singular {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) (p : ℝ) :
    CFC.rpow sigma p = cfc (fun x : ℝ => x ^ p) sigma := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hsigma

private theorem rpow_mul_rpow_singular {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) (p q : ℝ) :
    CFC.rpow sigma p * CFC.rpow sigma q =
      cfc (fun x : ℝ => x ^ p * x ^ q) sigma := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ sigma) :=
    fun f => (spectrum_real_finite_test sigma).continuousOn f
  rw [rpow_eq_cfc_singular hsigma p, rpow_eq_cfc_singular hsigma q]
  exact (cfc_mul _ _ sigma (hcont _) (hcont _)).symm

private theorem rpow_support_comm {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) :
    CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)) =
      CFC.rpow sigma (-(1 / 2)) * CFC.rpow sigma (1 / 2) := by
  rw [rpow_mul_rpow_singular hsigma, rpow_mul_rpow_singular hsigma]
  exact cfc_congr fun _ _ => mul_comm _ _

private theorem self_mul_rpow_support {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) :
    sigma * (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))) = sigma := by
  rw [← mul_assoc]
  nth_rewrite 1 [show sigma = CFC.rpow sigma (1 : ℝ) from
    (CFC.rpow_one sigma hsigma).symm]
  rw [rpow_mul_rpow_singular hsigma]
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ sigma) :=
    fun f => (spectrum_real_finite_test sigma).continuousOn f
  rw [rpow_eq_cfc_singular hsigma]
  rw [← cfc_mul _ _ sigma (hcont _) (hcont _)]
  trans cfc (fun x : ℝ => x) sigma
  · apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hsigma hx
    change x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) = x
    rcases eq_or_lt_of_le hx0 with rfl | hxpos
    · norm_num [Real.zero_rpow]
    · rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      norm_num
  · exact cfc_id' ℝ sigma

private theorem rpow_support_conjugate_eq {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) :
    (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))) * rho *
        (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))) = rho := by
  let P := CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  have hsigmaP : sigma * P = sigma := self_mul_rpow_support hsigma
  have hPsa : IsSelfAdjoint P := by
    have hneg : IsSelfAdjoint (CFC.rpow sigma (-(1 / 2))) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hpos : IsSelfAdjoint (CFC.rpow sigma (1 / 2)) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    simp only [IsSelfAdjoint, P]
    rw [star_mul,
      hneg.star_eq, hpos.star_eq, ← rpow_support_comm hsigma]
  have hrhoP : rho * P = rho := by
    refine LinearMap.ext fun v => ?_
    have hker : v - P v ∈ LinearMap.ker sigma := by
      rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hsigmaP, sub_self]
    have hz := LinearMap.mem_ker.mp (hsupp hker)
    rw [map_sub] at hz
    change (rho * P) v = rho v
    rw [Module.End.mul_apply]
    exact (sub_eq_zero.mp hz).symm
  have hPrho : P * rho = rho := by
    have h := congrArg star hrhoP
    rwa [star_mul, hPsa.star_eq, (IsSelfAdjoint.of_nonneg hrho).star_eq] at h
  change P * rho * P = rho
  rw [hPrho, hrhoP]

private theorem rpow_apply_eigenvector_singular
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ] {sigma : L ℋ} (hsigma : 0 ≤ sigma)
    (p mu : ℝ) {v : ℋ} (hev : sigma v = (mu : ℂ) • v)
    (hmu : mu ∈ spectrum ℝ sigma) :
    CFC.rpow sigma p v = ((mu ^ p : ℝ) : ℂ) • v := by
  rw [rpow_eq_cfc_singular hsigma]
  exact cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hsigma)
    (fun x : ℝ => x ^ p) hev hmu

private theorem outer_product_apply_test {ℋ₁ ℋ₂ : Type*} [Qudit ℋ₁] [Qudit ℋ₂]
    (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outer_product u v x = (inner ℂ u x : ℂ) • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

private noncomputable def outerLTest {ℋ : Type*} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] L ℋ where
  toFun v := outer_product u v
  map_add' v w := by ext x; simp [outer_product_apply_test, smul_add]
  map_smul' c v := by
    ext x
    simp only [outer_product_apply_test, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem continuous_outerL_test {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => outer_product u v) :=
  (outerLTest u).continuous_of_finiteDimensional

private theorem tendsto_rpow_exponent_to_support
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {ι : Type*} {l : Filter ι} {e : ι → ℝ} {sigma : L ℋ}
    (hsigma : 0 ≤ sigma) (he : Tendsto e l (𝓝 (0 : ℝ)))
    (heneg : ∀ᶠ i in l, e i < 0) :
    Tendsto (fun i => CFC.rpow sigma (e i)) l
      (𝓝 (CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2)))) := by
  classical
  set n := Module.finrank ℂ ℋ
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hsigmaPos : sigma.IsPositive := (LinearMap.nonneg_iff_isPositive sigma).mp hsigma
  have hsigmaSym := hsigmaPos.isSymmetric
  let b := hsigmaSym.eigenvectorBasis hn
  let eig := hsigmaSym.eigenvalues hn
  have heig0 : ∀ j, 0 ≤ eig j := hsigmaPos.nonneg_eigenvalues hn
  have heigApply : ∀ j, sigma (b j) = ((eig j : ℝ) : ℂ) • b j :=
    hsigmaSym.apply_eigenvectorBasis hn
  have hbne : ∀ j, b j ≠ 0 := fun j => b.orthonormal.ne_zero j
  have heigSpec : ∀ j, eig j ∈ spectrum ℝ sigma := fun j =>
    mem_spectrum_real_of_eigenvector_lm (hbne j) (heigApply j)
  let P := CFC.rpow sigma (1 / 2) * CFC.rpow sigma (-(1 / 2))
  have hpoint : ∀ j, Tendsto (fun i => CFC.rpow sigma (e i) (b j)) l (𝓝 (P (b j))) := by
    intro j
    have hrpow : ∀ p : ℝ,
        CFC.rpow sigma p (b j) = (((eig j) ^ p : ℝ) : ℂ) • b j := fun p =>
      rpow_apply_eigenvector_singular hsigma p (eig j) (heigApply j) (heigSpec j)
    have hPapply : P (b j) =
        (((eig j) ^ (-(1 / 2 : ℝ)) * (eig j) ^ (1 / 2 : ℝ) : ℝ) : ℂ) • b j := by
      simp only [P, Module.End.mul_apply, hrpow, map_smul, smul_smul]
      norm_cast
    rw [hPapply]
    simp only [hrpow]
    apply Filter.Tendsto.smul_const
    apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    rcases eq_or_lt_of_le (heig0 j) with hzero | hpos
    · rw [← hzero]
      simp only [Real.zero_rpow (show (-(1 / 2 : ℝ)) ≠ 0 by norm_num), zero_mul]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [heneg] with i hi
      rw [Real.zero_rpow (ne_of_lt hi)]
    · have htarget : eig j ^ (-(1 / 2 : ℝ)) * eig j ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hpos]
        norm_num
      rw [htarget]
      simpa [Function.comp_def, Real.rpow_zero] using
        ((Real.continuous_const_rpow (ne_of_gt hpos)).tendsto (0 : ℝ)).comp he
  have hrecon : P = ∑ j, outer_product (b j) (P (b j)) :=
    linearMap_eq_sum_outer_product b P
  have hfun : (fun i => CFC.rpow sigma (e i)) =
      fun i => ∑ j, outer_product (b j) (CFC.rpow sigma (e i) (b j)) :=
    funext fun i => linearMap_eq_sum_outer_product b _
  change Tendsto (fun i => CFC.rpow sigma (e i)) l (𝓝 P)
  rw [hrecon, hfun]
  apply tendsto_finset_sum
  intro j _
  exact ((continuous_outerL_test (b j)).tendsto _).comp (hpoint j)

private theorem hasDerivAt_trace_mul_rpow_singular
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hsigma : 0 ≤ sigma) (hsupp : suppLE rho sigma)
    {f : ℝ → ℝ} {a f' : ℝ} (hf : HasDerivAt f f' a) (hfa : f a = 0) :
    HasDerivAt (fun t => (Tr (rho * CFC.rpow sigma (f t))).re)
      (f' * (Tr (rho * CFC.log sigma)).re) a := by
  classical
  set n := Module.finrank ℂ ℋ
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hsigmaPos : sigma.IsPositive := (LinearMap.nonneg_iff_isPositive sigma).mp hsigma
  have hsigmaSym := hsigmaPos.isSymmetric
  let b := hsigmaSym.eigenvectorBasis hn
  let eig := hsigmaSym.eigenvalues hn
  let c : Fin n → ℝ := fun j => (inner ℂ (b j) (rho (b j))).re
  have heig0 : ∀ j, 0 ≤ eig j := hsigmaPos.nonneg_eigenvalues hn
  have heigApply : ∀ j, sigma (b j) = ((eig j : ℝ) : ℂ) • b j :=
    hsigmaSym.apply_eigenvectorBasis hn
  have hbne : ∀ j, b j ≠ 0 := fun j => b.orthonormal.ne_zero j
  have heigSpec : ∀ j, eig j ∈ spectrum ℝ sigma := fun j =>
    mem_spectrum_real_of_eigenvector_lm (hbne j) (heigApply j)
  have hc0 : ∀ j, eig j = 0 → c j = 0 := by
    intro j hj
    have hbker : b j ∈ LinearMap.ker sigma := by
      rw [LinearMap.mem_ker, heigApply j, hj]
      simp
    have hrhob : rho (b j) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp [c, hrhob]
  have hrpowApply : ∀ (p : ℝ) j,
      CFC.rpow sigma p (b j) = (((eig j) ^ p : ℝ) : ℂ) • b j := fun p j =>
    rpow_apply_eigenvector_singular hsigma p (eig j) (heigApply j) (heigSpec j)
  have hlogApply : ∀ j,
      CFC.log sigma (b j) = ((Real.log (eig j) : ℝ) : ℂ) • b j := fun j =>
    cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hsigma) Real.log
      (heigApply j) (heigSpec j)
  have hexpand : ∀ t,
      (Tr (rho * CFC.rpow sigma (f t))).re = ∑ j, eig j ^ (f t) * c j := by
    intro t
    rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.rpow sigma (f t)) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.End.mul_apply, hrpowApply, map_smul, inner_smul_right,
      Complex.re_ofReal_mul]
  have hlogExpand :
      (Tr (rho * CFC.log sigma)).re = ∑ j, Real.log (eig j) * c j := by
    rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.log sigma) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Module.End.mul_apply, hlogApply, map_smul, inner_smul_right,
      Complex.re_ofReal_mul]
  rw [show (fun t => (Tr (rho * CFC.rpow sigma (f t))).re) =
      (fun t => ∑ j, eig j ^ (f t) * c j) from funext hexpand,
    hlogExpand, Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro j _
  rcases eq_or_lt_of_le (heig0 j) with hzero | hpos
  · have hc : c j = 0 := hc0 j hzero.symm
    simp only [hc, mul_zero]
    exact hasDerivAt_const (x := a) (c := 0)
  · have hd := hf.const_rpow hpos |>.mul_const (c j)
    rw [hfa, Real.rpow_zero] at hd
    convert hd using 1
    ring

private theorem tendsto_sandwiched_inner_one_right
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) :
    Tendsto (fun alpha : ℝ =>
      CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
        CFC.rpow sigma ((1 - alpha) / (2 * alpha)))
      (𝓝[>] (1 : ℝ)) (𝓝 rho) := by
  let e : ℝ → ℝ := fun alpha => (1 - alpha) / (2 * alpha)
  have he : Tendsto e (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt e 1 := by
      unfold e
      fun_prop (disch := norm_num)
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num [e]
  have heneg : ∀ᶠ alpha in 𝓝[>] (1 : ℝ), e alpha < 0 := by
    filter_upwards [self_mem_nhdsWithin] with alpha halpha
    unfold e
    exact div_neg_of_neg_of_pos (sub_neg.mpr halpha)
      (mul_pos (by norm_num) (lt_trans zero_lt_one halpha))
  have hR := tendsto_rpow_exponent_to_support hsigma he heneg
  have hrhoConst : Tendsto (fun _ : ℝ => rho) (𝓝[>] (1 : ℝ)) (𝓝 rho) :=
    tendsto_const_nhds
  have hmul := (hR.mul hrhoConst).mul hR
  rw [rpow_support_conjugate_eq hrho hsigma hsupp] at hmul
  change Tendsto (fun alpha => CFC.rpow sigma (e alpha) * rho *
    CFC.rpow sigma (e alpha)) (𝓝[>] (1 : ℝ)) (𝓝 rho)
  exact hmul

private theorem tendsto_sandwiched_outer_slope
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) :
    Tendsto (fun alpha : ℝ =>
      ((sandwichedQuasi alpha rho sigma).re -
        (Tr (CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
          CFC.rpow sigma ((1 - alpha) / (2 * alpha)))).re) / (alpha - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 ((Tr (rho * CFC.log rho)).re)) := by
  let K : ℝ → L ℋ := fun alpha =>
    CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
      CFC.rpow sigma ((1 - alpha) / (2 * alpha))
  have hK : Tendsto K (𝓝[>] (1 : ℝ)) (𝓝 rho) :=
    tendsto_sandwiched_inner_one_right hrho hsigma hsupp
  have hp : Tendsto (fun alpha : ℝ => alpha - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert ((continuous_id.sub continuous_const).tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds using 1
    norm_num
  have hKnn : ∀ alpha, 0 ≤ K alpha := fun _ =>
    conjugate_nonneg_of_nonneg hrho CFC.rpow_nonneg
  have hcfc := entropySlope_cfc_tendsto hp hK
    (Filter.Eventually.of_forall hKnn) hrho
  have htrace : Tendsto
      (fun alpha => (Tr (cfc (entropySlope (alpha - 1)) (K alpha))).re)
      (𝓝[>] (1 : ℝ)) (𝓝 ((Tr (rho * CFC.log rho)).re)) :=
    (QuantumState.continuous_re_trace_lm.tendsto _).comp hcfc
  refine htrace.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  have hp0 : 0 < alpha - 1 := sub_pos.mpr halpha
  have heq := cfc_entropySlope_eq (hKnn alpha) hp0
  change (Tr (cfc (entropySlope (alpha - 1)) (K alpha))).re =
    ((sandwichedQuasi alpha rho sigma).re - (Tr (K alpha)).re) / (alpha - 1)
  rw [heq]
  unfold sandwichedQuasi
  change _ = ((Tr (CFC.rpow (K alpha) alpha)).re - (Tr (K alpha)).re) / (alpha - 1)
  rw [← Complex.coe_smul, map_smul, map_sub]
  simp only [smul_eq_mul, Complex.re_ofReal_mul, Complex.sub_re]
  have halpha : 1 + (alpha - 1) = alpha := by ring
  rw [halpha]
  field_simp

private theorem rpow_sq_singular {ℋ : Type*} [Qudit ℋ]
    {sigma : L ℋ} (hsigma : 0 ≤ sigma) (p : ℝ) :
    CFC.rpow sigma p * CFC.rpow sigma p = CFC.rpow sigma (p + p) := by
  rw [rpow_mul_rpow_singular hsigma, rpow_eq_cfc_singular hsigma]
  apply cfc_congr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hsigma hx
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · by_cases hp : p = 0
    · subst hp
      norm_num [Real.rpow_zero]
    · change (0 : ℝ) ^ p * 0 ^ p = 0 ^ (p + p)
      have hpp : p + p ≠ 0 := by
        intro h
        apply hp
        linarith
      rw [Real.zero_rpow hp, Real.zero_rpow hpp]
      ring
  · change x ^ p * x ^ p = x ^ (p + p)
    exact (Real.rpow_add hxpos p p).symm

private theorem trace_sandwiched_inner_eq
    {ℋ : Type*} [Qudit ℋ] {rho sigma : L ℋ} (hsigma : 0 ≤ sigma)
    (alpha : ℝ) :
    Tr (CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
        CFC.rpow sigma ((1 - alpha) / (2 * alpha))) =
      Tr (rho * CFC.rpow sigma ((1 - alpha) / alpha)) := by
  let p := (1 - alpha) / (2 * alpha)
  have hexp : (1 - alpha) / alpha = p + p := by
    unfold p
    ring
  rw [hexp]
  change Tr (CFC.rpow sigma p * rho * CFC.rpow sigma p) =
    Tr (rho * CFC.rpow sigma (p + p))
  calc
    Tr (CFC.rpow sigma p * rho * CFC.rpow sigma p) =
        Tr (CFC.rpow sigma p * (CFC.rpow sigma p * rho)) :=
      by rw [LinearMap.trace_mul_comm]
    _ = Tr ((CFC.rpow sigma p * CFC.rpow sigma p) * rho) := by rw [mul_assoc]
    _ = Tr (rho * (CFC.rpow sigma p * CFC.rpow sigma p)) :=
      by rw [LinearMap.trace_mul_comm]
    _ = Tr (rho * CFC.rpow sigma (p + p)) := by rw [rpow_sq_singular hsigma p]

private theorem tendsto_sandwiched_inner_trace_slope
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (_hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) :
    Tendsto (fun alpha : ℝ =>
      ((Tr (CFC.rpow sigma ((1 - alpha) / (2 * alpha)) * rho *
          CFC.rpow sigma ((1 - alpha) / (2 * alpha)))).re - (Tr rho).re) /
        (alpha - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (-(Tr (rho * CFC.log sigma)).re)) := by
  let f : ℝ → ℝ := fun alpha => (1 - alpha) / alpha
  have hf : HasDerivAt f (-1) 1 := by
    unfold f
    convert ((hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).sub
      (hasDerivAt_id (1 : ℝ))).div (hasDerivAt_id (1 : ℝ)) (by norm_num) using 1
    norm_num
  have hderiv := hasDerivAt_trace_mul_rpow_singular hsigma hsupp hf (by norm_num [f])
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  have hlim := hderiv.mono_left (nhdsWithin_mono _ fun _ h => ne_of_gt h)
  have hlim' : Tendsto (slope (fun t => (Tr (rho * CFC.rpow sigma (f t))).re) 1)
      (𝓝[>] (1 : ℝ)) (𝓝 (-(Tr (rho * CFC.log sigma)).re)) := by
    simpa using hlim
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  rw [slope_def_field]
  have hfone : f 1 = 0 := by norm_num [f]
  rw [hfone]
  have hrpow0 : CFC.rpow sigma 0 = 1 := CFC.rpow_zero sigma hsigma
  rw [hrpow0, mul_one]
  rw [← trace_sandwiched_inner_eq hsigma alpha]

private theorem tendsto_sandwiched_quasi_slope
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hsupp : suppLE rho sigma) :
    Tendsto (fun alpha : ℝ =>
      ((sandwichedQuasi alpha rho sigma).re - (Tr rho).re) / (alpha - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 ((Tr (rho * (CFC.log rho - CFC.log sigma))).re)) := by
  have houter := tendsto_sandwiched_outer_slope hrho hsigma hsupp
  have hinner := tendsto_sandwiched_inner_trace_slope hrho hsigma hsupp
  have hsum := houter.add hinner
  convert hsum using 1
  · funext alpha
    ring
  · rw [mul_sub, map_sub, Complex.sub_re]
    ring

private theorem sandwichedRenyiDiv_tendsto_umegaki_suppLE
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    {rho sigma : L ℋ} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hrho0 : rho ≠ 0) (hsupp : suppLE rho sigma) :
    Tendsto (fun alpha => sandwichedRenyiDiv alpha rho sigma)
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiNorm rho sigma)) := by
  let q : ℝ → ℝ := fun alpha => (sandwichedQuasi alpha rho sigma).re
  let d : ℝ := (Tr (rho * (CFC.log rho - CFC.log sigma))).re
  have hq1 : q 1 = (Tr rho).re :=
    sandwichedQuasi_one_re rho.toContinuousLinearMap sigma.toContinuousLinearMap
      (show 0 ≤ sigma.toContinuousLinearMap from hsigma)
      (show 0 ≤ rho.toContinuousLinearMap from hrho)
  have hrpos : 0 < (Tr rho).re := QuantumEntropy.trace_re_pos_of_ne_zero hrho hrho0
  have hslope : Tendsto (slope q 1) (𝓝[>] (1 : ℝ)) (𝓝 d) := by
    have h := tendsto_sandwiched_quasi_slope hrho hsigma hsupp
    convert h using 1
    funext alpha
    rw [slope_def_field, hq1]
  have hqderiv : HasDerivWithinAt q d (Set.Ioi 1) 1 :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (1 : ℝ))).mpr hslope
  have hlogderiv := hqderiv.log (by rw [hq1]; exact ne_of_gt hrpos)
  have hlogslope :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (1 : ℝ))).mp hlogderiv
  have htarget : d / q 1 = umegakiNorm rho sigma := by
    rw [hq1]
    rfl
  rw [htarget] at hlogslope
  refine hlogslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  have hqpos : 0 < q alpha :=
    sandwichedQuasi_re_pos_of_suppLE halpha hrho hsigma hsupp hrho0
  change slope (fun alpha => Real.log (q alpha)) 1 alpha =
    sandwichedRenyiDiv alpha rho sigma
  rw [slope_def_field]
  unfold sandwichedRenyiDiv
  rw [show (sandwichedQuasi alpha rho sigma).re = q alpha from rfl,
    show q 1 = (Tr rho).re from hq1,
    Real.log_div (ne_of_gt hqpos) (ne_of_gt hrpos)]
  ring

/-- The support-sensitive sandwiched Rényi divergence converges from above to
    the extended Umegaki relative entropy for every nonzero positive first argument. -/
theorem sandwichedRenyiDivNN_tendsto_umegaki
    {ℋ : Type*} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hrho0 : rho ≠ 0) :
    Tendsto (fun alpha => sandwichedRenyiDivNN alpha rho sigma)
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiRelEntropyNN rho sigma)) := by
  by_cases hsupp : suppLE rho sigma
  · have hreal := sandwichedRenyiDiv_tendsto_umegaki_suppLE
      hrho hsigma hrho0 hsupp
    have hcoe : Tendsto (fun alpha =>
        ((sandwichedRenyiDiv alpha rho sigma : ℝ) : EReal))
        (𝓝[>] (1 : ℝ)) (𝓝 ((umegakiNorm rho sigma : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr hreal
    have htarget : umegakiRelEntropyNN rho sigma =
        ((umegakiNorm rho sigma : ℝ) : EReal) := by
      unfold umegakiRelEntropyNN
      rw [if_pos hsupp]
    rw [htarget]
    refine hcoe.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with alpha halpha
    unfold sandwichedRenyiDivNN
    rw [if_neg]
    push_neg
    exact ⟨fun _ => hsupp, fun h => absurd halpha (not_lt_of_ge h.le)⟩
  · have htarget : umegakiRelEntropyNN rho sigma = (⊤ : EReal) := by
      unfold umegakiRelEntropyNN
      rw [if_neg hsupp]
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with alpha halpha
    unfold sandwichedRenyiDivNN
    rw [if_pos (Or.inl ⟨halpha, hsupp⟩)]


end Umegaki

end SandwichedRenyiRelativeEntropy
