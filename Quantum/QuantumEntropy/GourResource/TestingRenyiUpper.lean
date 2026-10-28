import Quantum.QuantumEntropy.TraceConjPowLMCompat.GSLCore
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
/-
sandwiched ≤ Petz (on the required range).
-/


open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)
open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower NNReal ℂ (L H) :=
  RestrictScalars.isScalarTower NNReal ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem rpow_eigen
    {A : Type u} [Qudit A] [Nontrivial A] {X : L A} (hX : 0 ≤ X)
    (p : ℝ) {v : A} (hv0 : v ≠ 0) {r : ℝ} (hv : X v = (r : ℂ) • v) :
    CFC.rpow X p v = ((r ^ p : ℝ) : ℂ) • v := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hX]
  exact SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hX)
    (fun x : ℝ => x ^ p) hv
    (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm hv0 hv)

private theorem rpow_comp
    {A : Type u} [Qudit A] [Nontrivial A] {X : L A} (hX : 0 ≤ X) (p q : ℝ) :
    CFC.rpow (CFC.rpow X p) q = CFC.rpow X (p * q) := by
  let hpos := (LinearMap.nonneg_iff_isPositive X).mp hX
  let b := hpos.isSymmetric.eigenvectorBasis rfl
  apply b.toBasis.ext
  intro i
  change CFC.rpow (CFC.rpow X p) q (b i) = CFC.rpow X (p * q) (b i)
  have hv := hpos.isSymmetric.apply_eigenvectorBasis rfl i
  have hv0 := b.orthonormal.ne_zero i
  have hXp : CFC.rpow X p (b i) =
      ((hpos.isSymmetric.eigenvalues rfl i ^ p : ℝ) : ℂ) • b i := rpow_eigen hX p hv0 hv
  rw [rpow_eigen (X := CFC.rpow X p) CFC.rpow_nonneg q hv0 hXp,
    rpow_eigen hX (p * q) hv0 hv, ← Real.rpow_mul (hpos.nonneg_eigenvalues rfl i)]
  rfl

private theorem rpow_commute
    {A : Type u} [Qudit A] {X Y : L A} (h : Commute X Y) (p : ℝ) :
    Commute (CFC.rpow X p) Y := by
  exact h.cfc_nnreal (fun x => x ^ p)

private theorem commuting_sandwich_power
    {A : Type u} [Qudit A] [Nontrivial A] {X B : L A}
    (hX : 0 ≤ X) (hB : 0 ≤ B) (hcomm : Commute X B)
    {p : ℝ} (hp : 0 < p) :
    CFC.rpow (B * CFC.rpow X p * B) (1 / p) = X * CFC.rpow B (2 / p) := by
  let hXs := ((LinearMap.nonneg_iff_isPositive X).mp hX).isSymmetric
  let hBs := ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  have hM : 0 ≤ B * CFC.rpow X p * B := by
    simpa only [(IsSelfAdjoint.of_nonneg hB).star_eq] using
      (star_left_conjugate_nonneg (CFC.rpow_nonneg (a := X) (y := p)) B)
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hXs.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hBs hcomm]
  refine iSup_le fun r => iSup_le fun s => ?_
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  by_cases hv0 : v = 0
  · simp [hv0]
  have hr : (r.re : ℂ) = r := Complex.conj_eq_iff_re.mp
    (hXs.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv.1, hv0⟩))
  have hs : (s.re : ℂ) = s := Complex.conj_eq_iff_re.mp
    (hBs.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv.2, hv0⟩))
  have hXv : X v = (r.re : ℂ) • v := by
    simpa only [hr] using (Module.End.mem_eigenspace_iff.mp hv.1)
  have hBv : B v = (s.re : ℂ) • v := by
    simpa only [hs] using (Module.End.mem_eigenspace_iff.mp hv.2)
  have hr0 : 0 ≤ r.re := spectrum_nonneg_of_nonneg hX
    (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm hv0 hXv)
  have hs0 : 0 ≤ s.re := spectrum_nonneg_of_nonneg hB
    (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm hv0 hBv)
  have hMv : (B * CFC.rpow X p * B) v = ((s.re * r.re ^ p * s.re : ℝ) : ℂ) • v := by
    simp only [Module.End.mul_apply, hBv, map_smul, rpow_eigen hX p hv0 hXv, smul_smul]
    push_cast
    congr 1
    ring
  rw [rpow_eigen hM (1 / p) hv0 hMv]
  simp only [Module.End.mul_apply, rpow_eigen hB (2 / p) hv0 hBv, map_smul, hXv, smul_smul]
  have hreal : (s.re * r.re ^ p * s.re) ^ (1 / p) = s.re ^ (2 / p) * r.re := by
    rw [Real.mul_rpow (mul_nonneg hs0 (Real.rpow_nonneg hr0 _)) hs0,
      Real.mul_rpow hs0 (Real.rpow_nonneg hr0 _), ← Real.rpow_mul hr0,
      mul_one_div, div_self hp.ne', Real.rpow_one]
    calc
      s.re ^ (1 / p) * r.re * s.re ^ (1 / p) =
          (s.re ^ (1 / p) * s.re ^ (1 / p)) * r.re := by ring
      _ = s.re ^ (2 / p) * r.re := by
        rw [← Real.rpow_add' hs0 (by positivity : 0 < 1 / p + 1 / p).ne']
        congr 2
        ring
  rw [hreal]
  push_cast
  rfl

private theorem rpow_conj
    {A : Type u} [Qudit A] (U : unitary (L A)) (X : L A) (p : ℝ) :
    CFC.rpow ((U : L A) * X * (star U : L A)) p =
      (U : L A) * CFC.rpow X p * (star U : L A) := by
  let φ := Unitary.conjStarAlgAut ℂ (L A) U
  let f : NNReal → NNReal := fun x => x ^ p
  change cfc f (φ X) = φ (cfc f X)
  have hnn : (0 : L A) ≤ φ X ↔ (0 : L A) ≤ X := by
    conv_lhs => rw [show (0 : L A) = φ 0 from (map_zero φ).symm]
    exact OrderIsoClass.map_le_map_iff φ
  have hspec : spectrum NNReal (φ X) = spectrum NNReal X :=
    AlgEquiv.spectrum_eq (φ.restrictScalars NNReal).toAlgEquiv X
  by_cases h : (0 ≤ X) ∧ ContinuousOn f (spectrum NNReal X)
  · exact (StarAlgHomClass.map_cfc (S := ℂ) φ f X h.2 (map_continuous φ) h.1
      (hnn.mpr h.1)).symm
  · rw [cfc_apply_of_not_and X h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

private theorem trace_conj_power_conj
    {A : Type u} [Qudit A] (U : unitary (L A)) (X B : L A) (p : ℝ) :
    SandwichedRenyiRelativeEntropy.traceConjPow p
      ((U : L A) * B * (star U : L A)) ((U : L A) * X * (star U : L A)) =
      SandwichedRenyiRelativeEntropy.traceConjPow p B X := by
  let φ := Unitary.conjStarAlgAut ℂ (L A) U
  have hpow (Y : L A) (q : ℝ) : CFC.rpow (φ Y) q = φ (CFC.rpow Y q) :=
    rpow_conj U Y q
  change (Tr (CFC.rpow (star (φ B) * CFC.rpow (φ X) p * φ B) (1 / p))).re = _
  rw [hpow, ← map_star, ← map_mul, ← map_mul, hpow]
  exact congrArg Complex.re (SandwichedRenyiRelativeEntropy.trace_unitary_conj _ U)

private theorem sign_commutes
    {A : Type u} [Qudit A] (B : L A) (hB : B.IsSymmetric)
    (phase : spectralEigenvalue B → Bool) : Commute (spectralSignUnitary B phase) B := by
  unfold Commute SemiconjBy spectralSignUnitary
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_smul_comm, spectralProjector_mul B hB, mul_spectralProjector]

private theorem trace_conj_power_pinching
    {A : Type u} [Qudit A] [Nontrivial A] {X B : L A}
    (hX : X ∈ SandwichedRenyiRelativeEntropy.pdSetLM)
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    SandwichedRenyiRelativeEntropy.traceConjPow p B X ≤
      SandwichedRenyiRelativeEntropy.traceConjPow p B
        ((spectralPinchingChannel B
          ((LinearMap.nonneg_iff_isPositive B).mp
            (SandwichedRenyiRelativeEntropy.nonneg_of_pdSetLM hB)).isSymmetric).toFun X) := by
  classical
  let hBs := ((LinearMap.nonneg_iff_isPositive B).mp
    (SandwichedRenyiRelativeEntropy.nonneg_of_pdSetLM hB)).isSymmetric
  let I := spectralEigenvalue B → Bool
  let U : I → unitary (L A) := fun i =>
    ⟨spectralSignUnitary B i, spectralSignUnitary_mem_unitary B hBs i⟩
  let Y : I → L A := fun i => (U i : L A) * X * (star (U i) : L A)
  let w : ℝ := (Fintype.card I : ℝ)⁻¹
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : ∑ _i : I, w = 1 := by simp [w, hcard]
  have hY : ∀ i : I, Y i ∈ SandwichedRenyiRelativeEntropy.pdSetLM := by
    intro i
    have h := SandwichedRenyiRelativeEntropy.pdSetLM_conj hX
      (Unitary.isUnit_coe (U := star (U i)))
    simpa only [Unitary.coe_star, star_star] using h
  have hval : ∀ i : I, SandwichedRenyiRelativeEntropy.traceConjPow p B (Y i) =
      SandwichedRenyiRelativeEntropy.traceConjPow p B X := by
    intro i
    have hfix : (U i : L A) * B * (star (U i) : L A) = B := by
      rw [(sign_commutes B hBs i).eq, mul_assoc]
      change B * ((U i : L A) * (star (U i) : L A)) = B
      rw [(U i).property.2, mul_one]
    have h := trace_conj_power_conj (U i) X B p
    rw [hfix] at h
    exact h
  have havg : (spectralPinchingChannel B hBs).toFun X = ∑ i : I, w • Y i := by
    rw [spectralPinching_mixedUnitary_average]
    apply Finset.sum_congr rfl
    intro i _
    change (Fintype.card I : ℂ)⁻¹ • Y i = w • Y i
    rw [show (Fintype.card I : ℂ)⁻¹ = (w : ℂ) by simp [w]]
    exact Complex.coe_smul w (Y i)
  have h := (SandwichedRenyiRelativeEntropy.traceConjPow_concave_pos_lm hp hp1 B
    (SandwichedRenyiRelativeEntropy.isUnit_of_pdSetLM hB)).le_map_sum
      (t := Finset.univ) (w := fun _ : I => w) (p := Y)
      (fun _ _ => by dsimp [w]; positivity) hw (fun i _ => hY i)
  simpa only [hval, ← Finset.sum_smul, hw, one_smul, ← havg] using h

private theorem trace_conj_power_bound_pd
    {A : Type u} [Qudit A] [Nontrivial A] {X B : L A}
    (hX : X ∈ SandwichedRenyiRelativeEntropy.pdSetLM)
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    SandwichedRenyiRelativeEntropy.traceConjPow p B X ≤ (Tr (X * CFC.rpow B (2 / p))).re := by
  have hX0 := SandwichedRenyiRelativeEntropy.nonneg_of_pdSetLM hX
  have hB0 := SandwichedRenyiRelativeEntropy.nonneg_of_pdSetLM hB
  let hBs := ((LinearMap.nonneg_iff_isPositive B).mp hB0).isSymmetric
  let P := spectralPinchingChannel B hBs
  have hPX : 0 ≤ P.toFun X := by
    rw [spectralPinchingChannel_apply]
    apply Finset.sum_nonneg
    intro i _
    have hs : star (spectralProjector B i) = spectralProjector B i :=
      (spectralProjector_isSymmetric B i).adjoint_eq
    simpa only [hs] using (star_left_conjugate_nonneg hX0 (spectralProjector B i))
  have hfixed : P.toFun (CFC.rpow B (2 / p)) = CFC.rpow B (2 / p) :=
    (spectralPinchingChannel_eq_iff_commute B hBs _).mpr
      (rpow_commute (Commute.refl B) (2 / p))
  have htrace : Tr (P.toFun X * CFC.rpow B (2 / p)) = Tr (X * CFC.rpow B (2 / p)) := by
    calc
      Tr (P.toFun X * CFC.rpow B (2 / p)) = Tr (CFC.rpow B (2 / p) * P.toFun X) :=
        LinearMap.trace_mul_comm ℂ _ _
      _ = Tr (P.toFun (CFC.rpow B (2 / p)) * X) := trace_mul_spectralPinching B hBs _ _
      _ = Tr (CFC.rpow B (2 / p) * X) := by rw [hfixed]
      _ = Tr (X * CFC.rpow B (2 / p)) := LinearMap.trace_mul_comm ℂ _ _
  calc
    SandwichedRenyiRelativeEntropy.traceConjPow p B X ≤
        SandwichedRenyiRelativeEntropy.traceConjPow p B (P.toFun X) :=
      trace_conj_power_pinching hX hB hp hp1
    _ = (Tr (X * CFC.rpow B (2 / p))).re := by
      unfold SandwichedRenyiRelativeEntropy.traceConjPow
      rw [(IsSelfAdjoint.of_nonneg hB0).star_eq,
        commuting_sandwich_power hPX hB0 (spectralPinchingChannel_commute B hBs X) hp, htrace]

private theorem rpow_tendsto
    {A : Type u} [Qudit A] {ι : Type*} {l : Filter ι} {f : ι → L A} {X : L A}
    (hX : 0 ≤ X) (hf : Tendsto f l (𝓝 X)) (hf0 : ∀ᶠ i in l, 0 ≤ f i)
    {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun i => CFC.rpow (f i) p) l (𝓝 (CFC.rpow X p)) := by
  have hc : ContinuousOn (fun Y : L A => CFC.rpow Y p) {Y : L A | 0 ≤ Y} := by
    exact continuousOn_id.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p))
      Filter.univ_mem (ha' := fun _ hY => hY)
      (hf := NNReal.continuousOn_rpow_const (.inr hp))
  exact (hc X hX).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hf, hf0⟩)

private theorem trace_conj_power_bound
    {A : Type u} [Qudit A] [Nontrivial A] {X B : L A}
    (hX : 0 ≤ X) (hB : 0 ≤ B) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    SandwichedRenyiRelativeEntropy.traceConjPow p B X ≤ (Tr (X * CFC.rpow B (2 / p))).re := by
  let R : L A → ℝ → L A := fun Y ε => Y + (ε : ℂ) • 1
  have hpd (Y : L A) (hY : 0 ≤ Y) {ε : ℝ} (hε : 0 < ε) :
      R Y ε ∈ SandwichedRenyiRelativeEntropy.pdSetLM :=
    SandwichedRenyiRelativeEntropy.pdSetLM_add_nonneg hY
      (SandwichedRenyiRelativeEntropy.pos_smul_one_pdSetLM hε)
  have hpos (Y : L A) (hY : 0 ≤ Y) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ R Y ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact SandwichedRenyiRelativeEntropy.nonneg_of_pdSetLM (hpd Y hY hε)
  have hlim (Y : L A) : Tendsto (R Y) (𝓝[>] (0 : ℝ)) (𝓝 Y) := by
    simpa only [R, Complex.ofReal_zero, zero_smul, add_zero] using
      (tendsto_const_nhds.add
        (((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).smul_const (1 : L A)))
  have hXp := rpow_tendsto hX (hlim X) (hpos X hX) hp.le
  have hM : Tendsto (fun ε => star (R B ε) * CFC.rpow (R X ε) p * R B ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (star B * CFC.rpow X p * B)) :=
    ((hlim B).star.mul hXp).mul (hlim B)
  have hMq := rpow_tendsto (star_left_conjugate_nonneg CFC.rpow_nonneg B) hM
    (Eventually.of_forall fun ε => star_left_conjugate_nonneg CFC.rpow_nonneg (R B ε))
    (by positivity : 0 ≤ 1 / p)
  have hTr : Continuous (fun Y : L A => (Tr Y).re) :=
    Complex.continuous_re.comp (LinearMap.continuous_of_finiteDimensional (Tr : L A →ₗ[ℂ] ℂ))
  have hleft : Tendsto (fun ε => SandwichedRenyiRelativeEntropy.traceConjPow p (R B ε) (R X ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (SandwichedRenyiRelativeEntropy.traceConjPow p B X)) :=
    hTr.tendsto _ |>.comp hMq
  have hBq := rpow_tendsto hB (hlim B) (hpos B hB) (by positivity : 0 ≤ 2 / p)
  have hright : Tendsto (fun ε => (Tr (R X ε * CFC.rpow (R B ε) (2 / p))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (Tr (X * CFC.rpow B (2 / p))).re) :=
    hTr.tendsto _ |>.comp ((hlim X).mul hBq)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact trace_conj_power_bound_pd (hpd X hX hε) (hpd B hB hε) hp hp1

private theorem sandwiched_trace_le_petz
    {A : Type u} [Qudit A] [Nontrivial A] {ρ σ : L A}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) {α : ℝ} (hα : 1 < α) :
    (SandwichedRenyiRelativeEntropy.sandwichedQuasi α ρ σ).re ≤ OPT.petzTracePowerRaw α ρ σ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  let b : ℝ := (1 - α) / (2 * α)
  have hp : 0 < 1 / α := one_div_pos.mpr hα0
  have hp1 : 1 / α ≤ 1 := (div_le_one hα0).mpr hα.le
  have h := trace_conj_power_bound
    (X := CFC.rpow ρ α) (B := CFC.rpow σ b) CFC.rpow_nonneg CFC.rpow_nonneg hp hp1
  have hcomp : CFC.rpow (CFC.rpow ρ α) (1 / α) = ρ := by
    rw [rpow_comp hρ, mul_one_div, div_self hα0.ne']
    exact CFC.rpow_one ρ hρ
  have hb : b * (2 / (1 / α)) = 1 - α := by
    dsimp [b]
    field_simp
  have hstar : star (CFC.rpow σ b) = CFC.rpow σ b :=
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  unfold SandwichedRenyiRelativeEntropy.traceConjPow at h
  rw [hstar,
    hcomp, one_div_one_div, rpow_comp hσ, hb] at h
  exact h

private theorem rpow_ne_zero
    {A : Type u} [Qudit A] [Nontrivial A] {X : L A}
    (hX : 0 ≤ X) (hX0 : X ≠ 0) {p : ℝ} (hp : p ≠ 0) : CFC.rpow X p ≠ 0 := by
  intro hzero
  have h := rpow_comp hX p (1 / p)
  have h1 : CFC.rpow X 1 = X := CFC.rpow_one X hX
  rw [hzero, CFC.zero_rpow (one_div_ne_zero hp), mul_one_div, div_self hp, h1] at h
  exact hX0 h.symm

private theorem sandwiched_trace_pos
    {A : Type u} [Qudit A] [Nontrivial A] {ρ σ : L A}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    0 < (SandwichedRenyiRelativeEntropy.sandwichedQuasi α ρ σ).re := by
  have hρ0 : 0 ≤ ρ := (LinearMap.nonneg_iff_isPositive ρ).mpr hρ.1
  have hσ0 : 0 ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ.1
  let b : ℝ := (1 - α) / (2 * α)
  let P := OPT.petzSupportRpow σ b
  let N := OPT.petzSupportRpow σ (-b)
  let K := P * ρ * P
  have hP : 0 ≤ P := OPT.petzSupportRpow_nonneg σ b
  have hK : 0 ≤ K := by
    simpa only [(IsSelfAdjoint.of_nonneg hP).star_eq] using
      (star_left_conjugate_nonneg hρ0 P)
  have hNP : N * P = OPT.petzSupportRpow σ 0 := by
    dsimp [N, P]
    rw [OPT.petzSupportRpow_add hσ0, neg_add_cancel]
  have hPN : P * N = OPT.petzSupportRpow σ 0 := by
    dsimp [N, P]
    rw [OPT.petzSupportRpow_add hσ0, add_neg_cancel]
  have hK0 : K ≠ 0 := by
    intro hzero
    have hrec : N * K * N = ρ := by
      calc
        N * K * N = (N * P) * ρ * (P * N) := by dsimp [K]; noncomm_ring
        _ = ρ := by
          rw [hNP, hPN, OPT.petzSupportRpow_zero_mul_eq_of_ker_le hσ0 hρ0 hsupp,
            OPT.mul_petzSupportRpow_zero_eq_of_ker_le hσ0 hρ0 hsupp]
    rw [hzero, mul_zero, zero_mul] at hrec
    exact IsDensity.ne_zero hρ hrec.symm
  have hpos := QuantumEntropy.trace_re_pos_of_ne_zero
    CFC.rpow_nonneg (rpow_ne_zero hK hK0 (by linarith : α ≠ 0))
  have hb : b ≠ 0 := div_ne_zero (by linarith) (mul_ne_zero (by norm_num) (by linarith))
  simpa only [K, P, OPT.petzSupportRpow_of_ne_zero σ hb] using hpos

theorem gsl_c59 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (α : ℝ),
  α ∈ Set.Ioc 1 2 → sand.{u} α ρ.1 σ.1 ≤ petz.{u} α ρ.1 σ.1)
:= by
  intro A _ _ ρ σ α hα
  classical
  have hα0 : 0 < α := lt_trans zero_lt_one hα.1
  have hαne : α ≠ 1 := hα.1.ne'
  have hαlt : ¬ α < 1 := not_lt_of_ge hα.1.le
  by_cases hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1
  · have hzero : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα0).ne'
    have hone : ENNReal.ofReal α ≠ 1 := by
      intro h
      have ht := congrArg ENNReal.toReal h
      simp only [ENNReal.toReal_ofReal hα0.le, ENNReal.toReal_one] at ht
      exact hαne ht
    have hsand : sand α ρ.1 σ.1 =
        (((1 / (α - 1)) * Real.logb 2
          (SandwichedRenyiRelativeEntropy.sandwichedQuasi α ρ.1 σ.1).re : ℝ) : EReal) := by
      unfold sand
      rw [dif_pos ρ.2, dif_pos σ.2,
        SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits_standard_order
          hzero hone ENNReal.ofReal_ne_top
          (by rw [ENNReal.toReal_ofReal hα0.le]; linarith) ρ.1 σ.1 ρ.2 σ.2,
        ENNReal.toReal_ofReal hα0.le]
      simp only [SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite,
        hαne, hsupp, hαlt, not_true_eq_false, and_false, false_and, or_self,
        ↓reduceIte, ρ.2.2, Complex.one_re, div_one]
    have hpetz : petz α ρ.1 σ.1 =
        (((1 / (α - 1)) * Real.logb 2 (OPT.petzTracePowerRaw α ρ.1 σ.1) : ℝ) : EReal) := by
      simp only [petz, hα0.le, ρ.2, σ.2, ↓reduceDIte,
        OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
        hα0.ne', hαne, hsupp, true_or,
        OPT.petzSupportTracePower_eq_raw α ρ.1 σ.1 hα0.ne' hαne, one_div]
    rw [hsand, hpetz, EReal.coe_le_coe_iff]
    apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (sub_nonneg.mpr hα.1.le))
    exact Real.logb_le_logb_of_le (by norm_num)
      (sandwiched_trace_pos ρ.2 σ.2 hsupp hα.1)
      (sandwiched_trace_le_petz
        ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1) hα.1)
  · have hpetz : petz α ρ.1 σ.1 = ⊤ := by
      simp only [petz, hα0.le, ρ.2, σ.2, ↓reduceDIte,
        OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
        hα0.ne', hαne, hsupp, hαlt, false_and, or_self, ↓reduceDIte]
    rw [hpetz]
    exact le_top

end GourResource

