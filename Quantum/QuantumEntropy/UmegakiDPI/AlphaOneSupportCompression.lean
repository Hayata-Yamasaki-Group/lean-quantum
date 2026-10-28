import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupportResiduals

open QuantumState QuantumChannel GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology
namespace SandwichedRenyiRelativeEntropy.AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
attribute [local instance] subspaceQudit

omit [Nontrivial H] in
/-- Real spectral membership for linear endomorphisms. -/
lemma mem_spectrum_real_lm_iff {A : L H} {r : ℝ} :
    r ∈ spectrum ℝ A ↔ (r : ℂ) ∈ spectrum ℂ A := by
  letI : IsScalarTower ℝ ℂ (L H) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)]
  rfl

omit [Nontrivial H] in
/-- The real spectrum of a finite-dimensional linear endomorphism is finite. -/
lemma spectrum_real_finite_lm (A : L H) : Set.Finite (spectrum ℝ A) := by
  have heq : spectrum ℝ A = (fun r : ℝ => (r : ℂ)) ⁻¹' spectrum ℂ A := by
    ext r
    exact mem_spectrum_real_lm_iff
  rw [heq]
  exact (Module.End.finite_spectrum A).preimage
    (fun _ _ _ _ h => Complex.ofReal_injective h)

omit [Nontrivial H] in
/-- Polynomial functional calculus on an eigenvector, entirely in linear maps. -/
lemma aeval_apply_eigenvector_lm (A : L H) (μ : ℂ) (v : H)
    (hv : A v = μ • v) (q : Polynomial ℝ) :
    Polynomial.aeval A q v = Polynomial.aeval μ q • v := by
  letI : IsScalarTower ℝ ℂ (L H) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  have hp (n : ℕ) : (A ^ n) v = μ ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      change (A ^ n) (A v) = _
      rw [hv, map_smul, ih, smul_smul, pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, add_smul]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    change (algebraMap ℝ (L H) r) ((A ^ n) v) = _
    rw [hp, map_smul, IsScalarTower.algebraMap_apply ℝ ℂ (L H)]
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, smul_smul, mul_comm]

omit [Nontrivial H] in
/-- Finite ambient spectral interpolation replaces CFC by a real polynomial. -/
lemma exists_cfc_polynomial_lm {A : L H} (hA : IsSelfAdjoint A) (f : ℝ → ℝ) :
    ∃ q : Polynomial ℝ, (∀ r ∈ spectrum ℝ A, q.eval r = f r) ∧
      cfc f A = Polynomial.aeval A q := by
  classical
  let S := (spectrum_real_finite_lm A).toFinset
  let q := Lagrange.interpolate S id f
  have he (r : ℝ) (hr : r ∈ spectrum ℝ A) : q.eval r = f r :=
    Lagrange.eval_interpolate_at_node f Function.injective_id.injOn
      ((spectrum_real_finite_lm A).mem_toFinset.mpr hr)
  refine ⟨q, he, ?_⟩
  calc
    cfc f A = cfc q.eval A := cfc_congr (fun r hr => (he r hr).symm)
    _ = Polynomial.aeval A q := cfc_polynomial q A hA

/-- Eigenvectors of the compressed linear map lift to ambient eigenvectors. -/
lemma spectrum_compress_subset {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) :
    spectrum ℝ (compress σ A) ⊆ spectrum ℝ A := by
  intro r hr
  have hev := Module.End.HasEigenvalue.of_mem_spectrum (mem_spectrum_real_lm_iff.mp hr)
  obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
  have hv' : compress σ A v = (r : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv
  have he : A (v : H) = (r : ℂ) • (v : H) := by
    rw [← coe_compress_apply hA hsupp v]
    exact congrArg (fun y : supportSpace σ => (y : H)) hv'
  apply mem_spectrum_real_lm_iff.mpr
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector
  exact ⟨Module.End.mem_eigenspace_iff.mpr he, fun hz => hv0 (Subtype.ext hz)⟩

/-- Polynomial evaluations intertwine the support inclusion, by an eigenbasis. -/
lemma coe_aeval_compress_apply {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) (q : Polynomial ℝ) (x : supportSpace σ) :
    (Polynomial.aeval (compress σ A) q x : H) = Polynomial.aeval A q (x : H) := by
  classical
  have hp := (LinearMap.nonneg_iff_isPositive (compress σ A)).mp (compress_nonneg hA)
  let b := hp.isSymmetric.eigenvectorBasis rfl
  let eig := hp.isSymmetric.eigenvalues rfl
  have heig (i) : compress σ A (b i) = (eig i : ℂ) • b i :=
    hp.isSymmetric.apply_eigenvectorBasis rfl i
  have heigH (i) : A (b i : H) = (eig i : ℂ) • (b i : H) := by
    rw [← coe_compress_apply hA hsupp (b i)]
    exact congrArg (fun y : supportSpace σ => (y : H)) (heig i)
  have heq : (supportSpace σ).subtype ∘ₗ Polynomial.aeval (compress σ A) q =
      Polynomial.aeval A q ∘ₗ (supportSpace σ).subtype := by
    apply b.toBasis.ext
    intro i
    change (Polynomial.aeval (compress σ A) q (b i) : H) =
      Polynomial.aeval A q (b i : H)
    rw [aeval_apply_eigenvector_lm _ _ _ (heig i),
      aeval_apply_eigenvector_lm _ _ _ (heigH i)]
    rfl
  exact congrArg (fun T : supportSpace σ →ₗ[ℂ] H => T x) heq

/-- Both LM expressions reduce to one polynomial on the ambient finite spectrum. -/
lemma coe_cfc_compress_apply_lm {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) (f : ℝ → ℝ) (x : supportSpace σ) :
    (cfc f (compress σ A) x : H) = cfc f A (x : H) := by
  obtain ⟨q, hq, hAq⟩ := exists_cfc_polynomial_lm (IsSelfAdjoint.of_nonneg hA) f
  have hcq : cfc f (compress σ A) = Polynomial.aeval (compress σ A) q := by
    calc
      cfc f (compress σ A) = cfc q.eval (compress σ A) :=
        cfc_congr (fun r hr => (hq r (spectrum_compress_subset hA hsupp hr)).symm)
      _ = Polynomial.aeval (compress σ A) q :=
        cfc_polynomial q _ (IsSelfAdjoint.of_nonneg (compress_nonneg hA))
  rw [hcq, hAq]
  exact coe_aeval_compress_apply hA hsupp q x

/-- All exponent signs intertwine on the support; zero exponent keeps the identity. -/
lemma coe_rpow_compress_apply {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) (t : ℝ) (x : supportSpace σ) :
    (CFC.rpow (compress σ A) t x : H) = CFC.rpow A t (x : H) := by
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (ha := compress_nonneg hA),
    CFC.rpow_eq_cfc_real (ha := hA)]
  exact coe_cfc_compress_apply_lm hA hsupp (fun r => r ^ t) x

/-- Totalized logarithms reduce to the same interpolating polynomial on the support. -/
lemma coe_log_compress_apply {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) (x : supportSpace σ) :
    (CFC.log (compress σ A) x : H) = CFC.log A (x : H) := by
  exact coe_cfc_compress_apply_lm hA hsupp Real.log x

/-- Compression intertwines every real power, including the identity at zero. -/
lemma compress_rpow {A σ : L H} [Nontrivial (supportSpace σ)]
    (hA : 0 ≤ A) (hsupp : SupportLE A σ) (t : ℝ) :
    compress σ (CFC.rpow A t) = CFC.rpow (compress σ A) t := by
  ext x
  change (supportSpace σ).starProjection (CFC.rpow A t (x : H)) =
    (CFC.rpow (compress σ A) t x : H)
  rw [← coe_rpow_compress_apply hA hsupp]
  exact (supportSpace σ).starProjection_eq_self_iff.mpr (Subtype.property _)

/-- Compression of the logarithmic product is the logarithmic product in the corner. -/
lemma compress_umegaki_product {ρ σ : L H} [Nontrivial (supportSpace σ)]
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    compress σ (ρ * (CFC.log ρ - CFC.log σ)) =
      compress σ ρ * (CFC.log (compress σ ρ) - CFC.log (compress σ σ)) := by
  ext x
  change (supportSpace σ).starProjection
    (ρ (CFC.log ρ (x : H) - CFC.log σ (x : H))) =
    (compress σ ρ ((CFC.log (compress σ ρ) - CFC.log (compress σ σ)) x) : H)
  rw [coe_compress_apply hρ hsupp]
  change _ = ρ ((CFC.log (compress σ ρ) x : H) - (CFC.log (compress σ σ) x : H))
  rw [coe_log_compress_apply hρ hsupp, coe_log_compress_apply hσ (le_refl _)]
  exact (supportSpace σ).starProjection_eq_self_iff.mpr (apply_mem_supportSpace hρ hsupp _)

/-- Compression intertwines the sandwich for all inner exponents. -/
lemma compress_sandwich {ρ σ : L H} [Nontrivial (supportSpace σ)]
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) (t : ℝ) :
    compress σ (CFC.rpow σ t * ρ * CFC.rpow σ t) =
      CFC.rpow (compress σ σ) t * compress σ ρ * CFC.rpow (compress σ σ) t := by
  ext x
  have he :
      (CFC.rpow (compress σ σ) t (compress σ ρ (CFC.rpow (compress σ σ) t x)) : H) =
      CFC.rpow σ t (ρ (CFC.rpow σ t (x : H))) := by
    rw [coe_rpow_compress_apply hσ (le_refl _), coe_compress_apply hρ hsupp,
      coe_rpow_compress_apply hσ (le_refl _)]
  change (supportSpace σ).starProjection
    (CFC.rpow σ t (ρ (CFC.rpow σ t (x : H)))) =
    (CFC.rpow (compress σ σ) t (compress σ ρ (CFC.rpow (compress σ σ) t x)) : H)
  rw [← he]
  exact (supportSpace σ).starProjection_eq_self_iff.mpr (Subtype.property _)

/-- C02: exact compression invariance, including the alpha = 1 branch. -/
lemma compression_invariance {ρ σ : L H} [Nontrivial (supportSpace σ)]
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    Tr (compress σ ρ) = Tr ρ ∧
    (∀ α : ℝ, 0 < α →
      sandwichedQuasi α (compress σ ρ) (compress σ σ) = sandwichedQuasi α ρ σ) ∧
    ρ * (CFC.log ρ - CFC.log σ) =
      lift σ (compress σ ρ * (CFC.log (compress σ ρ) - CFC.log (compress σ σ))) ∧
    umegakiNorm (compress σ ρ) (compress σ σ) = umegakiNorm ρ σ := by
  have hprod := umegaki_product_eq_lift_compress hρ hσ hsupp
  rw [compress_umegaki_product hρ hσ hsupp] at hprod
  refine ⟨trace_compress hρ hsupp, ?_, hprod, ?_⟩
  · intro α hα
    let t := (1 - α) / (2 * α)
    let K := CFC.rpow σ t * ρ * CFC.rpow σ t
    have hK : 0 ≤ K := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
    have hKs : SupportLE K σ := sandwich_support hσ hsupp t
    have hpower : SupportLE (CFC.rpow K α) σ := by
      intro x hx
      exact rpow_apply_eq_zero_of_mem_ker hK (hKs hx) (ne_of_gt hα)
    change Tr (CFC.rpow
      (CFC.rpow (compress σ σ) t * compress σ ρ * CFC.rpow (compress σ σ) t) α) =
      Tr (CFC.rpow K α)
    rw [← compress_sandwich hρ hσ hsupp, ← compress_rpow hK hKs]
    exact trace_compress CFC.rpow_nonneg hpower
  · unfold umegakiNorm
    rw [trace_compress hρ hsupp, hprod, trace_lift]


end SandwichedRenyiRelativeEntropy.AlphaOneSupport
