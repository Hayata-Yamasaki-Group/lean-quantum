import Quantum.QuantumEntropy.CFCDerivLMCompat.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.Common.Support
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Support inclusion and spectral identities for linear maps. -/

namespace SandwichedRenyiRelativeEntropy
open QuantumState QuantumChannel
open scoped ComplexOrder
universe u

/-- Support inclusion for linear maps. -/
abbrev suppLE {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ρ σ : L ℋ) : Prop :=
  SupportLE ρ σ

private lemma pow_apply_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℂ} (hv : A v = c • v) :
    ∀ n : ℕ, (A ^ n) v = c ^ n • v
  | 0 => by rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | n + 1 => by
    rw [pow_succ, Module.End.mul_apply, hv, LinearMap.map_smul,
        pow_apply_of_eigenvector hv n, smul_smul]
    congr 1
    rw [← pow_succ']

/-- Real-polynomial eigenvector formula: `A v = (c:ℂ) • v ⟹ (aeval A p) v = (p.eval c) • v`. -/
private lemma aeval_apply_of_eigenvector_real
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℝ} (hv : A v = ((c : ℝ) : ℂ) • v) (p : Polynomial ℝ) :
    (Polynomial.aeval A p) v = ((p.eval c : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [LinearMap.smul_apply, Module.End.one_apply]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, LinearMap.add_apply, hp, hq,
        Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [smul_mul_assoc, one_mul, LinearMap.smul_apply,
        pow_apply_of_eigenvector hv (n + 1), smul_smul]

/-- `spectrum ℝ A` is finite for `A : L ℋ` (finite dimension). -/
private lemma spectrum_real_finite {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (A : L ℋ) :
    (spectrum ℝ A).Finite := by
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- **CFC on an eigenvector (real version).** If `A` is self-adjoint, `A v = μ • v`, and
    `μ ∈ spectrum ℝ A`, then `cfc f A v = f(μ) • v`. Proof by Lagrange interpolation:
    a polynomial `q` agreeing with `f` on the (finite) spectrum gives `cfc f A = aeval A q`,
    and `aeval A q v = q(μ) • v = f(μ) • v`. -/
lemma cfc_real_apply_eigenvector_lm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    cfc f A v = ((f μ : ℝ) : ℂ) • v := by
  classical
  set S : Finset ℝ := (spectrum_real_finite A).toFinset with hS
  set q : Polynomial ℝ := Lagrange.interpolate S id f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have hEvalNode : ∀ x ∈ S, q.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (r := f) (v := id) hInj hx
    simpa using this
  have hEqOn : (spectrum ℝ A).EqOn f (fun x => q.eval x) := by
    intro x hx
    have hxS : x ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hx
    exact (hEvalNode x hxS).symm
  have h1 : cfc f A = cfc (fun x => q.eval x) A := cfc_congr hEqOn
  have h2 : cfc (fun x => q.eval x) A = Polynomial.aeval A q := cfc_polynomial q A
  have hμS : μ ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hμ
  rw [h1, h2, aeval_apply_of_eigenvector_real hv q, hEvalNode μ hμS]


lemma mem_spectrum_real_of_eigenvector_lm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {μ : ℝ} (hv0 : v ≠ 0) (hv : A v = (μ : ℂ) • v) :
    μ ∈ spectrum ℝ A := by
  have hev : Module.End.HasEigenvalue A (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]; exact hv
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := hev.mem_spectrum
  letI : IsScalarTower ℝ ℂ (L ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  rw [← spectrum.preimage_algebraMap ℂ] at *
  simpa using hmem


end SandwichedRenyiRelativeEntropy



namespace SandwichedRenyiRelativeEntropy
open QuantumState
universe u
variable {ℋ : Type u} [Qudit ℋ]

alias suppLE_of_CPTP := supportLE_map_of_cptp

end SandwichedRenyiRelativeEntropy

namespace SandwichedRenyiRelativeEntropy
open QuantumState
universe u

lemma norm_le_re_trace_lm {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {C : L ℋ} (hC : 0 ≤ C) : ‖C‖ ≤ (Tr C).re := by
  have hCc : (0 : B ℋ) ≤ C.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hC)
  simpa using QuantumEntropy.norm_le_re_trace hCc
end SandwichedRenyiRelativeEntropy
