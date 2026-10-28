/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

/-!
# Tensor product CFC infrastructure

Infrastructure for the continuous functional calculus on tensor products,
proving that `CFC.rpow` distributes over tensor products of operators:
`(A ⊗ B)^p = A^p ⊗ B^p`.

## Strategy

Factor `TensorProduct.map A B = A.rTensor ℋ₂ * B.lTensor ℋ₁` where the two factors commute,
then use `StarAlgHomClass.map_cfc` to distribute `CFC.rpow` through each factor.

## Main results

* `TensorCFC.rTensorStarAlgHom` / `lTensorStarAlgHom`:
  The maps `A ↦ A.rTensor ℋ₂` and `B ↦ B.lTensor ℋ₁` as star algebra homomorphisms.
* `TensorCFC.rpow_rTensor` / `rpow_lTensor`:
  `CFC.rpow` distributes through `rTensor` / `lTensor`.
* `TensorCFC.rpow_tensorProduct`:
  `CFC.rpow (map A B) p = map (CFC.rpow A p) (CFC.rpow B p)` (modulo `rpow_mul_comm_nonneg`).
-/

open QuantumState QuantumChannel TensorProduct
open scoped NNReal Polynomial

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Natural-power eigenvector formula: `A v = c • v ⟹ Aⁿ v = cⁿ • v`. -/
private lemma pow_apply_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {c : ℂ} (hv : A v = c • v) :
    ∀ n : ℕ, (A ^ n) v = c ^ n • v
  | 0 => by rw [pow_zero, ContinuousLinearMap.one_apply, pow_zero, one_smul]
  | n + 1 => by
    rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hv, map_smul,
        pow_apply_of_eigenvector hv n, smul_smul]
    congr 1
    rw [← pow_succ']

end

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Real-polynomial eigenvector formula: `A v = (c:ℂ) • v ⟹ (aeval A p) v = (p.eval c)
  • v`. -/
private lemma aeval_apply_of_eigenvector_real
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {c : ℝ} (hv : A v = ((c : ℝ) : ℂ) • v) (p : Polynomial ℝ) :
    (Polynomial.aeval A p) v = ((p.eval c : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    rw [show ((algebraMap ℝ (B ℋ)) r : B ℋ) = ((r : ℝ) : ℂ) • (1 : B ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : B ℋ) = (algebraMap ℂ (B ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, ContinuousLinearMap.add_apply, hp, hq,
        Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow]
    rw [show ((algebraMap ℝ (B ℋ)) r : B ℋ) = ((r : ℝ) : ℂ) • (1 : B ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : B ℋ) = (algebraMap ℂ (B ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [smul_mul_assoc, one_mul, ContinuousLinearMap.smul_apply,
        pow_apply_of_eigenvector hv (n + 1), smul_smul]

end

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- **CFC on an eigenvector (real version).** If `A` is self-adjoint, `A v = μ • v`, and
    `μ ∈ spectrum ℝ A`, then `cfc f A v = f(μ) • v`. Proof by Lagrange interpolation:
    a polynomial `q` agreeing with `f` on the (finite) spectrum gives `cfc f A = aeval A q`,
    and `aeval A q v = q(μ) • v = f(μ) • v`. -/
lemma cfc_real_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    cfc f A v = ((f μ : ℝ) : ℂ) • v := by
  classical
  set S : Finset ℝ := (TensorCFC.spectrum_real_finite A).toFinset with hS
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

end

end TensorCFC
