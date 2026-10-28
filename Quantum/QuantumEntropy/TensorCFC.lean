/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange
import Quantum.QuantumMechanics.Channel.Basic
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

universe u v
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-! ### Star algebra homomorphisms for rTensor / lTensor -/

noncomputable def rTensorStarAlgHom : L ℋ₁ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun f := f.rTensor ℋ₂
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' f := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_rTensor f).symm

noncomputable def lTensorStarAlgHom : L ℋ₂ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun g := g.lTensor ℋ₁
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' g := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_lTensor g).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma rTensorStarAlgHom_apply (f : L ℋ₁) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f = f.rTensor ℋ₂ := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma lTensorStarAlgHom_apply (g : L ℋ₂) :
    (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g = g.lTensor ℋ₁ := rfl

/-! ### Factorization and commutativity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_rTensor_mul_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f * (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (f.rTensor ℋ₂).comp (g.lTensor ℋ₁) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_lTensor_mul_rTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g * (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (g.lTensor ℋ₁).comp (f.rTensor ℋ₂) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma commute_rTensor_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    Commute ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) f)
      ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) g) := by
  change _ * _ = _ * _
  rw [← map_eq_rTensor_mul_lTensor, ← map_eq_lTensor_mul_rTensor]

/-! ### Nonneg preservation -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma rTensorStarAlgHom_nonneg (f : L ℋ₁) (hf : 0 ≤ f) :
    0 ≤ (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 f).mp hf
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨rTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨rTensorStarAlgHom s, by
          change star (rTensorStarAlgHom s) * rTensorStarAlgHom s = rTensorStarAlgHom x
          rw [← map_star rTensorStarAlgHom, ← map_mul rTensorStarAlgHom]
          exact congr_arg rTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma lTensorStarAlgHom_nonneg (g : L ℋ₂) (hg : 0 ≤ g) :
    0 ≤ (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 g).mp hg
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨lTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨lTensorStarAlgHom s, by
          change star (lTensorStarAlgHom s) * lTensorStarAlgHom s = lTensorStarAlgHom x
          rw [← map_star lTensorStarAlgHom, ← map_mul lTensorStarAlgHom]
          exact congr_arg lTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

/-! ### CFC eigenvalue property

In finite dimensions, the CFC maps eigenvectors to eigenvectors with eigenvalues
transformed by the function: if `T v = μ • v` then `cfc f T v = f(μ) • v`.
The proof uses Lagrange interpolation on the finite spectrum combined with
`cfc_congr` and `cfc_polynomial`. -/

private lemma isScalarTower_real {ℋ : Type*} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (B ℋ) :=
  ⟨fun r s a => by
    change ((r : ℂ) • s) • a = (r : ℂ) • s • a
    rw [smul_assoc]⟩

private lemma pow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (T ^ (n + 1)) v = (T ^ n) (T v) := rfl
    rw [this, hv, map_smul, ih, smul_smul, pow_succ']

private lemma aeval_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (q : ℝ[X]) :
    (Polynomial.aeval T q) v = (Polynomial.aeval μ q) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    simp only [map_add, ContinuousLinearMap.add_apply, hp₁, hp₂, add_smul]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    change (algebraMap ℝ (B ℋ) r) ((T ^ n) v) = _
    rw [pow_apply_eigenvector T μ v hv n, map_smul,
        IsScalarTower.algebraMap_apply ℝ ℂ (B ℋ)]
    simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_smul, mul_comm]

lemma spectrum_real_finite {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) : Set.Finite (spectrum ℝ T) := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), ContinuousLinearMap.spectrum_eq]
  exact (Module.End.finite_spectrum (T : L ℋ)).preimage
    (fun _ _ _ _ h => RCLike.ofReal_injective h)

private lemma cfc_apply_eigenvector_continuous {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    cfc f T v = (algebraMap ℝ ℂ (f μ)) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  have hfin := spectrum_real_finite T
  set S := hfin.toFinset
  have hS_mem : ∀ x : ℝ, x ∈ S ↔ x ∈ spectrum ℝ T := fun x => hfin.mem_toFinset
  have hμ_mem_S : μ ∈ S := (hS_mem μ).mpr hμ
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑S : Set ℝ) :=
    Function.injective_id.injOn
  let q := Lagrange.interpolate S id (fun s => f s)
  have hq_eval : ∀ x ∈ S, Polynomial.eval x q = f x :=
    fun x hx => Lagrange.eval_interpolate_at_node (fun s => f s) hinj hx
  have hcfc_eq : cfc f T = cfc q.eval T := by
    apply cfc_congr
    intro x hx
    exact (hq_eval x ((hS_mem x).mpr hx)).symm
  have hpoly : cfc q.eval T = Polynomial.aeval T q :=
    cfc_polynomial q T
  rw [hcfc_eq, hpoly, aeval_apply_eigenvector T (algebraMap ℝ ℂ μ) v hv q]
  congr 1
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  congr 1
  exact hq_eval μ hμ_mem_S

private lemma cfc_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    cfc f T v = (algebraMap ℝ ℂ (f μ)) • v := by
  exact cfc_apply_eigenvector_continuous T hT_sa f v μ hv hμ

lemma rpow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT : 0 ≤ T) (p : ℝ) (v : ℋ) (μ : ℝ)
    (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    CFC.rpow T p v = (algebraMap ℝ ℂ (μ ^ p)) • v := by
  rw [CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := T) (y := p) (ha := hT)]
  exact cfc_apply_eigenvector T (IsSelfAdjoint.of_nonneg hT)
    (fun x : ℝ => x ^ p) v μ hv hμ

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_nonneg_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  rw [map_eq_rTensor_mul_lTensor]
  exact Commute.mul_nonneg
    (rTensorStarAlgHom_nonneg A hA)
    (lTensorStarAlgHom_nonneg B hB)
    (commute_rTensor_lTensor A B)

private lemma eigenvalue_nonneg_of_nonneg {ℋ : Type*} [Qudit ℋ]
    {n : ℕ} (T : L ℋ) (hT : 0 ≤ T) (hT_sym : T.IsSymmetric) (hn : Module.finrank ℂ ℋ = n)
    (i : Fin n) : 0 ≤ hT_sym.eigenvalues hn i := by
  have hpos := (LinearMap.nonneg_iff_isPositive T).mp hT
  set v := hT_sym.eigenvectorBasis hn i
  have hv_ne : v ≠ 0 := (hT_sym.eigenvectorBasis hn).toBasis.ne_zero i
  have hinn := hpos.2 v
  rw [hT_sym.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul] at hinn
  refine nonneg_of_mul_nonneg_left hinn ?_
  rw [inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hv_ne) 2

/-- An operator whose eigenbasis is known has its real power determined on that basis. -/
private lemma rpow_eq_of_eigenbasis {E : Type*} [Qudit E] {ι : Type*}
    (T S : E →L[ℂ] E) (hT : 0 ≤ T) (p : ℝ) (b : Module.Basis ι ℂ E) (μ : ι → ℝ)
    (hTb : ∀ i, T (b i) = (algebraMap ℝ ℂ (μ i)) • b i)
    (hSb : ∀ i, S (b i) = (algebraMap ℝ ℂ (μ i ^ p)) • b i) :
    CFC.rpow T p = S := by
  haveI := isScalarTower_real (ℋ := E)
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun i => ?_
  have hspec : μ i ∈ spectrum ℝ T := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage,
      ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hTb i), b.ne_zero i⟩).mem_spectrum
  exact (rpow_apply_eigenvector T hT p (b i) (μ i) (hTb i) hspec).trans (hSb i).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- A tensor product of operators acts diagonally on a tensor product of eigenbases. -/
private lemma map_toCLM_tensorBasis {ι κ : Type*} (A : L ℋ₁) (B : L ℋ₂)
    (b₁ : Module.Basis ι ℂ ℋ₁) (b₂ : Module.Basis κ ℂ ℋ₂) (a : ι → ℝ) (c : κ → ℝ) (μ : ι × κ → ℝ)
    (ha : ∀ i, A (b₁ i) = (algebraMap ℝ ℂ (a i)) • b₁ i)
    (hc : ∀ j, B (b₂ j) = (algebraMap ℝ ℂ (c j)) • b₂ j)
    (hμ : ∀ i j, a i * c j = μ (i, j)) (ij : ι × κ) :
    (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
        ((b₁.tensorProduct b₂) ij) =
      (algebraMap ℝ ℂ (μ ij)) • (b₁.tensorProduct b₂) ij := by
  obtain ⟨i, j⟩ := ij
  change TensorProduct.map A B ((b₁.tensorProduct b₂) (i, j)) = _
  rw [Module.Basis.tensorProduct_apply, map_tmul, ha, hc, TensorProduct.smul_tmul_smul, ← map_mul,
    hμ]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- The tensor product of two positive operators is positive, as a continuous linear map. -/
private lemma map_toCLM_nonneg (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (0 : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) ≤
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap := by
  have hA_pos := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hB_pos := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hB
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    ((LinearMap.isPositive_toContinuousLinearMap_iff _).mpr
      ((LinearMap.nonneg_iff_isPositive _).mp
        (map_nonneg_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
          ((LinearMap.nonneg_iff_isPositive _).2 hA_pos.toLinearMap)
          ((LinearMap.nonneg_iff_isPositive _).2 hB_pos.toLinearMap))))

/-- Eigenbasis data of a positive operator: eigenvalue equations, nonnegativity, and the
action of its real power on the eigenbasis. -/
private lemma eigenbasis_rpow_data {E : Type*} [Qudit E] (T : E →L[ℂ] E) (hT : 0 ≤ T)
    (hT_sym : (T : L E).IsSymmetric) (p : ℝ) (i : Fin (Module.finrank ℂ E)) :
    T ((hT_sym.eigenvectorBasis rfl).toBasis i) =
        (algebraMap ℝ ℂ (hT_sym.eigenvalues rfl i)) • (hT_sym.eigenvectorBasis rfl).toBasis i ∧
      0 ≤ hT_sym.eigenvalues rfl i ∧
      ((CFC.rpow T p : E →L[ℂ] E) : L E) ((hT_sym.eigenvectorBasis rfl).toBasis i) =
        (algebraMap ℝ ℂ (hT_sym.eigenvalues rfl i ^ p)) •
          (hT_sym.eigenvectorBasis rfl).toBasis i := by
  haveI := isScalarTower_real (ℋ := E)
  have hT_lm : (0 : L E) ≤ T := (LinearMap.nonneg_iff_isPositive _).2
    ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT).toLinearMap
  have heig : T ((hT_sym.eigenvectorBasis rfl).toBasis i) =
      (algebraMap ℝ ℂ (hT_sym.eigenvalues rfl i)) • (hT_sym.eigenvectorBasis rfl).toBasis i := by
    rw [OrthonormalBasis.coe_toBasis, RCLike.algebraMap_eq_ofReal]
    exact hT_sym.apply_eigenvectorBasis _ i
  have hspec : hT_sym.eigenvalues rfl i ∈ spectrum ℝ T := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage,
      ContinuousLinearMap.spectrum_eq]
    exact (hT_sym.hasEigenvalue_eigenvalues _ i).mem_spectrum
  exact ⟨heig, eigenvalue_nonneg_of_nonneg (T : L E) hT_lm hT_sym _ i,
    rpow_apply_eigenvector T hT p _ _ heig hspec⟩

section TensorRpowStatements

-- The statements below need `NonnegSpectrumClass ℝ` on operators of a tensor product. Try first,
-- only inside this section, the C⋆-algebra instance that the default search ends up using.
attribute [local instance high] CStarAlgebra.instNonnegSpectrumClass'

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/--
Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence).
-/
theorem rpow_tensorProduct (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) (p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow
        (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) :
          L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap p =
      (TensorProduct.map
        ((CFC.rpow A p : ℋ₁ →L[ℂ] ℋ₁) : L ℋ₁)
        ((CFC.rpow B p : ℋ₂ →L[ℂ] ℋ₂) : L ℋ₂) :
          L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap := by
  have hA_sym := ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric
  have hB_sym := ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  have hA_d := eigenbasis_rpow_data A hA hA_sym p
  have hB_d := eigenbasis_rpow_data B hB hB_sym p
  exact rpow_eq_of_eigenbasis _ _ (map_toCLM_nonneg A B hA hB) p
    ((hA_sym.eigenvectorBasis rfl).toBasis.tensorProduct (hB_sym.eigenvectorBasis rfl).toBasis)
    (fun ij => hA_sym.eigenvalues rfl ij.1 * hB_sym.eigenvalues rfl ij.2)
    (map_toCLM_tensorBasis _ _ _ _ _ _ _ (fun i => (hA_d i).1) (fun j => (hB_d j).1)
      fun _ _ => rfl)
    (map_toCLM_tensorBasis _ _ _ _ (fun i => hA_sym.eigenvalues rfl i ^ p)
      (fun j => hB_sym.eigenvalues rfl j ^ p) _ (fun i => (hA_d i).2.2) (fun j => (hB_d j).2.2)
      fun i j => (Real.mul_rpow (hA_d i).2.1 (hB_d j).2.1).symm)

end TensorRpowStatements

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- A real eigenvalue (with nonzero eigenvector) lies in `spectrum ℝ A`. -/
lemma mem_spectrum_real_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {μ : ℝ} (hv0 : v ≠ 0) (hv : A v = (μ : ℂ) • v) :
    μ ∈ spectrum ℝ A := by
  have hev : Module.End.HasEigenvalue (A : L ℋ) (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]; exact hv
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hev.mem_spectrum
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  simpa using hmem

end

end TensorCFC
