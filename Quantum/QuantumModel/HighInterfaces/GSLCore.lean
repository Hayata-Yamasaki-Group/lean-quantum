import Quantum.QuantumMechanics.QuantumChannelKWCompat.GSLCore
import Quantum.QuantumModel.Purification.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.Matrix.Order
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCoreDefinitions.GSLCore
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumModel.OperationalInstances.GSLCore
import Quantum.QuantumModel.StructuralCalculus.GSLCore
import Quantum.QuantumModel.TensorCalculus.GSLCore
import Quantum.QuantumModel.UnitTrace.GSLCore

/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

/-!
# Finite-dimensional quantum-model interfaces

Instances for deterministic-family completion and raw effect extensionality (through rank-one
preparations), and the bridge from Hilbert-space bipartite vectors to categorical states and
their left marginals.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

variable {A B : Sys}

/-! ## Raw effect extensionality -/

/-- The one-Kraus preparation associated with a unit vector. -/
private noncomputable def rankOnePreparationKraus (v : Space A) :
    KrausFamily tensorUnitSystem A where
  index := PUnit
  fintypeIndex := inferInstance
  decidableEqIndex := inferInstance
  operator := fun _ => QuantumChannel.outer_product unitVector v

/-- The categorical pure preparation associated with a Hilbert-space vector. -/
noncomputable def rankOnePreparation (v : Space A) :
    tensorUnitSystem ⟶ A :=
  (rankOnePreparationKraus v).map

private theorem outer_product_unitVector_self :
    QuantumChannel.outer_product unitVector unitVector =
      (LinearMap.id : Operator tensorUnitSystem) := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i
  simpa [unitVector, QuantumChannel.outer_product_eq_rankOne] using
    (EuclideanSpace.basisFun_inner (Fin 1) ℂ x 0)

theorem rankOnePreparation_isNormalizedState (v : Space A)
    (hv : ‖v‖ = 1) :
    OPT.IsNormalizedState (Sys := Sys) (rankOnePreparation v) := by
  apply OPT.isDeterministicState_isNormalizedState (Sys := Sys)
  change IsChannel (rankOnePreparation v)
  refine ⟨(rankOnePreparationKraus v).map_isCompletelyPositive,
    rankOnePreparationKraus v, rfl, ?_⟩
  simp only [KrausFamily.normalization, rankOnePreparationKraus,
    Finset.univ_unique, Finset.sum_singleton]
  rw [DensityMatrix.adjoint_outer_product]
  rw [show
      (QuantumChannel.outer_product v unitVector).comp
          (QuantumChannel.outer_product unitVector v) =
        QuantumChannel.outer_product unitVector unitVector by
    apply LinearMap.ext
    intro x
    simp [QuantumChannel.outer_product_eq_rankOne,
      inner_self_eq_norm_sq_to_K, hv]]
  exact outer_product_unitVector_self

theorem rankOnePreparation_apply_id (v : Space A) :
    HPHom.toRawSuperoperator (rankOnePreparation v)
        (LinearMap.id : Operator tensorUnitSystem) =
      QuantumChannel.outer_product v v := by
  change (rankOnePreparationKraus v).rawMap LinearMap.id = _
  simp only [KrausFamily.rawMap, rankOnePreparationKraus,
    Finset.univ_unique, Finset.sum_singleton]
  change (QuantumChannel.outer_product unitVector v).comp
      ((LinearMap.id : Operator tensorUnitSystem).comp
        (LinearMap.adjoint (QuantumChannel.outer_product unitVector v))) = _
  rw [LinearMap.id_comp, DensityMatrix.adjoint_outer_product]
  apply LinearMap.ext
  intro x
  simp [QuantumChannel.outer_product_eq_rankOne]

/-- Hermitian operators on the tensor unit are determined by the real part of
their trace. -/
private theorem unitOperator_eq_of_isSymmetric_of_trace_re_eq
    (X Y : Operator tensorUnitSystem)
    (hX : X.IsSymmetric) (hY : Y.IsSymmetric)
    (h : (QuantumState.Tr X).re = (QuantumState.Tr Y).re) :
    X = Y := by
  have hXstar : star X = X := by
    rw [LinearMap.star_eq_adjoint, hX.adjoint_eq]
  have hYstar : star Y = Y := by
    rw [LinearMap.star_eq_adjoint, hY.adjoint_eq]
  have hXim : (QuantumState.Tr X).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simpa only [starRingEnd_apply, trace_unitOperator] using
      ((operatorUnitEquiv_symm_map_star X).symm.trans
        (congrArg operatorUnitEquiv.symm hXstar))
  have hYim : (QuantumState.Tr Y).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simpa only [starRingEnd_apply, trace_unitOperator] using
      ((operatorUnitEquiv_symm_map_star Y).symm.trans
        (congrArg operatorUnitEquiv.symm hYstar))
  have htrace : QuantumState.Tr X = QuantumState.Tr Y := by
    apply Complex.ext
    · exact h
    · rw [hXim, hYim]
  rw [← operatorUnitEquiv_trace X, ← operatorUnitEquiv_trace Y, htrace]

private theorem outer_product_polarization (x y : Space A) :
    QuantumChannel.outer_product x y =
      (4 : ℂ)⁻¹ •
        (QuantumChannel.outer_product (x + y) (x + y) -
          QuantumChannel.outer_product (x - y) (x - y) -
          Complex.I •
            (QuantumChannel.outer_product (x + Complex.I • y)
                (x + Complex.I • y) -
              QuantumChannel.outer_product (x - Complex.I • y)
                (x - Complex.I • y))) := by
  apply LinearMap.ext
  intro z
  simp only [QuantumChannel.outer_product_eq_rankOne, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_add, map_sub, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    ContinuousLinearMap.coe_sub, map_smul, ContinuousLinearMap.map_smulₛₗ, Complex.conj_I, neg_smul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_add, ContinuousLinearMap.coe_neg,
    ContinuousLinearMap.coe_smul, sub_neg_eq_add, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.neg_apply]
  match_scalars
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

private theorem outer_product_smul_self
    {E : Type*} [QuantumState.Qudit E] (c : ℂ) (x : E) :
    QuantumChannel.outer_product (c • x) (c • x) =
      (star c * c) • QuantumChannel.outer_product x x := by
  apply LinearMap.ext
  intro y
  change inner ℂ (c • x) y • (c • x) =
    (star c * c) • (inner ℂ x y • x)
  rw [inner_smul_left]
  simp only [starRingEnd_apply]
  module

private theorem operatorEquivMatrix_outer_product_basis
    (p q i j : Fin A.dim) :
    operatorEquivMatrix A
        (QuantumChannel.outer_product
          (EuclideanSpace.single q (1 : ℂ))
          (EuclideanSpace.single p (1 : ℂ))) i j =
      if i = p then if j = q then 1 else 0 else 0 := by
  unfold operatorEquivMatrix
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (QuantumChannel.outer_product
        (EuclideanSpace.single q (1 : ℂ))
        (EuclideanSpace.single p (1 : ℂ))
        (EuclideanSpace.single j (1 : ℂ))) = _
  rw [QuantumChannel.outer_product_eq_rankOne]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (inner ℂ (EuclideanSpace.single q (1 : ℂ))
          (EuclideanSpace.single j (1 : ℂ)) •
        EuclideanSpace.single p (1 : ℂ)) = _
  rw [inner_smul_right]
  simp only [EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, map_one, one_mul]
  split_ifs <;> simp_all

private theorem operator_eq_sum_outer_product_basis (X : Operator A) :
    X = ∑ i : Fin A.dim, ∑ j : Fin A.dim,
      (operatorEquivMatrix A X i j) •
        QuantumChannel.outer_product
          ((EuclideanSpace.basisFun (Fin A.dim) ℂ) j)
          ((EuclideanSpace.basisFun (Fin A.dim) ℂ) i) := by
  apply (operatorEquivMatrix A).injective
  change (operatorEquivMatrix A).toAlgEquiv.toLinearEquiv X =
    (operatorEquivMatrix A).toAlgEquiv.toLinearEquiv
      (∑ i : Fin A.dim, ∑ j : Fin A.dim,
        (operatorEquivMatrix A X i j) •
          QuantumChannel.outer_product
            ((EuclideanSpace.basisFun (Fin A.dim) ℂ) j)
            ((EuclideanSpace.basisFun (Fin A.dim) ℂ) i))
  rw [map_sum]
  simp_rw [map_sum,
    (operatorEquivMatrix A).toAlgEquiv.toLinearEquiv.map_smul]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp [operatorEquivMatrix_outer_product_basis (A := A)]

/-- Born pairing against unit-vector preparations separates all
Hermiticity-preserving quantum effects. -/
instance instEffectRawExtensionalityTheory :
    OPT.EffectRawExtensionalityTheory Sys where
  effect_eq_of_operationalClass_eq := by
    intro A a b hclass
    have hequiv : OPT.EffectOperationalEquiv (Sys := Sys) a b :=
      (OPT.effectOperationalEquiv_iff_class_eq (Sys := Sys)).2 hclass
    have hunit : ∀ (v : Space A), ‖v‖ = 1 →
        HPHom.toRawSuperoperator a (QuantumChannel.outer_product v v) =
          HPHom.toRawSuperoperator b (QuantumChannel.outer_product v v) := by
      intro v hv
      have hprob := hequiv (rankOnePreparation v)
        (rankOnePreparation_isNormalizedState v hv).1
      change
        (QuantumState.Tr
          (HPHom.toRawSuperoperator a
            (HPHom.toRawSuperoperator (rankOnePreparation v)
              (LinearMap.id : Operator tensorUnitSystem)))).re =
        (QuantumState.Tr
          (HPHom.toRawSuperoperator b
            (HPHom.toRawSuperoperator (rankOnePreparation v)
              (LinearMap.id : Operator tensorUnitSystem)))).re at hprob
      rw [rankOnePreparation_apply_id] at hprob
      let P : Operator A := QuantumChannel.outer_product v v
      have hP : P.IsSymmetric := by
        simp [P, QuantumChannel.outer_product_eq_rankOne]
      have haP : (HPHom.toRawSuperoperator a P).IsSymmetric := by
        apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).2
        change star (HPHom.toRawSuperoperator a P) =
          HPHom.toRawSuperoperator a P
        rw [← HPHom.map_star]
        exact congrArg (HPHom.toRawSuperoperator a)
          (by rw [LinearMap.star_eq_adjoint, hP.adjoint_eq])
      have hbP : (HPHom.toRawSuperoperator b P).IsSymmetric := by
        apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).2
        change star (HPHom.toRawSuperoperator b P) =
          HPHom.toRawSuperoperator b P
        rw [← HPHom.map_star]
        exact congrArg (HPHom.toRawSuperoperator b)
          (by rw [LinearMap.star_eq_adjoint, hP.adjoint_eq])
      exact unitOperator_eq_of_isSymmetric_of_trace_re_eq
        (HPHom.toRawSuperoperator a P)
        (HPHom.toRawSuperoperator b P) haP hbP (by simpa [P] using hprob)
    have hself : ∀ v : Space A,
        HPHom.toRawSuperoperator a (QuantumChannel.outer_product v v) =
          HPHom.toRawSuperoperator b (QuantumChannel.outer_product v v) := by
      intro v
      by_cases hv : v = 0
      · subst v
        simp [QuantumChannel.outer_product_eq_rankOne]
      · let u : Space A := (‖v‖⁻¹ : ℂ) • v
        have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        have hu : ‖u‖ = 1 := by
          simp [u, norm_smul, hvnorm]
        have huv := hunit u hu
        have hv_scale : (‖v‖ : ℂ) • u = v := by
          simp [u, hvnorm]
        rw [← hv_scale, outer_product_smul_self,
          (HPHom.toRawSuperoperator a).map_smul,
          (HPHom.toRawSuperoperator b).map_smul, huv]
    have houter : ∀ x y : Space A,
        HPHom.toRawSuperoperator a (QuantumChannel.outer_product x y) =
          HPHom.toRawSuperoperator b (QuantumChannel.outer_product x y) := by
      intro x y
      rw [outer_product_polarization]
      simp only [map_smul, map_sub, hself]
    apply HPHom.ext
    intro X
    rw [operator_eq_sum_outer_product_basis X]
    simp only [map_sum, map_smul, houter]

/-! ## Bridges from Hilbert-space purification to categorical states -/

/-- Product-basis identification between the Hilbert tensor carrier used by
the purification spike and the categorical tensor-system carrier. -/
noncomputable def jointSpaceEquiv (A R : Sys) :
    JointSpace A R ≃ₗᵢ[ℂ] Space (tensorSystem A R) :=
  ((spaceONB A).tensorProduct (spaceONB R)).equiv
    (spaceONB (tensorSystem A R)) finProdFinEquiv

theorem jointSpaceEquiv_tmul_basis (A R : Sys)
    (i : Fin A.dim) (j : Fin R.dim) :
    jointSpaceEquiv A R
        ((spaceONB A i) ⊗ₜ[ℂ] (spaceONB R j)) =
      spaceONB (tensorSystem A R) (finProdFinEquiv (i, j)) := by
  rw [← OrthonormalBasis.tensorProduct_apply]
  exact OrthonormalBasis.equiv_apply_basis _ _ _ _

/-- Discarding a categorical right-system basis component is the standard
right tensor slice on the Hilbert tensor carrier. -/
private theorem discardSlice (A R : Sys) (j : Fin R.dim) :
    ((spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap.comp
        (tensorOperator LinearMap.id ((traceKrausFamily R).operator j))).comp
        (jointSpaceEquiv A R).toLinearEquiv.toLinearMap =
      QuantumChannel.tensorRightSlice (spaceONB R) j := by
  classical
  apply ((spaceONB A).tensorProduct (spaceONB R)).toBasis.ext
  intro p
  rw [OrthonormalBasis.toBasis_tensorProduct,
    Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply]
  change (spaceReindexEquiv (rightUnitorIndexEquiv A))
      (tensorOperator LinearMap.id ((traceKrausFamily R).operator j)
        (jointSpaceEquiv A R
          ((spaceONB A p.1) ⊗ₜ[ℂ] (spaceONB R p.2)))) =
    QuantumChannel.tensorRightSlice (spaceONB R) j
      ((spaceONB A p.1) ⊗ₜ[ℂ] (spaceONB R p.2))
  rw [jointSpaceEquiv_tmul_basis]
  ext k
  change (spaceBasis A).repr
      (((spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap.comp
        (tensorOperator LinearMap.id ((traceKrausFamily R).operator j)))
        (spaceBasis (tensorSystem A R) (finProdFinEquiv p))) k = _
  rw [show (spaceBasis A).repr
      (((spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap.comp
        (tensorOperator LinearMap.id ((traceKrausFamily R).operator j)))
        (spaceBasis (tensorSystem A R) (finProdFinEquiv p))) k =
      LinearMap.toMatrix (spaceBasis (tensorSystem A R)) (spaceBasis A)
        ((spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap.comp
          (tensorOperator LinearMap.id ((traceKrausFamily R).operator j)))
        k (finProdFinEquiv p) by
          rw [LinearMap.toMatrix_apply]]
  rw [LinearMap.toMatrix_comp
      (spaceBasis (tensorSystem A R))
      (spaceBasis (tensorSystem A tensorUnitSystem)) (spaceBasis A),
    spaceReindexEquiv_matrix, tensorOperator_matrix]
  let zeroUnit : Fin tensorUnitSystem.dim :=
    ⟨0, tensorUnitSystem.dim_pos⟩
  have hpair :
      finProdFinEquiv.symm
          ((rightUnitorIndexEquiv A).symm k) = (k, zeroUnit) := by
    apply Prod.ext
    · apply Fin.ext
      change ((rightUnitorIndexEquiv A).symm k).val /
          tensorUnitSystem.dim = k.val
      simp [rightUnitorIndexEquiv, tensorUnitSystem]
      rfl
    · apply Fin.ext
      change ((rightUnitorIndexEquiv A).symm k).val %
          tensorUnitSystem.dim = zeroUnit.val
      simp only [tensorUnitSystem, rightUnitorIndexEquiv, finCongr_symm, zeroUnit]
      exact Nat.mod_one _
  change (∑ x : Fin (tensorSystem A tensorUnitSystem).dim,
      (if k = rightUnitorIndexEquiv A x then 1 else 0) *
        (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (fun x y : ℂ => x * y)
            (LinearMap.toMatrix (spaceBasis A) (spaceBasis A) LinearMap.id)
            (LinearMap.toMatrix (spaceBasis R) (spaceBasis tensorUnitSystem)
              ((traceKrausFamily R).operator j))))
          x (finProdFinEquiv p)) = _
  rw [Finset.sum_eq_single ((rightUnitorIndexEquiv A).symm k)]
  · simp only [Equiv.apply_symm_apply, if_true, one_mul]
    dsimp only [Matrix.reindexLinearEquiv, Matrix.reindex,
      Matrix.submatrix]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Equiv.symm_apply_apply]
    rw [hpair]
    simp only [LinearMap.toMatrix_id_eq_basis_toMatrix, OrthonormalBasis.coe_toBasis,
      traceKrausFamily, EuclideanSpace.basisFun_apply, QuantumChannel.outer_product_eq_rankOne,
      Matrix.kroneckerMap_apply, QuantumChannel.tensorRightSlice_tmul, Module.Basis.coord_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, PiLp.smul_apply,
      EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    change (spaceBasis A).toMatrix (spaceBasis A) k p.1 * _ = _
    rw [Module.Basis.toMatrix_self]
    have hzero : zeroUnit = unitIndex := by
      apply Fin.ext
      simp [tensorUnitSystem, unitIndex]
    simp [Matrix.one_apply, LinearMap.toMatrix_apply, unitVector,
      unitIndex, hzero, InnerProductSpace.rankOne_apply]
  · intro x _ hx
    have hkx : k ≠ rightUnitorIndexEquiv A x := by
      intro hkx
      apply hx
      exact (rightUnitorIndexEquiv A).injective
        (by simpa using hkx.symm)
    simp [hkx]
  · simp

private def identityKrausFamily (A : Sys) : KrausFamily A A where
  index := PUnit
  fintypeIndex := inferInstance
  decidableEqIndex := inferInstance
  operator := fun _ => LinearMap.id

private theorem identityKrausFamily_map (A : Sys) :
    (identityKrausFamily A).map = 𝟙 A := by
  apply HPHom.ext
  intro X
  change (identityKrausFamily A).rawMap X = X
  simp [identityKrausFamily, KrausFamily.rawMap,
    QuantumChannel.krausTerm]

/-- The categorical deterministic discard is exactly the spike's right
partial trace under `jointSpaceEquiv`. -/
private theorem discard_outer (A R : Sys) (psi : JointSpace A R) :
    QuantumChannel.krausTerm
        (spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap
        (((identityKrausFamily A).tensor (traceKrausFamily R)).rawMap
          (QuantumChannel.outer_product
            (jointSpaceEquiv A R psi) (jointSpaceEquiv A R psi))) =
      QuantumChannel.TrRight
        (QuantumChannel.outer_product psi psi) := by
  classical
  rw [KrausFamily.rawMap]
  simp only [KrausFamily.tensor, identityKrausFamily]
  change QuantumChannel.krausTerm
      (spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap
      ((∑ x : PUnit × Fin R.dim,
          QuantumChannel.krausTerm
            (tensorOperator LinearMap.id
              ((traceKrausFamily R).operator x.2)))
        (QuantumChannel.outer_product
          (jointSpaceEquiv A R psi) (jointSpaceEquiv A R psi))) = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton,
    LinearMap.sum_apply, map_sum]
  rw [QuantumChannel.TrRight_outer_product_compat (spaceONB R)]
  apply Finset.sum_congr rfl
  intro j _
  change QuantumChannel.krausTerm
      (spaceReindexEquiv (rightUnitorIndexEquiv A)).toLinearMap
      (QuantumChannel.krausTerm
        (tensorOperator LinearMap.id ((traceKrausFamily R).operator j))
        (QuantumChannel.outer_product
          (jointSpaceEquiv A R psi) (jointSpaceEquiv A R psi))) = _
  simp only [QuantumChannel.krausTerm]
  change (spaceReindexEquiv
      (rightUnitorIndexEquiv A)).toLinearMap.comp
        (((tensorOperator LinearMap.id
          ((traceKrausFamily R).operator j)).comp
            ((QuantumChannel.outer_product
              (jointSpaceEquiv A R psi)
              (jointSpaceEquiv A R psi)).comp
                (LinearMap.adjoint
                  (tensorOperator LinearMap.id
                    ((traceKrausFamily R).operator j))))).comp
          (LinearMap.adjoint
            (spaceReindexEquiv
              (rightUnitorIndexEquiv A)).toLinearMap)) = _
  rw [QuantumChannel.comp_outer_product_adjoint]
  rw [QuantumChannel.comp_outer_product_adjoint]
  have hs := LinearMap.congr_fun (discardSlice A R j) psi
  exact congrArg₂ QuantumChannel.outer_product hs hs

section JointSpaceCoord

-- The statement below elaborates `InnerProductSpace ℂ (JointSpace A R)`; preferring the
-- Mathlib tensor-product instance avoids the slow search through the `Qudit` route.
attribute [local instance high] TensorProduct.instInnerProductSpace

theorem jointSpaceEquiv_coord (A R : Sys) (z : JointSpace A R)
    (k : Fin (tensorSystem A R).dim) :
    (jointSpaceEquiv A R z).ofLp k =
      (((spaceONB A).tensorProduct (spaceONB R)).repr z).ofLp
        (finProdFinEquiv.symm k) := by
  change (spaceONB (tensorSystem A R)).repr
      (jointSpaceEquiv A R z) k =
    ((spaceONB A).tensorProduct (spaceONB R)).repr z
      (finProdFinEquiv.symm k)
  rw [OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.repr_apply_apply]
  have hbasis := jointSpaceEquiv_tmul_basis A R
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  rw [show spaceONB (tensorSystem A R) k =
      jointSpaceEquiv A R
        (((spaceONB A).tensorProduct (spaceONB R))
          (finProdFinEquiv.symm k)) by
    rw [OrthonormalBasis.tensorProduct_apply, hbasis,
      finProdFinEquiv.apply_symm_apply]]
  exact (jointSpaceEquiv A R).inner_map_map _ _

end JointSpaceCoord

/-- The Hilbert-space right action is the categorical Kronecker action under
the product-basis identification. -/
theorem jointSpaceEquiv_map {A B R S : Sys}
    (V : Space A →ₗ[ℂ] Space B) (W : Space R →ₗ[ℂ] Space S)
    (z : JointSpace A R) :
    jointSpaceEquiv B S (TensorProduct.map V W z) =
      tensorOperator V W (jointSpaceEquiv A R z) := by
  change ((jointSpaceEquiv B S).toLinearEquiv.toLinearMap.comp
      (TensorProduct.map V W)) z =
    ((tensorOperator V W).comp
      (jointSpaceEquiv A R).toLinearEquiv.toLinearMap) z
  apply LinearMap.congr_fun
  apply ((spaceONB A).tensorProduct (spaceONB R)).toBasis.ext
  intro p
  rw [OrthonormalBasis.toBasis_tensorProduct,
    Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  ext k
  change (jointSpaceEquiv B S
      (V (spaceONB A p.1) ⊗ₜ[ℂ] W (spaceONB R p.2))).ofLp k =
    (tensorOperator V W
      (jointSpaceEquiv A R
        (spaceONB A p.1 ⊗ₜ[ℂ] spaceONB R p.2))).ofLp k
  rw [jointSpaceEquiv_coord]
  rw [OrthonormalBasis.tensorProduct_repr_tmul_apply']
  rw [jointSpaceEquiv_tmul_basis]
  change _ = (spaceBasis (tensorSystem B S)).repr
      (tensorOperator V W
        (spaceBasis (tensorSystem A R) (finProdFinEquiv p))) k
  rw [← LinearMap.toMatrix_apply, tensorOperator_matrix]
  simp only [finProdFinEquiv_symm_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.repr_apply_apply, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply,
    LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply]
  exact mul_comm _ _

/-- Marginalizing the categorical rank-one preparation obtained from a spike
vector returns the spike partial trace on its output density operator. -/
theorem marginalLeft_rankOnePreparation_joint {A R : Sys}
    (psi : JointSpace A R) :
    HPHom.toRawSuperoperator
        (OPT.marginalLeft (Sys := Sys)
          (rankOnePreparation (jointSpaceEquiv A R psi)))
        (LinearMap.id : Operator tensorUnitSystem) =
      partialTrace (QuantumChannel.outer_product psi psi) := by
  have htensor :
      ((identityKrausFamily A).tensor (traceKrausFamily R)).map =
        𝟙 A ⊗ₘ OPT.detEffect (Sys := Sys) R := by
    rw [KrausFamily.tensor_map, identityKrausFamily_map,
      traceKrausFamily_map]
    rfl
  have hcomp : ∀ {X Y Z : Sys} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Operator X),
      HPHom.toRawSuperoperator (f ≫ g) T =
        HPHom.toRawSuperoperator g (HPHom.toRawSuperoperator f T) := fun _ _ _ => rfl
  unfold OPT.marginalLeft
  rw [hcomp, hcomp]
  rw [rankOnePreparation_apply_id, ← htensor,
    KrausFamily.map_toRawSuperoperator,
    rightUnitor_hom_eq_krausTerm,
    toRawSuperoperator_krausTermHom]
  exact discard_outer A R psi

theorem state_eq_of_apply_id_eq {A : Sys}
    {rho sigma : OPT.State (Sys := Sys) A}
    (h : HPHom.toRawSuperoperator rho
          (LinearMap.id : Operator tensorUnitSystem) =
        HPHom.toRawSuperoperator sigma
          (LinearMap.id : Operator tensorUnitSystem)) :
    rho = sigma := by
  apply HPHom.ext
  intro X
  rw [← operatorUnitEquiv_trace X, operatorUnitEquiv_eq_smul_id,
    map_smul, map_smul]
  exact congrArg (fun Y => QuantumState.Tr X • Y) h

private theorem marginalLeft_isState_of_normalized {A B : Sys}
    {Psi : OPT.State (Sys := Sys) (A ⊗ B)}
    (hPsi : OPT.IsNormalizedState (Sys := Sys) Psi) :
    OPT.IsState (Sys := Sys) (OPT.marginalLeft (Sys := Sys) Psi) := by
  simpa [OPT.marginalLeft, OPT.conditionRight, OPT.applyEffectRight] using
    OPT.conditionRight_isState (Sys := Sys)
      (OPT.detEffect_isEffect (Sys := Sys) B) hPsi.1

/-- Marginalizing a normalized quantum state preserves normalization. -/
theorem marginalLeft_isNormalizedState_of_normalized {A B : Sys}
    {Psi : OPT.State (Sys := Sys) (A ⊗ B)}
    (hPsi : OPT.IsNormalizedState (Sys := Sys) Psi) :
    OPT.IsNormalizedState (Sys := Sys)
      (OPT.marginalLeft (Sys := Sys) Psi) := by
  refine ⟨marginalLeft_isState_of_normalized hPsi, ?_⟩
  calc
    OPT.prob (Sys := Sys) (OPT.detEffect (Sys := Sys) A)
        (OPT.marginalLeft (Sys := Sys) Psi) =
      OPT.prob (Sys := Sys)
        (OPT.tensorEffect (Sys := Sys) (OPT.detEffect (Sys := Sys) A)
          (OPT.detEffect (Sys := Sys) B)) Psi := by
        simpa [OPT.marginalLeft, OPT.conditionRight, OPT.applyEffectRight] using
          OPT.conditionRight_effect_eval (Sys := Sys)
            (OPT.detEffect (Sys := Sys) A)
            (OPT.detEffect (Sys := Sys) B) Psi
    _ = OPT.prob (Sys := Sys) (OPT.detEffect (Sys := Sys) (A ⊗ B)) Psi := by
      rw [OPT.detEffect_tensor (Sys := Sys) A B]
    _ = 1 := hPsi.2

end QuantumModel
