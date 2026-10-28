/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.Skeleton.GSLCore
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Foundational categorical instances for finite-dimensional quantum systems

Morphisms are Hermiticity-preserving maps.  The tensor product is transported through
Kronecker coordinates, with Hermiticity preservation proved before the monoidal and
symmetric coherence instances are assembled.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TensorProduct
open scoped Kronecker Matrix

@[reducible]
private def homAddCommGroup (A B : Sys) : AddCommGroup (A ⟶ B) :=
  hpHomAddCommGroup A B

instance preadditive : Preadditive Sys where
  homGroup := homAddCommGroup
  add_comp := by
    intro A B C f g h
    apply HPHom.ext
    intro X
    exact (HPHom.toRawSuperoperator h).map_add
      (HPHom.toRawSuperoperator f X) (HPHom.toRawSuperoperator g X)
  comp_add := by
    intro A B C f g h
    apply HPHom.ext
    intro X
    rfl

@[reducible]
private noncomputable def homRealModule (A B : Sys) : Module ℝ (A ⟶ B) :=
  hpHomModule A B

instance realLinear : CategoryTheory.Linear ℝ Sys where
  homModule := homRealModule
  smul_comp := by
    intro A B C r f g
    apply HPHom.ext
    intro X
    exact (HPHom.toRawSuperoperator g).map_smul (r : ℂ)
      (HPHom.toRawSuperoperator f X)
  comp_smul := by
    intro A B C f r g
    apply HPHom.ext
    intro X
    rfl

/-! ## The underlying operator functor and Kronecker coordinates -/

/-- Forget Hermiticity preservation and view a system as its complex operator module. -/
noncomputable def operatorFunctor : CategoryTheory.Functor Sys (ModuleCat ℂ) where
  obj A := ModuleCat.of ℂ (Operator A)
  map f := ModuleCat.ofHom (HPHom.toRawSuperoperator f)
  map_id _ := rfl
  map_comp _ _ := rfl

instance operatorFunctorFaithful : operatorFunctor.Faithful where
  map_injective {X Y} := by
    intro f g h
    apply HPHom.ext
    intro Z
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) Z

/-- Matrix Kronecker coordinates identify the tensor product of operator spaces with
the operator space of the tensor system. -/
noncomputable def operatorTensorEquiv (A B : Sys) :
    Operator A ⊗[ℂ] Operator B ≃ₗ[ℂ] Operator (tensorSystem A B) :=
  (TensorProduct.congr (operatorEquivMatrix A).toAlgEquiv.toLinearEquiv
      (operatorEquivMatrix B).toAlgEquiv.toLinearEquiv).trans
    ((kroneckerLinearEquiv (Fin A.dim) (Fin A.dim)
      (Fin B.dim) (Fin B.dim) ℂ).trans
      ((Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).trans
        (operatorEquivMatrix (tensorSystem A B)).symm.toAlgEquiv.toLinearEquiv))

@[simp]
theorem operatorTensorEquiv_tmul (A B : Sys) (X : Operator A) (Y : Operator B) :
    operatorEquivMatrix (tensorSystem A B)
        (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y)) =
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (operatorEquivMatrix A X ⊗ₖ operatorEquivMatrix B Y) := by
  change operatorEquivMatrix (tensorSystem A B)
      ((operatorEquivMatrix (tensorSystem A B)).symm
        (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          (operatorEquivMatrix A X ⊗ₖ operatorEquivMatrix B Y))) = _
  simp

private theorem conjTranspose_reindexLinearEquiv
    {m n m' n' : Type*} (em : m ≃ m') (en : n ≃ n')
    (M : Matrix m n ℂ) :
    (Matrix.reindexLinearEquiv ℂ ℂ em en M)ᴴ =
      Matrix.reindexLinearEquiv ℂ ℂ en em Mᴴ := by
  rfl

/-- Kronecker coordinates commute with the operator star. -/
theorem operatorTensorEquiv_map_star (A B : Sys)
    (Z : Operator A ⊗[ℂ] Operator B) :
    operatorTensorEquiv A B (star Z) = star (operatorTensorEquiv A B Z) := by
  induction Z using TensorProduct.induction_on with
  | zero =>
      rw [star_zero, (operatorTensorEquiv A B).map_zero, star_zero]
  | tmul X Y =>
      apply (operatorEquivMatrix (tensorSystem A B)).injective
      rw [TensorProduct.star_tmul]
      change operatorEquivMatrix (tensorSystem A B)
          (operatorTensorEquiv A B (star X ⊗ₜ[ℂ] star Y)) =
        operatorEquivMatrix (tensorSystem A B)
          (star (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y)))
      rw [operatorTensorEquiv_tmul]
      rw [show operatorEquivMatrix (tensorSystem A B)
          (star (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y))) =
          star (operatorEquivMatrix (tensorSystem A B)
            (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y))) by
        exact map_star (operatorEquivMatrix (tensorSystem A B)) _]
      rw [operatorTensorEquiv_tmul]
      simp only [map_star]
      change Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          ((operatorEquivMatrix A X)ᴴ ⊗ₖ (operatorEquivMatrix B Y)ᴴ) =
        (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          (operatorEquivMatrix A X ⊗ₖ operatorEquivMatrix B Y))ᴴ
      rw [conjTranspose_reindexLinearEquiv, Matrix.conjTranspose_kronecker]
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

theorem operatorTensorEquiv_symm_map_star (A B : Sys)
    (X : Operator (tensorSystem A B)) :
    (operatorTensorEquiv A B).symm (star X) =
      star ((operatorTensorEquiv A B).symm X) := by
  apply (operatorTensorEquiv A B).injective
  rw [operatorTensorEquiv_map_star]
  simp

/-- The one-dimensional tensor unit. -/
def tensorUnitSystem : Sys where
  dim := 1
  dim_pos := by omega

/-- A one-by-one matrix is its unique scalar entry. -/
noncomputable def scalarMatrixOneEquiv :
    Matrix (Fin 1) (Fin 1) ℂ ≃ₗ[ℂ] ℂ where
  toFun M := M 0 0
  invFun z := fun _ _ ↦ z
  left_inv M := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scalar coordinates for operators on the tensor unit. -/
noncomputable def operatorUnitEquiv : ℂ ≃ₗ[ℂ] Operator tensorUnitSystem :=
  scalarMatrixOneEquiv.symm.trans
    (operatorEquivMatrix tensorUnitSystem).toAlgEquiv.toLinearEquiv.symm

theorem operatorUnitEquiv_map_star (z : ℂ) :
    operatorUnitEquiv (star z) = star (operatorUnitEquiv z) := by
  apply (operatorEquivMatrix tensorUnitSystem).injective
  change operatorEquivMatrix tensorUnitSystem
      ((operatorEquivMatrix tensorUnitSystem).symm (fun _ _ ↦ star z)) =
    operatorEquivMatrix tensorUnitSystem
      (star ((operatorEquivMatrix tensorUnitSystem).symm (fun _ _ ↦ z)))
  rw [show operatorEquivMatrix tensorUnitSystem
      (star ((operatorEquivMatrix tensorUnitSystem).symm (fun _ _ ↦ z))) =
      star (operatorEquivMatrix tensorUnitSystem
        ((operatorEquivMatrix tensorUnitSystem).symm (fun _ _ ↦ z))) by
    exact map_star (operatorEquivMatrix tensorUnitSystem) _]
  simp only [StarAlgEquiv.apply_symm_apply]
  ext i j
  fin_cases i
  fin_cases j
  rfl

private theorem linearEquiv_symm_map_star
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module ℂ M] [Module ℂ N] [Star M] [Star N]
    (e : M ≃ₗ[ℂ] N) (h : ∀ x, e (star x) = star (e x)) (y : N) :
    e.symm (star y) = star (e.symm y) := by
  apply e.injective
  rw [h]
  simp

theorem operatorUnitEquiv_symm_map_star (X : Operator tensorUnitSystem) :
    operatorUnitEquiv.symm (star X) = star (operatorUnitEquiv.symm X) :=
  linearEquiv_symm_map_star operatorUnitEquiv operatorUnitEquiv_map_star X

private theorem tensorCongr_map_star
    {M N P Q : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] [AddCommMonoid Q] [Module ℂ M] [Module ℂ N]
    [Module ℂ P] [Module ℂ Q] [StarAddMonoid M] [StarAddMonoid N]
    [StarAddMonoid P] [StarAddMonoid Q] [StarModule ℂ M] [StarModule ℂ N]
    [StarModule ℂ P] [StarModule ℂ Q]
    (e : M ≃ₗ[ℂ] P) (f : N ≃ₗ[ℂ] Q)
    (he : ∀ x, e (star x) = star (e x))
    (hf : ∀ y, f (star y) = star (f y)) (Z : M ⊗[ℂ] N) :
    TensorProduct.congr e f (star Z) = star (TensorProduct.congr e f Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y => simp [he, hf]
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

private theorem tensorLid_map_star
    {M : Type*} [AddCommMonoid M] [Module ℂ M]
    [StarAddMonoid M] [StarModule ℂ M] (Z : ℂ ⊗[ℂ] M) :
    TensorProduct.lid ℂ M (star Z) = star (TensorProduct.lid ℂ M Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul z X => simp
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

private theorem tensorRid_map_star
    {M : Type*} [AddCommMonoid M] [Module ℂ M]
    [StarAddMonoid M] [StarModule ℂ M] (Z : M ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ M (star Z) = star (TensorProduct.rid ℂ M Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul X z => simp
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

private theorem tensorAssoc_map_star
    {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module ℂ M] [Module ℂ N] [Module ℂ P]
    [StarAddMonoid M] [StarAddMonoid N] [StarAddMonoid P]
    [StarModule ℂ M] [StarModule ℂ N] [StarModule ℂ P]
    (Z : (M ⊗[ℂ] N) ⊗[ℂ] P) :
    TensorProduct.assoc ℂ M N P (star Z) =
      star (TensorProduct.assoc ℂ M N P Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul XY Z =>
      induction XY using TensorProduct.induction_on with
      | zero => simp
      | tmul X Y => simp
      | add X Y hX hY => simp only [star_add, add_tmul, map_add, hX, hY]
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

namespace HPHom

/-- The raw Kronecker tensor of two HP maps. -/
noncomputable def tensorRaw {A B C D : Sys} (f : HPHom A B) (g : HPHom C D) :
    RawSuperoperator (tensorSystem A C) (tensorSystem B D) :=
  (operatorTensorEquiv B D).toLinearMap.comp
    ((TensorProduct.map (toRawSuperoperator f) (toRawSuperoperator g)).comp
      (operatorTensorEquiv A C).symm.toLinearMap)

private theorem tensorProduct_map_star
    {A B C D : Sys} (f : HPHom A B) (g : HPHom C D)
    (Z : Operator A ⊗[ℂ] Operator C) :
    TensorProduct.map (toRawSuperoperator f) (toRawSuperoperator g) (star Z) =
      star (TensorProduct.map (toRawSuperoperator f) (toRawSuperoperator g) Z) := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y => simp [map_star]
  | add X Y hX hY => simp only [star_add, map_add, hX, hY]

/-- The underlying Kronecker tensor of HP maps is again Hermiticity preserving. -/
theorem tensor_isHP {A B C D : Sys} (f : HPHom A B) (g : HPHom C D)
    (X : Operator (tensorSystem A C)) :
    tensorRaw f g (star X) = star (tensorRaw f g X) := by
  change operatorTensorEquiv B D
      (TensorProduct.map (toRawSuperoperator f) (toRawSuperoperator g)
        ((operatorTensorEquiv A C).symm (star X))) =
    star (operatorTensorEquiv B D
      (TensorProduct.map (toRawSuperoperator f) (toRawSuperoperator g)
        ((operatorTensorEquiv A C).symm X)))
  rw [operatorTensorEquiv_symm_map_star]
  rw [tensorProduct_map_star]
  rw [operatorTensorEquiv_map_star]

/-- Tensor product of Hermiticity-preserving morphisms. -/
noncomputable def tensor {A B C D : Sys} (f : HPHom A B) (g : HPHom C D) :
    HPHom (tensorSystem A C) (tensorSystem B D) :=
  ⟨WithConv.toConv (tensorRaw f g),
    LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr
      (tensor_isHP f g)⟩

end HPHom

/-! ## Star-preserving structural equivalences -/

noncomputable def leftUnitorLinearEquiv (A : Sys) :
    Operator (tensorSystem tensorUnitSystem A) ≃ₗ[ℂ] Operator A :=
  (operatorTensorEquiv tensorUnitSystem A).symm |>.trans
    ((TensorProduct.congr operatorUnitEquiv.symm (LinearEquiv.refl ℂ (Operator A))).trans
      (TensorProduct.lid ℂ (Operator A)))

noncomputable def rightUnitorLinearEquiv (A : Sys) :
    Operator (tensorSystem A tensorUnitSystem) ≃ₗ[ℂ] Operator A :=
  (operatorTensorEquiv A tensorUnitSystem).symm |>.trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ (Operator A)) operatorUnitEquiv.symm).trans
      (TensorProduct.rid ℂ (Operator A)))

noncomputable def associatorLinearEquiv (A B C : Sys) :
    Operator (tensorSystem (tensorSystem A B) C) ≃ₗ[ℂ]
      Operator (tensorSystem A (tensorSystem B C)) :=
  (operatorTensorEquiv (tensorSystem A B) C).symm |>.trans
    ((TensorProduct.congr (operatorTensorEquiv A B).symm
        (LinearEquiv.refl ℂ (Operator C))).trans
      ((TensorProduct.assoc ℂ (Operator A) (Operator B) (Operator C)).trans
        ((TensorProduct.congr (LinearEquiv.refl ℂ (Operator A))
          (operatorTensorEquiv B C)).trans
          (operatorTensorEquiv A (tensorSystem B C)))))

theorem leftUnitorLinearEquiv_map_star (A : Sys)
    (X : Operator (tensorSystem tensorUnitSystem A)) :
    leftUnitorLinearEquiv A (star X) = star (leftUnitorLinearEquiv A X) := by
  change TensorProduct.lid ℂ (Operator A)
      (TensorProduct.congr operatorUnitEquiv.symm (LinearEquiv.refl ℂ (Operator A))
        ((operatorTensorEquiv tensorUnitSystem A).symm (star X))) =
    star (TensorProduct.lid ℂ (Operator A)
      (TensorProduct.congr operatorUnitEquiv.symm (LinearEquiv.refl ℂ (Operator A))
        ((operatorTensorEquiv tensorUnitSystem A).symm X)))
  rw [operatorTensorEquiv_symm_map_star]
  rw [tensorCongr_map_star operatorUnitEquiv.symm (LinearEquiv.refl ℂ (Operator A))
    operatorUnitEquiv_symm_map_star (by simp)]
  rw [tensorLid_map_star]

theorem rightUnitorLinearEquiv_map_star (A : Sys)
    (X : Operator (tensorSystem A tensorUnitSystem)) :
    rightUnitorLinearEquiv A (star X) = star (rightUnitorLinearEquiv A X) := by
  change TensorProduct.rid ℂ (Operator A)
      (TensorProduct.congr (LinearEquiv.refl ℂ (Operator A)) operatorUnitEquiv.symm
        ((operatorTensorEquiv A tensorUnitSystem).symm (star X))) =
    star (TensorProduct.rid ℂ (Operator A)
      (TensorProduct.congr (LinearEquiv.refl ℂ (Operator A)) operatorUnitEquiv.symm
        ((operatorTensorEquiv A tensorUnitSystem).symm X)))
  rw [operatorTensorEquiv_symm_map_star]
  rw [tensorCongr_map_star (LinearEquiv.refl ℂ (Operator A)) operatorUnitEquiv.symm
    (by simp) operatorUnitEquiv_symm_map_star]
  rw [tensorRid_map_star]

theorem associatorLinearEquiv_map_star (A B C : Sys)
    (X : Operator (tensorSystem (tensorSystem A B) C)) :
    associatorLinearEquiv A B C (star X) =
      star (associatorLinearEquiv A B C X) := by
  change operatorTensorEquiv A (tensorSystem B C)
      (TensorProduct.congr (LinearEquiv.refl ℂ (Operator A)) (operatorTensorEquiv B C)
        (TensorProduct.assoc ℂ (Operator A) (Operator B) (Operator C)
          (TensorProduct.congr (operatorTensorEquiv A B).symm
            (LinearEquiv.refl ℂ (Operator C))
            ((operatorTensorEquiv (tensorSystem A B) C).symm (star X))))) =
    star (operatorTensorEquiv A (tensorSystem B C)
      (TensorProduct.congr (LinearEquiv.refl ℂ (Operator A)) (operatorTensorEquiv B C)
        (TensorProduct.assoc ℂ (Operator A) (Operator B) (Operator C)
          (TensorProduct.congr (operatorTensorEquiv A B).symm
            (LinearEquiv.refl ℂ (Operator C))
            ((operatorTensorEquiv (tensorSystem A B) C).symm X)))))
  rw [operatorTensorEquiv_symm_map_star]
  rw [tensorCongr_map_star (operatorTensorEquiv A B).symm
    (LinearEquiv.refl ℂ (Operator C))
    (operatorTensorEquiv_symm_map_star A B) (by simp)]
  rw [tensorAssoc_map_star]
  rw [tensorCongr_map_star (LinearEquiv.refl ℂ (Operator A))
    (operatorTensorEquiv B C) (by simp) (operatorTensorEquiv_map_star B C)]
  rw [operatorTensorEquiv_map_star]

namespace HPHom

/-- Bundle a star-preserving complex-linear equivalence as an HP morphism. -/
noncomputable def ofLinearEquiv {A B : Sys} (e : Operator A ≃ₗ[ℂ] Operator B)
    (h : ∀ X, e (star X) = star (e X)) : HPHom A B :=
  ⟨WithConv.toConv e.toLinearMap,
    LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr h⟩

noncomputable def leftUnitorHom (A : Sys) :
    HPHom (tensorSystem tensorUnitSystem A) A :=
  ofLinearEquiv (leftUnitorLinearEquiv A) (leftUnitorLinearEquiv_map_star A)

noncomputable def leftUnitorInv (A : Sys) :
    HPHom A (tensorSystem tensorUnitSystem A) :=
  ofLinearEquiv (leftUnitorLinearEquiv A).symm
    (linearEquiv_symm_map_star (leftUnitorLinearEquiv A)
      (leftUnitorLinearEquiv_map_star A))

noncomputable def rightUnitorHom (A : Sys) :
    HPHom (tensorSystem A tensorUnitSystem) A :=
  ofLinearEquiv (rightUnitorLinearEquiv A) (rightUnitorLinearEquiv_map_star A)

noncomputable def rightUnitorInv (A : Sys) :
    HPHom A (tensorSystem A tensorUnitSystem) :=
  ofLinearEquiv (rightUnitorLinearEquiv A).symm
    (linearEquiv_symm_map_star (rightUnitorLinearEquiv A)
      (rightUnitorLinearEquiv_map_star A))

noncomputable def associatorHom (A B C : Sys) :
    HPHom (tensorSystem (tensorSystem A B) C)
      (tensorSystem A (tensorSystem B C)) :=
  ofLinearEquiv (associatorLinearEquiv A B C)
    (associatorLinearEquiv_map_star A B C)

noncomputable def associatorInv (A B C : Sys) :
    HPHom (tensorSystem A (tensorSystem B C))
      (tensorSystem (tensorSystem A B) C) :=
  ofLinearEquiv (associatorLinearEquiv A B C).symm
    (linearEquiv_symm_map_star (associatorLinearEquiv A B C)
      (associatorLinearEquiv_map_star A B C))

end HPHom

noncomputable def leftUnitorIso (A : Sys) :
    tensorSystem tensorUnitSystem A ≅ A where
  hom := HPHom.leftUnitorHom A
  inv := HPHom.leftUnitorInv A
  hom_inv_id := by
    apply HPHom.ext
    intro X
    exact (leftUnitorLinearEquiv A).symm_apply_apply X
  inv_hom_id := by
    apply HPHom.ext
    intro X
    exact (leftUnitorLinearEquiv A).apply_symm_apply X

noncomputable def rightUnitorIso (A : Sys) :
    tensorSystem A tensorUnitSystem ≅ A where
  hom := HPHom.rightUnitorHom A
  inv := HPHom.rightUnitorInv A
  hom_inv_id := by
    apply HPHom.ext
    intro X
    exact (rightUnitorLinearEquiv A).symm_apply_apply X
  inv_hom_id := by
    apply HPHom.ext
    intro X
    exact (rightUnitorLinearEquiv A).apply_symm_apply X

noncomputable def associatorIso (A B C : Sys) :
    tensorSystem (tensorSystem A B) C ≅ tensorSystem A (tensorSystem B C) where
  hom := HPHom.associatorHom A B C
  inv := HPHom.associatorInv A B C
  hom_inv_id := by
    apply HPHom.ext
    intro X
    exact (associatorLinearEquiv A B C).symm_apply_apply X
  inv_hom_id := by
    apply HPHom.ext
    intro X
    exact (associatorLinearEquiv A B C).apply_symm_apply X

/-! ## Monoidal and symmetric coherence -/

noncomputable def operatorTensorIso (A B : Sys) :
    operatorFunctor.obj A ⊗ operatorFunctor.obj B ≅
      operatorFunctor.obj (tensorSystem A B) :=
  (operatorTensorEquiv A B).toModuleIso

noncomputable def operatorUnitIso :
    𝟙_ (ModuleCat ℂ) ≅ operatorFunctor.obj tensorUnitSystem :=
  operatorUnitEquiv.toModuleIso

noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct Sys where
  tensorObj := tensorSystem
  whiskerLeft X _ _ f := HPHom.tensor (𝟙 X) f
  whiskerRight f Y := HPHom.tensor f (𝟙 Y)
  tensorHom := HPHom.tensor
  tensorUnit := tensorUnitSystem
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso

private noncomputable def monoidalInducingData :
    CategoryTheory.Monoidal.InducingFunctorData operatorFunctor where
  μIso := operatorTensorIso
  whiskerLeft_eq := by
    intro X Y₁ Y₂ f
    rfl
  whiskerRight_eq := by
    intro X₁ X₂ f Y
    rfl
  tensorHom_eq := by
    intro X₁ Y₁ X₂ Y₂ f g
    rfl
  εIso := operatorUnitIso
  associator_eq := by
    intro X Y Z
    rfl
  leftUnitor_eq := by
    intro X
    rfl
  rightUnitor_eq := by
    intro X
    rfl

noncomputable instance monoidalCategory : MonoidalCategory Sys :=
  CategoryTheory.Monoidal.induced operatorFunctor monoidalInducingData

noncomputable instance operatorFunctorMonoidal : operatorFunctor.Monoidal :=
  CategoryTheory.Monoidal.fromInducedMonoidal operatorFunctor monoidalInducingData

instance operatorFunctorAdditive : operatorFunctor.Additive where
  map_add := by
    intro X Y f g
    rfl

instance monoidalPreadditive : MonoidalPreadditive Sys :=
  monoidalPreadditive_of_faithful operatorFunctor

instance monoidalRealLinear : MonoidalLinear ℝ Sys where
  whiskerLeft_smul := by
    intro X Y Z r f
    change HPHom.tensor (𝟙 X) (r • f) = r • HPHom.tensor (𝟙 X) f
    apply HPHom.ext
    intro W
    change operatorTensorEquiv X Z
        (TensorProduct.map (HPHom.toRawSuperoperator (𝟙 X))
          ((r : ℂ) • HPHom.toRawSuperoperator f)
          ((operatorTensorEquiv X Y).symm W)) =
      (r : ℂ) • operatorTensorEquiv X Z
        (TensorProduct.map (HPHom.toRawSuperoperator (𝟙 X))
          (HPHom.toRawSuperoperator f) ((operatorTensorEquiv X Y).symm W))
    rw [TensorProduct.map_smul_right]
    exact (operatorTensorEquiv X Z).map_smul (r : ℂ) _
  smul_whiskerRight := by
    intro r Y Z f X
    change HPHom.tensor (r • f) (𝟙 X) = r • HPHom.tensor f (𝟙 X)
    apply HPHom.ext
    intro W
    change operatorTensorEquiv Z X
        (TensorProduct.map ((r : ℂ) • HPHom.toRawSuperoperator f)
          (HPHom.toRawSuperoperator (𝟙 X))
          ((operatorTensorEquiv Y X).symm W)) =
      (r : ℂ) • operatorTensorEquiv Z X
        (TensorProduct.map (HPHom.toRawSuperoperator f)
          (HPHom.toRawSuperoperator (𝟙 X))
          ((operatorTensorEquiv Y X).symm W))
    rw [TensorProduct.map_smul_left]
    exact (operatorTensorEquiv Z X).map_smul (r : ℂ) _

end QuantumModel
