/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Algebra.Star.LinearMap
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Finite-dimensional quantum-system skeleton

This file fixes the ambient category of finite-dimensional quantum systems.
Objects carry a strictly positive dimension.  The full complex-linear maps are retained
as raw superoperators, while categorical morphisms are the Hermiticity-preserving ones.
-/

namespace QuantumModel

open QuantumState
open CategoryTheory
open scoped ComplexStarModule

noncomputable section

-- These high-priority local paths keep the real module structures on self-adjoint
-- subtypes deterministic during elaboration.
attribute [local instance 10000] SemigroupAction.toSMul MulAction.toSemigroupAction
  DistribMulAction.toMulAction Module.toDistribMulAction Submodule.module
  selfAdjoint.instModuleSubtypeMemAddSubgroupOfStarModule

/-- A canonical finite-dimensional quantum system.  Dimension zero is excluded. -/
structure Sys where
  dim : ℕ
  dim_pos : 0 < dim

/-- The canonical Hilbert space attached to a system in the skeleton. -/
abbrev Space (A : Sys) := EuclideanSpace ℂ (Fin A.dim)

noncomputable instance spaceFiniteDimensional (A : Sys) : Module.Finite ℂ (Space A) :=
  Module.Finite.of_basis (EuclideanSpace.basisFun (Fin A.dim) ℂ).toBasis

noncomputable instance spaceQudit (A : Sys) : Qudit (Space A) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := Module.Finite.fg_top

/-- The full complex operator space attached to `A`. -/
abbrev Operator (A : Sys) := L (Space A)

/-- Canonical matrix coordinates for the operator space of `A`. -/
noncomputable def operatorEquivMatrix (A : Sys) :
    Operator A ≃⋆ₐ[ℂ] Matrix (Fin A.dim) (Fin A.dim) ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin A.dim) ℂ)

/-- The full complex-linear maps between operator spaces. -/
abbrev RawSuperoperator (A B : Sys) := Operator A →ₗ[ℂ] Operator B

/-- Hermiticity-preserving complex-linear maps, expressed as the self-adjoint part for
the intrinsic star on linear maps. -/
abbrev HPHom (A B : Sys) := selfAdjoint (WithConv (RawSuperoperator A B))

instance (priority := 10000) hpHomAddCommGroup (A B : Sys) :
    AddCommGroup (HPHom A B) :=
  (selfAdjoint (WithConv (RawSuperoperator A B))).toAddCommGroup

instance (priority := 10000) hpHomSMul (A B : Sys) : SMul ℝ (HPHom A B) where
  smul r f := ⟨(r : ℂ) • f.1, by
    rw [selfAdjoint.mem_iff]
    simp⟩

noncomputable instance (priority := 10000) hpHomModule (A B : Sys) :
    Module ℝ (HPHom A B) :=
  (selfAdjoint.submodule ℝ (WithConv (RawSuperoperator A B))).module

namespace HPHom

/-- Forget Hermiticity preservation and expose the underlying complex-linear map. -/
def toRawSuperoperator {A B : Sys} (f : HPHom A B) : RawSuperoperator A B :=
  f.1.ofConv

instance {A B : Sys} : Coe (HPHom A B) (RawSuperoperator A B) :=
  ⟨toRawSuperoperator⟩

instance {A B : Sys} : CoeFun (HPHom A B) (fun _ ↦ Operator A → Operator B) :=
  ⟨fun f ↦ toRawSuperoperator f⟩

/-- The defining star-preservation equation for an HP map. -/
theorem map_star {A B : Sys} (f : HPHom A B) (X : Operator A) :
    f (star X) = star (f X) :=
  (LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star f.1).mp f.2 X

/-- Pointwise extensionality for HP maps. -/
@[ext]
theorem ext {A B : Sys} {f g : HPHom A B}
    (h : ∀ X, f X = g X) : f = g := by
  apply Subtype.ext
  apply WithConv.ext
  apply LinearMap.ext
  exact h

/-- The identity HP map. -/
def id (A : Sys) : HPHom A A :=
  ⟨WithConv.toConv LinearMap.id,
    LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (by simp)⟩

/-- Composition of HP maps. -/
def comp {A B C : Sys} (g : HPHom B C) (f : HPHom A B) : HPHom A C :=
  ⟨WithConv.toConv
      ((toRawSuperoperator g).comp (toRawSuperoperator f)), by
    apply LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr
    intro X
    change g (f (star X)) = star (g (f X))
    rw [map_star, map_star]⟩

@[simp]
theorem toRawSuperoperator_zero {A B : Sys} :
    toRawSuperoperator (0 : HPHom A B) = 0 :=
  rfl

@[simp]
theorem toRawSuperoperator_add {A B : Sys} (f g : HPHom A B) :
    toRawSuperoperator (f + g) =
      toRawSuperoperator f + toRawSuperoperator g :=
  rfl

end HPHom

noncomputable instance instCategorySys : Category Sys where
  Hom A B := HPHom A B
  id := HPHom.id
  comp f g := HPHom.comp g f
  id_comp f := by
    ext X
    rfl
  comp_id f := by
    ext X
    rfl
  assoc f g h := by
    ext X
    rfl

/-- The tensor product object in the finite-dimensional system skeleton. -/
def tensorSystem (A B : Sys) : Sys where
  dim := A.dim * B.dim
  dim_pos := Nat.mul_pos A.dim_pos B.dim_pos

end

end QuantumModel
