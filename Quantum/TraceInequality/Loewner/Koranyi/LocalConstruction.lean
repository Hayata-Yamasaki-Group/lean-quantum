import Quantum.TraceInequality.Loewner.Koranyi.AugmentedPoints
import Quantum.TraceInequality.Loewner.Koranyi.FiniteResolventWitness
import Quantum.TraceInequality.Loewner.Koranyi.FiniteKoranyiInsideMass

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Basis.Basic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory

open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
# Local Chapter 27 construction for the Prop. 27.3 dyadic backbone

This file is the theorem-52 local stage.  It builds the direct Chapter 27
finite-dimensional operator on the augmented point family.  It does not use the
Step57 reciprocal-side operator as the construction theorem.
-/

/-- Direct local finite-dimensional construction for Chapter 27 Prop. 27.3.
Proposition 27.3 of [simon2019]. -/
structure AugmentedLoewnerLocalConstruction (f : ℝ → ℝ) (m : ℕ) where
  H : Type
  instNormedAddCommGroup : NormedAddCommGroup H
  instInnerProductSpace : InnerProductSpace ℂ H
  instFiniteDimensional : FiniteDimensional ℂ H
  v : Fin (augmentedBackbonePointCount m + 1) → H
  φ : H
  A : H →ₗ[ℂ] H
  hGram :
    ∀ i j : Fin (augmentedBackbonePointCount m + 1),
      inner (𝕜 := ℂ) (v i) (v j) =
        (loewnerKernel f (augmentedBackbonePointFamily m i)
          (augmentedBackbonePointFamily m j) : ℂ)
  hSpanTop : Submodule.span ℂ (Set.range v) = ⊤
  hPhi :
    ∀ i : Fin (augmentedBackbonePointCount m + 1),
      inner (𝕜 := ℂ) (v i) φ =
        (f (augmentedBackbonePointFamily m i) : ℂ)
  hA_symm : A.IsSymmetric
  hSolution :
    ∀ i : Fin (augmentedBackbonePointCount m + 1),
      (A - (augmentedBackbonePointFamily m i : ℂ) •
          (LinearMap.id : H →ₗ[ℂ] H)) (v i) = φ

attribute [instance] AugmentedLoewnerLocalConstruction.instNormedAddCommGroup
attribute [instance] AugmentedLoewnerLocalConstruction.instInnerProductSpace
attribute [instance] AugmentedLoewnerLocalConstruction.instFiniteDimensional

namespace AugmentedLoewnerLocalConstruction

variable {f : ℝ → ℝ} {m : ℕ}

/-- The finite witness represented by the direct local construction. -/
def toFiniteWitness (C : AugmentedLoewnerLocalConstruction f m) : FiniteResolventWitness f m where
  H := C.H
  instNormedAddCommGroup := C.instNormedAddCommGroup
  instInnerProductSpace := C.instInnerProductSpace
  instFiniteDimensional := C.instFiniteDimensional
  T := C.A
  hT := C.hA_symm
  φ := C.φ

/-- Dyadic-center solutions obtained by selecting dyadic points inside the augmented family. -/
theorem dyadic_solution
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    ∃ δ : C.H,
      (C.A - (zeroAnchoredDyadicPointFamily m i : ℂ) •
          (LinearMap.id : C.H →ₗ[ℂ] C.H)) δ = C.φ := by
  refine ⟨C.v (augmentedBackboneDyadicIndex m i), ?_⟩
  have hsol := C.hSolution (augmentedBackboneDyadicIndex m i)
  have hpoint :
      augmentedBackbonePointFamily m (augmentedBackboneDyadicIndex m i) =
        zeroAnchoredDyadicPointFamily m i :=
    augmentedBackbonePointFamily_dyadicIndex m i
  simpa [hpoint] using hsol

/--
The dyadic inverse-square estimate produced by the direct local construction,
with the explicit selected Gram vector norm as the local bound.
-/
theorem dyadic_sqInvDist_le_solution_norm
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
        ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
          (T := C.A) (hT := C.hA_symm) C.φ)) ≤
      ENNReal.ofReal (‖C.v (augmentedBackboneDyadicIndex m i)‖ ^ 2) := by
  have hsol := C.hSolution (augmentedBackboneDyadicIndex m i)
  have hpoint :
      augmentedBackbonePointFamily m (augmentedBackboneDyadicIndex m i) =
        zeroAnchoredDyadicPointFamily m i :=
    augmentedBackbonePointFamily_dyadicIndex m i
  exact
    (by
      simpa [hpoint] using
        (_root_.Quantum.TraceInequality.Loewner.lintegral_sqInvDist_diracMeasure_le_of_solution
          (T := C.A) (hT := C.hA_symm) (φ := C.φ)
          (δ := C.v (augmentedBackboneDyadicIndex m i))
          (x0 := augmentedBackbonePointFamily m (augmentedBackboneDyadicIndex m i))
          hsol))

end AugmentedLoewnerLocalConstruction

private lemma direct_loewner_identity (f : ℝ → ℝ) (x y : ℝ) :
    ((x : ℂ) * (loewnerKernel f x y : ℂ) + (f y : ℂ)) =
      ((y : ℂ) * (loewnerKernel f x y : ℂ) + (f x : ℂ)) := by
  by_cases hxy : x = y
  · subst hxy
    ring
  · have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hreal :
        x * loewnerKernel f x y + f y =
          y * loewnerKernel f x y + f x := by
      simp [loewnerKernel_eq_div (f := f) (x := x) (y := y) hxy]
      field_simp [hsub]
      ring
    exact_mod_cast hreal

private theorem exists_prop273LocalConstruction_of_posDef
    {f : ℝ → ℝ} {m : ℕ}
    (hL :
      (loewnerMatrix
        (n := augmentedBackbonePointCount m) f
        (augmentedBackbonePointFamily m)).PosDef) :
    ∃ _ : AugmentedLoewnerLocalConstruction f m, True := by
  classical
  let y : Fin (augmentedBackbonePointCount m + 1) → ℝ :=
    augmentedBackbonePointFamily m
  rcases Quantum.TraceInequality.Loewner.exists_gram_vectors
      (n := augmentedBackbonePointCount m) (f := f) (y := y) hL.posSemidef with
    ⟨H, instN, instI, instFD, v, hGram, hSpanTop⟩
  letI : NormedAddCommGroup H := instN
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hgram :
      Matrix.gram ℂ v =
        loewnerMatrix (n := augmentedBackbonePointCount m) f y := by
    ext i j
    simpa [Matrix.gram_apply, loewnerMatrix] using hGram i j
  have hpos : (Matrix.gram ℂ v).PosDef := by
    simpa [hgram, y] using hL
  have hv_li : LinearIndependent ℂ v :=
    Matrix.linearIndependent_of_posDef_gram (𝕜 := ℂ) (v := v) hpos
  have hv_sp' : (⊤ : Submodule ℂ H) ≤ Submodule.span ℂ (Set.range v) := by
    simp [hSpanTop]
  let b : Module.Basis (Fin (augmentedBackbonePointCount m + 1)) ℂ H :=
    Module.Basis.mk hv_li hv_sp'
  have hb : ∀ i : Fin (augmentedBackbonePointCount m + 1), b i = v i := by
    intro i
    exact Module.Basis.mk_apply (hli := hv_li) (hsp := hv_sp') (v := v) i
  let ℓ : H →ₗ[ℂ] ℂ := b.constr ℂ fun i => (f (y i) : ℂ)
  let ℓc : StrongDual ℂ H :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := H) (F' := ℂ)) ℓ
  let φ : H := (InnerProductSpace.toDual ℂ H).symm ℓc
  have hPhi_left :
      ∀ i : Fin (augmentedBackbonePointCount m + 1),
        inner (𝕜 := ℂ) φ (v i) = (f (y i) : ℂ) := by
    intro i
    have hdual : inner (𝕜 := ℂ) φ (v i) = ℓ (v i) := by
      dsimp [φ]
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    have hbasis : ℓ (v i) = (f (y i) : ℂ) := by
      have : ℓ (b i) = (f (y i) : ℂ) := by
        exact b.constr_basis (S := ℂ) (f := fun i => (f (y i) : ℂ)) i
      simpa [hb i] using this
    exact hdual.trans hbasis
  have hPhi :
      ∀ i : Fin (augmentedBackbonePointCount m + 1),
        inner (𝕜 := ℂ) (v i) φ = (f (y i) : ℂ) := by
    intro i
    have hconj : star (inner (𝕜 := ℂ) φ (v i)) = inner (𝕜 := ℂ) (v i) φ :=
      inner_conj_symm (v i) φ
    have hstar : star (f (y i) : ℂ) = (f (y i) : ℂ) := by
      simp
    calc
      inner (𝕜 := ℂ) (v i) φ = star (inner (𝕜 := ℂ) φ (v i)) := hconj.symm
      _ = (f (y i) : ℂ) := by simp [hPhi_left i, hstar]
  let w : Fin (augmentedBackbonePointCount m + 1) → H :=
    fun i => (y i : ℂ) • v i + φ
  let A : H →ₗ[ℂ] H := b.constr ℂ w
  have hA_apply :
      ∀ i : Fin (augmentedBackbonePointCount m + 1),
        A (v i) = (y i : ℂ) • v i + φ := by
    intro i
    have : A (b i) = w i := by
      exact b.constr_basis (S := ℂ) (f := w) i
    simpa [hb i, w] using this
  have hSolution :
      ∀ i : Fin (augmentedBackbonePointCount m + 1),
        (A - (y i : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)) (v i) = φ := by
    intro i
    have hAvi := hA_apply i
    calc
      (A - (y i : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)) (v i)
          = A (v i) - (y i : ℂ) • v i := by
              rfl
      _ = φ := by
            rw [hAvi]
            simp
  have hsymm_on_v :
      ∀ i j : Fin (augmentedBackbonePointCount m + 1),
        inner (𝕜 := ℂ) (A (v i)) (v j) =
          inner (𝕜 := ℂ) (v i) (A (v j)) := by
    intro i j
    have hA_i := hA_apply i
    have hA_j := hA_apply j
    have hG : inner (𝕜 := ℂ) (v i) (v j) =
        (loewnerKernel f (y i) (y j) : ℂ) := hGram i j
    have hφj : inner (𝕜 := ℂ) φ (v j) = (f (y j) : ℂ) := hPhi_left j
    have hiφ : inner (𝕜 := ℂ) (v i) φ = (f (y i) : ℂ) := hPhi i
    have hleft_expand :
        inner (𝕜 := ℂ) (A (v i)) (v j) =
          (y i : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
            inner (𝕜 := ℂ) φ (v j) := by
      rw [hA_i]
      calc
        inner (𝕜 := ℂ) ((y i : ℂ) • v i + φ) (v j)
            = inner (𝕜 := ℂ) ((y i : ℂ) • v i) (v j) +
                inner (𝕜 := ℂ) φ (v j) := by
                rw [inner_add_left]
        _ = (y i : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
                inner (𝕜 := ℂ) φ (v j) := by
              have hs :
                  inner (𝕜 := ℂ) ((y i : ℂ) • v i) (v j) =
                    star (y i : ℂ) * inner (𝕜 := ℂ) (v i) (v j) := by
                simpa using
                  (inner_smul_left (𝕜 := ℂ) (x := v i) (y := v j) (r := (y i : ℂ)))
              have hstar : star (y i : ℂ) = (y i : ℂ) := by
                simp
              rw [hs, hstar]
    have hright_expand :
        inner (𝕜 := ℂ) (v i) (A (v j)) =
          (y j : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
            inner (𝕜 := ℂ) (v i) φ := by
      rw [hA_j]
      calc
        inner (𝕜 := ℂ) (v i) ((y j : ℂ) • v j + φ)
            = inner (𝕜 := ℂ) (v i) ((y j : ℂ) • v j) +
                inner (𝕜 := ℂ) (v i) φ := by
                rw [inner_add_right]
        _ = (y j : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
                inner (𝕜 := ℂ) (v i) φ := by
              have hs :
                  inner (𝕜 := ℂ) (v i) ((y j : ℂ) • v j) =
                    (y j : ℂ) * inner (𝕜 := ℂ) (v i) (v j) := by
                simpa using
                  (inner_smul_right (𝕜 := ℂ) (x := v i) (y := v j) (r := (y j : ℂ)))
              rw [hs]
    calc
      inner (𝕜 := ℂ) (A (v i)) (v j)
          = (y i : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
              inner (𝕜 := ℂ) φ (v j) := hleft_expand
      _ = (y i : ℂ) * (loewnerKernel f (y i) (y j) : ℂ) + (f (y j) : ℂ) := by
              simp [hG, hφj]
      _ = (y j : ℂ) * (loewnerKernel f (y i) (y j) : ℂ) + (f (y i) : ℂ) :=
              direct_loewner_identity f (y i) (y j)
      _ = (y j : ℂ) * inner (𝕜 := ℂ) (v i) (v j) +
              inner (𝕜 := ℂ) (v i) φ := by
              simp [hG, hiφ]
      _ = inner (𝕜 := ℂ) (v i) (A (v j)) := hright_expand.symm
  have hsymm_basis :
      ∀ i j : Fin (augmentedBackbonePointCount m + 1),
        inner (𝕜 := ℂ) (A (b i)) (b j) =
          inner (𝕜 := ℂ) (b i) (A (b j)) := by
    intro i j
    simpa [hb i, hb j] using hsymm_on_v i j
  have hsymm : A.IsSymmetric := by
    intro x z
    set sx : Finset (Fin (augmentedBackbonePointCount m + 1)) := Finset.univ
    set sz : Finset (Fin (augmentedBackbonePointCount m + 1)) := Finset.univ
    set fx : Fin (augmentedBackbonePointCount m + 1) → H := fun i => (b.repr x i) • b i
    set fz : Fin (augmentedBackbonePointCount m + 1) → H := fun j => (b.repr z j) • b j
    have hx : x = ∑ i ∈ sx, fx i := by
      exact (b.sum_repr x).symm
    have hz : z = ∑ j ∈ sz, fz j := by
      exact (b.sum_repr z).symm
    rw [hx, hz]
    rw [map_sum (g := A) (f := fx) (s := sx)]
    rw [map_sum (g := A) (f := fz) (s := sz)]
    rw [sum_inner sx (fun i => A (fx i)) (∑ j ∈ sz, fz j)]
    rw [sum_inner sx fx (∑ j ∈ sz, A (fz j))]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [inner_sum sz fz (A (fx i))]
    rw [inner_sum sz (fun j => A (fz j)) (fx i)]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hL :
        inner (𝕜 := ℂ) (A (fx i)) (fz j)
          =
            (starRingEnd ℂ) (b.repr x i) * (b.repr z j) *
              inner (𝕜 := ℂ) (A (b i)) (b j) := by
      dsimp [fx, fz]
      calc
        inner (𝕜 := ℂ) (A ((b.repr x i) • b i)) ((b.repr z j) • b j)
            = inner (𝕜 := ℂ) ((b.repr x i) • A (b i)) ((b.repr z j) • b j) := by
                simp
        _ = (starRingEnd ℂ) (b.repr x i) *
              inner (𝕜 := ℂ) (A (b i)) ((b.repr z j) • b j) := by
              simp [inner_smul_left]
        _ =
            (starRingEnd ℂ) (b.repr x i) *
              ((b.repr z j) * inner (𝕜 := ℂ) (A (b i)) (b j)) := by
              simp [inner_smul_right]
        _ =
            (starRingEnd ℂ) (b.repr x i) * (b.repr z j) *
              inner (𝕜 := ℂ) (A (b i)) (b j) := by
              simp [mul_assoc]
    have hR :
        inner (𝕜 := ℂ) (fx i) (A (fz j))
          =
            (starRingEnd ℂ) (b.repr x i) * (b.repr z j) *
              inner (𝕜 := ℂ) (b i) (A (b j)) := by
      dsimp [fx, fz]
      calc
        inner (𝕜 := ℂ) ((b.repr x i) • b i) (A ((b.repr z j) • b j))
            = inner (𝕜 := ℂ) ((b.repr x i) • b i) ((b.repr z j) • A (b j)) := by
                simp
        _ =
            (starRingEnd ℂ) (b.repr x i) *
              inner (𝕜 := ℂ) (b i) ((b.repr z j) • A (b j)) := by
              simp [inner_smul_left]
        _ =
            (starRingEnd ℂ) (b.repr x i) *
              ((b.repr z j) * inner (𝕜 := ℂ) (b i) (A (b j))) := by
              simp [inner_smul_right]
        _ =
            (starRingEnd ℂ) (b.repr x i) * (b.repr z j) *
              inner (𝕜 := ℂ) (b i) (A (b j)) := by
              simp [mul_assoc]
    simp [hL, hR, hsymm_basis, mul_assoc]
  refine
    ⟨{ H := H
       instNormedAddCommGroup := instN
       instInnerProductSpace := instI
       instFiniteDimensional := instFD
       v := v
       φ := φ
       A := A
       hGram := ?_
       hSpanTop := hSpanTop
       hPhi := ?_
       hA_symm := hsymm
       hSolution := ?_ }, trivial⟩
  · intro i j
    simpa [y] using hGram i j
  · intro i
    simpa [y] using hPhi i
  · intro i
    simpa [y] using hSolution i

/-- Direct local Chapter 27 construction from positivity of the augmented Loewner matrix.
Proposition 27.3 of [simon2019]. -/
noncomputable def augmentedLoewnerLocalConstruction_of_posDef
    {f : ℝ → ℝ} {m : ℕ}
    (hL :
      (loewnerMatrix
        (n := augmentedBackbonePointCount m) f
        (augmentedBackbonePointFamily m)).PosDef) :
    AugmentedLoewnerLocalConstruction f m :=
  Classical.choose (exists_prop273LocalConstruction_of_posDef (f := f) (m := m) hL)

/-- Direct local Chapter 27 construction supplied by global strict positivity.
Proposition 27.3 of [simon2019]. -/
noncomputable def augmentedLoewnerLocalConstruction_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ) :
    AugmentedLoewnerLocalConstruction f m :=
  augmentedLoewnerLocalConstruction_of_posDef
    (f := f) (m := m)
    (h (augmentedBackbonePointCount m) (augmentedBackbonePointFamily m)
      (pointsHyp_augmentedBackbonePointFamily m))

end

end Quantum.TraceInequality.Loewner
