import Quantum.TraceInequality.Loewner.Koranyi.DyadicPointFamily
import Quantum.TraceInequality.Loewner.Koranyi.SignedPoints

namespace Quantum.TraceInequality.Loewner

open Set

noncomputable section

/-!
# Augmented point families for the Chapter 27 Proposition 27.3 backbone

The theorem-51 producer needs a single finite point family that contains both
the signed-points used by the boundary-trace backbone and the dyadic centers
used by Proposition 27.3.  This file provides only that finite point-family
layer and its selectors.
-/

/-- Finite set containing `0`, the signed points at stage `m`, and the dyadic centers.
Proposition 27.3 of [simon2019]. -/
def augmentedBackbonePointSet (m : ℕ) : Finset ℝ :=
  insert 0
    ((Finset.univ.image fun i : Fin (m + 1) =>
        _root_.Quantum.TraceInequality.Loewner.signedPoints m i) ∪
      (Finset.univ.image fun i : Fin (nonzeroInteriorDyadicPointCount m + 1) =>
        zeroAnchoredDyadicPointFamily m i))

/-- Nonzero part of `augmentedBackbonePointSet`.
Proposition 27.3 of [simon2019]. -/
def augmentedBackbonePointSetNonzero (m : ℕ) : Finset ℝ :=
  (augmentedBackbonePointSet m).erase 0

/-- Number of nonzero augmented points.
Proposition 27.3 of [simon2019]. -/
def augmentedBackbonePointCount (m : ℕ) : ℕ :=
  (augmentedBackbonePointSetNonzero m).card

/-- Augmented point family with `0` at index `0`.
Proposition 27.3 of [simon2019]. -/
noncomputable def augmentedBackbonePointFamily
    (m : ℕ) : Fin (augmentedBackbonePointCount m + 1) → ℝ :=
  Fin.cases 0 fun i => (augmentedBackbonePointSetNonzero m).orderEmbOfFin rfl i

/-- The augmented backbone point family sends the index `0` to the point `0`. -/
@[simp] lemma augmentedBackbonePointFamily_zero (m : ℕ) :
    augmentedBackbonePointFamily m 0 = 0 :=
  rfl

/-- On successor indices the augmented backbone point family enumerates the nonzero
augmented points in increasing order. -/
@[simp] lemma augmentedBackbonePointFamily_succ (m : ℕ)
    (i : Fin (augmentedBackbonePointCount m)) :
    augmentedBackbonePointFamily m i.succ =
      (augmentedBackbonePointSetNonzero m).orderEmbOfFin rfl i :=
  rfl

/-- Every successor entry of the augmented family belongs to its nonzero point set.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_succ_mem_nonzero (m : ℕ)
    (i : Fin (augmentedBackbonePointCount m)) :
    augmentedBackbonePointFamily m i.succ ∈ augmentedBackbonePointSetNonzero m := by
  exact (augmentedBackbonePointSetNonzero m).orderEmbOfFin_mem rfl i

/-- Every successor entry of the augmented family is nonzero.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_succ_ne_zero (m : ℕ)
    (i : Fin (augmentedBackbonePointCount m)) :
    augmentedBackbonePointFamily m i.succ ≠ 0 := by
  have hmem := augmentedBackbonePointFamily_succ_mem_nonzero m i
  exact (Finset.mem_erase.mp hmem).1

private lemma augmentedBackbonePointSet_mem_Ioo_of_mem {m : ℕ} {x : ℝ}
    (hx : x ∈ augmentedBackbonePointSet m) :
    x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases Finset.mem_insert.mp hx with hx0 | hx
  · simp [hx0]
  · rcases Finset.mem_union.mp hx with hxSigned | hxDyadic
    · rcases Finset.mem_image.mp hxSigned with ⟨i, _, rfl⟩
      exact (_root_.Quantum.TraceInequality.Loewner.pointsHyp_signedPoints (n := m)).2.2.1 i
    · rcases Finset.mem_image.mp hxDyadic with ⟨i, _, rfl⟩
      exact zeroAnchoredDyadicPointFamily_mem_Ioo m i

/-- All augmented backbone points lie in the open interval `(-1,1)`.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_mem_Ioo
    (m : ℕ) (i : Fin (augmentedBackbonePointCount m + 1)) :
    augmentedBackbonePointFamily m i ∈ Set.Ioo (-1 : ℝ) 1 := by
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
      have hmemNonzero := augmentedBackbonePointFamily_succ_mem_nonzero m i
      exact augmentedBackbonePointSet_mem_Ioo_of_mem (Finset.mem_erase.mp hmemNonzero).2

/-- The augmented backbone family is injective.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_injective (m : ℕ) :
    Function.Injective (augmentedBackbonePointFamily m) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
          exfalso
          exact augmentedBackbonePointFamily_succ_ne_zero m j hij.symm
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          exfalso
          exact augmentedBackbonePointFamily_succ_ne_zero m i (by simpa using hij)
      | succ j =>
          apply congrArg Fin.succ
          have hpoints :
              (augmentedBackbonePointSetNonzero m).orderEmbOfFin rfl i =
                (augmentedBackbonePointSetNonzero m).orderEmbOfFin rfl j := by
            simpa using hij
          exact ((augmentedBackbonePointSetNonzero m).orderEmbOfFin rfl).injective hpoints

/--
The augmented family satisfies the Chapter 27 point hypotheses required by the
Koranyi finite construction.

Proposition 27.3 of [simon2019].
-/
lemma pointsHyp_augmentedBackbonePointFamily (m : ℕ) :
    _root_.Quantum.TraceInequality.pointsHyp
      (n := augmentedBackbonePointCount m) (augmentedBackbonePointFamily m) := by
  refine ⟨augmentedBackbonePointFamily_zero m, augmentedBackbonePointFamily_injective m,
    augmentedBackbonePointFamily_mem_Ioo m, ?_⟩
  intro i hi hzero
  have hEq : augmentedBackbonePointFamily m i = augmentedBackbonePointFamily m 0 := by
    simp [hzero]
  exact hi ((augmentedBackbonePointFamily_injective m) hEq)

private lemma signedPoint_mem_augmentedBackbonePointSet (m : ℕ) (i : Fin (m + 1)) :
    _root_.Quantum.TraceInequality.Loewner.signedPoints m i ∈ augmentedBackbonePointSet m := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

private lemma dyadicPoint_mem_augmentedBackbonePointSet
    (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    zeroAnchoredDyadicPointFamily m i ∈ augmentedBackbonePointSet m := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

private lemma signedPoint_mem_augmentedBackbonePointSetNonzero
    (m : ℕ) (i : Fin (m + 1))
    (h : _root_.Quantum.TraceInequality.Loewner.signedPoints m i ≠ 0) :
    _root_.Quantum.TraceInequality.Loewner.signedPoints m i ∈ augmentedBackbonePointSetNonzero m :=
  Finset.mem_erase.mpr ⟨h, signedPoint_mem_augmentedBackbonePointSet m i⟩

private lemma dyadicPoint_mem_augmentedBackbonePointSetNonzero
    (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1))
    (h : zeroAnchoredDyadicPointFamily m i ≠ 0) :
    zeroAnchoredDyadicPointFamily m i ∈ augmentedBackbonePointSetNonzero m :=
  Finset.mem_erase.mpr ⟨h, dyadicPoint_mem_augmentedBackbonePointSet m i⟩

/-- Index of a signed point in the augmented family.
Proposition 27.3 of [simon2019]. -/
noncomputable def augmentedBackboneSignedIndex (m : ℕ) (i : Fin (m + 1)) :
    Fin (augmentedBackbonePointCount m + 1) :=
  if h : _root_.Quantum.TraceInequality.Loewner.signedPoints m i = 0 then 0
  else
    Fin.succ
      (((augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl).symm
        ⟨_root_.Quantum.TraceInequality.Loewner.signedPoints m i,
          signedPoint_mem_augmentedBackbonePointSetNonzero m i h⟩)

/-- The signed-point selector evaluates to the corresponding signed point.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_signedIndex
    (m : ℕ) (i : Fin (m + 1)) :
    augmentedBackbonePointFamily m (augmentedBackboneSignedIndex m i) =
      _root_.Quantum.TraceInequality.Loewner.signedPoints m i := by
  by_cases h : _root_.Quantum.TraceInequality.Loewner.signedPoints m i = 0
  · simp [augmentedBackboneSignedIndex, h]
  · simp only [augmentedBackboneSignedIndex, h, dite_false, augmentedBackbonePointFamily_succ]
    have hidx :
        (augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl
            (((augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl).symm
              ⟨_root_.Quantum.TraceInequality.Loewner.signedPoints m i,
                signedPoint_mem_augmentedBackbonePointSetNonzero m i h⟩) =
          ⟨_root_.Quantum.TraceInequality.Loewner.signedPoints m i,
            signedPoint_mem_augmentedBackbonePointSetNonzero m i h⟩ := by
      simp
    exact congrArg Subtype.val hidx

/-- Index of a dyadic point in the augmented family.
Proposition 27.3 of [simon2019]. -/
noncomputable def augmentedBackboneDyadicIndex
    (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    Fin (augmentedBackbonePointCount m + 1) :=
  if h : zeroAnchoredDyadicPointFamily m i = 0 then 0
  else
    Fin.succ
      (((augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl).symm
        ⟨zeroAnchoredDyadicPointFamily m i, dyadicPoint_mem_augmentedBackbonePointSetNonzero m i h⟩)

/-- The dyadic-point selector evaluates to the corresponding dyadic point.
Proposition 27.3 of [simon2019]. -/
lemma augmentedBackbonePointFamily_dyadicIndex
    (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    augmentedBackbonePointFamily m (augmentedBackboneDyadicIndex m i) =
      zeroAnchoredDyadicPointFamily m i := by
  by_cases h : zeroAnchoredDyadicPointFamily m i = 0
  · simp [augmentedBackboneDyadicIndex, h]
  · simp only [augmentedBackboneDyadicIndex, h, dite_false, augmentedBackbonePointFamily_succ]
    have hidx :
        (augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl
            (((augmentedBackbonePointSetNonzero m).orderIsoOfFin rfl).symm
              ⟨zeroAnchoredDyadicPointFamily m i,
                dyadicPoint_mem_augmentedBackbonePointSetNonzero m i h⟩) =
          ⟨zeroAnchoredDyadicPointFamily m i,
            dyadicPoint_mem_augmentedBackbonePointSetNonzero m i h⟩ := by
      simp
    exact congrArg Subtype.val hidx

end

end Quantum.TraceInequality.Loewner
