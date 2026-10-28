import Quantum.TraceInequality.Loewner.Koranyi.FiniteResolventWitness
import Quantum.TraceInequality.Loewner.Koranyi.LocalConstruction
import Quantum.TraceInequality.Loewner.Koranyi.DyadicMassZero

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped Topology
open scoped NNReal
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
# Book-route inside mass estimate for Chapter 27 Proposition 27.3

This file keeps the Chapter 27 book route separate from the canonical
signed-evaluation transfer route.  It proves inside-mass decay for the Dirac
measures attached directly to `AugmentedLoewnerLocalConstruction`, assuming the
book-side uniform derivative bound as an explicit input.
-/

namespace AugmentedLoewnerLocalConstruction

variable {f : ℝ → ℝ} {m : ℕ}

/-- The selected dyadic Gram vector has squared norm equal to the diagonal
Löwner kernel, i.e. `deriv f` at the selected dyadic point. -/
theorem norm_sq_dyadicIndex_eq_deriv
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    ‖C.v (augmentedBackboneDyadicIndex m i)‖ ^ 2 =
      deriv f (zeroAnchoredDyadicPointFamily m i) := by
  let idx := augmentedBackboneDyadicIndex m i
  have hdiag :
      inner (𝕜 := ℂ) (C.v idx) (C.v idx) =
        (loewnerKernel f (augmentedBackbonePointFamily m idx)
          (augmentedBackbonePointFamily m idx) : ℂ) :=
    C.hGram idx idx
  have hre := congrArg Complex.re hdiag
  have hnorm :
      ‖C.v idx‖ ^ 2 =
        loewnerKernel f (augmentedBackbonePointFamily m idx)
          (augmentedBackbonePointFamily m idx) :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) (x := C.v idx)).symm.trans hre
  have hpoint :
      augmentedBackbonePointFamily m idx = zeroAnchoredDyadicPointFamily m i := by
    simpa [idx] using augmentedBackbonePointFamily_dyadicIndex m i
  simpa [idx, hpoint] using hnorm

/-- The local dyadic inverse-square estimate in the derivative form used in
Chapter 27 Proposition 27.3. -/
theorem dyadic_sqInvDist_le_deriv
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
        ∂(C.toFiniteWitness.diracMeasure)) ≤
      ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) := by
  have hnorm := C.norm_sq_dyadicIndex_eq_deriv i
  simpa [FiniteResolventWitness.diracMeasure,
    AugmentedLoewnerLocalConstruction.toFiniteWitness, hnorm] using
    C.dyadic_sqInvDist_le_solution_norm i

/-- Book-route inside-mass bound from a uniform derivative bound on the dyadic
family. -/
theorem insideMass_le_of_uniform_deriv_bound
    (C : AugmentedLoewnerLocalConstruction f m) (K : ENNReal)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ K) :
    C.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1) ≤
      ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
  have hbound :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
            ∂(C.toFiniteWitness.diracMeasure)) ≤ K := by
    intro i
    exact (C.dyadic_sqInvDist_le_deriv i).trans (hK i)
  have hstage :=
    finiteKoranyi_insideMass_le_of_uniform_sqInvDist
      (T := C.A) (hT := C.hA_symm) (φ := C.φ) (m := m) (K := K)
      (by
        intro i
        simpa [FiniteResolventWitness.diracMeasure,
          AugmentedLoewnerLocalConstruction.toFiniteWitness] using hbound i)
  simpa [FiniteResolventWitness.diracMeasure, AugmentedLoewnerLocalConstruction.toFiniteWitness,
    Nat.cast_add, Nat.cast_one] using hstage

end AugmentedLoewnerLocalConstruction

private lemma prop273Book_nonzeroInteriorDyadicPointCount_succ_le_pow (m : ℕ) :
    nonzeroInteriorDyadicPointCount m + 1 ≤ (2 : ℕ) ^ (m + 3) := by
  have hsub : insert (0 : ℤ) (nonzeroInteriorDyadicIndices m) ⊆ dyadicGridIndices m := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact dyadicGridIndices_contains_zero m
    · exact nonzeroInteriorDyadicIndices_subset_dyadicGridIndices m hk
  have hnot : (0 : ℤ) ∉ nonzeroInteriorDyadicIndices m := by
    simp [nonzeroInteriorDyadicIndices]
  have hcard_sub :
      (insert (0 : ℤ) (nonzeroInteriorDyadicIndices m)).card ≤ (dyadicGridIndices m).card :=
    Finset.card_le_card hsub
  have hcard : nonzeroInteriorDyadicPointCount m + 1 ≤ (dyadicGridIndices m).card := by
    simpa [nonzeroInteriorDyadicPointCount, Finset.card_insert_of_notMem hnot, Nat.add_comm] using
      hcard_sub
  have hpow : (dyadicGridIndices m).card ≤ (2 : ℕ) ^ (m + 3) := by
    simpa [dyadicGridIndices] using
      _root_.Quantum.TraceInequality.Loewner.dyadicCenters_card_le_pow (m := m)
  exact hcard.trans hpow

/-- The book-route dyadic inside-mass prefactor is bounded by `8 * dyadicGridRadius m`.
Proposition 27.3 of [simon2019]. -/
theorem bookDyadicInsideMassPrefactor_le (m : ℕ) :
    ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) ≤
      ENNReal.ofReal (8 * dyadicGridRadius m) := by
  have hcard :
      ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) ≤
        (((2 : ℕ) ^ (m + 3) : ℕ) : ENNReal) := by
    exact_mod_cast prop273Book_nonzeroInteriorDyadicPointCount_succ_le_pow m
  calc
    ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) ≤
        (((2 : ℕ) ^ (m + 3) : ℕ) : ENNReal) *
          ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) := by
          gcongr
    _ = ENNReal.ofReal (8 * dyadicGridRadius m) := by
          simpa [dyadicGridRadius] using
            _root_.Quantum.TraceInequality.Loewner.ennreal_prefactor_eq (m := m)

/--
Book-route inside-mass decay for the measures produced directly by the local
Chapter 27 construction, assuming the dyadic-family derivative bound supplied
by the smooth `\widetilde M_\infty` stage of the book proof.

Proposition 27.3 of [simon2019].
-/
theorem bookInsideMass_tendsto_zero_of_uniform_deriv_bound
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (C : ℝ≥0)
    (hDeriv :
      ∀ m : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (C : ENNReal)) :
    Tendsto
      (fun m : ℕ =>
        let LC := augmentedLoewnerLocalConstruction_of_globalStrictPosDef h m
        (LC.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1)).toReal)
      atTop (𝓝 0) := by
  have hradius :
      Tendsto (fun m : ℕ => dyadicGridRadius m) atTop (𝓝 (0 : ℝ)) := by
    simpa [dyadicGridRadius] using
      _root_.Quantum.TraceInequality.Loewner.tendsto_dyadicRadius_zero
  have hUpper :
      Tendsto (fun m : ℕ => (8 * (C : ℝ)) * dyadicGridRadius m)
        atTop (𝓝 0) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hradius.const_mul (8 * (C : ℝ))
  have hBound :
      ∀ᶠ m : ℕ in atTop,
        (let LC := augmentedLoewnerLocalConstruction_of_globalStrictPosDef h m
         (LC.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1)).toReal) ≤
          (8 * (C : ℝ)) * dyadicGridRadius m := by
    refine Eventually.of_forall ?_
    intro m
    let LC := augmentedLoewnerLocalConstruction_of_globalStrictPosDef h m
    have hstage :
        LC.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1) ≤
          ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
            ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * (C : ENNReal) :=
      LC.insideMass_le_of_uniform_deriv_bound (K := (C : ENNReal)) (hDeriv m)
    have hpref := bookDyadicInsideMassPrefactor_le m
    have hENN :
        LC.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1) ≤
          ENNReal.ofReal (8 * dyadicGridRadius m) * (C : ENNReal) := by
      calc
        LC.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1) ≤
            ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
              ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * (C : ENNReal) := hstage
        _ ≤ ENNReal.ofReal (8 * dyadicGridRadius m) * (C : ENNReal) := by
              gcongr
    have hfinite :
        ENNReal.ofReal (8 * dyadicGridRadius m) * (C : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
    have hreal := ENNReal.toReal_mono hfinite hENN
    have hright :
        (ENNReal.ofReal (8 * dyadicGridRadius m) * (C : ENNReal)).toReal =
          8 * dyadicGridRadius m * (C : ℝ) := by
      have hnonneg : 0 ≤ 8 * dyadicGridRadius m := by
        exact mul_nonneg (by norm_num) (le_of_lt (dyadicGridRadius_pos m))
      have hCnonneg : 0 ≤ (C : ℝ) := by
        exact_mod_cast C.2
      calc
        (ENNReal.ofReal (8 * dyadicGridRadius m) * (C : ENNReal)).toReal =
            (ENNReal.ofReal (8 * dyadicGridRadius m) *
              ENNReal.ofReal (C : ℝ)).toReal := by
              simp
        _ = (ENNReal.ofReal ((8 * dyadicGridRadius m) * (C : ℝ))).toReal := by
              rw [ENNReal.ofReal_mul hnonneg]
        _ = (8 * dyadicGridRadius m) * (C : ℝ) := by
              exact ENNReal.toReal_ofReal (mul_nonneg hnonneg hCnonneg)
    rw [hright] at hreal
    simpa [LC, mul_assoc, mul_comm, mul_left_comm] using hreal
  exact squeeze_zero'
    (Eventually.of_forall fun _m => ENNReal.toReal_nonneg)
    hBound hUpper

end

end Quantum.TraceInequality.Loewner
