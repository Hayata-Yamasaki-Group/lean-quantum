import Quantum.TraceInequality.Loewner.Koranyi.RawWitnessConstruction

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

namespace RawFiniteWitness

variable {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}

/-- The self-adjoint operator in a raw finite witness is symmetric. -/
theorem hA_symm (W : RawFiniteWitness f y) : W.A.IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint W.A).2 W.hA

/-- The witness vectors form the canonical basis of the raw finite Hilbert space. -/
noncomputable def vBasis (W : RawFiniteWitness f y) :
    Module.Basis (Fin (n + 1)) ℂ W.H :=
  Module.Basis.mk W.hLinearIndependent <| by
    simp [W.hSpanTop]

/-- The canonical witness basis evaluates to the stored witness vector. -/
@[simp] theorem vBasis_apply (W : RawFiniteWitness f y) (i : Fin (n + 1)) :
    W.vBasis i = W.v i := by
  simp [vBasis, Module.Basis.mk_apply]

/-- The coordinate vector of `v i` in the witness basis is the `i`-th unit vector. -/
@[simp] theorem vBasis_repr_v (W : RawFiniteWitness f y) (i : Fin (n + 1)) :
    W.vBasis.repr (W.v i) = Finsupp.single i (1 : ℂ) := by
  rw [← W.vBasis_apply]
  exact W.vBasis.repr_self i

/-- The span of all nonzero-index witness vectors. -/
noncomputable def nonzeroSpan (W : RawFiniteWitness f y) : Submodule ℂ W.H :=
  Submodule.span ℂ (W.v '' ({0}ᶜ : Set (Fin (n + 1))))

/-- Coordinates of `A v_i` in the witness basis for a nonzero index. -/
theorem vBasis_repr_A_apply_of_ne_zero (W : RawFiniteWitness f y) {i : Fin (n + 1)}
    (hi : i ≠ 0) :
    W.vBasis.repr (W.A (W.v i)) =
      (1 / (y i : ℂ)) • (Finsupp.single i (1 : ℂ) - Finsupp.single 0 (1 : ℂ)) := by
  rw [W.hA_apply i hi, W.hφ]
  simp [W.vBasis_repr_v, sub_eq_add_neg]


/-- The self-coordinate of `A v_i` is `1 / y_i` for nonzero `i`. -/
@[simp] theorem vBasis_repr_A_apply_of_ne_zero_apply_self (W : RawFiniteWitness f y)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    W.vBasis.repr (W.A (W.v i)) i = (1 / (y i : ℂ)) := by
  rw [W.vBasis_repr_A_apply_of_ne_zero hi]
  simp [hi]

/-- Off-diagonal nonzero coordinates of `A v_j` vanish in the witness basis. -/
@[simp] theorem vBasis_repr_A_apply_of_ne_zero_apply_other (W : RawFiniteWitness f y)
    {i j : Fin (n + 1)} (hj : j ≠ 0) (hi : i ≠ 0) (hij : i ≠ j) :
    W.vBasis.repr (W.A (W.v j)) i = 0 := by
  rw [W.vBasis_repr_A_apply_of_ne_zero hj]
  simp [hij, hi]

/-- The raw finite Hilbert space has dimension `n + 1`. -/
theorem finrank_eq (W : RawFiniteWitness f y) : Module.finrank ℂ W.H = n + 1 := by
  simpa using Module.finrank_eq_card_basis W.vBasis

/-- The distinguished vector `v 0` is not in the span of the nonzero vectors. -/
theorem v0_not_mem_span_nonzero (W : RawFiniteWitness f y) :
    W.v 0 ∉ W.nonzeroSpan := by
  simpa using (W.hLinearIndependent.notMem_span 0)

/-- Orthogonal residual of `v 0` after projecting to the nonzero-vector span. -/
noncomputable def orthResidual (W : RawFiniteWitness f y) : W.H :=
  W.v 0 - W.nonzeroSpan.starProjection (W.v 0)

/-- The orthogonal residual lies in the orthogonal complement of `nonzeroSpan`. -/
theorem orthResidual_mem_orthogonal (W : RawFiniteWitness f y) :
    W.orthResidual ∈ W.nonzeroSpanᗮ := by
  change W.v 0 - W.nonzeroSpan.starProjection (W.v 0) ∈ W.nonzeroSpanᗮ
  exact Submodule.sub_starProjection_mem_orthogonal (K := W.nonzeroSpan) (v := W.v 0)

/-- The orthogonal residual has zero inner product with every nonzero witness vector. -/
theorem orthResidual_inner_nonzero_eq_zero (W : RawFiniteWitness f y)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    inner (𝕜 := ℂ) W.orthResidual (W.v i) = 0 := by
  have hmem : W.v i ∈ W.nonzeroSpan := by
    exact Submodule.subset_span ⟨i, by simpa using hi, rfl⟩
  exact (Submodule.mem_orthogonal' W.nonzeroSpan W.orthResidual).1
    W.orthResidual_mem_orthogonal (W.v i) hmem

/-- The orthogonal residual is nonzero because `v 0` is outside `nonzeroSpan`. -/
theorem orthResidual_ne_zero (W : RawFiniteWitness f y) :
    W.orthResidual ≠ 0 := by
  intro hzero
  have hproj : W.nonzeroSpan.starProjection (W.v 0) = W.v 0 := by
    have hsub : W.v 0 - W.nonzeroSpan.starProjection (W.v 0) = 0 := by
      simpa [orthResidual] using hzero
    exact (sub_eq_zero.mp hsub).symm
  have hv0_mem : W.v 0 ∈ W.nonzeroSpan := by
    simpa [Submodule.starProjection_eq_self_iff] using hproj
  exact W.v0_not_mem_span_nonzero hv0_mem

/-- The residual pairing with `v 0` equals the residual squared norm. -/
theorem orthResidual_inner_v0_eq_inner_self (W : RawFiniteWitness f y) :
    inner (𝕜 := ℂ) W.orthResidual (W.v 0) =
      inner (𝕜 := ℂ) W.orthResidual W.orthResidual := by
  have hproj_mem : W.nonzeroSpan.starProjection (W.v 0) ∈ W.nonzeroSpan :=
    W.nonzeroSpan.starProjection_apply_mem (x := W.v 0)
  have horth :
      inner (𝕜 := ℂ) W.orthResidual (W.nonzeroSpan.starProjection (W.v 0)) = 0 :=
    (Submodule.mem_orthogonal' W.nonzeroSpan W.orthResidual).1
      W.orthResidual_mem_orthogonal
      (W.nonzeroSpan.starProjection (W.v 0)) hproj_mem
  calc
    inner (𝕜 := ℂ) W.orthResidual (W.v 0)
        = inner (𝕜 := ℂ) W.orthResidual
            (W.orthResidual + W.nonzeroSpan.starProjection (W.v 0)) := by
            simp [orthResidual, sub_add_cancel]
    _ = inner (𝕜 := ℂ) W.orthResidual W.orthResidual := by
          simp [inner_add_right, horth]

/-- The residual pairing with `v 0` is nonzero. -/
theorem orthResidual_inner_v0_ne_zero (W : RawFiniteWitness f y) :
    inner (𝕜 := ℂ) W.orthResidual (W.v 0) ≠ 0 := by
  have hself : inner (𝕜 := ℂ) W.orthResidual W.orthResidual ≠ 0 :=
    (inner_self_ne_zero (𝕜 := ℂ) (x := W.orthResidual)).2 W.orthResidual_ne_zero
  simpa [W.orthResidual_inner_v0_eq_inner_self] using hself

/-- The orthogonal residual normalized to pair to `1` with `v 0`. -/
noncomputable def normalizedOrthResidual (W : RawFiniteWitness f y) : W.H :=
  (1 / star (inner (𝕜 := ℂ) W.orthResidual (W.v 0))) • W.orthResidual

/-- The normalized residual pairs to `1` with `v 0`. -/
theorem normalizedOrthResidual_inner_v0 (W : RawFiniteWitness f y) :
    inner (𝕜 := ℂ) W.normalizedOrthResidual (W.v 0) = 1 := by
  calc
    inner (𝕜 := ℂ) W.normalizedOrthResidual (W.v 0)
        = star (1 / star (inner (𝕜 := ℂ) W.orthResidual (W.v 0))) *
            inner (𝕜 := ℂ) W.orthResidual (W.v 0) := by
            simp [normalizedOrthResidual, inner_smul_left]
    _ = (1 / inner (𝕜 := ℂ) W.orthResidual (W.v 0)) *
          inner (𝕜 := ℂ) W.orthResidual (W.v 0) := by
          simp
    _ = 1 := by
          field_simp [W.orthResidual_inner_v0_ne_zero]

/-- The normalized residual is orthogonal to every nonzero witness vector. -/
theorem normalizedOrthResidual_inner_nonzero_eq_zero (W : RawFiniteWitness f y)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    inner (𝕜 := ℂ) W.normalizedOrthResidual (W.v i) = 0 := by
  simp [normalizedOrthResidual, inner_smul_left, W.orthResidual_inner_nonzero_eq_zero hi]


private noncomputable def adjustedAAtZero (W : RawFiniteWitness f y) (β : ℝ) :
    W.H →ₗ[ℂ] W.H :=
  W.vBasis.constr ℂ fun i =>
    if i = 0 then W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual else W.A (W.v i)

private theorem adjustedAAtZero_apply_v (W : RawFiniteWitness f y) (β : ℝ)
    (i : Fin (n + 1)) :
    W.adjustedAAtZero β (W.v i) =
      if i = 0 then W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual else W.A (W.v i) := by
  simpa [adjustedAAtZero] using W.vBasis.constr_basis (S := ℂ)
    (f := fun i =>
      if i = 0 then W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual else W.A (W.v i)) i

private theorem adjustedAAtZero_apply_v_zero (W : RawFiniteWitness f y) (β : ℝ) :
    W.adjustedAAtZero β (W.v 0) =
      W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual := by
  simpa using W.adjustedAAtZero_apply_v β 0

private theorem adjustedAAtZero_apply_v_of_ne_zero (W : RawFiniteWitness f y) (β : ℝ)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    W.adjustedAAtZero β (W.v i) = W.A (W.v i) := by
  simpa [hi] using W.adjustedAAtZero_apply_v β i

private theorem adjustedAAtZero_isSymmetric (W : RawFiniteWitness f y) (β : ℝ) :
    (W.adjustedAAtZero β).IsSymmetric := by
  intro x y'
  set b := W.vBasis
  set sx : Finset (Fin (n + 1)) := Finset.univ
  set sy : Finset (Fin (n + 1)) := Finset.univ
  set fx : Fin (n + 1) → W.H := fun i => (b.repr x i) • b i
  set fy : Fin (n + 1) → W.H := fun j => (b.repr y' j) • b j
  have hsymm_basis :
      ∀ i j : Fin (n + 1),
        inner (𝕜 := ℂ) (W.adjustedAAtZero β (b i)) (b j) =
          inner (𝕜 := ℂ) (b i) (W.adjustedAAtZero β (b j)) := by
    intro i j
    rw [show b i = W.v i by simp [b], show b j = W.v j by simp [b]]
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        calc
          inner (𝕜 := ℂ) (W.adjustedAAtZero β (W.v 0)) (W.v 0)
              =
                inner (𝕜 := ℂ)
                  (W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual) (W.v 0) := by
                    rw [W.adjustedAAtZero_apply_v_zero β]
          _ =
                inner (𝕜 := ℂ) (W.A (W.v 0)) (W.v 0) + (β : ℂ) := by
                    rw [inner_add_left, inner_smul_left, W.normalizedOrthResidual_inner_v0]
                    simp
          _ =
                inner (𝕜 := ℂ) (W.v 0) (W.A (W.v 0)) + (β : ℂ) := by
                    rw [W.hA_symm]
          _ =
                inner (𝕜 := ℂ) (W.v 0)
                  (W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual) := by
                    rw [inner_add_right, inner_smul_right]
                    have hinner :
                        inner (𝕜 := ℂ) (W.v 0) W.normalizedOrthResidual = 1 := by
                      simpa [inner_conj_symm] using
                        congrArg star W.normalizedOrthResidual_inner_v0
                    simp [hinner]
          _ = inner (𝕜 := ℂ) (W.v 0) (W.adjustedAAtZero β (W.v 0)) := by
                    rw [W.adjustedAAtZero_apply_v_zero β]
      · calc
          inner (𝕜 := ℂ) (W.adjustedAAtZero β (W.v 0)) (W.v j)
              =
                inner (𝕜 := ℂ)
                  (W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual) (W.v j) := by
                    rw [W.adjustedAAtZero_apply_v_zero β]
          _ = inner (𝕜 := ℂ) (W.A (W.v 0)) (W.v j) := by
                    rw [inner_add_left, inner_smul_left,
                      W.normalizedOrthResidual_inner_nonzero_eq_zero hj]
                    simp
          _ = inner (𝕜 := ℂ) (W.v 0) (W.A (W.v j)) := by
                    rw [W.hA_symm]
          _ = inner (𝕜 := ℂ) (W.v 0) (W.adjustedAAtZero β (W.v j)) := by
                    rw [W.adjustedAAtZero_apply_v_of_ne_zero β hj]
    · by_cases hj : j = 0
      · subst hj
        have h0i :=
          congrArg star
            (show
              inner (𝕜 := ℂ) (W.adjustedAAtZero β (W.v 0)) (W.v i) =
                inner (𝕜 := ℂ) (W.v 0) (W.adjustedAAtZero β (W.v i)) by
              calc
                inner (𝕜 := ℂ) (W.adjustedAAtZero β (W.v 0)) (W.v i)
                    =
                      inner (𝕜 := ℂ)
                        (W.A (W.v 0) + (β : ℂ) • W.normalizedOrthResidual) (W.v i) := by
                          rw [W.adjustedAAtZero_apply_v_zero β]
                _ = inner (𝕜 := ℂ) (W.A (W.v 0)) (W.v i) := by
                          rw [inner_add_left, inner_smul_left,
                            W.normalizedOrthResidual_inner_nonzero_eq_zero hi]
                          simp
                _ = inner (𝕜 := ℂ) (W.v 0) (W.A (W.v i)) := by
                          rw [W.hA_symm]
                _ = inner (𝕜 := ℂ) (W.v 0) (W.adjustedAAtZero β (W.v i)) := by
                          rw [W.adjustedAAtZero_apply_v_of_ne_zero β hi])
        simpa [inner_conj_symm] using h0i.symm
      · rw [W.adjustedAAtZero_apply_v_of_ne_zero β hi,
          W.adjustedAAtZero_apply_v_of_ne_zero β hj]
        exact W.hA_symm (W.v i) (W.v j)
  have hx : x = ∑ i ∈ sx, fx i := by
    exact (b.sum_repr x).symm
  have hy : y' = ∑ j ∈ sy, fy j := by
    exact (b.sum_repr y').symm
  rw [hx, hy]
  rw [map_sum (g := W.adjustedAAtZero β) (f := fx) (s := sx)]
  rw [map_sum (g := W.adjustedAAtZero β) (f := fy) (s := sy)]
  rw [sum_inner sx (fun i => W.adjustedAAtZero β (fx i)) (∑ j ∈ sy, fy j)]
  rw [sum_inner sx fx (∑ j ∈ sy, W.adjustedAAtZero β (fy j))]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [inner_sum sy fy (W.adjustedAAtZero β (fx i))]
  rw [inner_sum sy (fun j => W.adjustedAAtZero β (fy j)) (fx i)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hL :
      inner (𝕜 := ℂ) (W.adjustedAAtZero β (fx i)) (fy j)
        =
          (starRingEnd ℂ) (b.repr x i) * (b.repr y' j) *
            inner (𝕜 := ℂ) (W.adjustedAAtZero β (b i)) (b j) := by
    dsimp [fx, fy]
    calc
      inner (𝕜 := ℂ) (W.adjustedAAtZero β ((b.repr x i) • b i)) ((b.repr y' j) • b j)
          =
            inner (𝕜 := ℂ) ((b.repr x i) • W.adjustedAAtZero β (b i))
              ((b.repr y' j) • b j) := by
                simp
      _ =
          (starRingEnd ℂ) (b.repr x i) * (b.repr y' j) *
            inner (𝕜 := ℂ) (W.adjustedAAtZero β (b i)) (b j) := by
          rw [inner_smul_left, inner_smul_right]
          ring
  have hR :
      inner (𝕜 := ℂ) (fx i) (W.adjustedAAtZero β (fy j))
        =
          (starRingEnd ℂ) (b.repr x i) * (b.repr y' j) *
            inner (𝕜 := ℂ) (b i) (W.adjustedAAtZero β (b j)) := by
    dsimp [fx, fy]
    calc
      inner (𝕜 := ℂ) ((b.repr x i) • b i)
          (W.adjustedAAtZero β ((b.repr y' j) • b j))
          =
            inner (𝕜 := ℂ) ((b.repr x i) • b i)
              ((b.repr y' j) • W.adjustedAAtZero β (b j)) := by
                simp
      _ =
          (starRingEnd ℂ) (b.repr x i) * (b.repr y' j) *
            inner (𝕜 := ℂ) (b i) (W.adjustedAAtZero β (b j)) := by
          rw [inner_smul_left, inner_smul_right]
          ring
  rw [hL, hR, hsymm_basis i j]

private noncomputable def adjustedWitnessAtZero (W : RawFiniteWitness f y) (β : ℝ) :
    RawFiniteWitness f y where
  hy := W.hy
  H := W.H
  instNormedAddCommGroup := W.instNormedAddCommGroup
  instInnerProductSpace := W.instInnerProductSpace
  instFiniteDimensional := W.instFiniteDimensional
  v := W.v
  φ := W.φ
  A := W.adjustedAAtZero β
  hGram := W.hGram
  hφ := W.hφ
  hSpanTop := W.hSpanTop
  hA := (LinearMap.isSymmetric_iff_isSelfAdjoint _).1 (W.adjustedAAtZero_isSymmetric β)
  hA_apply := by
    intro i hi
    rw [W.adjustedAAtZero_apply_v_of_ne_zero β hi]
    exact W.hA_apply i hi
  hWitness := by
    intro i hi
    rw [W.adjustedAAtZero_apply_v_of_ne_zero β hi]
    exact W.hWitness i hi
  hNormSq := W.hNormSq
  hLinearIndependent := W.hLinearIndependent

/-- The nonzero differences `v_i - v_0` are linearly independent. -/
theorem linearIndependent_vSubV0 (W : RawFiniteWitness f y) :
    LinearIndependent ℂ (fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hcoord := congrArg (fun z => W.vBasis.repr z i.1) hs
  have hcoord' : (∑ x ∈ s, if x = i then g x else 0) = 0 := by
    simpa [W.vBasis_repr_v, i.2, Finsupp.single_apply, Subtype.ext_iff] using hcoord
  rw [Finset.sum_ite_eq_of_mem' s i g hi] at hcoord'
  exact hcoord'

/-- A vector killed by `A` has the same pairing with `v_i` and `φ` for `i ≠ 0`. -/
theorem inner_eq_inner_phi_of_A_eq_zero (W : RawFiniteWitness f y) {x : W.H}
    (hx : W.A x = 0) {i : Fin (n + 1)} (hi : i ≠ 0) :
    inner (𝕜 := ℂ) x (W.v i) = inner (𝕜 := ℂ) x W.φ := by
  have hAxvi : inner (𝕜 := ℂ) x (W.A (W.v i)) = 0 := by
    rw [← W.hA_symm x (W.v i)]
    simp [hx]
  rw [W.hA_apply i hi] at hAxvi
  have hyi0 : (y i : ℂ) ≠ 0 := by
    rcases W.hy with ⟨_, _, _, hyne0⟩
    exact_mod_cast (hyne0 i hi)
  have hsub : inner (𝕜 := ℂ) x (W.v i - W.φ) = 0 := by
    have hscaled :
        (1 / (y i : ℂ)) * inner (𝕜 := ℂ) x (W.v i - W.φ) = 0 := by
      simpa [inner_smul_right] using hAxvi
    have hmul := mul_eq_zero.mp hscaled
    cases hmul with
    | inl hzero =>
        have hzero' : (y i : ℂ)⁻¹ = 0 := by
          simpa [one_div] using hzero
        exact (inv_ne_zero hyi0 hzero').elim
    | inr hzero =>
        exact hzero
  simpa [inner_sub_right, sub_eq_zero] using hsub

/-- A vector killed by `A` has constant pairing with all witness vectors. -/
theorem inner_eq_inner_v0_of_A_eq_zero (W : RawFiniteWitness f y) {x : W.H}
    (hx : W.A x = 0) (i : Fin (n + 1)) :
    inner (𝕜 := ℂ) x (W.v i) = inner (𝕜 := ℂ) x (W.v 0) := by
  by_cases hi : i = 0
  · subst hi
    rfl
  · rw [← W.hφ]
    exact W.inner_eq_inner_phi_of_A_eq_zero hx hi

/-- A vector killed by `A` is orthogonal to every difference `v_i - v_0`. -/
theorem inner_sub_eq_zero_of_A_eq_zero (W : RawFiniteWitness f y) {x : W.H}
    (hx : W.A x = 0) (i : Fin (n + 1)) :
    inner (𝕜 := ℂ) x (W.v i - W.v 0) = 0 := by
  rw [inner_sub_right, W.inner_eq_inner_v0_of_A_eq_zero hx i, sub_self]


/-- Each difference `v_i - v_0` for `i ≠ 0` lies in the range of `A`. -/
theorem vSubV0_mem_range_A_of_ne_zero (W : RawFiniteWitness f y) {i : Fin (n + 1)}
    (hi : i ≠ 0) :
    W.v i - W.v 0 ∈ LinearMap.range W.A := by
  refine ⟨(y i : ℂ) • W.v i, ?_⟩
  rw [map_smul, W.hA_apply i hi, W.hφ]
  have hyi0 : (y i : ℂ) ≠ 0 := by
    rcases W.hy with ⟨_, _, _, hyne0⟩
    exact_mod_cast (hyne0 i hi)
  calc
    (y i : ℂ) • ((1 / (y i : ℂ)) • (W.v i - W.v 0))
        = ((y i : ℂ) * (1 / (y i : ℂ))) • (W.v i - W.v 0) := by
            simp [smul_smul]
    _ = W.v i - W.v 0 := by
          simp [div_eq_mul_inv, hyi0]

/-- The span of nonzero differences is contained in the range of `A`. -/
theorem vSubV0_span_le_range_A (W : RawFiniteWitness f y) :
    Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ≤
      LinearMap.range W.A := by
  rw [Submodule.span_le]
  intro z hz
  rcases hz with ⟨i, rfl⟩
  exact W.vSubV0_mem_range_A_of_ne_zero i.2

/-- The nonzero-difference span and the line through `v 0` span all of `H`. -/
theorem span_vSubV0_sup_v0_eq_top (W : RawFiniteWitness f y) :
    Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ⊔
      (ℂ ∙ W.v 0) = ⊤ := by
  have hspan_le :
      Submodule.span ℂ (Set.range W.v) ≤
        Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ⊔
          (ℂ ∙ W.v 0) := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst hi
      refine Submodule.mem_sup.2 ?_
      exact ⟨0, by simp, W.v 0, Submodule.mem_span_singleton_self (W.v 0), by simp⟩
    · have hdiff :
          W.v i - W.v 0 ∈
            Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) :=
        Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      have hv0 : W.v 0 ∈ ℂ ∙ W.v 0 := Submodule.mem_span_singleton_self (W.v 0)
      have :
          W.v i = (W.v i - W.v 0) + W.v 0 := by
        simp
      rw [this]
      refine Submodule.mem_sup.2 ?_
      exact ⟨W.v i - W.v 0, hdiff, W.v 0, hv0, by simp⟩
  have htop_le :
      (⊤ : Submodule ℂ W.H) ≤
        Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ⊔
          (ℂ ∙ W.v 0) := by
    rw [← W.hSpanTop]
    exact hspan_le
  exact top_le_iff.mp htop_le

/-- The distinguished vector `v 0` is not in the span of nonzero differences. -/
theorem v0_not_mem_span_vSubV0 (W : RawFiniteWitness f y) :
    W.v 0 ∉
      Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  intro hv0
  let U : Submodule ℂ W.H :=
    Submodule.span ℂ (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)
  have hzero_mem : W.v 0 ∈ U := hv0
  have hnonzero_mem :
      ∀ i : { i : Fin (n + 1) // i ≠ 0 }, W.v i.1 ∈
        U := by
    intro i
    have hdiff :
        W.v i.1 - W.v 0 ∈
          U :=
      Submodule.subset_span ⟨i, rfl⟩
    have :
        W.v i.1 = (W.v i.1 - W.v 0) + W.v 0 := by
      simp
    rw [this]
    exact add_mem hdiff hzero_mem
  have hspan_v :
      Submodule.span ℂ (Set.range W.v) ≤ U := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨i, rfl⟩
    by_cases hi : i = 0
    · simpa [hi] using hzero_mem
    · exact hnonzero_mem ⟨i, hi⟩
  have htop : U = ⊤ := by
    apply top_unique
    simpa [U, W.hSpanTop] using hspan_v
  have hfin :
      Module.finrank ℂ W.H = Fintype.card { i : Fin (n + 1) // i ≠ 0 } := by
    calc
      Module.finrank ℂ W.H = Module.finrank ℂ (⊤ : Submodule ℂ W.H) := by
        symm
        exact finrank_top ℂ W.H
      _ = Module.finrank ℂ U := by rw [htop]
      _ = Fintype.card { i : Fin (n + 1) // i ≠ 0 } := by
        simpa [U] using
          (finrank_span_eq_card (R := ℂ)
            (b := fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)
            W.linearIndependent_vSubV0)
  have hcard :
      Fintype.card { i : Fin (n + 1) // i ≠ 0 } = n := by
    rw [Fintype.card_subtype_compl (fun i : Fin (n + 1) => i = 0), Fintype.card_fin,
      Fintype.card_subtype_eq (0 : Fin (n + 1))]
    simp
  have : n + 1 = n := by
    rw [← W.finrank_eq, hfin, hcard]
  exact Nat.succ_ne_self n this

/-- Successor-indexed differences span the same subspace as all nonzero differences. -/
theorem span_succ_vSubV0_eq_span_vSubV0 (W : RawFiniteWitness f y) :
    Submodule.span ℂ (Set.range fun j : Fin n => W.v j.succ - W.v 0) =
      Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨j.succ, by simp⟩, rfl⟩
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rcases i with ⟨i, hi⟩
    have hi_pos : 0 < i.1 := Fin.pos_iff_ne_zero.mpr hi
    let j : Fin n := ⟨i.1 - 1, by omega⟩
    have hj : j.succ = i := by
      apply Fin.ext
      exact Nat.succ_pred_eq_of_pos hi_pos
    simpa [hj] using
      (Submodule.subset_span
        (s := Set.range fun j : Fin n => W.v j.succ - W.v 0) ⟨j, rfl⟩ :
          W.v j.succ - W.v 0 ∈
            Submodule.span ℂ (Set.range fun j : Fin n => W.v j.succ - W.v 0))

/-- The basis with first vector `v 0` and tail `v_{j.succ} - v_0` is independent. -/
theorem linearIndependent_v0_cons_vSubV0 (W : RawFiniteWitness f y) :
    LinearIndependent ℂ
      (Fin.cons (W.v 0) (fun j : Fin n => W.v j.succ - W.v 0) : Fin (n + 1) → W.H) := by
  have hli_tail :
      LinearIndependent ℂ (fun j : Fin n => W.v j.succ - W.v 0) := by
    refine W.linearIndependent_vSubV0.comp
      (fun j : Fin n => ⟨j.succ, by simp⟩) ?_
    intro i j hij
    simpa using congrArg Subtype.val hij
  refine hli_tail.fin_cons ?_
  rw [W.span_succ_vSubV0_eq_span_vSubV0]
  exact W.v0_not_mem_span_vSubV0

/-- The `v 0` plus nonzero-difference family spans the raw finite Hilbert space. -/
theorem span_v0_cons_vSubV0_eq_top (W : RawFiniteWitness f y) :
    Submodule.span ℂ
      (Set.range
        (Fin.cons (W.v 0) (fun j : Fin n => W.v j.succ - W.v 0) :
          Fin (n + 1) → W.H)) = ⊤ := by
  apply top_unique
  rw [← W.span_vSubV0_sup_v0_eq_top]
  apply sup_le
  · rw [← W.span_succ_vSubV0_eq_span_vSubV0, Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j.succ, by simp⟩
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Submodule.subset_span ⟨0, by simp⟩

/-- Basis whose first vector is `v 0` and whose tail is `v_i - v_0`. -/
noncomputable def v0SubBasis (W : RawFiniteWitness f y) :
    Module.Basis (Fin (n + 1)) ℂ W.H :=
  Module.Basis.mk W.linearIndependent_v0_cons_vSubV0 <| by
    rw [W.span_v0_cons_vSubV0_eq_top]

/-- The zero entry of `v0SubBasis` is `v 0`. -/
@[simp] theorem v0SubBasis_apply_zero (W : RawFiniteWitness f y) :
    W.v0SubBasis 0 = W.v 0 := by
  simp [v0SubBasis, Module.Basis.mk_apply]

/-- Successor entries of `v0SubBasis` are the differences `v_{j.succ} - v_0`. -/
@[simp] theorem v0SubBasis_apply_succ (W : RawFiniteWitness f y) (j : Fin n) :
    W.v0SubBasis j.succ = W.v j.succ - W.v 0 := by
  simp [v0SubBasis, Module.Basis.mk_apply]

/--
Every nonzero entry of `v0SubBasis` is the corresponding difference
`v_i - v_0`.
-/
@[simp] theorem v0SubBasis_apply_ne_zero (W : RawFiniteWitness f y) {i : Fin (n + 1)}
    (hi : i ≠ 0) :
    W.v0SubBasis i = W.v i - W.v 0 := by
  rcases Fin.exists_succ_eq_of_ne_zero hi with ⟨j, rfl⟩
  simp

/-- The coordinate vector of `v 0` in `v0SubBasis` is the zeroth unit vector. -/
@[simp] theorem v0SubBasis_repr_v0 (W : RawFiniteWitness f y) :
    W.v0SubBasis.repr (W.v 0) = Finsupp.single 0 (1 : ℂ) := by
  rw [← W.v0SubBasis_apply_zero]
  exact W.v0SubBasis.repr_self 0

/-- The coordinate vector of `v_{j.succ} - v_0` is the successor unit vector. -/
@[simp] theorem v0SubBasis_repr_vSubV0 (W : RawFiniteWitness f y) (j : Fin n) :
    W.v0SubBasis.repr (W.v j.succ - W.v 0) = Finsupp.single j.succ (1 : ℂ) := by
  rw [← W.v0SubBasis_apply_succ j]
  exact W.v0SubBasis.repr_self j.succ

/-- Every witness vector has zeroth coordinate `1` in `v0SubBasis`. -/
@[simp] theorem v0SubBasis_repr_v_apply_zero (W : RawFiniteWitness f y)
    (i : Fin (n + 1)) :
    W.v0SubBasis.repr (W.v i) 0 = 1 := by
  by_cases hi : i = 0
  · subst hi
    simp
  · rcases Fin.exists_succ_eq_of_ne_zero hi with ⟨j, rfl⟩
    calc
      W.v0SubBasis.repr (W.v j.succ) 0
          = W.v0SubBasis.repr ((W.v j.succ - W.v 0) + W.v 0) 0 := by
              rw [sub_add_cancel]
      _ = W.v0SubBasis.repr (W.v j.succ - W.v 0) 0 +
            W.v0SubBasis.repr (W.v 0) 0 := by
              rw [map_add]
              rfl
      _ = 1 := by
              simp [Fin.succ_ne_zero]

/-- The zeroth `v0SubBasis` coordinate is the sum of witness-basis coordinates. -/
theorem v0SubBasis_repr_zero_eq_sum_vBasis_repr (W : RawFiniteWitness f y)
    (x : W.H) :
    W.v0SubBasis.repr x 0 = ∑ i : Fin (n + 1), W.vBasis.repr x i := by
  calc
    W.v0SubBasis.repr x 0
        = W.v0SubBasis.repr
            (∑ i : Fin (n + 1), (W.vBasis.repr x i) • W.vBasis i) 0 := by
            rw [W.vBasis.sum_repr x]
    _ = ∑ i : Fin (n + 1), W.vBasis.repr x i := by
            simp

/-- The normalized residual's slope coordinate is the sum of its witness coordinates. -/
theorem slopeCoord_eq_sum_vBasis_repr_normalizedOrthResidual
    (W : RawFiniteWitness f y) :
    W.v0SubBasis.repr W.normalizedOrthResidual 0 =
      ∑ i : Fin (n + 1), W.vBasis.repr W.normalizedOrthResidual i :=
  W.v0SubBasis_repr_zero_eq_sum_vBasis_repr W.normalizedOrthResidual

/-- Normal equations for the witness-basis coordinates of the normalized residual. -/
theorem vBasis_repr_normalizedOrthResidual_normal_equations
    (W : RawFiniteWitness f y) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1),
        star (W.vBasis.repr W.normalizedOrthResidual i) *
          inner (𝕜 := ℂ) (W.v i) (W.v j)) =
      if j = 0 then 1 else 0 := by
  have hsum :=
    congrArg (fun z => inner (𝕜 := ℂ) z (W.v j))
      (W.vBasis.sum_repr W.normalizedOrthResidual)
  have hinner :
      (∑ i : Fin (n + 1),
          star (W.vBasis.repr W.normalizedOrthResidual i) *
            inner (𝕜 := ℂ) (W.v i) (W.v j)) =
        inner (𝕜 := ℂ) W.normalizedOrthResidual (W.v j) := by
    have hleft :
        inner (𝕜 := ℂ)
            (∑ i : Fin (n + 1),
              (W.vBasis.repr W.normalizedOrthResidual i) • W.v i) (W.v j) =
          ∑ i : Fin (n + 1),
            star (W.vBasis.repr W.normalizedOrthResidual i) *
              inner (𝕜 := ℂ) (W.v i) (W.v j) := by
      simp [sum_inner, inner_smul_left]
    exact hleft.symm.trans (by simpa [W.vBasis_apply] using hsum)
  rw [hinner]
  by_cases hj : j = 0
  · subst hj
    simpa using W.normalizedOrthResidual_inner_v0
  · simpa [hj] using W.normalizedOrthResidual_inner_nonzero_eq_zero hj

/-- Coordinates of `A v_{j.succ}` in the `v0SubBasis` basis. -/
@[simp] theorem v0SubBasis_repr_A_apply_succ (W : RawFiniteWitness f y) (j : Fin n) :
    W.v0SubBasis.repr (W.A (W.v j.succ)) =
      Finsupp.single j.succ (1 / (y j.succ : ℂ)) := by
  have hj : (j.succ : Fin (n + 1)) ≠ 0 := by simp
  rw [W.hA_apply j.succ hj, W.hφ]
  simp

/-- The zeroth `v0SubBasis` coordinate of `A v_{j.succ}` is zero. -/
@[simp] theorem v0SubBasis_repr_A_apply_succ_zero (W : RawFiniteWitness f y) (j : Fin n) :
    W.v0SubBasis.repr (W.A (W.v j.succ)) 0 = 0 := by
  simp

/-- The successor self-coordinate of `A v_{j.succ}` is `1 / y_{j.succ}`. -/
@[simp] theorem v0SubBasis_repr_A_apply_succ_self (W : RawFiniteWitness f y) (j : Fin n) :
    W.v0SubBasis.repr (W.A (W.v j.succ)) j.succ = 1 / (y j.succ : ℂ) := by
  simp

/-- Zero zeroth coordinate in `v0SubBasis` implies membership in the difference span. -/
theorem mem_span_vSubV0_of_v0SubBasis_repr_zero_eq_zero (W : RawFiniteWitness f y)
    {x : W.H} (hx0 : W.v0SubBasis.repr x 0 = 0) :
    x ∈ Submodule.span ℂ
      (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  let S : Set (Fin (n + 1)) := {i | i ≠ 0}
  have hx_tail : x ∈ Submodule.span ℂ (W.v0SubBasis '' S) := by
    rw [W.v0SubBasis.mem_span_image]
    intro i hi hi0
    subst hi0
    exact (Finsupp.mem_support_iff.mp hi) hx0
  have hle :
      Submodule.span ℂ (W.v0SubBasis '' S) ≤
        Submodule.span ℂ
          (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨i, hi, rfl⟩
    have hi' : i ≠ 0 := by simpa [S] using hi
    rw [W.v0SubBasis_apply_ne_zero hi']
    exact Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩
  exact hle hx_tail

/-- Membership in the difference span forces zeroth `v0SubBasis` coordinate zero. -/
theorem v0SubBasis_repr_zero_eq_zero_of_mem_span_vSubV0 (W : RawFiniteWitness f y)
    {x : W.H}
    (hx :
      x ∈ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    W.v0SubBasis.repr x 0 = 0 := by
  refine Submodule.span_induction (R := ℂ)
    (p := fun x _ => W.v0SubBasis.repr x 0 = 0)
    ?mem ?zero ?add ?smul hx
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    have hrepr :
        W.v0SubBasis.repr (W.v i.1 - W.v 0) = Finsupp.single i.1 (1 : ℂ) := by
      rw [← W.v0SubBasis_apply_ne_zero i.2]
      exact W.v0SubBasis.repr_self i.1
    simp [hrepr, i.2]
  · simp
  · intro x₁ x₂ _ _ hx₁ hx₂
    simp [map_add, hx₁, hx₂]
  · intro a x _ hx
    simp [map_smul, hx]

/-- The difference span is exactly the kernel of the zeroth `v0SubBasis` coordinate. -/
theorem mem_span_vSubV0_iff_v0SubBasis_repr_zero_eq_zero (W : RawFiniteWitness f y)
    {x : W.H} :
    x ∈ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ↔
      W.v0SubBasis.repr x 0 = 0 :=
  ⟨W.v0SubBasis_repr_zero_eq_zero_of_mem_span_vSubV0,
    W.mem_span_vSubV0_of_v0SubBasis_repr_zero_eq_zero⟩

private theorem adjustedAAtZero_v0SubBasis_coord (W : RawFiniteWitness f y) (β : ℝ) :
    W.v0SubBasis.repr (W.adjustedAAtZero β (W.v 0)) 0 =
      W.v0SubBasis.repr (W.A (W.v 0)) 0 +
        (β : ℂ) * W.v0SubBasis.repr W.normalizedOrthResidual 0 := by
  rw [W.adjustedAAtZero_apply_v_zero β]
  rw [map_add, map_smul]
  rfl

private theorem adjustedAAtZero_not_mem_vSubV0_of_coord (W : RawFiniteWitness f y) (β : ℝ)
    (hcoord : W.v0SubBasis.repr (W.adjustedAAtZero β (W.v 0)) 0 ≠ 0) :
    W.adjustedAAtZero β (W.v 0) ∉
      Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  rw [W.mem_span_vSubV0_iff_v0SubBasis_repr_zero_eq_zero]
  exact hcoord

private theorem exists_beta_adjustedAAtZero_coord_ne_zero_of_slope
    (W : RawFiniteWitness f y)
    (hslope : W.v0SubBasis.repr W.normalizedOrthResidual 0 ≠ 0) :
    ∃ β : ℝ, W.v0SubBasis.repr (W.adjustedAAtZero β (W.v 0)) 0 ≠ 0 := by
  by_cases h0 : W.v0SubBasis.repr (W.A (W.v 0)) 0 = 0
  · refine ⟨1, ?_⟩
    rw [W.adjustedAAtZero_v0SubBasis_coord, h0]
    simpa using hslope
  · exact ⟨0, by simpa [W.adjustedAAtZero_v0SubBasis_coord] using h0⟩

private theorem exists_adjustedAAtZero_not_mem_vSubV0_of_slope
    (W : RawFiniteWitness f y)
    (hslope : W.v0SubBasis.repr W.normalizedOrthResidual 0 ≠ 0) :
    ∃ β : ℝ,
      W.adjustedAAtZero β (W.v 0) ∉
        Submodule.span ℂ
          (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  rcases W.exists_beta_adjustedAAtZero_coord_ne_zero_of_slope hslope with ⟨β, hβ⟩
  exact ⟨β, W.adjustedAAtZero_not_mem_vSubV0_of_coord β hβ⟩

/--
If the orthogonal residual has nonzero `v₀`-coordinate, adjust the free value
of `A v₀` to obtain a raw witness whose `A v₀` has nonzero `v₀`-coordinate.

This is a conditional constructor: it does not claim that the slope condition
follows from Loewner positivity.
-/
theorem exists_adjustedWitnessAtZero_v0_coord_ne_of_slope
    (W : RawFiniteWitness f y)
    (hslope : W.v0SubBasis.repr W.normalizedOrthResidual 0 ≠ 0) :
    ∃ W' : RawFiniteWitness f y,
      W'.v0SubBasis.repr (W'.A (W'.v 0)) 0 ≠ 0 := by
  rcases W.exists_beta_adjustedAAtZero_coord_ne_zero_of_slope hslope with ⟨β, hβ⟩
  refine ⟨W.adjustedWitnessAtZero β, ?_⟩
  simpa [adjustedWitnessAtZero] using hβ

/-- Nonmembership of `A v_0` in the difference span gives nonzero zeroth coordinate. -/
theorem v0SubBasis_repr_A_v0_zero_ne_of_not_mem_vSubV0 (W : RawFiniteWitness f y)
    (hA0 :
      W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    W.v0SubBasis.repr (W.A (W.v 0)) 0 ≠ 0 := by
  intro hzero
  exact hA0 (W.mem_span_vSubV0_of_v0SubBasis_repr_zero_eq_zero hzero)

/-- `A v_0` is outside the difference span iff its zeroth coordinate is nonzero. -/
theorem A_v0_not_mem_span_vSubV0_iff (W : RawFiniteWitness f y) :
    W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) ↔
      W.v0SubBasis.repr (W.A (W.v 0)) 0 ≠ 0 := by
  rw [not_iff_not]
  exact W.mem_span_vSubV0_iff_v0SubBasis_repr_zero_eq_zero

/-- Removing the zeroth coordinate from `A v_0` leaves a vector in the difference span. -/
theorem A_v0_sub_coord0_smul_v0_mem_span_vSubV0 (W : RawFiniteWitness f y) :
    W.A (W.v 0) - W.v0SubBasis.repr (W.A (W.v 0)) 0 • W.v 0 ∈
      Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
  apply W.mem_span_vSubV0_of_v0SubBasis_repr_zero_eq_zero
  simp

/-- If `A v_0` is not in the difference span, then `v 0` is in the range of `A`. -/
theorem v0_mem_range_A_of_not_mem_vSubV0 (W : RawFiniteWitness f y)
    (hA0 :
      W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    W.v 0 ∈ LinearMap.range W.A := by
  let q : ℂ := W.v0SubBasis.repr (W.A (W.v 0)) 0
  have hq : q ≠ 0 := W.v0SubBasis_repr_A_v0_zero_ne_of_not_mem_vSubV0 hA0
  have htail :
      W.A (W.v 0) - q • W.v 0 ∈
        Submodule.span ℂ
          (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0) := by
    simpa [q] using W.A_v0_sub_coord0_smul_v0_mem_span_vSubV0
  have htail_range : W.A (W.v 0) - q • W.v 0 ∈ LinearMap.range W.A :=
    W.vSubV0_span_le_range_A htail
  have hAv0_range : W.A (W.v 0) ∈ LinearMap.range W.A := ⟨W.v 0, rfl⟩
  have hqv0_range : q • W.v 0 ∈ LinearMap.range W.A := by
    have hsub : W.A (W.v 0) - (W.A (W.v 0) - q • W.v 0) = q • W.v 0 := by
      simp
    rw [← hsub]
    exact Submodule.sub_mem _ hAv0_range htail_range
  have hinv : q⁻¹ • q • W.v 0 ∈ LinearMap.range W.A :=
    Submodule.smul_mem _ q⁻¹ hqv0_range
  simpa [smul_smul, hq] using hinv

/-- The same nondegeneracy condition makes the range of `A` all of `H`. -/
theorem range_A_eq_top_of_not_mem_vSubV0 (W : RawFiniteWitness f y)
    (hA0 :
      W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    LinearMap.range W.A = ⊤ := by
  apply top_unique
  rw [← W.span_vSubV0_sup_v0_eq_top]
  apply sup_le
  · exact W.vSubV0_span_le_range_A
  · rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact W.v0_mem_range_A_of_not_mem_vSubV0 hA0

/-- The same nondegeneracy condition makes `A` surjective. -/
theorem A_surjective_of_not_mem_vSubV0 (W : RawFiniteWitness f y)
    (hA0 :
      W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    Function.Surjective W.A :=
  LinearMap.range_eq_top.1 (W.range_A_eq_top_of_not_mem_vSubV0 hA0)

/-- In finite dimension, the same nondegeneracy condition makes `A` bijective. -/
theorem A_bijective_of_not_mem_vSubV0 (W : RawFiniteWitness f y)
    (hA0 :
      W.A (W.v 0) ∉ Submodule.span ℂ
        (Set.range fun i : { i : Fin (n + 1) // i ≠ 0 } => W.v i.1 - W.v 0)) :
    Function.Bijective W.A :=
  ⟨LinearMap.injective_iff_surjective.2 (W.A_surjective_of_not_mem_vSubV0 hA0),
    W.A_surjective_of_not_mem_vSubV0 hA0⟩

/-- The witness vectors viewed inside their own span. -/
noncomputable def vInSpan (W : RawFiniteWitness f y) :
    Fin (n + 1) → Submodule.span ℂ (Set.range W.v) :=
  fun i => ⟨W.v i, Submodule.subset_span (Set.mem_range_self i)⟩

/-- The basis of the span of witness vectors induced by the witness family. -/
noncomputable def vSpanBasis (W : RawFiniteWitness f y) :
    Module.Basis (Fin (n + 1)) ℂ (Submodule.span ℂ (Set.range W.v)) :=
  Module.Basis.mk (linearIndependent_span W.hLinearIndependent) <| by
    intro x _
    have h₁ :
        (((↑) : Submodule.span ℂ (Set.range W.v) → W.H) '' Set.range W.vInSpan) =
          Set.range W.v := by
      ext z
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨W.vInSpan i, ⟨i, rfl⟩, rfl⟩
    have h₂ :
        Submodule.map (Submodule.subtype (Submodule.span ℂ (Set.range W.v)))
            (Submodule.span ℂ (Set.range W.vInSpan)) =
          Submodule.span ℂ (Set.range W.v) := by
      rw [← Submodule.span_image]
      simp [h₁]
    have h₃ :
        ((x : Submodule.span ℂ (Set.range W.v)) : W.H) ∈
          Submodule.map (Submodule.subtype (Submodule.span ℂ (Set.range W.v)))
            (Submodule.span ℂ (Set.range W.vInSpan)) := by
      rw [h₂]
      exact x.property
    rcases Submodule.mem_map.1 h₃ with ⟨z, hz, hzx⟩
    have h_x_eq_z : x = z := by
      rw [Subtype.ext_iff, ← hzx]
      simp
    rwa [h_x_eq_z]

/-- Coercing the span basis vector back to `H` recovers the witness vector. -/
@[simp] theorem vSpanBasis_apply (W : RawFiniteWitness f y) (i : Fin (n + 1)) :
    ((W.vSpanBasis i : Submodule.span ℂ (Set.range W.v)) : W.H) = W.v i := by
  simp [vSpanBasis, Module.Basis.mk_apply]

/-- Coordinates of `vInSpan i` in the span basis are the `i`-th unit vector. -/
@[simp] theorem vSpanBasis_repr_vInSpan (W : RawFiniteWitness f y) (i : Fin (n + 1)) :
    W.vSpanBasis.repr (W.vInSpan i) = Finsupp.single i (1 : ℂ) := by
  have hvi : W.vInSpan i = W.vSpanBasis i := by
    ext
    simp [vInSpan, vSpanBasis_apply]
  rw [hvi]
  exact W.vSpanBasis.repr_self i

/-- The inverse linear map `A⁻¹` obtained from bijectivity of `A`. -/
noncomputable def Ainv (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) :
    W.H →ₗ[ℂ] W.H :=
  (LinearEquiv.ofBijective W.A hA_bij).symm.toLinearMap

/-- The inverse map sends `A x` back to `x`. -/
theorem Ainv_apply_A (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) (x : W.H) :
    W.Ainv hA_bij (W.A x) = x := by
  simp [Ainv]


/-- The inverse of the self-adjoint bijective raw operator is self-adjoint. -/
theorem Ainv_isSelfAdjoint (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) :
    IsSelfAdjoint (W.Ainv hA_bij) := by
  let T : W.H →ₗ[ℂ] W.H := W.Ainv hA_bij
  have hT : T.IsSymmetric := by
    intro x y
    rcases hA_bij.2 x with ⟨x', rfl⟩
    rcases hA_bij.2 y with ⟨y', rfl⟩
    calc
      inner (𝕜 := ℂ) (T (W.A x')) (W.A y') = inner (𝕜 := ℂ) x' (W.A y') := by
        simpa [T] using congrArg (fun z => inner (𝕜 := ℂ) z (W.A y')) (W.Ainv_apply_A hA_bij x')
      _ = inner (𝕜 := ℂ) (W.A x') y' := by
        simpa using (W.hA_symm x' y').symm
      _ = inner (𝕜 := ℂ) (W.A x') (T (W.A y')) := by
        simpa [T] using
          congrArg (fun z => inner (𝕜 := ℂ) (W.A x') z) (W.Ainv_apply_A hA_bij y').symm
  exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).1 hT

/-- A bijective raw operator gives the transformed resolvent witness equation. -/
theorem transformed_witness_of_bijective
    (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) :
    let T := W.Ainv hA_bij
    let ψ := T W.φ
    ∀ i, (T - (y i : ℂ) • (LinearMap.id : W.H →ₗ[ℂ] W.H)) (W.v i) = ψ := by
  intro T ψ i
  by_cases hi : i = 0
  · subst hi
    calc
      (T - (y 0 : ℂ) • (LinearMap.id : W.H →ₗ[ℂ] W.H)) (W.v 0)
          = T (W.v 0) := by
              simp [W.hy.1]
      _ = ψ := by simp [ψ, W.hφ]
  · have hbase := W.hWitness i hi
    have hbase' := congrArg T hbase
    calc
      (T - (y i : ℂ) • (LinearMap.id : W.H →ₗ[ℂ] W.H)) (W.v i)
          = T (W.v i) - (y i : ℂ) • W.v i := by
              simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      _ = T (W.φ) := by
            have hTAV : T (W.A (W.v i)) = W.v i := W.Ainv_apply_A hA_bij (W.v i)
            have hT_smul : T ((y i : ℂ) • W.A (W.v i)) = (y i : ℂ) • W.v i := by
              rw [T.map_smul, hTAV]
            have hbase'' :
                T (W.v i) - T ((y i : ℂ) • W.A (W.v i)) = T W.φ := by
              simpa [RCLike.real_smul_eq_coe_smul, LinearMap.map_sub] using hbase'
            rw [← hT_smul]
            exact hbase''
      _ = ψ := rfl

/-- The transformed witness gives the inverse-square integral bound by `‖v_i‖²`. -/
theorem lintegral_sqInvDist_diracMeasure_le_of_transformed_witness
    (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) (i : Fin (n + 1)) :
    let T := W.Ainv hA_bij
    let ψ := T W.φ
    let hT : T.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 (W.Ainv_isSelfAdjoint hA_bij)
    (∫⁻ t, sqInvDist (y i) t
        ∂(Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric (T := T) (hT := hT) ψ)) ≤
      ENNReal.ofReal (‖W.v i‖ ^ 2) := by
  intro T ψ hT
  exact
    Quantum.TraceInequality.Loewner.lintegral_sqInvDist_diracMeasure_le_of_solution
      (T := T) (hT := hT) (φ := ψ) (δ := W.v i) (x0 := y i)
      (transformed_witness_of_bijective W hA_bij i)

/-- The transformed witness gives the inverse-square bound by `deriv f (y_i)`. -/
theorem lintegral_sqInvDist_diracMeasure_le_of_transformed_witness_deriv
    (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) (i : Fin (n + 1)) :
    let T := W.Ainv hA_bij
    let ψ := T W.φ
    let hT : T.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 (W.Ainv_isSelfAdjoint hA_bij)
    (∫⁻ t, sqInvDist (y i) t
        ∂(Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric (T := T) (hT := hT) ψ)) ≤
      ENNReal.ofReal (deriv f (y i)) := by
  intro T ψ hT
  have hsq :
      ‖W.v i‖ ^ 2 = deriv f (y i) := by
    simp [W.hNormSq i, loewnerKernel]
  simpa [hsq] using
    (lintegral_sqInvDist_diracMeasure_le_of_transformed_witness W hA_bij i)


example (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) (i : Fin (n + 1)) :
    let T := W.Ainv hA_bij
    let ψ := T W.φ
    (T - (y i : ℂ) • (LinearMap.id : W.H →ₗ[ℂ] W.H)) (W.v i) = ψ :=
  transformed_witness_of_bijective W hA_bij i

example (W : RawFiniteWitness f y) (hA_bij : Function.Bijective W.A) (i : Fin (n + 1)) :
    let T := W.Ainv hA_bij
    let ψ := T W.φ
    let hT : T.IsSymmetric :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 (W.Ainv_isSelfAdjoint hA_bij)
    (∫⁻ t, sqInvDist (y i) t
        ∂(Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric (T := T) (hT := hT) ψ)) ≤
      ENNReal.ofReal (deriv f (y i)) :=
  lintegral_sqInvDist_diracMeasure_le_of_transformed_witness_deriv W hA_bij i

end RawFiniteWitness

end

end Loewner
end TraceInequality
end Quantum
