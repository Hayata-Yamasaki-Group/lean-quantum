import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HermiteApproximationCore

/-!
# Chapter 3 Hermite approximation input packages

This file packages Gershgorin cluster control and the high-level Hermite
polynomial approximation interfaces used to close raw entrywise CFC variation.
The finite-node Hermite basis and remainder estimates are in
`HermiteApproximationCore`.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/-- Gershgorin radius for the rank-one perturbation row at node `k`. -/
noncomputable def rankOneGershgorinRadius
    {n : ℕ} (u : Fin n → ℂ) (k : Fin n) : ℝ :=
  ‖u k‖ ^ 2 + ∑ l ∈ Finset.univ.erase k, ‖u k‖ * ‖u l‖

/-- Each rank-one Gershgorin row radius is nonnegative. -/
lemma rankOneGershgorinRadius_nonneg
    {n : ℕ} (u : Fin n → ℂ) (k : Fin n) :
    0 ≤ rankOneGershgorinRadius u k := by
  unfold rankOneGershgorinRadius
  positivity

/-- A single positive bound for all row radii in the rank-one Gershgorin estimate. -/
noncomputable def rankOneGershgorinTotalRadius
    {n : ℕ} (u : Fin n → ℂ) : ℝ :=
  1 + ∑ k : Fin n, rankOneGershgorinRadius u k

/-- The aggregate Gershgorin radius bound is strictly positive. -/
lemma rankOneGershgorinTotalRadius_pos
    {n : ℕ} (u : Fin n → ℂ) :
    0 < rankOneGershgorinTotalRadius u := by
  unfold rankOneGershgorinTotalRadius
  have hsum : 0 ≤ ∑ k : Fin n, rankOneGershgorinRadius u k := by
    exact Finset.sum_nonneg fun k _ => rankOneGershgorinRadius_nonneg u k
  linarith

/-- Every row Gershgorin radius is bounded by the aggregate radius. -/
lemma rankOneGershgorinRadius_le_total
    {n : ℕ} (u : Fin n → ℂ) (k : Fin n) :
    rankOneGershgorinRadius u k ≤
      rankOneGershgorinTotalRadius u := by
  unfold rankOneGershgorinTotalRadius
  have hsingle :
      rankOneGershgorinRadius u k ≤
        ∑ l : Fin n, rankOneGershgorinRadius u l :=
    Finset.single_le_sum
      (fun l _ => rankOneGershgorinRadius_nonneg u l)
      (Finset.mem_univ k)
  linarith

/--
Gershgorin gives the quantitative cluster estimate for the real spectrum of
the diagonal rank-one perturbation: every spectral point is within `O(ε)` of
one interpolation node.  This is the finite-dimensional spectral input needed
by the Hermite remainder norm bridge.
-/
lemma cStarDiagonalPerturbation_spectrum_gershgorin_cluster
    {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ) (ε : ℝ)
    {y : ℝ}
    (hy : y ∈ spectrum ℝ (cStarDiagonalPerturbation x u ε)) :
    ∃ k : Fin n,
      ‖y - x k‖ ≤ ‖ε‖ * rankOneGershgorinRadius u k := by
  classical
  let A : Matrix (Fin n) (Fin n) ℂ := diagonalPerturbation x u ε
  have hyC : (y : ℂ) ∈ spectrum ℂ A := by
    have hy' := hy
    rw [← spectrum.preimage_algebraMap ℂ] at hy'
    simp only [Set.mem_preimage] at hy'
    rw [cStarDiagonalPerturbation] at hy'
    change (algebraMap ℝ ℂ) y ∈ spectrum ℂ A at hy'
    simpa [A] using hy'
  have hEigen :
      Module.End.HasEigenvalue (Matrix.toLin' A) (y : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa [Matrix.spectrum_toLin'] using hyC
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (A := A) hEigen
  have hsum :
      (∑ l ∈ Finset.univ.erase k, ‖A k l‖) =
        ‖ε‖ * ∑ l ∈ Finset.univ.erase k, ‖u k‖ * ‖u l‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l hl
    have hlne : l ≠ k := (Finset.mem_erase.mp hl).1
    have hkne : k ≠ l := fun h => hlne h.symm
    simp [A, diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, Matrix.vecMulVec, hkne]
  have hball :
      ‖(y : ℂ) - A k k‖ ≤
        ‖ε‖ * ∑ l ∈ Finset.univ.erase k, ‖u k‖ * ‖u l‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    simpa [hsum, norm_sub_rev] using hk
  have hdiag :
      A k k = (x k : ℂ) + (ε : ℂ) * u k * star (u k) := by
    simp [A, diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, Matrix.vecMulVec]
    ring_nf
  have hdiag_norm :
      ‖A k k - (x k : ℂ)‖ = ‖ε‖ * ‖u k‖ ^ 2 := by
    rw [hdiag]
    have hmul :
        (x k : ℂ) + (ε : ℂ) * u k * star (u k) - (x k : ℂ) =
          (ε : ℂ) * u k * star (u k) := by ring
    rw [hmul, norm_mul, norm_mul, norm_star]
    rw [Complex.norm_real]
    ring_nf
  refine ⟨k, ?_⟩
  have htri :
      ‖(y : ℂ) - (x k : ℂ)‖ ≤
        ‖(y : ℂ) - A k k‖ + ‖A k k - (x k : ℂ)‖ := by
    calc
      ‖(y : ℂ) - (x k : ℂ)‖ =
          ‖((y : ℂ) - A k k) + (A k k - (x k : ℂ))‖ := by ring_nf
      _ ≤ ‖(y : ℂ) - A k k‖ + ‖A k k - (x k : ℂ)‖ := norm_add_le _ _
  have hcomplex :
      ‖(y : ℂ) - (x k : ℂ)‖ ≤
        ‖ε‖ * rankOneGershgorinRadius u k := by
    calc
      ‖(y : ℂ) - (x k : ℂ)‖
          ≤ ‖(y : ℂ) - A k k‖ + ‖A k k - (x k : ℂ)‖ := htri
      _ ≤ ‖ε‖ * ∑ l ∈ Finset.univ.erase k, ‖u k‖ * ‖u l‖ +
            ‖ε‖ * ‖u k‖ ^ 2 := add_le_add hball (le_of_eq hdiag_norm)
      _ = ‖ε‖ * rankOneGershgorinRadius u k := by
        rw [rankOneGershgorinRadius]
        ring
  simpa [← Complex.ofReal_sub] using hcomplex

/-- The scalar Hermite remainder is continuous on the open unit interval. -/
lemma hermiteRemainderFunction_continuousOn_Ioo
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (hermiteRemainderFunction f x) (Set.Ioo (-1 : ℝ) 1) := by
  unfold hermiteRemainderFunction
  exact hf.continuousOn.sub
    (hermiteInterpolatingPolynomial f x).continuous.continuousOn

/-- The normalized scalar Hermite remainder is continuous on the open unit interval. -/
lemma hermiteNormalizedRemainderFunction_continuousOn_Ioo
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (Set.Ioo (-1 : ℝ) 1) := by
  unfold hermiteNormalizedRemainderFunction
  exact (hermiteRemainderFunction_continuousOn_Ioo
    (f := f) (x := x) hf).sub continuousOn_const

/--
Scalar spectrum-bound input for the Hermite remainder after the Gershgorin
cluster estimate.  This is the exact bound needed by the `CStarMatrix` norm
bridge.
-/
structure DiagonalCFCHermiteRemainderSpectrumBoundInput
    (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  cstar_remainder_spectrum_bound :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ η : ℝ, 0 < η →
              ∀ᶠ ε in 𝓝[>] (0 : ℝ),
                ∀ y ∈ spectrum ℝ (cStarDiagonalPerturbation x u ε),
                  ‖hermiteRemainderFunction f x y‖ ≤ η * ε

/--
The Gershgorin cluster estimate and the nodewise little-o Hermite remainder
bound give the scalar spectrum bound needed by the CStar quotient bridge.
-/
def diagonalCFCHermiteRemainderSpectrumBoundInput_of_differentiable
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) :
    DiagonalCFCHermiteRemainderSpectrumBoundInput f where
  differentiable := hf
  cstar_remainder_spectrum_bound := by
    intro n x hx hinj u η hη
    let R : ℝ := rankOneGershgorinTotalRadius u
    have hRpos : 0 < R := rankOneGershgorinTotalRadius_pos u
    let α : ℝ := η / R
    have hαpos : 0 < α := div_pos hη hRpos
    have hlocal :
        ∀ k : Fin n, ∃ ρ : ℝ, 0 < ρ ∧
          ∀ ⦃t : ℝ⦄, dist t (x k) < ρ →
            ‖hermiteRemainderFunction f x t‖ ≤ α * ‖t - x k‖ := by
      intro k
      exact Metric.eventually_nhds_iff.mp
        (hermiteRemainderFunction_eventually_norm_le_mul_node
          (f := f) (x := x) hf hx hinj k hαpos)
    choose ρ hρpos hρ using hlocal
    have hsmall :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k : Fin n, ε < ρ k / R := by
      refine Filter.eventually_all.2 ?_
      intro k
      have hpos : 0 < ρ k / R := div_pos (hρpos k) hRpos
      exact (eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hεpos hεsmall
    intro y hy
    obtain ⟨k, hcluster⟩ :=
      cStarDiagonalPerturbation_spectrum_gershgorin_cluster
        (x := x) (u := u) (ε := ε) hy
    have hRnonneg : 0 ≤ R := hRpos.le
    have hradius_nonneg : 0 ≤ rankOneGershgorinRadius u k :=
      rankOneGershgorinRadius_nonneg u k
    have hradius_le : rankOneGershgorinRadius u k ≤ R :=
      rankOneGershgorinRadius_le_total u k
    have hdist_norm :
        ‖y - x k‖ ≤ ε * rankOneGershgorinRadius u k := by
      simpa [Real.norm_of_nonneg hεpos.le] using hcluster
    have hdist_lt : dist y (x k) < ρ k := by
      rw [Real.dist_eq]
      have hleR :
          ε * rankOneGershgorinRadius u k ≤ ε * R := by
        exact mul_le_mul_of_nonneg_left hradius_le hεpos.le
      have hltR : ε * R < ρ k := by
        have hsmallk := hεsmall k
        have hmul := mul_lt_mul_of_pos_right hsmallk hRpos
        have hdiv : ρ k / R * R = ρ k := by
          field_simp [ne_of_gt hRpos]
        simpa [hdiv, mul_comm, mul_left_comm, mul_assoc] using hmul
      exact lt_of_le_of_lt (hdist_norm.trans hleR) hltR
    have hnear :
        ‖hermiteRemainderFunction f x y‖ ≤ α * ‖y - x k‖ :=
      hρ k hdist_lt
    have hαnonneg : 0 ≤ α := hαpos.le
    have hbound :
        ‖hermiteRemainderFunction f x y‖ ≤ α * (ε * R) := by
      calc
        ‖hermiteRemainderFunction f x y‖
            ≤ α * ‖y - x k‖ := hnear
        _ ≤ α * (ε * rankOneGershgorinRadius u k) := by
          exact mul_le_mul_of_nonneg_left hdist_norm hαnonneg
        _ ≤ α * (ε * R) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hradius_le hεpos.le) hαnonneg
    have hαR : α * (ε * R) = η * ε := by
      unfold α R
      field_simp [ne_of_gt (rankOneGershgorinTotalRadius_pos u)]
    simpa [hαR] using hbound

/--
Cluster-control input for turning the CFC norm bridge into the old Hermite
remainder-estimate package.

This structure does not prove the spectral cluster control itself.  Instead,
it records exactly the two facts needed by the previous raw quotient
reduction: continuity of the original normalized scalar function along the
small perturbation and convergence of the Hermite-remainder raw quotient.  For
differentiable `f` they are supplied on the way to
`diagonalCFCHermiteRemainderEstimateInput_of_differentiable` below.
-/
structure DiagonalCFCHermiteRemainderClusterControlInput
    (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  original_continuous_perturbation_eventually :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              ContinuousOn (fun t : ℝ => f t - f 0)
                (quasispectrum ℝ (diagonalPerturbation x u ε))
  original_continuous_diagonal :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ContinuousOn (fun t : ℝ => f t - f 0)
            (quasispectrum ℝ (diagonalMatrix x))
  remainder_raw_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient
                    (hermiteRemainderFunction f x) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
Compatibility input after the CFC norm bridge: the bridge is stated in the
`CStarMatrix` copy, while the older Hermite remainder package consumes the
plain matrix quotient.  This structure keeps only that quotient convergence as
input; it is supplied from differentiability by
`diagonalCFCHermiteRemainderCStarQuotientInput_of_differentiable` below.
-/
structure DiagonalCFCHermiteRemainderCStarQuotientInput
    (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  original_continuous_perturbation_eventually :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              ContinuousOn (fun t : ℝ => f t - f 0)
                (quasispectrum ℝ (diagonalPerturbation x u ε))
  original_continuous_diagonal :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ContinuousOn (fun t : ℝ => f t - f 0)
            (quasispectrum ℝ (diagonalMatrix x))
  cstar_remainder_raw_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  hermiteRemainderCStarRawEntrywiseVariationQuotient
                    f x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
The scalar spectrum-bound input supplies the CStar raw quotient convergence
needed by the quotient compatibility layer.  The result is intentionally phrased through
`_of_spectrumBound`: it does not hide the scalar quantitative estimate.
-/
def diagonalCFCHermiteRemainderCStarQuotientInput_of_spectrumBound
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermiteRemainderSpectrumBoundInput f) :
    DiagonalCFCHermiteRemainderCStarQuotientInput f where
  differentiable := input.differentiable
  original_continuous_perturbation_eventually := by
    intro n x hx _hinj u
    have hfcont : ContinuousOn (fun t : ℝ => f t - f 0) (Set.Ioo (-1 : ℝ) 1) :=
      input.differentiable.continuousOn.sub continuousOn_const
    filter_upwards [diagonalPerturbation_mem_domain_eventually x hx u] with
      ε hdom
    exact hfcont.mono hdom.2
  original_continuous_diagonal := by
    intro n x hx _hinj
    have hfcont : ContinuousOn (fun t : ℝ => f t - f 0) (Set.Ioo (-1 : ℝ) 1) :=
      input.differentiable.continuousOn.sub continuousOn_const
    exact hfcont.mono (diagonalMatrix_mem_domain x hx).2
  cstar_remainder_raw_tendsto_zero := by
    intro n x hx hinj u i j
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hη : 0 < δ / 2 := half_pos hδ
    filter_upwards [
      input.cstar_remainder_spectrum_bound n x hx hinj u (δ / 2) hη,
      cStarDiagonalPerturbation_mem_domain_eventually x hx u,
      self_mem_nhdsWithin] with ε hbound hdom hεmem
    have hε : 0 < ε := hεmem
    have hNA :
        ContinuousOn (hermiteNormalizedRemainderFunction f x)
          (quasispectrum ℝ (cStarDiagonalPerturbation x u ε)) :=
      (hermiteNormalizedRemainderFunction_continuousOn_Ioo
        (f := f) (x := x) input.differentiable).mono hdom.2
    have hND :
        ContinuousOn (hermiteNormalizedRemainderFunction f x)
          (quasispectrum ℝ (cStarDiagonalMatrix x)) :=
      (hermiteNormalizedRemainderFunction_continuousOn_Ioo
        (f := f) (x := x) input.differentiable).mono
        (cStarDiagonalMatrix_mem_domain x hx).2
    have hRA :
        ContinuousOn (hermiteRemainderFunction f x)
          (spectrum ℝ (cStarDiagonalPerturbation x u ε)) :=
      (hermiteRemainderFunction_continuousOn_Ioo
        (f := f) (x := x) input.differentiable).mono
        (fun y hy => hdom.2 (spectrum_subset_quasispectrum ℝ
          (cStarDiagonalPerturbation x u ε) hy))
    have hRD :
        ContinuousOn (hermiteRemainderFunction f x)
          (spectrum ℝ (cStarDiagonalMatrix x)) :=
      (hermiteRemainderFunction_continuousOn_Ioo
        (f := f) (x := x) input.differentiable).mono
        (fun y hy => (cStarDiagonalMatrix_mem_domain x hx).2
          (spectrum_subset_quasispectrum ℝ (cStarDiagonalMatrix x) hy))
    have hDzero :
        cfc (hermiteRemainderFunction f x)
          (cStarDiagonalMatrix x) = 0 :=
      hermiteRemainderFunction_cstarCFC_diagonal_eq_zero
        (f := f) (x := x) hinj
    have hquot :
        ‖hermiteRemainderCStarRawEntrywiseVariationQuotient
            f x u ε i j‖ ≤ ε⁻¹ * ((δ / 2) * ε) :=
      hermiteRemainder_cstarRawQuotient_norm_le_of_spectrum_bound
        (f := f) (x := x) (u := u) (ε := ε) (c := (δ / 2) * ε)
        (i := i) (j := j) hε (by positivity) hNA hND hRA hRD hDzero
        (by
          intro y hy
          exact hbound y hy)
    have hquot' :
        ‖hermiteRemainderCStarRawEntrywiseVariationQuotient
            f x u ε i j‖ ≤ δ / 2 := by
      have hmul : ε⁻¹ * ((δ / 2) * ε) = δ / 2 := by
        field_simp [ne_of_gt hε]
      simpa [hmul] using hquot
    rw [dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hquot' (by linarith)

/-- Differentiability supplies the CStar raw quotient convergence package. -/
def diagonalCFCHermiteRemainderCStarQuotientInput_of_differentiable
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) :
    DiagonalCFCHermiteRemainderCStarQuotientInput f :=
  diagonalCFCHermiteRemainderCStarQuotientInput_of_spectrumBound
    (diagonalCFCHermiteRemainderSpectrumBoundInput_of_differentiable hf)

/--
Transport CStarMatrix quotient convergence back to the plain quotient package.
The theorem name intentionally keeps `_of_cstarQuotient`: it is not a closed
cluster-control theorem.
-/
def diagonalCFCHermiteRemainderClusterControlInput_of_cstarQuotient
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermiteRemainderCStarQuotientInput f) :
    DiagonalCFCHermiteRemainderClusterControlInput f where
  differentiable := input.differentiable
  original_continuous_perturbation_eventually :=
    input.original_continuous_perturbation_eventually
  original_continuous_diagonal := input.original_continuous_diagonal
  remainder_raw_tendsto_zero := by
    intro n x hx hinj u i j
    have heq :
        (fun ε : ℝ =>
          hermiteRemainderCStarRawEntrywiseVariationQuotient
            f x u ε i j) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε : ℝ =>
            diagonalCFCRawEntrywiseVariationQuotient
              (hermiteRemainderFunction f x) x u ε i j) :=
      Filter.Eventually.of_forall fun ε =>
        hermiteRemainderCStarRawEntrywiseVariationQuotient_eq_plain
          (f := f) x u ε i j
    exact (input.cstar_remainder_raw_tendsto_zero n x hx hinj u i j).congr' heq

/--
Hermite/remainder input that turns polynomial raw coefficient formulas into the
raw CFC first-variation input for the original function.

For each finite node set and rank-one direction, `polynomial` is the book's
finite-dimensional Hermite surrogate.  The fields say that the polynomial raw
formula is available, its divided-difference entries match those of `f` on the
chosen nodes, and the CFC coefficient remainder has zero first-order limit.
-/
structure DiagonalCFCRawEntrywisePolynomialApproximationInput
    (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  polynomial :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
        Function.Injective x →
          (Fin n → ℂ) → ℝ[X]
  polynomial_raw_tendsto :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  polynomialRawEntrywiseVariationQuotient
                    (polynomial n x hx hinj u) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 (polynomialRawLoewnerDerivativeEntry
                  (polynomial n x hx hinj u) x u i j))
  polynomial_matches_loewner :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              polynomialRawLoewnerDerivativeEntry
                  (polynomial n x hx hinj u) x u i j =
                rawLoewnerDerivativeEntry f x u i j
  remainder_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
                    polynomialRawEntrywiseVariationQuotient
                      (polynomial n x hx hinj u) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
Hermite node-matching version of the polynomial approximation input.

The finite polynomial surrogate only has to match `f` and `deriv f` on the
chosen nodes.  The Löwner divided-difference target is then recovered by the
Hermite matching lemma above.
-/
structure DiagonalCFCHermitePolynomialApproximationInput
    (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  polynomial :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
        Function.Injective x →
          (Fin n → ℂ) → ℝ[X]
  node_value_matches :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            hermiteNodeValueMatches f (polynomial n x hx hinj u) x
  node_deriv_matches :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            hermiteNodeDerivMatches f (polynomial n x hx hinj u) x
  polynomial_raw_tendsto :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  polynomialRawEntrywiseVariationQuotient
                    (polynomial n x hx hinj u) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 (polynomialRawLoewnerDerivativeEntry
                  (polynomial n x hx hinj u) x u i j))
  remainder_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
                    polynomialRawEntrywiseVariationQuotient
                      (polynomial n x hx hinj u) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
Hermite remainder input after the polynomial surrogate has been constructed.

The polynomial is the explicit finite-node Hermite interpolant.  What remains
as input is only the polynomial raw coefficient formula for that interpolant
and the zero first-order CFC remainder estimate for the original function.
-/
structure DiagonalCFCHermiteRemainderInput (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  polynomial_raw_tendsto :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  polynomialRawEntrywiseVariationQuotient
                    (hermiteInterpolatingPolynomial f x) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 (polynomialRawLoewnerDerivativeEntry
                  (hermiteInterpolatingPolynomial f x) x u i j))
  remainder_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
                    polynomialRawEntrywiseVariationQuotient
                      (hermiteInterpolatingPolynomial f x) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
Hermite remainder-estimate input after closing the polynomial raw CFC
coefficient formula.

The explicit Hermite polynomial is already available, and polynomial raw
coefficient convergence is now supplied by
`polynomialRawEntrywiseVariation_tendsto`.  The only CFC-side input
left here is the first-order remainder estimate for replacing `f` by its
finite-node Hermite surrogate.
-/
structure DiagonalCFCHermiteRemainderEstimateInput (f : ℝ → ℝ) where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  remainder_tendsto_zero :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      ∀ _hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1,
        ∀ _hinj : Function.Injective x,
          ∀ u : Fin n → ℂ,
            ∀ i j : Fin n,
              Filter.Tendsto
                (fun ε : ℝ =>
                  diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
                    polynomialRawEntrywiseVariationQuotient
                      (hermiteInterpolatingPolynomial f x) x u ε i j)
                (𝓝[>] (0 : ℝ))
                (𝓝 0)

/--
Cluster control for the Hermite remainder supplies the remainder-estimate input
used by the entrywise Hermite pipeline.  The theorem name intentionally carries
`_of_clusterControl`: the cluster control is an explicit input here.  From
differentiability alone, the remainder-estimate input is supplied by
`diagonalCFCHermiteRemainderEstimateInput_of_differentiable` below.
-/
def diagonalCFCHermiteRemainderEstimateInput_of_clusterControl
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermiteRemainderClusterControlInput f) :
    DiagonalCFCHermiteRemainderEstimateInput f where
  differentiable := input.differentiable
  remainder_tendsto_zero := by
    intro n x hx hinj u i j
    have hFD := input.original_continuous_diagonal n x hx hinj
    have heq :
        (fun ε : ℝ =>
          diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
            polynomialRawEntrywiseVariationQuotient
              (hermiteInterpolatingPolynomial f x) x u ε i j) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε : ℝ =>
            diagonalCFCRawEntrywiseVariationQuotient
              (hermiteRemainderFunction f x) x u ε i j) := by
      filter_upwards [input.original_continuous_perturbation_eventually n x hx hinj u] with
        ε hFA
      exact hermiteRemainder_rawQuotient_error_eq
        (f := f) (x := x) (u := u) (ε := ε) (i := i) (j := j) hFA hFD
    exact (input.remainder_raw_tendsto_zero n x hx hinj u i j).congr' heq.symm

/--
Directly recover the Hermite remainder-estimate input from the CStar quotient
compatibility layer.
-/
def diagonalCFCHermiteRemainderEstimateInput_of_cstarQuotient
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermiteRemainderCStarQuotientInput f) :
    DiagonalCFCHermiteRemainderEstimateInput f :=
  diagonalCFCHermiteRemainderEstimateInput_of_clusterControl
    (diagonalCFCHermiteRemainderClusterControlInput_of_cstarQuotient input)

/-- Differentiability supplies the Hermite CFC remainder estimate package. -/
def diagonalCFCHermiteRemainderEstimateInput_of_differentiable
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)) :
    DiagonalCFCHermiteRemainderEstimateInput f :=
  diagonalCFCHermiteRemainderEstimateInput_of_cstarQuotient
    (diagonalCFCHermiteRemainderCStarQuotientInput_of_differentiable hf)

/--
The closed polynomial raw coefficient formula fills the compatibility input
that still expected `polynomial_raw_tendsto`.
-/
def hermiteRemainderInput_of_remainderEstimateInput
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermiteRemainderEstimateInput f) :
    DiagonalCFCHermiteRemainderInput f where
  differentiable := input.differentiable
  polynomial_raw_tendsto := by
    intro _n _x _hx _hinj _u _i _j
    exact polynomialRawEntrywiseVariation_tendsto
  remainder_tendsto_zero := input.remainder_tendsto_zero

/--
The explicit Hermite interpolant supplies the node value and derivative
matching fields required by the previous Hermite polynomial approximation
input.
-/
def hermitePolynomialApproximationInput_of_hermiteRemainderInput
    {f : ℝ → ℝ} (input : DiagonalCFCHermiteRemainderInput f) :
    DiagonalCFCHermitePolynomialApproximationInput f where
  differentiable := input.differentiable
  polynomial := fun _n x _hx _hinj _u => hermiteInterpolatingPolynomial f x
  node_value_matches := by
    intro _n _x _hx hinj _u
    exact hermiteInterpolatingPolynomial_valueMatches hinj
  node_deriv_matches := by
    intro _n _x _hx hinj _u
    exact hermiteInterpolatingPolynomial_derivMatches hinj
  polynomial_raw_tendsto := input.polynomial_raw_tendsto
  remainder_tendsto_zero := input.remainder_tendsto_zero

/--
Hermite node matching supplies the `polynomial_matches_loewner` field expected
by the previous polynomial approximation input.
-/
def polynomialApproximationInput_of_hermitePolynomialApproximationInput
    {f : ℝ → ℝ}
    (input : DiagonalCFCHermitePolynomialApproximationInput f) :
    DiagonalCFCRawEntrywisePolynomialApproximationInput f where
  differentiable := input.differentiable
  polynomial := input.polynomial
  polynomial_raw_tendsto := input.polynomial_raw_tendsto
  polynomial_matches_loewner := by
    intro n x hx hinj u i j
    exact polynomialRawLoewnerDerivativeEntry_eq_raw_of_hermiteMatches
      (input.node_value_matches n x hx hinj u)
      (input.node_deriv_matches n x hx hinj u) i j
  remainder_tendsto_zero := input.remainder_tendsto_zero

end

end Quantum.TraceInequality.Loewner
