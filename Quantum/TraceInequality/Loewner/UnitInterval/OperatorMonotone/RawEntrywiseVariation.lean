import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.DiagonalFirstVariation

/-!
# Chapter 3 raw entrywise variation

This file contains the separated test-vector quotient, raw CFC matrix-coefficient
quotient, and polynomial divided-difference layer used before the Hermite
approximation step.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped FinMatrixCStar
open scoped Polynomial
open scoped Topology

/-!
## Separated perturbation/test-vector first variation

The same-vector rank-one order ray above is useful as an interface, but the
book's Löwner quadratic form is obtained by separating the positive
perturbation direction from the vector used to test the resulting positive
matrix.  The declarations below record that corrected convention explicitly.
-/

/--
Scalar difference quotient along the positive rank-one direction determined by
`u`, tested against an independent vector `v`.
-/
def diagonalSeparatedVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) (ε : ℝ) : ℂ :=
  (ε⁻¹ : ℝ) •
    (star v ⬝ᵥ
      ((cfcₙ (fun t : ℝ => f t - f 0) (diagonalPerturbation x u ε) -
        cfcₙ (fun t : ℝ => f t - f 0) (diagonalMatrix x)) *ᵥ v))

/--
The same separated quotient after applying finite-dimensional monotonicity in
the `CStarMatrix` C*-algebra copy.
-/
def cStarDiagonalSeparatedVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) (ε : ℝ) : ℂ :=
  (ε⁻¹ : ℝ) •
    (star v ⬝ᵥ
      (((CStarMatrix.ofMatrix.symm
          (cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalPerturbation x u ε))) -
        (CStarMatrix.ofMatrix.symm
          (cfcₙ (fun t : ℝ => f t - f 0)
            (cStarDiagonalMatrix x)))) *ᵥ v))

/-- The plain and `CStarMatrix` separated quotients have the same formula. -/
lemma diagonalSeparatedVariationQuotient_eq_cstar
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) (ε : ℝ) :
    diagonalSeparatedVariationQuotient f x u v ε =
      cStarDiagonalSeparatedVariationQuotient f x u v ε := by
  rfl

/-- Entrywise contribution to the separated diagonal CFC variation quotient. -/
def diagonalCFCSeparatedEntrywiseVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) : ℂ :=
  (ε⁻¹ : ℝ) •
    (star (v i) *
      ((cfcₙ (fun t : ℝ => f t - f 0) (diagonalPerturbation x u ε) -
        cfcₙ (fun t : ℝ => f t - f 0) (diagonalMatrix x)) i j) *
      v j)

/--
Entrywise contribution of the divided-difference derivative in the separated
rank-one direction `u`, tested against `v`.
-/
def separatedLoewnerDerivativeEntry
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ)
    (i j : Fin n) : ℂ :=
  star (v i) *
    ((loewnerKernel f (x i) (x j) : ℂ) * u i * star (u j)) *
      v j

/-- The limiting separated quadratic form for the first variation. -/
def separatedLoewnerQuadraticForm
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) : ℂ :=
  star v ⬝ᵥ
    ((Matrix.of
      (fun i j : Fin n =>
        (loewnerKernel f (x i) (x j) : ℂ) * u i * star (u j))) *ᵥ v)

/-- The separated CFC variation quotient expands as the sum of entrywise terms. -/
lemma diagonalSeparatedVariationQuotient_eq_sum_entries
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) (ε : ℝ) :
    diagonalSeparatedVariationQuotient f x u v ε =
      ∑ i : Fin n, ∑ j : Fin n,
        diagonalCFCSeparatedEntrywiseVariationQuotient f x u v ε i j := by
  simp [diagonalSeparatedVariationQuotient,
    diagonalCFCSeparatedEntrywiseVariationQuotient, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc]

/-- The separated Löwner quadratic form expands as the sum of entrywise terms. -/
lemma separatedLoewnerQuadraticForm_eq_sum_entries
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ) :
    separatedLoewnerQuadraticForm f x u v =
      ∑ i : Fin n, ∑ j : Fin n,
        separatedLoewnerDerivativeEntry f x u v i j := by
  simp [separatedLoewnerQuadraticForm, separatedLoewnerDerivativeEntry,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- With the separating vector equal to one, the separated form is the ordinary form. -/
lemma separatedLoewnerQuadraticForm_one_eq
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℂ) :
    separatedLoewnerQuadraticForm f x (fun _ : Fin n => (1 : ℂ)) v =
      star v ⬝ᵥ
        ((Matrix.of
          (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))) *ᵥ v) := by
  simp [separatedLoewnerQuadraticForm, dotProduct, Matrix.mulVec]

/-!
### Raw coefficient layer

The separated entrywise quotient is just the raw CFC matrix-coefficient
quotient multiplied by the fixed test-vector weights.  This layer isolates the
actual CFC first-variation formula as an unweighted matrix coefficient limit.
-/

/-- Raw matrix-coefficient CFC variation quotient along the rank-one direction `u`. -/
def diagonalCFCRawEntrywiseVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) : ℂ :=
  (ε⁻¹ : ℝ) •
    ((cfcₙ (fun t : ℝ => f t - f 0) (diagonalPerturbation x u ε) -
      cfcₙ (fun t : ℝ => f t - f 0) (diagonalMatrix x)) i j)

/-- Raw divided-difference matrix coefficient expected from the CFC first variation. -/
def rawLoewnerDerivativeEntry
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (i j : Fin n) : ℂ :=
  (loewnerKernel f (x i) (x j) : ℂ) * u i * star (u j)

/-- The separated entrywise quotient is the raw quotient with fixed vector weights. -/
lemma diagonalCFCSeparatedEntrywiseVariationQuotient_eq_weighted_raw
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) :
    diagonalCFCSeparatedEntrywiseVariationQuotient f x u v ε i j =
      star (v i) *
        diagonalCFCRawEntrywiseVariationQuotient f x u ε i j *
          v j := by
  simp [diagonalCFCSeparatedEntrywiseVariationQuotient,
    diagonalCFCRawEntrywiseVariationQuotient]
  ring

/-- The separated Löwner derivative entry is the raw entry with fixed vector weights. -/
lemma separatedLoewnerDerivativeEntry_eq_weighted_raw
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u v : Fin n → ℂ)
    (i j : Fin n) :
    separatedLoewnerDerivativeEntry f x u v i j =
      star (v i) * rawLoewnerDerivativeEntry f x u i j * v j := by
  simp [separatedLoewnerDerivativeEntry, rawLoewnerDerivativeEntry,
    mul_assoc]

/--
Raw coefficient convergence supplies the separated weighted entrywise
convergence by multiplication with fixed test-vector coefficients.
-/
theorem separatedEntrywise_tendsto_of_rawEntrywise
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u v : Fin n → ℂ} {i j : Fin n}
    (hraw :
      Filter.Tendsto
        (fun ε : ℝ => diagonalCFCRawEntrywiseVariationQuotient f x u ε i j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (rawLoewnerDerivativeEntry f x u i j))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        diagonalCFCSeparatedEntrywiseVariationQuotient f x u v ε i j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (separatedLoewnerDerivativeEntry f x u v i j)) := by
  have hweighted :
      Filter.Tendsto
        (fun ε : ℝ =>
          star (v i) *
            diagonalCFCRawEntrywiseVariationQuotient f x u ε i j *
              v j)
        (𝓝[>] (0 : ℝ))
        (𝓝 (star (v i) * rawLoewnerDerivativeEntry f x u i j * v j)) :=
    (tendsto_const_nhds.mul hraw).mul tendsto_const_nhds
  simpa [diagonalCFCSeparatedEntrywiseVariationQuotient_eq_weighted_raw,
    separatedLoewnerDerivativeEntry_eq_weighted_raw] using hweighted

/-!
### Polynomial divided-difference layer

This layer records the polynomial divided-difference target for the raw matrix
coefficient formula and packages the Hermite/remainder estimate as a precise
input to the raw coefficient route.  The route is completed in
`loewnerPosOnUnitInterval_of_finiteMatrixMonotone` (`HiaiRegularity.lean`).
-/

/-- Divided difference of a polynomial, using the same convention as `loewnerKernel`. -/
def polynomialDividedDifference (p : ℝ[X]) (x y : ℝ) : ℝ :=
  loewnerKernel (fun t : ℝ => p.eval t) x y

/-- Polynomial version of the raw divided-difference matrix coefficient. -/
def polynomialRawLoewnerDerivativeEntry
    (p : ℝ[X]) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (i j : Fin n) : ℂ :=
  (polynomialDividedDifference p (x i) (x j) : ℂ) * u i * star (u j)

/-- Polynomial raw matrix-coefficient quotient, still expressed through `cfcₙ`. -/
def polynomialRawEntrywiseVariationQuotient
    (p : ℝ[X]) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) : ℂ :=
  diagonalCFCRawEntrywiseVariationQuotient (fun t : ℝ => p.eval t) x u ε i j

/-- Normalized non-unital CFC of a polynomial is ordinary matrix polynomial evaluation. -/
lemma polynomial_cfcₙ_eq_aeval_sub_const
    {n : ℕ} (p : ℝ[X]) (M : Matrix (Fin n) (Fin n) ℂ)
    (_hM : IsSelfAdjoint M) :
    cfcₙ (fun t : ℝ => p.eval t - p.eval 0) M =
      Polynomial.aeval M (p - Polynomial.C (p.eval 0)) := by
  calc
    cfcₙ (fun t : ℝ => p.eval t - p.eval 0) M =
        cfc (fun t : ℝ => p.eval t - p.eval 0) M := by
      exact cfcₙ_eq_cfc (f := fun t : ℝ => p.eval t - p.eval 0) (a := M)
        (hf0 := by simp)
    _ = cfc (fun t : ℝ => Polynomial.eval t (p - Polynomial.C (p.eval 0))) M := by
      congr 1
      ext t
      simp
    _ = Polynomial.aeval M (p - Polynomial.C (p.eval 0)) := by
      exact cfc_polynomial (p - Polynomial.C (p.eval 0)) M

/-- Noncommutative telescoping identity for a difference of powers. -/
lemma pow_sub_pow_telescoping {R : Type*} [Ring R] (A D : R) (k : ℕ) :
    A ^ k - D ^ k =
      ∑ r ∈ Finset.range k, A ^ r * (A - D) * D ^ (k.pred - r) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        A ^ (k + 1) - D ^ (k + 1) =
            (A ^ k - D ^ k) * D + A ^ k * (A - D) := by
          noncomm_ring
        _ = (∑ r ∈ Finset.range k, A ^ r * (A - D) * D ^ (k.pred - r)) * D +
              A ^ k * (A - D) := by
          rw [ih]
        _ = (∑ r ∈ Finset.range k,
              A ^ r * (A - D) * D ^ ((k + 1).pred - r)) +
              A ^ k * (A - D) * D ^ ((k + 1).pred - k) := by
          by_cases hk : k = 0
          · subst k
            simp
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
            have hsum :
                (∑ r ∈ Finset.range k, A ^ r * (A - D) * D ^ (k.pred - r)) * D =
                  ∑ r ∈ Finset.range k,
                    A ^ r * (A - D) * D ^ ((k + 1).pred - r) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro r hr
              have hpow :
                  D ^ (k.pred - r) * D = D ^ ((k + 1).pred - r) := by
                rw [← pow_succ]
                congr 1
                have hrlt : r < k := Finset.mem_range.mp hr
                have hkpred : k.pred + 1 = k := Nat.succ_pred_eq_of_pos hkpos
                have hsuccpred : (k + 1).pred = k := by simp
                omega
              rw [mul_assoc, hpow]
            simpa using congrArg (fun z => z + A ^ k * (A - D)) hsum
        _ = ∑ r ∈ Finset.range (k + 1),
              A ^ r * (A - D) * D ^ ((k + 1).pred - r) := by
          simpa using
            (Finset.sum_range_succ
              (fun r : ℕ => A ^ r * (A - D) * D ^ ((k + 1).pred - r)) k).symm

/-- Raw monomial quotient before summing polynomial coefficients. -/
def powerRawEntrywiseVariationQuotient
    (m : ℕ) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) : ℂ :=
  (ε⁻¹ : ℝ) •
    (((diagonalPerturbation x u ε) ^ m -
      (diagonalMatrix x) ^ m) i j)

/-- Raw monomial first-variation limit. -/
def powerRawLoewnerDerivativeEntry
    (m : ℕ) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (i j : Fin n) : ℂ :=
  (∑ r ∈ Finset.range m,
      (x i : ℂ) ^ r * (x j : ℂ) ^ (m.pred - r)) *
    u i * star (u j)

/-- Powers of the diagonal node matrix are still diagonal. -/
lemma diagonalMatrix_pow_apply
    {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (i j : Fin n) :
    ((diagonalMatrix x) ^ m) i j =
      if i = j then (x i : ℂ) ^ m else 0 := by
  induction m generalizing i j with
  | zero =>
      simp [Matrix.one_apply]
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      by_cases hij : i = j
      · subst j
        rw [Finset.sum_eq_single i]
        · rw [ih i i]
          simp [diagonalMatrix, pow_succ]
        · intro k _hk hki
          rw [ih i k]
          simp [diagonalMatrix, hki]
        · intro hi
          simp at hi
      · have hzero :
            ∀ k : Fin n,
              ((diagonalMatrix x) ^ m) i k *
                (diagonalMatrix x) k j = 0 := by
          intro k
          by_cases hik : i = k
          · subst k
            simp [diagonalMatrix, hij]
          · rw [ih i k]
            simp [diagonalMatrix, hik]
        rw [if_neg hij]
        exact Finset.sum_eq_zero (fun k _hk => hzero k)

/-- A diagonal/rank-one/diagonal product has the expected single coefficient. -/
lemma diagonal_rankOne_diagonal_apply
    {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (r s : ℕ) (i j : Fin n) :
    (((diagonalMatrix x) ^ r *
        rankOnePerturbation u *
          (diagonalMatrix x) ^ s) i j) =
      (x i : ℂ) ^ r * u i * star (u j) * (x j : ℂ) ^ s := by
  rw [Matrix.mul_apply]
  have hleft :
      ∀ k : Fin n,
        (((diagonalMatrix x) ^ r * rankOnePerturbation u) i k) =
          (x i : ℂ) ^ r * u i * star (u k) := by
    intro k
    rw [Matrix.mul_apply]
    have hsingle :
        ∑ l : Fin n,
          ((diagonalMatrix x) ^ r) i l *
            (rankOnePerturbation u) l k =
          ((diagonalMatrix x) ^ r) i i *
            (rankOnePerturbation u) i k := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro l _hl hli
        have hil : i ≠ l := fun h => hli h.symm
        simp [diagonalMatrix_pow_apply, hil]
      · intro hi
        simp at hi
    rw [hsingle]
    simp [diagonalMatrix_pow_apply, rankOnePerturbation,
      Matrix.vecMulVec]
    ring
  have hsingle :
      ∑ k : Fin n,
        (((diagonalMatrix x) ^ r * rankOnePerturbation u) i k) *
          ((diagonalMatrix x) ^ s) k j =
        (((diagonalMatrix x) ^ r * rankOnePerturbation u) i j) *
          ((diagonalMatrix x) ^ s) j j := by
    refine Finset.sum_eq_single j ?_ ?_
    · intro k _hk hkj
      simp [diagonalMatrix_pow_apply, hkj]
    · intro hj
      simp at hj
  rw [hsingle, hleft]
  simp [diagonalMatrix_pow_apply, mul_assoc]

/-- The power quotient is eventually the finite telescoping sum. -/
lemma powerRawEntrywiseVariationQuotient_eventually_eq_sum
    {m n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ) (i j : Fin n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      powerRawEntrywiseVariationQuotient m x u ε i j =
        ∑ r ∈ Finset.range m,
          (((diagonalPerturbation x u ε) ^ r *
              rankOnePerturbation u *
                (diagonalMatrix x) ^ (m.pred - r)) i j) := by
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  let A := diagonalPerturbation x u ε
  let D := diagonalMatrix x
  let P := rankOnePerturbation u
  have hdiff : A - D = ε • P := by
    ext a b
    simp [A, D, P, diagonalPerturbation]
  have htel := pow_sub_pow_telescoping A D m
  have happly := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) htel
  have happly' :
      (A ^ m - D ^ m) i j =
        ∑ r ∈ Finset.range m, (A ^ r * (A - D) * D ^ (m.pred - r)) i j := by
    calc
      (A ^ m - D ^ m) i j =
          (∑ r ∈ Finset.range m, A ^ r * (A - D) * D ^ (m.pred - r)) i j := happly
      _ = ∑ r ∈ Finset.range m, (A ^ r * (A - D) * D ^ (m.pred - r)) i j := by
        simp [Matrix.sum_apply]
  change (ε⁻¹ : ℝ) • ((A ^ m - D ^ m) i j) =
    ∑ r ∈ Finset.range m, (A ^ r * P * D ^ (m.pred - r)) i j
  rw [happly']
  rw [hdiff]
  calc
    (ε⁻¹ : ℝ) •
        (∑ r ∈ Finset.range m, (A ^ r * ε • P * D ^ (m.pred - r)) i j) =
        ∑ r ∈ Finset.range m,
          (ε⁻¹ : ℝ) • (A ^ r * ε • P * D ^ (m.pred - r)) i j := by
      exact Finset.smul_sum
    _ = ∑ r ∈ Finset.range m, (A ^ r * P * D ^ (m.pred - r)) i j := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      have hmatrix :
          A ^ r * ε • P * D ^ (m.pred - r) =
            ε • (A ^ r * P * D ^ (m.pred - r)) := by
        rw [show A ^ r * ε • P = ε • (A ^ r * P) from
          Matrix.mul_smul (R := ℝ) (A ^ r) ε P]
        rw [show ε • (A ^ r * P) * D ^ (m.pred - r) =
            ε • ((A ^ r * P) * D ^ (m.pred - r)) from
          Matrix.smul_mul (R := ℝ) ε (A ^ r * P) (D ^ (m.pred - r))]
      rw [hmatrix]
      simp [hεne]

/-- Each telescoping summand converges to the corresponding diagonal summand. -/
lemma powerRawEntrywiseVariation_term_tendsto
    {m n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ) (r : ℕ) (i j : Fin n) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (((diagonalPerturbation x u ε) ^ r *
            rankOnePerturbation u *
              (diagonalMatrix x) ^ (m.pred - r)) i j))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((diagonalMatrix x) ^ r *
          rankOnePerturbation u *
            (diagonalMatrix x) ^ (m.pred - r)) i j))) := by
  have hbase :
      Filter.Tendsto (fun ε : ℝ => diagonalPerturbation x u ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (diagonalMatrix x)) :=
    (diagonalPerturbation_tendsto_zero x u).mono_left nhdsWithin_le_nhds
  have hpow :
      Filter.Tendsto (fun ε : ℝ => (diagonalPerturbation x u ε) ^ r)
        (𝓝[>] (0 : ℝ)) (𝓝 ((diagonalMatrix x) ^ r)) :=
    hbase.pow r
  have hmat :
      Filter.Tendsto
        (fun ε : ℝ =>
          (diagonalPerturbation x u ε) ^ r *
            rankOnePerturbation u *
              (diagonalMatrix x) ^ (m.pred - r))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((diagonalMatrix x) ^ r *
          rankOnePerturbation u *
            (diagonalMatrix x) ^ (m.pred - r))) :=
    (hpow.mul tendsto_const_nhds).mul tendsto_const_nhds
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmat i) j

/-- The raw monomial quotient converges to the divided-difference finite sum. -/
theorem powerRawEntrywiseVariation_tendsto
    {m n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {i j : Fin n} :
    Filter.Tendsto
      (fun ε : ℝ => powerRawEntrywiseVariationQuotient m x u ε i j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (powerRawLoewnerDerivativeEntry m x u i j)) := by
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∑ r ∈ Finset.range m,
            (((diagonalPerturbation x u ε) ^ r *
                rankOnePerturbation u *
                  (diagonalMatrix x) ^ (m.pred - r)) i j))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ r ∈ Finset.range m,
          (((diagonalMatrix x) ^ r *
              rankOnePerturbation u *
                (diagonalMatrix x) ^ (m.pred - r)) i j))) := by
    refine tendsto_finset_sum (Finset.range m) ?_
    intro r _hr
    exact powerRawEntrywiseVariation_term_tendsto x u r i j
  have hsum_eval :
      (∑ r ∈ Finset.range m,
          (((diagonalMatrix x) ^ r *
              rankOnePerturbation u *
                (diagonalMatrix x) ^ (m.pred - r)) i j)) =
        powerRawLoewnerDerivativeEntry m x u i j := by
    simp [powerRawLoewnerDerivativeEntry,
      diagonal_rankOne_diagonal_apply, Finset.sum_mul, mul_assoc]
    ring_nf
  have heq :
      (fun ε : ℝ =>
        ∑ r ∈ Finset.range m,
          (((diagonalPerturbation x u ε) ^ r *
              rankOnePerturbation u *
                (diagonalMatrix x) ^ (m.pred - r)) i j)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ => powerRawEntrywiseVariationQuotient m x u ε i j) :=
    (powerRawEntrywiseVariationQuotient_eventually_eq_sum x u i j).mono
      (fun _ε h => h.symm)
  have hsum' := hsum.congr' heq
  rw [hsum_eval] at hsum'
  exact hsum'

/-- Geometric-sum form of the divided difference of a monomial. -/
lemma polynomialDividedDifference_monomial
    (m : ℕ) (a x y : ℝ) :
    polynomialDividedDifference (Polynomial.monomial m a) x y =
      a * ∑ r ∈ Finset.range m, x ^ r * y ^ (m.pred - r) := by
  by_cases hxy : x = y
  · subst y
    have hsum :
        (∑ r ∈ Finset.range m, x ^ r * x ^ (m.pred - r)) =
          (m : ℝ) * x ^ (m - 1) := by
      have hterm :
          ∀ r ∈ Finset.range m, x ^ r * x ^ (m.pred - r) = x ^ (m - 1) := by
        intro r hr
        rw [← pow_add]
        congr 1
        have hrlt : r < m := Finset.mem_range.mp hr
        have hpred : m.pred = m - 1 := rfl
        omega
      calc
        (∑ r ∈ Finset.range m, x ^ r * x ^ (m.pred - r)) =
            ∑ _r ∈ Finset.range m, x ^ (m - 1) := by
          exact Finset.sum_congr rfl hterm
        _ = (m : ℝ) * x ^ (m - 1) := by
          simp
    rw [polynomialDividedDifference, loewnerKernel_self, hsum]
    simp [Polynomial.eval_monomial]
  · have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    rw [polynomialDividedDifference,
      loewnerKernel_eq_div (f := fun t : ℝ => (Polynomial.monomial m a).eval t) hxy]
    have hgeom := (Commute.all x y).geom_sum₂_mul m
    have hgeom' :
        (∑ r ∈ Finset.range m, x ^ r * y ^ (m.pred - r)) * (x - y) =
          x ^ m - y ^ m := by
      simpa [Nat.pred_eq_sub_one] using hgeom
    simp [Polynomial.eval_monomial]
    field_simp [hne]
    calc
      a * (x ^ m - y ^ m) =
          a * ((∑ r ∈ Finset.range m, x ^ r * y ^ (m.pred - r)) * (x - y)) := by
        rw [hgeom']
      _ = a * (x - y) *
          ∑ r ∈ Finset.range m, x ^ r * y ^ (m - 1 - r) := by
        simp [Nat.pred_eq_sub_one]
        ring

/-- The polynomial divided-difference coefficient of a monomial. -/
lemma polynomialRawLoewnerDerivativeEntry_monomial
    {m n : ℕ} {a : ℝ} {x : Fin n → ℝ} {u : Fin n → ℂ} {i j : Fin n} :
    polynomialRawLoewnerDerivativeEntry (Polynomial.monomial m a) x u i j =
      (a : ℂ) * powerRawLoewnerDerivativeEntry m x u i j := by
  rw [polynomialRawLoewnerDerivativeEntry,
    powerRawLoewnerDerivativeEntry,
    polynomialDividedDifference_monomial]
  simp only [Nat.pred_eq_sub_one, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow,
    RCLike.star_def]
  ring_nf

/-- Real scalar matrices act entrywise by scalar multiplication. -/
lemma matrix_algebraMap_mul_apply
    {n : ℕ} (a : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) a) * M) i j =
      (a : ℂ) * M i j := by
  rw [Algebra.algebraMap_eq_smul_one]
  have hmul :
      (a • (1 : Matrix (Fin n) (Fin n) ℂ)) * M =
        a • ((1 : Matrix (Fin n) (Fin n) ℂ) * M) :=
    Matrix.smul_mul a (1 : Matrix (Fin n) (Fin n) ℂ) M
  have hentry := congrFun (congrFun hmul i) j
  calc
    ((a • (1 : Matrix (Fin n) (Fin n) ℂ)) * M) i j =
        (a • ((1 : Matrix (Fin n) (Fin n) ℂ) * M)) i j := hentry
    _ = (a • M) i j := by rw [Matrix.one_mul]
    _ = (a : ℂ) * M i j := by rw [Matrix.smul_apply, Complex.real_smul]

/-- Normalized CFC of a monomial is the corresponding matrix power. -/
lemma polynomialRawEntrywiseVariationQuotient_monomial
    {m n : ℕ} {a : ℝ} {x : Fin n → ℝ} {u : Fin n → ℂ}
    {ε : ℝ} {i j : Fin n} :
    polynomialRawEntrywiseVariationQuotient (Polynomial.monomial m a) x u ε i j =
      (a : ℂ) * powerRawEntrywiseVariationQuotient m x u ε i j := by
  by_cases hm : m = 0
  · subst m
    rw [polynomialRawEntrywiseVariationQuotient,
      diagonalCFCRawEntrywiseVariationQuotient,
      powerRawEntrywiseVariationQuotient]
    rw [polynomial_cfcₙ_eq_aeval_sub_const
        (Polynomial.monomial 0 a) (diagonalPerturbation x u ε)
        (diagonalPerturbation_isSelfAdjoint x u ε),
      polynomial_cfcₙ_eq_aeval_sub_const
        (Polynomial.monomial 0 a) (diagonalMatrix x)
        (diagonalMatrix_isSelfAdjoint x)]
    simp [Matrix.sub_apply]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmono_eval0 :
        (Polynomial.monomial m a).eval (0 : ℝ) = 0 := by
      simp [Polynomial.eval_monomial, hm]
    rw [polynomialRawEntrywiseVariationQuotient,
      diagonalCFCRawEntrywiseVariationQuotient,
      powerRawEntrywiseVariationQuotient]
    rw [polynomial_cfcₙ_eq_aeval_sub_const
        (Polynomial.monomial m a) (diagonalPerturbation x u ε)
        (diagonalPerturbation_isSelfAdjoint x u ε),
      polynomial_cfcₙ_eq_aeval_sub_const
        (Polynomial.monomial m a) (diagonalMatrix x)
        (diagonalMatrix_isSelfAdjoint x)]
    simp [hmono_eval0, Polynomial.aeval_monomial, Matrix.sub_apply,
      matrix_algebraMap_mul_apply]
    ring

/-- Monomial polynomial raw coefficient convergence. -/
theorem polynomialRawEntrywiseVariation_tendsto_monomial
    {m n : ℕ} {a : ℝ} {x : Fin n → ℝ} {u : Fin n → ℂ} {i j : Fin n} :
    Filter.Tendsto
      (fun ε : ℝ =>
        polynomialRawEntrywiseVariationQuotient
          (Polynomial.monomial m a) x u ε i j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (polynomialRawLoewnerDerivativeEntry
        (Polynomial.monomial m a) x u i j)) := by
  have hpow :
      Filter.Tendsto
        (fun ε : ℝ => (a : ℂ) *
          powerRawEntrywiseVariationQuotient m x u ε i j)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((a : ℂ) * powerRawLoewnerDerivativeEntry m x u i j)) :=
    tendsto_const_nhds.mul powerRawEntrywiseVariation_tendsto
  have heq :
      (fun ε : ℝ => (a : ℂ) *
          powerRawEntrywiseVariationQuotient m x u ε i j) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          polynomialRawEntrywiseVariationQuotient
            (Polynomial.monomial m a) x u ε i j) :=
    Filter.Eventually.of_forall
      (fun ε => (polynomialRawEntrywiseVariationQuotient_monomial
        (m := m) (a := a) (x := x) (u := u) (ε := ε) (i := i) (j := j)).symm)
  have ht := hpow.congr' heq
  simpa [polynomialRawLoewnerDerivativeEntry_monomial] using ht

/-- Polynomial divided differences are additive. -/
lemma polynomialDividedDifference_add
    (p q : ℝ[X]) (x y : ℝ) :
    polynomialDividedDifference (p + q) x y =
      polynomialDividedDifference p x y +
        polynomialDividedDifference q x y := by
  by_cases hxy : x = y
  · subst y
    rw [polynomialDividedDifference, polynomialDividedDifference,
      polynomialDividedDifference, loewnerKernel_self, loewnerKernel_self,
      loewnerKernel_self]
    rw [Polynomial.deriv, Polynomial.deriv, Polynomial.deriv]
    simp [Polynomial.eval_add]
  · rw [polynomialDividedDifference,
      polynomialDividedDifference, polynomialDividedDifference,
      loewnerKernel_eq_div
        (f := fun t : ℝ => (p + q).eval t) hxy,
      loewnerKernel_eq_div (f := fun t : ℝ => p.eval t) hxy,
      loewnerKernel_eq_div (f := fun t : ℝ => q.eval t) hxy]
    field_simp [sub_ne_zero.mpr hxy, Polynomial.eval_add]
    simp [Polynomial.eval_add]
    ring

/-- Polynomial raw derivative entries are additive in the polynomial. -/
lemma polynomialRawLoewnerDerivativeEntry_add
    {n : ℕ} (p q : ℝ[X]) (x : Fin n → ℝ) (u : Fin n → ℂ) (i j : Fin n) :
    polynomialRawLoewnerDerivativeEntry (p + q) x u i j =
      polynomialRawLoewnerDerivativeEntry p x u i j +
        polynomialRawLoewnerDerivativeEntry q x u i j := by
  rw [polynomialRawLoewnerDerivativeEntry,
    polynomialRawLoewnerDerivativeEntry,
    polynomialRawLoewnerDerivativeEntry,
    polynomialDividedDifference_add]
  simp [Complex.ofReal_add]
  ring

/-- Polynomial raw quotients are additive in the polynomial. -/
lemma polynomialRawEntrywiseVariationQuotient_add
    {n : ℕ} (p q : ℝ[X]) (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) :
    polynomialRawEntrywiseVariationQuotient (p + q) x u ε i j =
      polynomialRawEntrywiseVariationQuotient p x u ε i j +
        polynomialRawEntrywiseVariationQuotient q x u ε i j := by
  rw [polynomialRawEntrywiseVariationQuotient,
    polynomialRawEntrywiseVariationQuotient,
    polynomialRawEntrywiseVariationQuotient,
    diagonalCFCRawEntrywiseVariationQuotient,
    diagonalCFCRawEntrywiseVariationQuotient,
    diagonalCFCRawEntrywiseVariationQuotient]
  rw [polynomial_cfcₙ_eq_aeval_sub_const (p + q)
      (diagonalPerturbation x u ε)
      (diagonalPerturbation_isSelfAdjoint x u ε),
    polynomial_cfcₙ_eq_aeval_sub_const (p + q)
      (diagonalMatrix x) (diagonalMatrix_isSelfAdjoint x),
    polynomial_cfcₙ_eq_aeval_sub_const p
      (diagonalPerturbation x u ε)
      (diagonalPerturbation_isSelfAdjoint x u ε),
    polynomial_cfcₙ_eq_aeval_sub_const p
      (diagonalMatrix x) (diagonalMatrix_isSelfAdjoint x),
    polynomial_cfcₙ_eq_aeval_sub_const q
      (diagonalPerturbation x u ε)
      (diagonalPerturbation_isSelfAdjoint x u ε),
    polynomial_cfcₙ_eq_aeval_sub_const q
      (diagonalMatrix x) (diagonalMatrix_isSelfAdjoint x)]
  simp [Polynomial.eval_add, Matrix.add_apply, Matrix.sub_apply]
  ring_nf

/-- Polynomial CFC raw entrywise variation converges to the divided-difference entry. -/
theorem polynomialRawEntrywiseVariation_tendsto
    {p : ℝ[X]} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {i j : Fin n} :
    Filter.Tendsto
      (fun ε : ℝ =>
        polynomialRawEntrywiseVariationQuotient p x u ε i j)
      (𝓝[>] (0 : ℝ))
      (𝓝 (polynomialRawLoewnerDerivativeEntry p x u i j)) := by
  induction p using Polynomial.induction_on' with
  | monomial m a =>
      exact polynomialRawEntrywiseVariation_tendsto_monomial
  | add p q hp hq =>
      have hsum :
          Filter.Tendsto
            (fun ε : ℝ =>
              polynomialRawEntrywiseVariationQuotient p x u ε i j +
                polynomialRawEntrywiseVariationQuotient q x u ε i j)
            (𝓝[>] (0 : ℝ))
            (𝓝 (polynomialRawLoewnerDerivativeEntry p x u i j +
              polynomialRawLoewnerDerivativeEntry q x u i j)) :=
        hp.add hq
      have heq :
          (fun ε : ℝ =>
              polynomialRawEntrywiseVariationQuotient p x u ε i j +
                polynomialRawEntrywiseVariationQuotient q x u ε i j)
            =ᶠ[𝓝[>] (0 : ℝ)]
            (fun ε : ℝ =>
              polynomialRawEntrywiseVariationQuotient (p + q) x u ε i j) :=
        Filter.Eventually.of_forall
          (fun ε => (polynomialRawEntrywiseVariationQuotient_add
            p q x u ε i j).symm)
      have ht := hsum.congr' heq
      simpa [polynomialRawLoewnerDerivativeEntry_add] using ht

end

end Quantum.TraceInequality.Loewner
