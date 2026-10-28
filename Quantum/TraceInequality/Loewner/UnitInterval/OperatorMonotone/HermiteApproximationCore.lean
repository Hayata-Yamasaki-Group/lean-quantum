import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.RawEntrywiseVariation

/-!
# Chapter 3 Hermite approximation layer

This file contains the finite-node Hermite interpolant, Hermite remainder
estimates, and polynomial-approximation interfaces used to close raw entrywise
CFC variation.
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

/-- Value matching of a Hermite polynomial surrogate on the finite node set. -/
def hermiteNodeValueMatches
    (f : ℝ → ℝ) (p : ℝ[X]) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, p.eval (x i) = f (x i)

/--
Derivative matching of a Hermite polynomial surrogate on the finite node set.
This is the only derivative information used by the divided-difference target.
-/
def hermiteNodeDerivMatches
    (f : ℝ → ℝ) (p : ℝ[X]) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, deriv (fun t : ℝ => p.eval t) (x i) = deriv f (x i)

/--
Hermite value/derivative matching identifies the polynomial divided difference
with the Löwner kernel of the original function on the chosen nodes.
-/
theorem polynomialDividedDifference_eq_loewnerKernel_of_hermiteMatches
    {f : ℝ → ℝ} {p : ℝ[X]} {n : ℕ} {x : Fin n → ℝ}
    (hval : hermiteNodeValueMatches f p x)
    (hderiv : hermiteNodeDerivMatches f p x)
    (i j : Fin n) :
    polynomialDividedDifference p (x i) (x j) =
      loewnerKernel f (x i) (x j) := by
  by_cases hxy : x i = x j
  · rw [polynomialDividedDifference, hxy, loewnerKernel_self,
      loewnerKernel_self, hderiv j]
  · rw [polynomialDividedDifference,
      loewnerKernel_eq_div (f := fun t : ℝ => p.eval t) hxy,
      loewnerKernel_eq_div (f := f) hxy, hval i, hval j]

/--
Hermite node matching identifies the polynomial raw coefficient limit with the
raw Löwner coefficient limit for `f`.
-/
theorem polynomialRawLoewnerDerivativeEntry_eq_raw_of_hermiteMatches
    {f : ℝ → ℝ} {p : ℝ[X]} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ}
    (hval : hermiteNodeValueMatches f p x)
    (hderiv : hermiteNodeDerivMatches f p x)
    (i j : Fin n) :
    polynomialRawLoewnerDerivativeEntry p x u i j =
      rawLoewnerDerivativeEntry f x u i j := by
  rw [polynomialRawLoewnerDerivativeEntry, rawLoewnerDerivativeEntry,
    polynomialDividedDifference_eq_loewnerKernel_of_hermiteMatches
      hval hderiv i j]

/-!
### Explicit Hermite polynomial surrogate on finite node sets

The next layer removes the existence of the Hermite node-matching polynomial
from the input.  We use the standard Lagrange basis and the usual first-order
Hermite basis polynomials.
-/

/-- Lagrange basis polynomial for the finite node family `x`. -/
def lagrangeBasis {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase k,
    Polynomial.C ((x k - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))

/-- Lagrange basis evaluates to the Kronecker delta on an injective node set. -/
lemma lagrangeBasis_eval
    {n : ℕ} {x : Fin n → ℝ} (hinj : Function.Injective x)
    (k i : Fin n) :
    (lagrangeBasis x k).eval (x i) = if i = k then 1 else 0 := by
  classical
  by_cases hik : i = k
  · subst i
    rw [lagrangeBasis, Polynomial.eval_prod (s := Finset.univ.erase k)]
    rw [if_pos rfl]
    refine Finset.prod_eq_one (s := Finset.univ.erase k)
      (f := fun j : Fin n =>
        (Polynomial.C ((x k - x j)⁻¹) *
          (Polynomial.X - Polynomial.C (x j))).eval (x k)) ?_
    intro j hj
    have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
    have hxne : x k - x j ≠ 0 := by
      exact sub_ne_zero.mpr (fun hxEq => hjne ((hinj hxEq).symm))
    simp [Polynomial.eval_mul, Polynomial.eval_sub, hxne]
  · rw [lagrangeBasis, Polynomial.eval_prod (s := Finset.univ.erase k)]
    have hi_mem : i ∈ Finset.univ.erase k := by
      exact Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
    have hzero :
        (Polynomial.C ((x k - x i)⁻¹) * (Polynomial.X - Polynomial.C (x i))).eval
          (x i) = 0 := by
      simp [Polynomial.eval_mul, Polynomial.eval_sub]
    rw [if_neg hik]
    exact Finset.prod_eq_zero hi_mem hzero

/-- The Hermite value basis polynomial attached to node `k`. -/
def hermiteValueBasis {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ[X] :=
  (1 - Polynomial.C
    (2 * (lagrangeBasis x k).derivative.eval (x k)) *
      (Polynomial.X - Polynomial.C (x k))) *
    (lagrangeBasis x k) ^ 2

/-- The Hermite derivative basis polynomial attached to node `k`. -/
def hermiteDerivBasis {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ[X] :=
  (Polynomial.X - Polynomial.C (x k)) * (lagrangeBasis x k) ^ 2

/-- Value of the Hermite value basis on the node set. -/
lemma hermiteValueBasis_eval
    {n : ℕ} {x : Fin n → ℝ} (hinj : Function.Injective x)
    (k i : Fin n) :
    (hermiteValueBasis x k).eval (x i) = if i = k then 1 else 0 := by
  classical
  have hL := lagrangeBasis_eval (x := x) hinj k i
  by_cases hik : i = k
  · subst i
    simp [hermiteValueBasis, hL]
  · simp [hermiteValueBasis, hL, hik]

/-- Value of the Hermite derivative basis on the node set. -/
lemma hermiteDerivBasis_eval
    {n : ℕ} {x : Fin n → ℝ} (hinj : Function.Injective x)
    (k i : Fin n) :
    (hermiteDerivBasis x k).eval (x i) = 0 := by
  classical
  have hL := lagrangeBasis_eval (x := x) hinj k i
  by_cases hik : i = k
  · subst i
    simp [hermiteDerivBasis, hL]
  · simp [hermiteDerivBasis, hL, hik]

/-- Formal derivative of the Hermite value basis vanishes on all nodes. -/
lemma hermiteValueBasis_derivative_eval
    {n : ℕ} {x : Fin n → ℝ} (hinj : Function.Injective x)
    (k i : Fin n) :
    (hermiteValueBasis x k).derivative.eval (x i) = 0 := by
  classical
  have hL := lagrangeBasis_eval (x := x) hinj k i
  by_cases hik : i = k
  · subst i
    simp [hermiteValueBasis, Polynomial.derivative_mul,
      Polynomial.derivative_pow, hL]
  · simp [hermiteValueBasis, Polynomial.derivative_mul,
      Polynomial.derivative_pow, hL, hik]

/-- Formal derivative of the Hermite derivative basis is the Kronecker delta. -/
lemma hermiteDerivBasis_derivative_eval
    {n : ℕ} {x : Fin n → ℝ} (hinj : Function.Injective x)
    (k i : Fin n) :
    (hermiteDerivBasis x k).derivative.eval (x i) =
      if i = k then 1 else 0 := by
  classical
  have hL := lagrangeBasis_eval (x := x) hinj k i
  by_cases hik : i = k
  · subst i
    simp [hermiteDerivBasis, Polynomial.derivative_mul,
      Polynomial.derivative_pow, hL]
  · simp [hermiteDerivBasis, Polynomial.derivative_mul,
      Polynomial.derivative_pow, hL, hik]

/-- The explicit Hermite polynomial surrogate for values and first derivatives. -/
def hermiteInterpolatingPolynomial
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ[X] :=
  ∑ k : Fin n,
    (Polynomial.C (f (x k)) * hermiteValueBasis x k +
      Polynomial.C (deriv f (x k)) * hermiteDerivBasis x k)

/-- The explicit Hermite surrogate matches the function values on the nodes. -/
lemma hermiteInterpolatingPolynomial_valueMatches
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    hermiteNodeValueMatches f
      (hermiteInterpolatingPolynomial f x) x := by
  classical
  intro i
  simp only [hermiteInterpolatingPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    (∑ k : Fin n,
        (f (x k) * (hermiteValueBasis x k).eval (x i) +
          deriv f (x k) * (hermiteDerivBasis x k).eval (x i))) =
        ∑ k : Fin n, if k = i then f (x i) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      by_cases hki : k = i
      · subst k
        simp [hermiteValueBasis_eval (x := x) hinj i i,
          hermiteDerivBasis_eval (x := x) hinj i i]
      · have hik : i ≠ k := fun h => hki h.symm
        simp [hermiteValueBasis_eval (x := x) hinj k i,
          hermiteDerivBasis_eval (x := x) hinj k i, hik, hki]
    _ = f (x i) := by
      simp

/-- The explicit Hermite surrogate matches the function derivatives on the nodes. -/
lemma hermiteInterpolatingPolynomial_derivMatches
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    hermiteNodeDerivMatches f
      (hermiteInterpolatingPolynomial f x) x := by
  classical
  intro i
  rw [Polynomial.deriv]
  simp only [hermiteInterpolatingPolynomial, Polynomial.derivative_sum,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add, Polynomial.eval_finset_sum, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  calc
    (∑ k : Fin n,
        (f (x k) * (hermiteValueBasis x k).derivative.eval (x i) +
          deriv f (x k) * (hermiteDerivBasis x k).derivative.eval (x i))) =
        ∑ k : Fin n, if k = i then deriv f (x i) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      by_cases hki : k = i
      · subst k
        simp [hermiteValueBasis_derivative_eval (x := x) hinj i i,
          hermiteDerivBasis_derivative_eval (x := x) hinj i i]
      · have hik : i ≠ k := fun h => hki h.symm
        simp [hermiteValueBasis_derivative_eval (x := x) hinj k i,
          hermiteDerivBasis_derivative_eval (x := x) hinj k i, hik, hki]
    _ = deriv f (x i) := by
      simp

/-- Scalar Hermite remainder after subtracting the finite-node interpolant. -/
def hermiteRemainderFunction
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  f t - (hermiteInterpolatingPolynomial f x).eval t

/-- The explicit Hermite remainder vanishes at each interpolation node. -/
lemma hermiteRemainderFunction_node_eq_zero
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) (i : Fin n) :
    hermiteRemainderFunction f x (x i) = 0 := by
  have hval :=
    hermiteInterpolatingPolynomial_valueMatches (f := f) (x := x) hinj i
  simp [hermiteRemainderFunction, hval]

/-- The explicit Hermite remainder has zero derivative at each interpolation node. -/
lemma hermiteRemainderFunction_hasDerivAt_node
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1))
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (i : Fin n) :
    HasDerivAt (hermiteRemainderFunction f x) 0 (x i) := by
  let p := hermiteInterpolatingPolynomial f x
  have hfAt : DifferentiableAt ℝ f (x i) :=
    hf.differentiableAt (IsOpen.mem_nhds isOpen_Ioo (hx i))
  have hpDeriv : p.derivative.eval (x i) = deriv f (x i) := by
    rw [← Polynomial.deriv p]
    exact hermiteInterpolatingPolynomial_derivMatches (f := f) (x := x) hinj i
  have hpAt : HasDerivAt (fun t : ℝ => p.eval t) (deriv f (x i)) (x i) := by
    simpa [hpDeriv] using p.hasDerivAt (x i)
  have hsub : HasDerivAt (fun t : ℝ => f t - p.eval t)
      (deriv f (x i) - deriv f (x i)) (x i) :=
    hfAt.hasDerivAt.sub hpAt
  simpa [hermiteRemainderFunction, p] using hsub

/-- The explicit Hermite remainder has zero derivative at each interpolation node. -/
lemma hermiteRemainderFunction_deriv_node_eq_zero
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1))
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (i : Fin n) :
    deriv (hermiteRemainderFunction f x) (x i) = 0 :=
  (hermiteRemainderFunction_hasDerivAt_node
    (f := f) (x := x) hf hx hinj i).deriv

/--
At each interpolation node, the scalar Hermite remainder is little-o of the
distance to that node.  This is the scalar input for the later CFC norm
estimate.
-/
lemma hermiteRemainderFunction_isLittleO_node
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1))
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (i : Fin n) :
    (fun t : ℝ => hermiteRemainderFunction f x t) =o[𝓝 (x i)]
      (fun t : ℝ => t - x i) := by
  let r := hermiteRemainderFunction f x
  have hder : HasDerivAt r 0 (x i) := by
    exact hermiteRemainderFunction_hasDerivAt_node
      (f := f) (x := x) hf hx hinj i
  have hlittle :=
    (hasDerivAt_iff_isLittleO.mp hder)
  have hnode : r (x i) = 0 :=
    hermiteRemainderFunction_node_eq_zero (f := f) (x := x) hinj i
  simpa [r, hnode] using hlittle

/--
The scalar little-o statement in the concrete estimate form used by the CFC
norm bridge.  Near each node, the Hermite remainder is bounded by an arbitrary
multiple of the node distance.
-/
lemma hermiteRemainderFunction_eventually_norm_le_mul_node
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1))
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (i : Fin n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝 (x i),
      ‖hermiteRemainderFunction f x t‖ ≤ η * ‖t - x i‖ :=
  (hermiteRemainderFunction_isLittleO_node
    (f := f) (x := x) hf hx hinj i).bound hη

/--
The raw coefficient quotient error is exactly the normalized raw quotient of
the scalar Hermite remainder.  This keeps the CFC estimate focused on one
function, namely `f - p`.
-/
lemma hermiteRemainder_rawQuotient_error_eq
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ}
    {ε : ℝ} {i j : Fin n}
    (hFA : ContinuousOn (fun t : ℝ => f t - f 0)
      (quasispectrum ℝ (diagonalPerturbation x u ε)))
    (hFD : ContinuousOn (fun t : ℝ => f t - f 0)
      (quasispectrum ℝ (diagonalMatrix x))) :
    diagonalCFCRawEntrywiseVariationQuotient f x u ε i j -
        polynomialRawEntrywiseVariationQuotient
          (hermiteInterpolatingPolynomial f x) x u ε i j =
      diagonalCFCRawEntrywiseVariationQuotient
        (hermiteRemainderFunction f x) x u ε i j := by
  let p := hermiteInterpolatingPolynomial f x
  let A := diagonalPerturbation x u ε
  let D := diagonalMatrix x
  let F : ℝ → ℝ := fun t => f t - f 0
  let P : ℝ → ℝ := fun t => p.eval t - p.eval 0
  let R : ℝ → ℝ := fun t => hermiteRemainderFunction f x t -
    hermiteRemainderFunction f x 0
  have hA : cfcₙ F A - cfcₙ P A = cfcₙ R A := by
    rw [← cfcₙ_sub F P A (hf := hFA)]
    exact cfcₙ_congr fun t _ht => by
      simp [F, P, R, hermiteRemainderFunction, p]
      ring
  have hD : cfcₙ F D - cfcₙ P D = cfcₙ R D := by
    rw [← cfcₙ_sub F P D (hf := hFD)]
    exact cfcₙ_congr fun t _ht => by
      simp [F, P, R, hermiteRemainderFunction, p]
      ring
  simp only [polynomialRawEntrywiseVariationQuotient,
    diagonalCFCRawEntrywiseVariationQuotient]
  change
      (ε⁻¹ : ℝ) • ((cfcₙ F A - cfcₙ F D) i j) -
          (ε⁻¹ : ℝ) • ((cfcₙ P A - cfcₙ P D) i j) =
        (ε⁻¹ : ℝ) • ((cfcₙ R A - cfcₙ R D) i j)
  have hentry :
      (cfcₙ F A - cfcₙ F D) i j - (cfcₙ P A - cfcₙ P D) i j =
        (cfcₙ R A - cfcₙ R D) i j := by
    have hAD : (cfcₙ F A - cfcₙ P A) i j = (cfcₙ R A) i j := by
      simpa [Matrix.sub_apply] using congr_fun (congr_fun hA i) j
    have hDD : (cfcₙ F D - cfcₙ P D) i j = (cfcₙ R D) i j := by
      simpa [Matrix.sub_apply] using congr_fun (congr_fun hD i) j
    simp only [Matrix.sub_apply] at hAD hDD ⊢
    calc
      cfcₙ F A i j - cfcₙ F D i j - (cfcₙ P A i j - cfcₙ P D i j) =
          (cfcₙ F A i j - cfcₙ P A i j) -
            (cfcₙ F D i j - cfcₙ P D i j) := by
        ring
      _ = cfcₙ R A i j - cfcₙ R D i j := by
        rw [hAD, hDD]
  calc
    (ε⁻¹ : ℝ) • ((cfcₙ F A - cfcₙ F D) i j) -
        (ε⁻¹ : ℝ) • ((cfcₙ P A - cfcₙ P D) i j) =
      (ε⁻¹ : ℝ) •
        ((cfcₙ F A - cfcₙ F D) i j - (cfcₙ P A - cfcₙ P D) i j) := by
        module
    _ = (ε⁻¹ : ℝ) • ((cfcₙ R A - cfcₙ R D) i j) := by
      rw [hentry]

/-- Normalized Hermite remainder, the scalar function used by `cfcₙ`. -/
def hermiteNormalizedRemainderFunction
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  hermiteRemainderFunction f x t - hermiteRemainderFunction f x 0

/-- The normalized Hermite remainder vanishes at zero, as required by `cfcₙ`. -/
lemma hermiteNormalizedRemainderFunction_zero
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) :
    hermiteNormalizedRemainderFunction f x 0 = 0 := by
  simp [hermiteNormalizedRemainderFunction]

/-- The Hermite remainder is zero on the spectrum of the diagonal node matrix. -/
lemma hermiteRemainderFunction_eq_zero_on_diagonal_spectrum
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    Set.EqOn (hermiteRemainderFunction f x) (fun _ : ℝ => 0)
      (spectrum ℝ (diagonalMatrix x)) := by
  intro y hy
  rw [← spectrum.preimage_algebraMap ℂ] at hy
  simp only [Set.mem_preimage] at hy
  rw [diagonalMatrix, spectrum_diagonal] at hy
  rcases hy with ⟨i, hi⟩
  have hyeq : y = x i := Complex.ofReal_injective hi.symm
  simp [hyeq, hermiteRemainderFunction_node_eq_zero (f := f) (x := x) hinj i]

/-- Applying the Hermite remainder to the diagonal node matrix gives zero. -/
lemma hermiteRemainderFunction_cfc_diagonal_eq_zero
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    cfc (hermiteRemainderFunction f x) (diagonalMatrix x) = 0 := by
  have hEq :=
    hermiteRemainderFunction_eq_zero_on_diagonal_spectrum
      (f := f) (x := x) hinj
  rw [cfc_congr hEq]
  simp [cfc_const_zero]

/--
The same diagonal-zero identity in the `CStarMatrix` copy.  This is only a
transport lemma: it does not prove any new spectral estimate.
-/
lemma hermiteRemainderFunction_cstarCFC_diagonal_eq_zero
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    cfc (hermiteRemainderFunction f x)
      (cStarDiagonalMatrix x) = 0 := by
  simpa [cStarDiagonalMatrix] using
    congrArg CStarMatrix.ofMatrix
      (hermiteRemainderFunction_cfc_diagonal_eq_zero
        (f := f) (x := x) hinj)

/--
For Hermite remainders, the normalized non-unital quotient reduces to ordinary
unital CFC of the unnormalized scalar remainder at the perturbed matrix.  The
constant normalization cancels, and the diagonal term is zero by Hermite node
matching.
-/
lemma hermiteNormalizedRemainder_cfcₙ_sub_diagonal_eq_cfc_remainder
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {ε : ℝ}
    (hinj : Function.Injective x)
    (hNA : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (diagonalPerturbation x u ε)))
    (hND : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (diagonalMatrix x)))
    (hRA : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (diagonalPerturbation x u ε)))
    (hRD : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (diagonalMatrix x))) :
    cfcₙ (hermiteNormalizedRemainderFunction f x)
        (diagonalPerturbation x u ε) -
      cfcₙ (hermiteNormalizedRemainderFunction f x)
        (diagonalMatrix x) =
      cfc (hermiteRemainderFunction f x)
        (diagonalPerturbation x u ε) := by
  let r : ℝ → ℝ := hermiteRemainderFunction f x
  let rn : ℝ → ℝ := hermiteNormalizedRemainderFunction f x
  let A := diagonalPerturbation x u ε
  let D := diagonalMatrix x
  have hAn : cfcₙ rn A = cfc rn A := by
    exact cfcₙ_eq_cfc (a := A) (hf := hNA)
      (hf0 := hermiteNormalizedRemainderFunction_zero f x)
  have hDn : cfcₙ rn D = cfc rn D := by
    exact cfcₙ_eq_cfc (a := D) (hf := hND)
      (hf0 := hermiteNormalizedRemainderFunction_zero f x)
  have hAsub :
      cfc rn A =
        cfc r A - cfc (fun _ : ℝ => r 0) A := by
    rw [← cfc_sub r (fun _ : ℝ => r 0) A (hf := hRA)]
    exact cfc_congr fun t _ht => by
      simp [rn, r, hermiteNormalizedRemainderFunction]
  have hDsub :
      cfc rn D =
        cfc r D - cfc (fun _ : ℝ => r 0) D := by
    rw [← cfc_sub r (fun _ : ℝ => r 0) D (hf := hRD)]
    exact cfc_congr fun t _ht => by
      simp [rn, r, hermiteNormalizedRemainderFunction]
  have hDzero : cfc r D = 0 := by
    simpa [r, D] using
      hermiteRemainderFunction_cfc_diagonal_eq_zero (f := f) (x := x) hinj
  rw [hAn, hDn, hAsub, hDsub, hDzero]
  rw [cfc_const (r 0) (diagonalPerturbation x u ε)
      (diagonalPerturbation_isSelfAdjoint x u ε),
    cfc_const (r 0) (diagonalMatrix x)
      (diagonalMatrix_isSelfAdjoint x)]
  simp [A, r]

/--
The Hermite-remainder raw quotient in the `CStarMatrix` copy, where the
isometric CFC norm API is available.  This is the norm-estimate bridge for the
plain matrix quotient used in the preceding algebraic reductions.
-/
def hermiteRemainderCStarRawEntrywiseVariationQuotient
    (f : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) : ℂ :=
  (ε⁻¹ : ℝ) •
    ((cfcₙ (hermiteNormalizedRemainderFunction f x)
        (cStarDiagonalPerturbation x u ε) -
      cfcₙ (hermiteNormalizedRemainderFunction f x)
        (cStarDiagonalMatrix x)) i j)

/--
The Hermite-remainder raw quotient in the `CStarMatrix` copy is definitionally
the same coefficient as the plain matrix raw quotient.  The `CStarMatrix` layer
is used only to access the CFC norm API.
-/
lemma hermiteRemainderCStarRawEntrywiseVariationQuotient_eq_plain
    {f : ℝ → ℝ} {n : ℕ} (x : Fin n → ℝ) (u : Fin n → ℂ)
    (ε : ℝ) (i j : Fin n) :
    hermiteRemainderCStarRawEntrywiseVariationQuotient f x u ε i j =
      diagonalCFCRawEntrywiseVariationQuotient
        (hermiteRemainderFunction f x) x u ε i j := by
  rfl

/--
For Hermite remainders in the `CStarMatrix` copy, the normalized non-unital CFC
difference reduces to ordinary CFC of the unnormalized scalar remainder at the
perturbed matrix, once the diagonal remainder term has been eliminated.
-/
lemma hermiteNormalizedRemainder_cstarCFCₙ_sub_diagonal_eq_cfc_remainder_of_diagonal_zero
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {ε : ℝ}
    (hNA : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (cStarDiagonalPerturbation x u ε)))
    (hND : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (cStarDiagonalMatrix x)))
    (hRA : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (cStarDiagonalPerturbation x u ε)))
    (hRD : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (cStarDiagonalMatrix x)))
    (hDzero :
      cfc (hermiteRemainderFunction f x) (cStarDiagonalMatrix x) = 0) :
    cfcₙ (hermiteNormalizedRemainderFunction f x)
        (cStarDiagonalPerturbation x u ε) -
      cfcₙ (hermiteNormalizedRemainderFunction f x)
        (cStarDiagonalMatrix x) =
      cfc (hermiteRemainderFunction f x)
        (cStarDiagonalPerturbation x u ε) := by
  let r : ℝ → ℝ := hermiteRemainderFunction f x
  let rn : ℝ → ℝ := hermiteNormalizedRemainderFunction f x
  let A := cStarDiagonalPerturbation x u ε
  let D := cStarDiagonalMatrix x
  have hAn : cfcₙ rn A = cfc rn A := by
    exact cfcₙ_eq_cfc (a := A) (hf := hNA)
      (hf0 := hermiteNormalizedRemainderFunction_zero f x)
  have hDn : cfcₙ rn D = cfc rn D := by
    exact cfcₙ_eq_cfc (a := D) (hf := hND)
      (hf0 := hermiteNormalizedRemainderFunction_zero f x)
  have hAsub :
      cfc rn A =
        cfc r A - cfc (fun _ : ℝ => r 0) A := by
    rw [← cfc_sub r (fun _ : ℝ => r 0) A (hf := hRA)]
    exact cfc_congr fun t _ht => by
      simp [rn, r, hermiteNormalizedRemainderFunction]
  have hDsub :
      cfc rn D =
        cfc r D - cfc (fun _ : ℝ => r 0) D := by
    rw [← cfc_sub r (fun _ : ℝ => r 0) D (hf := hRD)]
    exact cfc_congr fun t _ht => by
      simp [rn, r, hermiteNormalizedRemainderFunction]
  have hDzero' : cfc r D = 0 := by
    simpa [r, D] using hDzero
  have hDsa : IsSelfAdjoint D := by
    change IsSelfAdjoint (cStarDiagonalMatrix x)
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint x).star_eq
    simpa [cStarDiagonalMatrix] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => CStarMatrix.ofMatrix M) h
  have hconstA :
      cfc (fun _ : ℝ => r 0) A =
        (algebraMap ℝ (CStarMatrix (Fin n) (Fin n) ℂ)) (r 0) := by
    exact cfc_const (r 0) A (by
      simpa [A] using cStarDiagonalPerturbation_isSelfAdjoint x u ε)
  have hconstD :
      cfc (fun _ : ℝ => r 0) D =
        (algebraMap ℝ (CStarMatrix (Fin n) (Fin n) ℂ)) (r 0) := by
    exact cfc_const (r 0) D hDsa
  rw [hAn, hDn, hAsub, hDsub, hDzero']
  rw [hconstA, hconstD]
  simp [A, r]

/--
A scalar bound for the Hermite remainder on the real spectrum controls every
matrix coefficient of its `CStarMatrix` CFC.
-/
lemma hermiteRemainder_cstarCFC_entry_norm_le_of_spectrum_bound
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {ε c : ℝ}
    {i j : Fin n}
    (hc : 0 ≤ c)
    (hbound :
      ∀ y ∈ spectrum ℝ (cStarDiagonalPerturbation x u ε),
        ‖hermiteRemainderFunction f x y‖ ≤ c) :
    ‖(cfc (hermiteRemainderFunction f x)
        (cStarDiagonalPerturbation x u ε)) i j‖ ≤ c := by
  have hnorm :
      ‖cfc (hermiteRemainderFunction f x)
        (cStarDiagonalPerturbation x u ε)‖ ≤ c :=
    norm_cfc_le (a := cStarDiagonalPerturbation x u ε) hc hbound
  exact (CStarMatrix.norm_entry_le_norm
    (M := cfc (hermiteRemainderFunction f x)
      (cStarDiagonalPerturbation x u ε))).trans hnorm

/--
The `CStarMatrix` CFC norm estimate, divided by a positive perturbation
parameter, bounds the Hermite-remainder raw quotient.  The diagonal-zero
assumption is the cluster/spectral compatibility datum, so this lemma is
deliberately not stated as a closed remainder theorem; the closed estimate is
`diagonalCFCHermiteRemainderEstimateInput_of_differentiable` in
`HermiteApproximation.lean`.
-/
lemma hermiteRemainder_cstarRawQuotient_norm_le_of_spectrum_bound
    {f : ℝ → ℝ} {n : ℕ} {x : Fin n → ℝ} {u : Fin n → ℂ} {ε c : ℝ}
    {i j : Fin n}
    (hε : 0 < ε) (hc : 0 ≤ c)
    (hNA : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (cStarDiagonalPerturbation x u ε)))
    (hND : ContinuousOn (hermiteNormalizedRemainderFunction f x)
      (quasispectrum ℝ (cStarDiagonalMatrix x)))
    (hRA : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (cStarDiagonalPerturbation x u ε)))
    (hRD : ContinuousOn (hermiteRemainderFunction f x)
      (spectrum ℝ (cStarDiagonalMatrix x)))
    (hDzero :
      cfc (hermiteRemainderFunction f x) (cStarDiagonalMatrix x) = 0)
    (hbound :
      ∀ y ∈ spectrum ℝ (cStarDiagonalPerturbation x u ε),
        ‖hermiteRemainderFunction f x y‖ ≤ c) :
    ‖hermiteRemainderCStarRawEntrywiseVariationQuotient
        f x u ε i j‖ ≤ ε⁻¹ * c := by
  have hsub :=
    hermiteNormalizedRemainder_cstarCFCₙ_sub_diagonal_eq_cfc_remainder_of_diagonal_zero
      (f := f) (x := x) (u := u) (ε := ε) hNA hND hRA hRD hDzero
  have hentry :
      ((cfcₙ (hermiteNormalizedRemainderFunction f x)
          (cStarDiagonalPerturbation x u ε) -
        cfcₙ (hermiteNormalizedRemainderFunction f x)
          (cStarDiagonalMatrix x)) i j) =
        (cfc (hermiteRemainderFunction f x)
          (cStarDiagonalPerturbation x u ε)) i j := by
    simpa using congr_fun (congr_fun hsub i) j
  have hcoeff :
      ‖(cfc (hermiteRemainderFunction f x)
          (cStarDiagonalPerturbation x u ε)) i j‖ ≤ c :=
    hermiteRemainder_cstarCFC_entry_norm_le_of_spectrum_bound
      (f := f) (x := x) (u := u) (ε := ε) (i := i) (j := j) hc hbound
  rw [hermiteRemainderCStarRawEntrywiseVariationQuotient]
  change
      ‖(ε⁻¹ : ℝ) •
        ((cfcₙ (hermiteNormalizedRemainderFunction f x)
              (cStarDiagonalPerturbation x u ε) -
            cfcₙ (hermiteNormalizedRemainderFunction f x)
              (cStarDiagonalMatrix x)) i j)‖ ≤ ε⁻¹ * c
  rw [hentry, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  exact mul_le_mul_of_nonneg_left hcoeff (inv_nonneg.mpr hε.le)
end

end Quantum.TraceInequality.Loewner
