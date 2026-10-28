/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebTrace.Monotonicity
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Klein's inequality via Peierls and supporting lines

This file formalizes a generalization of the inequality (2.13) of Carlen 2010. The formal proof
uses the Peierls inequality and the scalar supporting-line inequality, not Carlen's directional
derivative proof through convexity of `t |-> Tr[f (B + tC)]`.
-/

namespace KleinInequality

universe u

open LownerHeinzTheorem
open LiebAndoTrace
open scoped BigOperators

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [CompleteSpace H]
variable [FiniteDimensional Complex H] [Nontrivial H]

private lemma peierls_unitary_row_normSq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (i : n) :
    (Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k)) = 1 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self U) i) i
  have hreal := congrArg Complex.re h
  simpa [Matrix.mul_apply, Complex.normSq_apply] using hreal

private lemma peierls_unitary_col_normSq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (j : n) :
    (Finset.univ.sum fun i : n => Complex.normSq ((U : Matrix n n ℂ) i j)) = 1 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self U) j) j
  have hreal := congrArg Complex.re h
  simpa [Matrix.mul_apply, Complex.normSq_apply] using hreal

private lemma peierls_conjugate_diagonal_apply_re {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (d : n -> ℝ) (i : n) :
    Complex.re (((U : Matrix n n ℂ) *
      Matrix.diagonal (fun k : n => (d k : ℂ)) * star (U : Matrix n n ℂ)) i i) =
      Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * d k := by
  simp only [Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.star_apply, RCLike.star_def,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    Complex.conj_re, Complex.mul_im, zero_add, Complex.conj_im, mul_neg, sub_neg_eq_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply]
  ring

private lemma peierls_conjugate_diagonal_trace_re {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (d : n -> ℝ) :
    Complex.re (Matrix.trace ((U : Matrix n n ℂ) *
      Matrix.diagonal (fun k : n => (d k : ℂ)) * star (U : Matrix n n ℂ))) =
      Finset.univ.sum d := by
  calc
    Complex.re (Matrix.trace ((U : Matrix n n ℂ) *
        Matrix.diagonal (fun k : n => (d k : ℂ)) * star (U : Matrix n n ℂ))) =
        Complex.re (Matrix.trace (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) *
          Matrix.diagonal (fun k : n => (d k : ℂ)))) := by
      rw [Matrix.trace_mul_cycle]
    _ = Complex.re (Matrix.trace (Matrix.diagonal (fun k : n => (d k : ℂ)))) := by
      rw [Unitary.coe_star_mul_self U, one_mul]
    _ = Finset.univ.sum d := by
      simp [Matrix.trace]

/-- Matrix Peierls inequality for a Hermitian matrix. -/
/- Matrix Peierls inequality -/
/- Statement: Let $M$ be a Hermitian matrix over $\mathbb{C}$ indexed by a finite
    type $n$, and let $f : \mathbb{R}\to\mathbb{R}$ be convex. Then the sum of
    $f$ applied to the real diagonal entries of $M$ is bounded above by the real part of
    the trace of the explicit Hermitian matrix functional calculus $f(M)$. -/
/- Proof: Diagonalize $M$ as $U\operatorname{diag}(\lambda_k)U^*$ using the unitary
    spectral theorem for Hermitian matrices. For a fixed row $i$, the numbers
    $|U_{ik}|^2$ are nonnegative and sum to $1$, and the real part of the $i$th diagonal entry is
    $\sum_k |U_{ik}|^2\lambda_k$. Convexity and Jensen's finite-sum inequality give the
    row estimate
    \[
      f(\operatorname{Re} M_{ii})
        \le \sum_k |U_{ik}|^2 f(\lambda_k).
    \]
    Summing in $i$ and using the column normalization of the unitary matrix collapses the
    double sum to $\sum_k f(\lambda_k)$. The trace of
    $U\operatorname{diag}(f(\lambda_k))U^*$ is the same sum by cyclicity of matrix trace,
    proving the stated matrix inequality. -/
private lemma peierls_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ -> ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hf : ConvexOn ℝ Set.univ f) :
    (Finset.univ.sum fun i : n => f (Complex.re (A i i))) <=
      Complex.re (Matrix.trace (hA.cfc f)) := by
  let U := hA.eigenvectorUnitary
  let lam := hA.eigenvalues
  have hdiagA : ∀ i : n,
      Complex.re (A i i) =
        Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * lam k := by
    intro i
    rw [hA.spectral_theorem]
    change Complex.re (((U : Matrix n n ℂ) *
      Matrix.diagonal (fun k : n => ((lam k : ℝ) : ℂ)) * star (U : Matrix n n ℂ)) i i) =
        Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * lam k
    exact peierls_conjugate_diagonal_apply_re U lam i
  have htrace :
      Complex.re (Matrix.trace (hA.cfc f)) =
        Finset.univ.sum fun k : n => f (lam k) := by
    change Complex.re (Matrix.trace ((U : Matrix n n ℂ) *
      Matrix.diagonal (fun k : n => ((f (lam k) : ℝ) : ℂ)) * star (U : Matrix n n ℂ))) =
        Finset.univ.sum fun k : n => f (lam k)
    exact peierls_conjugate_diagonal_trace_re U (fun k : n => f (lam k))
  have hrow : ∀ i : n,
      f (Complex.re (A i i)) <=
        Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * f (lam k) := by
    intro i
    rw [hdiagA i]
    have hj := hf.map_sum_le
      (t := Finset.univ)
      (w := fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k))
      (p := lam)
      (by intro k hk; exact Complex.normSq_nonneg _)
      (by simpa using peierls_unitary_row_normSq_sum U i)
      (by intro k hk; exact Set.mem_univ _)
    simpa [smul_eq_mul] using hj
  calc
    (Finset.univ.sum fun i : n => f (Complex.re (A i i))) <=
        Finset.univ.sum fun i : n =>
          Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * f (lam k) := by
      exact Finset.sum_le_sum fun i hi => hrow i
    _ = Finset.univ.sum fun k : n => f (lam k) := by
      calc
        (Finset.univ.sum fun i : n =>
            Finset.univ.sum fun k : n => Complex.normSq ((U : Matrix n n ℂ) i k) * f (lam k)) =
            Finset.univ.sum fun k : n =>
              Finset.univ.sum fun i : n => Complex.normSq ((U : Matrix n n ℂ) i k) * f (lam k) := by
          exact Finset.sum_comm
        _ = Finset.univ.sum fun k : n =>
              (Finset.univ.sum fun i : n =>
                Complex.normSq ((U : Matrix n n ℂ) i k)) * f (lam k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_mul]
        _ = Finset.univ.sum fun k : n => f (lam k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [peierls_unitary_col_normSq_sum U k]
          ring
    _ = Complex.re (Matrix.trace (hA.cfc f)) := htrace.symm

private noncomputable def peierlsCLMToMatrixOrthonormal {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {I : Type*} [Fintype I] [DecidableEq I] [FiniteDimensional ℂ E]
    (u : OrthonormalBasis I ℂ E) : (E →L[ℂ] E) →⋆ₐ[ℂ] Matrix I I ℂ where
  toFun T := LinearMap.toMatrixOrthonormal u (T : E →ₗ[ℂ] E)
  map_one' := by
    simp
  map_mul' S T := by
    simpa using
      (map_mul (LinearMap.toMatrixOrthonormal u) (S : E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E))
  map_zero' := by
    simp
  map_add' S T := by
    simp
  commutes' c := by
    change LinearMap.toMatrixOrthonormal u
        ((algebraMap ℂ (E →L[ℂ] E) c : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      algebraMap ℂ (Matrix I I ℂ) c
    rw [show ((algebraMap ℂ (E →L[ℂ] E) c : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        (algebraMap ℂ (E →ₗ[ℂ] E) c) by
      ext x
      simp]
    exact AlgHomClass.commutes (LinearMap.toMatrixOrthonormal u) c
  map_star' T := by
    simpa using (map_star (LinearMap.toMatrixOrthonormal u) (T : E →ₗ[ℂ] E))

private noncomputable def peierlsCLMToMatrixOrthonormalReal {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {I : Type*} [Fintype I] [DecidableEq I] [FiniteDimensional ℂ E]
    (u : OrthonormalBasis I ℂ E) : (E →L[ℂ] E) →⋆ₐ[ℝ] Matrix I I ℂ where
  toFun T := LinearMap.toMatrixOrthonormal u (T : E →ₗ[ℂ] E)
  map_one' := by
    simp
  map_mul' S T := by
    simpa using
      (map_mul (LinearMap.toMatrixOrthonormal u) (S : E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E))
  map_zero' := by
    simp
  map_add' S T := by
    simp
  commutes' r := by
    haveI : IsScalarTower ℝ ℂ E := RestrictScalars.isScalarTower ℝ ℂ E
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [LinearMap.toMatrixOrthonormal_apply_apply]
      rw [Matrix.algebraMap_matrix_apply]
      change inner ℂ (u i) ((r • (1 : E →L[ℂ] E)) (u i)) =
        if i = i then (r : ℂ) else 0
      rw [ContinuousLinearMap.smul_apply]
      change inner ℂ (u i) ((r : ℂ) • u i) = if i = i then (r : ℂ) else 0
      rw [inner_smul_right, u.inner_eq_one]
      simp
    · rw [Algebra.algebraMap_eq_smul_one]
      simp only [LinearMap.toMatrixOrthonormal_apply_apply]
      rw [Matrix.algebraMap_matrix_apply]
      change inner ℂ (u i) ((r • (1 : E →L[ℂ] E)) (u j)) =
        if i = j then (r : ℂ) else 0
      rw [ContinuousLinearMap.smul_apply]
      change inner ℂ (u i) ((r : ℂ) • u j) = if i = j then (r : ℂ) else 0
      rw [inner_smul_right, u.inner_eq_zero hij]
      simp [hij]
  map_star' T := by
    simpa using (map_star (LinearMap.toMatrixOrthonormal u) (T : E →ₗ[ℂ] E))

open scoped Matrix.Norms.L2Operator in
/-- Matrix representation commutes with the real continuous functional calculus. -/
/- Matrix representation of the real continuous functional calculus -/
/- Statement: Let $E$ be a finite-dimensional complex Hilbert space, let
    $A \in L(E)$ be self-adjoint, and let $u$ be a finite orthonormal basis. If
    $f$ is continuous on the real spectrum of $A$, then the matrix of $f(A)$ in the basis
    $u$ is the real continuous functional calculus of the matrix of $A$. -/
/- Proof: The assignment sending a bounded operator to its matrix in the orthonormal
    basis $u$ is a real star-algebra homomorphism. It is continuous, since it has the same
    underlying map as the complex-linear matrix representation and the spaces are finite
    dimensional. Applying the functoriality theorem `StarAlgHomClass.map_cfc` for continuous
    functional calculus to this homomorphism, the self-adjoint operator $A$, and the continuous
    function $f$ gives exactly the stated identity. -/
private lemma peierls_toMatrix_cfcR {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E]
    {I : Type*} [Fintype I] [DecidableEq I]
    (u : OrthonormalBasis I ℂ E) (f : ℝ -> ℝ) (A : (E →L[ℂ] E))
    (hA : IsSelfAdjoint A) (hf : ContinuousOn f (spectrum ℝ A)) :
    peierlsCLMToMatrixOrthonormalReal u (cfcR (ℋ := E) f A) =
      letI : CStarAlgebra (Matrix I I ℂ) := {}
      cfc (R := ℝ) (p := IsSelfAdjoint) f (peierlsCLMToMatrixOrthonormalReal u A) := by
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  have hφ : Continuous (peierlsCLMToMatrixOrthonormalReal u) := by
    have hφC : Continuous (peierlsCLMToMatrixOrthonormal u) := by
      exact LinearMap.continuous_of_finiteDimensional
        (peierlsCLMToMatrixOrthonormal u).toAlgHom.toLinearMap
    simpa [peierlsCLMToMatrixOrthonormalReal, peierlsCLMToMatrixOrthonormal] using hφC
  have hφselfAdjoint : IsSelfAdjoint (peierlsCLMToMatrixOrthonormalReal u A) :=
    IsSelfAdjoint.map hA (peierlsCLMToMatrixOrthonormalReal u)
  simpa [cfcR, LownerHeinzCore.cfcR] using
    (StarAlgHomClass.map_cfc
      (R := ℝ)
      (φ := peierlsCLMToMatrixOrthonormalReal u)
      (f := f)
      (a := A)
      (hf := hf)
      (hφ := hφ)
      (ha := hA)
      (hφa := hφselfAdjoint))

omit [Nontrivial H] in
/-- Peierls inequality for a convex scalar function and an arbitrary orthonormal basis. -/
/- Peierls inequality (Carlen 2010, Theorem 2.9, formula (2.9)) -/
/- Statement: (Carlen 2010, Theorem 2.9, formula (2.9)) Let
    $A \in \mathbf{H}_n$, let
    $f : \mathbb{R} \to \mathbb{R}$ be convex, and let
    $\{u_i\}_{i \in I}$ be an orthonormal basis of the underlying finite-dimensional complex
    Hilbert space. Then
    \[
      \sum_i f(\operatorname{Re}\langle u_i,A u_i\rangle)
        \leq \operatorname{Re}\operatorname{Tr}(f(A)).
    \]
    The real part is inserted only to match the finite-dimensional complex Hilbert-space
    formalization; for self-adjoint $A$ each diagonal matrix coefficient is real. This declaration
    formalizes only the Peierls inequality from Carlen 2010 Theorem 2.9. The equality
    characterization in that theorem--equality when each $u_i$ is an eigenvector of $A$,
    and, for strictly convex $f$, only then--is not formalized in this
    declaration. -/
/- Proof: Let $M$ be the matrix of $A$ in the orthonormal basis $\{u_i\}$. Since $A$ is
    self-adjoint, $M$ is Hermitian. The matrix Peierls inequality
    the matrix Peierls inequality (private lemma `peierls_matrix`), proved from the unitary spectral
    decomposition of $M$ and Jensen's finite-sum inequality, gives
    \[
      \sum_i f(\operatorname{Re} M_{ii})
        \leq \operatorname{Re}\operatorname{Tr}(f(M)).
    \]
    The diagonal identity $M_{ii}=\langle u_i,A u_i\rangle$ converts the left-hand side to the
    displayed sum in this theorem. Since $f$ is convex on all of $\mathbb{R}$, it is continuous
    there and hence continuous on the real spectrum of $A$. On the right-hand side, the
    functional-calculus compatibility the private lemma `peierls_toMatrix_cfcR` identifies the
    matrix of $f(A)$ with $f(M)$, and the finite-dimensional trace formula in the same orthonormal
    basis identifies the real part of the matrix trace with `traceRe (cfcR f A)`. Combining
    these two identifications gives the stated Peierls inequality. As in the statement, the
    equality characterization from Carlen 2010 Theorem 2.9 is outside this formal declaration. -/
lemma peierls {I : Type*} [Fintype I] (u : OrthonormalBasis I Complex H)
    (f : Real -> Real) (A : (H →L[ℂ] H)) (hA : IsSelfAdjoint A)
    (hf : ConvexOn Real Set.univ f) :
    (Finset.univ.sum fun i : I => f (Complex.re (inner Complex (u i) (A (u i))))) <=
      traceRe (ℋ := H) (cfcR (ℋ := H) f A) := by
  classical
  letI : NormedAddCommGroup (Matrix I I ℂ) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedRing (Matrix I I ℂ) := Matrix.instL2OpNormedRing
  letI : NormedSpace ℂ (Matrix I I ℂ) := Matrix.instL2OpNormedSpace
  letI : NormedAlgebra ℂ (Matrix I I ℂ) := Matrix.instL2OpNormedAlgebra
  letI : StarRing (Matrix I I ℂ) := Matrix.instStarRing
  letI := Matrix.instCStarRing (n := I) (𝕜 := ℂ)
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  let M : Matrix I I ℂ := peierlsCLMToMatrixOrthonormalReal u A
  have hM : M.IsHermitian := by
    change IsSelfAdjoint M
    exact IsSelfAdjoint.map hA (peierlsCLMToMatrixOrthonormalReal u)
  have hpe := peierls_matrix f M hM hf
  have hfcont : ContinuousOn f (spectrum ℝ A) := by
    exact (hf.continuousOn isOpen_univ).mono (by intro x hx; exact Set.mem_univ x)
  have hmap :
      peierlsCLMToMatrixOrthonormalReal u (cfcR (ℋ := H) f A) = hM.cfc f := by
    calc
      peierlsCLMToMatrixOrthonormalReal u (cfcR (ℋ := H) f A)
          = cfc (R := ℝ) (p := IsSelfAdjoint) f M := by
        simpa [M] using peierls_toMatrix_cfcR u f A hA hfcont
      _ = hM.cfc f := by
        rw [hM.cfc_eq f]
  have htrace (T : (H →L[ℂ] H)) :
      traceRe (ℋ := H) T =
        Complex.re (Matrix.trace (peierlsCLMToMatrixOrthonormalReal u T)) := by
    have htr :=
      LinearMap.trace_eq_matrix_trace (R := ℂ) (b := u.toBasis) (f := (T : H →ₗ[ℂ] H))
    simpa [traceRe, peierlsCLMToMatrixOrthonormalReal, LinearMap.toMatrixOrthonormal] using
      congrArg Complex.re htr
  have hrhs :
      Complex.re (Matrix.trace (hM.cfc f)) =
        traceRe (ℋ := H) (cfcR (ℋ := H) f A) := by
    calc
      Complex.re (Matrix.trace (hM.cfc f)) =
          Complex.re (Matrix.trace
            (peierlsCLMToMatrixOrthonormalReal u (cfcR (ℋ := H) f A))) := by
        rw [hmap]
      _ = traceRe (ℋ := H) (cfcR (ℋ := H) f A) := (htrace _).symm
  have hM_apply : ∀ i : I, M i i = inner ℂ (u i) (A (u i)) := by
    intro i
    change (LinearMap.toMatrixOrthonormal u (A : H →ₗ[ℂ] H)) i i = inner ℂ (u i) (A (u i))
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    rfl
  have hpe' :
      (Finset.univ.sum fun i : I => f (Complex.re (inner ℂ (u i) (A (u i))))) <=
        Complex.re (Matrix.trace (hM.cfc f)) := by
    calc
      (Finset.univ.sum fun i : I => f (Complex.re (inner ℂ (u i) (A (u i))))) =
          Finset.univ.sum fun i : I => f (Complex.re (M i i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hM_apply i]
      _ <= Complex.re (Matrix.trace (hM.cfc f)) := hpe
  exact hpe'.trans_eq hrhs

/-- A differentiable point of a convex scalar function has a supporting line. -/
/- Supporting-line inequality for differentiable convex functions -/
/- Statement: Let $f : \mathbb{R}\to\mathbb{R}$ be convex and suppose that
    $df(\beta)$ is the derivative of $f$ at $\beta$. Then for every $a \in \mathbb{R}$,
    \[
      f(\beta)+df(\beta)(a-\beta) \leq f(a).
    \]
    This is the scalar supporting-line inequality used in place of Carlen 2010's matrix
    directional derivative argument. -/
/- Proof: If $a=\beta$, the assertion is equality. If $\beta<a$, the convexity theorem
    `ConvexOn.le_slope_of_hasDerivAt` gives
    \[
      df(\beta)\leq \frac{f(a)-f(\beta)}{a-\beta}.
    \]
    Since $a-\beta>0$, multiplication by $a-\beta$ gives the displayed supporting-line
    inequality. If $a<\beta$, the theorem
    `ConvexOn.slope_le_of_hasDerivAt`, applied to the ordered pair $(a,\beta)$, gives
    \[
      \frac{f(\beta)-f(a)}{\beta-a}\leq df(\beta).
    \]
    Multiplication by the positive number $\beta-a$ and rearrangement again gives
    $f(\beta)+df(\beta)(a-\beta)\leq f(a)$. These are exactly the one-dimensional
    subgradient inequalities for a differentiable convex function. -/
lemma convex_supporting_line (f df : Real -> Real) {a beta : Real}
    (hf : ConvexOn Real Set.univ f) (hdf : HasDerivAt f (df beta) beta) :
    f beta + df beta * (a - beta) <= f a := by
  by_cases h_eq : a = beta
  · subst a
    simp
  · rcases lt_or_gt_of_ne h_eq with hlt | hlt
    · have hslope : (f beta - f a) / (beta - a) <= df beta := by
        simpa [slope_def_field] using
          (hf.slope_le_of_hasDerivAt (x := a) (y := beta) (f' := df beta)
            (by simp) (by simp) hlt hdf)
      have hmul : f beta - f a <= df beta * (beta - a) := by
        have hnonneg : 0 <= beta - a := by linarith
        have hne : beta - a ≠ 0 := by linarith
        have hmul' := mul_le_mul_of_nonneg_right hslope hnonneg
        field_simp [hne] at hmul'
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      nlinarith
    · have hslope : df beta <= (f a - f beta) / (a - beta) := by
        simpa [slope_def_field] using
          (hf.le_slope_of_hasDerivAt (x := beta) (y := a) (f' := df beta)
            (by simp) (by simp) hlt hdf)
      have hmul : df beta * (a - beta) <= f a - f beta := by
        have hnonneg : 0 <= a - beta := by linarith
        have hne : a - beta ≠ 0 := by linarith
        have hmul' := mul_le_mul_of_nonneg_right hslope hnonneg
        field_simp [hne] at hmul'
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      linarith

/- The continuous functional calculus on a real eigenvector. -/
/- Real continuous functional calculus under an eigenvector equation -/
/- Statement: Let $T$ be a self-adjoint operator on a finite-dimensional complex Hilbert
    space. For any real number $r$ and any vector $x$, if $T x = r x$, then for every
    scalar function $f:\mathbb{R}\to\mathbb{R}$ the real continuous functional calculus satisfies
    \[
      f(T)x=f(r)x .
    \]
    No global continuity hypothesis on $f$ is needed, because only the finite real spectrum of
    $T$ is seen by the functional calculus. -/
/- Proof: The complex spectrum of the finite-dimensional operator $T$ is finite, and the
    real spectrum is its preimage under the real-to-complex algebra map, hence is finite as well.
    Interpolate the values of $f$ on this finite real spectrum by a real polynomial $q$ using
    Lagrange interpolation. Since $f$ and $q$ agree on the real spectrum,
    `cfc_congr` replaces `cfcR f T` by `cfcR q.eval T`, and
    `cfc_polynomial` identifies the latter with the polynomial functional calculus
    `aeval T q`. If $x=0$, the result is immediate. Otherwise, the equation $T x=r x$
    puts $r$ in the real spectrum, the polynomial functional calculus acts on $x$ by evaluation
    at $r$, and the interpolation identity gives $q(r)=f(r)$. -/
private lemma klein_cfcR_apply_of_eigenvector
    {𝓚 : Type u} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (𝓚 →L[ℂ] 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : (𝓚 →L[ℂ] 𝓚)} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : T x = (r : ℂ) • x) :
    cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  exact LiebAndoTrace.cfcR_apply_of_mem_eigenspace_real (𝓚 := 𝓚) f hT hx

omit [Nontrivial H] in
private lemma klein_trace_expansion_core {I : Type*} [Fintype I]
    (u : OrthonormalBasis I Complex H) (f df : Real -> Real) (A B : (H →L[ℂ] H)) (beta
        : I -> Real)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hB_eigen : forall i : I, B (u i) = (beta i : Complex) • u i) :
    traceRe (ℋ := H) (cfcR (ℋ := H) f B) = Finset.univ.sum (fun i : I => f (beta i)) /\
    traceRe (ℋ := H) ((A - B) * cfcR (ℋ := H) df B) =
        Finset.univ.sum
          (fun i : I =>
            df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) := by
  classical
  have _hA : IsSelfAdjoint A := hA
  have htrace_sum (T : (H →L[ℂ] H)) :
      traceRe (ℋ := H) T =
        Finset.univ.sum fun i : I => Complex.re (inner ℂ (u i) (T (u i))) := by
    rw [traceRe, LinearMap.trace_eq_sum_inner (T : H →ₗ[ℂ] H) u, Complex.re_sum]
    rfl
  have hcfc_apply (g : ℝ → ℝ) (i : I) :
      cfcR (ℋ := H) g B (u i) = (g (beta i) : ℂ) • u i := by
    exact klein_cfcR_apply_of_eigenvector (𝓚 := H) g hB
      (by simpa using hB_eigen i)
  constructor
  · calc
      traceRe (ℋ := H) (cfcR (ℋ := H) f B) =
          Finset.univ.sum fun i : I =>
            Complex.re (inner ℂ (u i) (cfcR (ℋ := H) f B (u i))) := htrace_sum _
      _ = Finset.univ.sum (fun i : I => f (beta i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcfc_apply f i, inner_smul_right, u.inner_eq_one]
        simp
  · calc
      traceRe (ℋ := H) ((A - B) * cfcR (ℋ := H) df B) =
          Finset.univ.sum fun i : I =>
            Complex.re (inner ℂ (u i) (((A - B) * cfcR (ℋ := H) df B) (u i))) := htrace_sum _
      _ = Finset.univ.sum
          (fun i : I =>
            df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        change Complex.re (inner ℂ (u i)
          ((A - B) ((cfcR (ℋ := H) df B) (u i)))) =
            df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)
        rw [hcfc_apply df i]
        rw [map_smul]
        simp only [ContinuousLinearMap.sub_apply, hB_eigen]
        rw [inner_smul_right, inner_sub_right, inner_smul_right, u.inner_eq_one]
        simp [Complex.mul_re]

omit [Nontrivial H] in
/- Trace expansion in an eigenbasis -/
/- Statement: Let $B$ be self-adjoint, let $\{u_i\}$ be an orthonormal basis of
    eigenvectors of $B$, and write $B u_i=\beta_i u_i$ with $\beta_i\in\mathbb{R}$. Then
    \[
      \operatorname{Re}\operatorname{Tr}(f(B))=\sum_i f(\beta_i)
    \]
    and, for any self-adjoint $A$,
    \[
      \operatorname{Re}\operatorname{Tr}((A-B)df(B))
        =\sum_i df(\beta_i)
          \bigl(\operatorname{Re}\langle u_i,A u_i\rangle-\beta_i\bigr).
    \]
    This is the bridge from the operator expression in Klein's inequality to the scalar
    supporting-line inequalities along the eigenbasis of $B$. -/
/- Proof: Since $B$ is self-adjoint on a finite-dimensional Hilbert space, its real
    spectrum is a finite discrete set. Thus the restrictions of the arbitrary scalar functions
    $f$ and $df$ to this spectrum are automatically continuous, in the precise
    `ContinuousOn` sense needed by the continuous functional calculus. The local refinement
    the private lemma `klein_cfcR_apply_of_eigenvector` implements this point by interpolating on
    the finite
    real spectrum: because $u_i$ is a $B$-eigenvector with real eigenvalue $\beta_i$, the
    functional calculus gives
    $f(B)u_i=f(\beta_i)u_i$ and $df(B)u_i=df(\beta_i)u_i$. The trace formula
    $\operatorname{Tr}(T)=\sum_i\langle u_i,T u_i\rangle$ in an orthonormal basis therefore
    gives the first identity. For the second identity, apply the same trace formula to
    $T=(A-B)df(B)$. On each basis vector,
    \[
      T u_i=df(\beta_i)(A-B)u_i
        =df(\beta_i)(A u_i-\beta_i u_i).
    \]
    Taking inner products against $u_i$, then real parts, yields
    \[
      \operatorname{Re}\langle u_i,T u_i\rangle
        =df(\beta_i)\bigl(\operatorname{Re}\langle u_i,A u_i\rangle-\beta_i\bigr),
    \]
    because $df(\beta_i)$ and $\beta_i$ are real and $\lVert u_i\rVert=1$.
    Summing over $i$ proves the displayed expansion. -/
lemma klein_trace_expansion {I : Type*} [Fintype I]
    (u : OrthonormalBasis I Complex H) (f df : Real -> Real) (A B : (H →L[ℂ] H)) (beta
        : I -> Real)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hB_eigen : forall i : I, B (u i) = (beta i : Complex) • u i) :
    traceRe (ℋ := H) (cfcR (ℋ := H) f B) = Finset.univ.sum (fun i : I => f (beta i)) /\
    traceRe (ℋ := H) ((A - B) * cfcR (ℋ := H) df B) =
        Finset.univ.sum
          (fun i : I =>
            df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) := by
  exact klein_trace_expansion_core u f df A B beta hA hB hB_eigen

omit [CompleteSpace H] [FiniteDimensional ℂ H] [Nontrivial H] in
/-- Finite sum of the scalar supporting-line inequalities along an orthonormal basis. -/
/- Finite-sum supporting-line bound -/
/- Statement: Let $\{u_i\}_{i\in I}$ be a finite orthonormal basis, let $A\in L(H)$,
    and let $\beta_i\in\mathbb{R}$ be arbitrary real numbers. Suppose that
    $f:\mathbb{R}\to\mathbb{R}$ is convex and that, for each $i$, $df(\beta_i)$ is the
    derivative value of $f$ at $\beta_i$. Then
    \[
      \sum_i \left(f(\beta_i)+df(\beta_i)
        (\operatorname{Re}\langle u_i,A u_i\rangle-\beta_i)\right)
      \leq
      \sum_i f(\operatorname{Re}\langle u_i,A u_i\rangle).
    \]
    This declaration is only the finite-sum supporting-line lemma; the later Klein reduction
    instantiates the numbers $\beta_i$ as eigenvalues of $B$.
    -/
/- Proof: For each $i$, apply `convex_supporting_line` with
    $a=\operatorname{Re}\langle u_i,A u_i\rangle$ and $\beta=\beta_i$. The derivative
    hypothesis supplies `HasDerivAt f (df beta_i) beta_i`, and convexity is the common
    convexity assumption. The resulting pointwise inequalities are finite in number, because
    the basis index is finite, so summing them over $i$ gives the displayed inequality. No
    self-adjointness of $A$ and no operator $B$ are used in this scalar summation step. -/
lemma klein_eigenbasis_sum_bound {I : Type*} [Fintype I]
    (u : OrthonormalBasis I Complex H) (f df : Real -> Real) (A : (H →L[ℂ] H)) (beta
        : I -> Real)
    (hf : ConvexOn Real Set.univ f)
    (hdf_beta : forall i : I, HasDerivAt f (df (beta i)) (beta i)) :
    Finset.univ.sum
        (fun i : I =>
          f (beta i) +
            df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) <=
      Finset.univ.sum
        (fun i : I => f (Complex.re (inner Complex (u i) (A (u i))))) := by
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact KleinInequality.convex_supporting_line f df (hf := hf) (hdf := hdf_beta i)

omit [Nontrivial H] in
/-- Klein's inequality when an eigenbasis of `B` has been fixed explicitly. -/
/- Klein inequality from an explicit eigenbasis -/
/- Statement: Assume $A$ and $B$ are self-adjoint and that an orthonormal basis
    $\{u_i\}$ diagonalizes $B$, say $B u_i=\beta_i u_i$. If $f$ is convex on
    $\mathbb{R}$ and $df(\beta_i)$ is the derivative of $f$ at every eigenvalue $\beta_i$,
    then
    \[
      0\leq \operatorname{Re}\operatorname{Tr}
      \left(f(A)-f(B)-(A-B)df(B)\right).
    \]
    This is the Peierls-plus-supporting-line proof of Klein's inequality with the diagonalizing
    basis of $B$ made explicit. -/
/- Proof: Let $a_i=\operatorname{Re}\langle u_i,A u_i\rangle$. By
    `klein_eigenbasis_sum_bound`,
    \[
      \left(\sum_i f(\beta_i)\right)
        + \left(\sum_i df(\beta_i)(a_i-\beta_i)\right)
        \leq \sum_i f(a_i).
    \]
    The Lean proof obtains this displayed form from the pointwise-sum statement by applying
    `Finset.sum_add_distrib`.
    By `peierls`, applied to the same orthonormal basis and to the self-adjoint
    operator $A$,
    \[
      \sum_i f(a_i)\leq \operatorname{Re}\operatorname{Tr}(f(A)).
    \]
    Hence
    \[
      \left(\sum_i f(\beta_i)\right)
        + \left(\sum_i df(\beta_i)(a_i-\beta_i)\right)
        \leq \operatorname{Re}\operatorname{Tr}(f(A)).
    \]
    Finally `klein_trace_expansion` identifies
    $\operatorname{Re}\operatorname{Tr}(f(B))$ with $\sum_i f(\beta_i)$ and identifies
    $\operatorname{Re}\operatorname{Tr}((A-B)df(B))$ with
    $\sum_i df(\beta_i)(a_i-\beta_i)$. Linearity of the real part of the trace rewrites the
    last displayed inequality exactly as
    \[
      0\leq \operatorname{Re}\operatorname{Tr}
      \left(f(A)-f(B)-(A-B)df(B)\right).
    \] -/
lemma klein_of_eigenbasis {I : Type*} [Fintype I]
    (u : OrthonormalBasis I Complex H) (f df : Real -> Real) (A B : (H →L[ℂ] H)) (beta
        : I -> Real)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hf : ConvexOn Real Set.univ f)
    (hB_eigen : forall i : I, B (u i) = (beta i : Complex) • u i)
    (hdf_beta : forall i : I, HasDerivAt f (df (beta i)) (beta i)) :
    0 <=
      traceRe (ℋ := H) (cfcR (ℋ := H) f A - cfcR (ℋ := H) f B - (A - B) * cfcR (ℋ := H) df B) := by
  classical
  obtain ⟨htraceB, htraceDfB⟩ :=
    KleinInequality.klein_trace_expansion u f df A B beta hA hB hB_eigen
  have hsum :
      Finset.univ.sum (fun i : I => f (beta i)) +
          Finset.univ.sum
            (fun i : I =>
              df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) <=
        Finset.univ.sum
          (fun i : I => f (Complex.re (inner Complex (u i) (A (u i))))) := by
    have hbound :=
      KleinInequality.klein_eigenbasis_sum_bound u f df A beta hf hdf_beta
    simpa [Finset.sum_add_distrib] using hbound
  have hpeierls :
      Finset.univ.sum
          (fun i : I => f (Complex.re (inner Complex (u i) (A (u i))))) <=
        traceRe (ℋ := H) (cfcR (ℋ := H) f A) :=
    KleinInequality.peierls u f A hA hf
  have hscalar :
      Finset.univ.sum (fun i : I => f (beta i)) +
          Finset.univ.sum
            (fun i : I =>
              df (beta i) * (Complex.re (inner Complex (u i) (A (u i))) - beta i)) <=
        traceRe (ℋ := H) (cfcR (ℋ := H) f A) :=
    hsum.trans hpeierls
  have htraceBound :
      traceRe (ℋ := H) (cfcR (ℋ := H) f B) +
          traceRe (ℋ := H) ((A - B) * cfcR (ℋ := H) df B) <=
        traceRe (ℋ := H) (cfcR (ℋ := H) f A) := by
    simpa only [htraceB, htraceDfB] using hscalar
  have hlinear :
      traceRe (ℋ := H) (cfcR (ℋ := H) f A - cfcR (ℋ := H) f B - (A - B) * cfcR (ℋ := H) df B) =
        traceRe (ℋ := H) (cfcR (ℋ := H) f A) -
          traceRe (ℋ := H) (cfcR (ℋ := H) f B) -
          traceRe (ℋ := H) ((A - B) * cfcR (ℋ := H) df B) := by
    simp [traceRe, map_sub, Complex.sub_re]
  rw [hlinear]
  linarith

omit [Nontrivial H] in
/-- Klein's inequality, in the differentiable-on-the-spectrum formal version. -/
/- Klein's inequality (Carlen 2010, Theorem 2.11, formula (2.13)) -/
/- Statement: This declaration formalizes only the differentiable all-real inequality
    (Carlen 2010, Theorem 2.11, formula (2.13)). For self-adjoint $A,B$ and a convex scalar
    function $f : \mathbb{R}\to\mathbb{R}$,
    \[
      0\leq \operatorname{Re}\operatorname{Tr}
      \left[f(A)-f(B)-(A-B)df(B)\right].
    \]
    Lean deviation: This is not a formalization of the whole of Carlen 2010, Theorem 2.11.
    The theorem's positive-definite-domain version, with $f:(0,\infty)\to\mathbb{R}$, and its
    strictly convex equality characterization, equality if and only if $A=B$, are outside the
    scope of this declaration. The formal statement is instead the differentiable-on-the-spectrum
    all-real version of formula (2.13): the derivative is a separate function
    $df : \mathbb{R}\to\mathbb{R}$, and the hypothesis asserts `HasDerivAt f (df x) x` for
    every $x$ in the real spectrum of $B$. This avoids the misformalization in which Lean's
    total `deriv f` would assign junk values at nondifferentiability points of a merely
    convex function. Carlen writes the displayed trace without an explicit real part, but the Lean
    statement is the `traceRe` version because $(A-B)df(B)$ need not be self-adjoint. -/
/- Proof: Lean deviation: The proof below is only for the restricted all-real
    differentiable inequality (2.13), not for the positive-definite-domain statement or the
    strictly convex equality condition in the surrounding Carlen 2010 theorem. Carlen 2010 proves
    (2.13) by setting
    $C=A-B$, considering $\varphi(t)=\operatorname{Tr}(f(B+tC))$, using the convexity of
    $\varphi$ from Theorem 2.10, and passing to the directional derivative at $t=0$. The
    current Mathlib development does not provide the Frechet derivative or eigenvalue
    perturbation API needed to formalize that route for general operator functional calculus.

    Instead choose, by the finite-dimensional spectral theorem for self-adjoint operators, an
    orthonormal basis $\{u_i\}$ of eigenvectors of $B$, with $B u_i=\beta_i u_i$ and
    $\beta_i\in\mathbb{R}$. Each $\beta_i$ lies in the real spectrum of $B$, so the hypothesis
    on `df` supplies the derivative condition at every $\beta_i$. Applying
    `klein_of_eigenbasis` to this eigenbasis gives exactly
    \[
      0\leq \operatorname{Re}\operatorname{Tr}
      \left(f(A)-f(B)-(A-B)df(B)\right),
    \]
    which is the formal statement. -/
theorem klein (f df : Real -> Real) (A B : (H →L[ℂ] H))
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hf : ConvexOn Real Set.univ f)
    (hdf : forall x : Real, x ∈ spectrum Real B -> HasDerivAt f (df x) x) :
    0 <=
      traceRe (ℋ := H) (cfcR (ℋ := H) f A - cfcR (ℋ := H) f B - (A - B) * cfcR (ℋ := H) df B) := by
  classical
  let n := Module.finrank Complex H
  let hBsym := hB.isSymmetric
  let u := hBsym.eigenvectorBasis (n := n) rfl
  let beta := hBsym.eigenvalues (n := n) rfl
  have hB_eigen : forall i : Fin n, B (u i) = (beta i : Complex) • u i := by
    intro i
    exact hBsym.apply_eigenvectorBasis (n := n) rfl i
  have hbeta_spec : forall i : Fin n, beta i ∈ spectrum Real B := by
    haveI : IsScalarTower Real Complex (H →L[ℂ] H) := RestrictScalars.isScalarTower
        Real Complex (H →L[ℂ] H)
    intro i
    rw [← spectrum.preimage_algebraMap Complex (R := Real), Set.mem_preimage]
    rw [ContinuousLinearMap.spectrum_eq]
    simpa [beta] using (hBsym.hasEigenvalue_eigenvalues (n := n) rfl i).mem_spectrum
  exact
    KleinInequality.klein_of_eigenbasis u f df A B beta hA hB hf hB_eigen
      (fun i => hdf (beta i) (hbeta_spec i))

/- Carlen (2010), Theorem 2.11 contains the following three claims; its first inequality is
formula (2.13), to which the theorem statement above corresponds. First, it concerns
self-adjoint operators on a finite-dimensional complex Hilbert space and a convex function
differentiable on all of the reals, with $df$ in the display being the derivative of $f$.
The source does not write the real part of this trace explicitly, but the trace in this display
is real for self-adjoint operators in finite dimensions, so it is equivalent to the form above.
Second, the same inequality holds when the two operators appearing in the first claim are
positive definite and a differentiable convex function
$f:(0,\infty)\to\mathbb{R}$ is taken. Third, in either of these two versions, if the function is
strictly convex, then equality holds if and only if $A=B$.

Differences in Lean: the current Lean declaration allows the same finite-dimensional
complex Hilbert space to be zero-dimensional, and proves, not the whole of
Carlen (2010), Theorem 2.11, but a generalized version of the inequality (2.13) with domain all of
the reals. The derivative candidate is introduced as a separate real function in the theorem
statement above, and it is assumed only that
`HasDerivAt f (df x) x` holds at each point of the real spectrum of the reference
operator. The global function
`deriv f` is not used. Also, since the product $(A-B)df(B)$ is not necessarily
self-adjoint, the Lean conclusion takes the real part of the trace via
`traceRe`. -/

end KleinInequality
