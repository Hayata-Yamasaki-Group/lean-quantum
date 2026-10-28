import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData


namespace Quantum.TraceInequality.Loewner

open scoped ComplexConjugate
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Finite-point Korányi-style construction (a Step-2 building block for a Loewner theorem proof).

This file intentionally avoids any external bibliography references in comments.  The goal is to
package the *finite* construction that starts from the positivity of a Loewner (divided-difference)
matrix and produces a Hilbert space model with an operator.
-/

/-!
The shared kernel, matrix, and point-family definitions live in
`Kernel.FiniteMatrixData`.  The remainder of this file builds the PSD-to-Gram
decomposition and the finite Hilbert-space construction.
-/

/-- A positive semidefinite complex matrix factors as `Yᴴ * Y`, through its spectral
decomposition. -/
private theorem posSemidef_eq_conjTranspose_mul_self_spectral {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    ∃ Y : Matrix ι ι ℂ, C = Matrix.conjTranspose Y * Y := by
  classical
  -- Take `Y = √D * Uᴴ` from the spectral decomposition `C = U * D * Uᴴ`.
  refine ⟨Matrix.diagonal (fun i => ((Real.sqrt (hC.1.eigenvalues i) : ℝ) : ℂ)) *
      star (hC.1.eigenvectorUnitary : Matrix ι ι ℂ), ?_⟩
  conv_lhs => rw [hC.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, star_star,
    Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 3
  funext i
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hC.eigenvalues_nonneg i)]
  rfl

section Construction

variable {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}

/-! ### Gram realization from positive semidefiniteness -/
/-- A positive semidefinite Loewner matrix admits a spanning Gram realization. -/
theorem exists_gram_vectors
    (hL : (loewnerMatrix (n := n) f y).PosSemidef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H),
        (∀ i j : Fin (n + 1),
            inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
          Submodule.span ℂ (Set.range v) = ⊤ := by
  classical
  obtain ⟨B, hB⟩ := posSemidef_eq_conjTranspose_mul_self_spectral hL
  -- Work in the standard Hilbert space `V := EuclideanSpace ℂ (Fin (n+1))`.
  let p : ENNReal := 2
  let V : Type := EuclideanSpace ℂ (Fin (n + 1))
  let T : V →ₗ[ℂ] V := (Matrix.toLpLin (p := p) (q := p) B)
  let e : Fin (n + 1) → V := fun i => EuclideanSpace.single i (1 : ℂ)
  let w : Fin (n + 1) → V := fun i => T (e i)
  let H : Submodule ℂ V := Submodule.span ℂ (Set.range w)
  let v : Fin (n + 1) → H := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  refine ⟨H, by infer_instance, by infer_instance, by infer_instance, v, ?_, ?_⟩
  · intro i j
    have hTi : (T (e i)).ofLp = B.col i := by
      dsimp [T]
      have h1 :
          (((Matrix.toLpLin (p := p) (q := p) B)
                (e i)).ofLp) =
              Matrix.toLin' B ((e i).ofLp) := by
        simp
      refine h1.trans ?_
      simp [e, Matrix.toLin'_apply']
    have hTj : (T (e j)).ofLp = B.col j := by
      dsimp [T]
      have h1 :
          (((Matrix.toLpLin (p := p) (q := p) B)
                (e j)).ofLp) =
              Matrix.toLin' B ((e j).ofLp) := by
        simp
      refine h1.trans ?_
      simp [e, Matrix.toLin'_apply']
    -- Now compute the inner product as a coordinate sum in `EuclideanSpace`.
    -- This matches the `(i,j)` entry of `Bᴴ * B`, hence (by `hB`) the Loewner matrix entry.
    have h_inner_cols :
        inner (𝕜 := ℂ) (T (e i)) (T (e j)) =
          (B.conjTranspose * B) i j := by
      -- Expand the inner product on `PiLp 2` and simplify to the matrix multiplication formula.
      -- `simp` uses `PiLp.inner_apply` and the explicit form of the inner product on `ℂ`.
      -- The only nontrivial step is commutativity in `ℂ`, handled by `simp`.
      simp [V, EuclideanSpace, PiLp.inner_apply, hTi, hTj, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.col_apply, mul_comm]
    have h_entry : (B.conjTranspose * B) i j = loewnerMatrix (n := n) f y i j := by
      simpa [Matrix.star_eq_conjTranspose] using (congrArg (fun M => M i j) hB).symm
    -- Translate back to the chosen Gram vectors `v i` in the range of `T`.
    simpa [v, w, loewnerMatrix] using h_inner_cols.trans (h_entry.trans rfl)
  · -- By construction, `H` is the span of the vectors `v i`.
    have hs : (∀ i, w i ∈ H) := fun i => Submodule.subset_span ⟨i, rfl⟩
    -- `span (range v) = ⊤` in `H` is equivalent to `span (range w) = H` in `V`.
    simpa [H, v] using
      (Submodule.span_range_subtype_eq_top_iff (R := ℂ) (p := H) (s := w) hs).2 rfl

/-! ### Positive-definite finite construction -/
/-- Positive definite finite Loewner data produce the Koranyi Hilbert-space model. -/
theorem koranyi_finite_construct
    (hy : pointsHyp (n := n) y)
    (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        IsSelfAdjoint A ∧
        (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        (∀ i, i ≠ 0 →
          (f (y i) : ℂ) = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ) := by
  classical
  rcases exists_gram_vectors (n := n) (f := f) (y := y) hL.posSemidef with
    ⟨H, instH, instI, instFD, v, hv, hv_span⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  let φ : H := v 0
  -- The operator `A` is constructed in the remaining part of Step 2 (Korányi finite construction).
  have hA :
      ∃ A : H →ₗ[ℂ] H,
        IsSelfAdjoint A ∧
          (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) := by
    -- Since the Loewner matrix is positive definite, the Gram vectors `v` are linearly
    -- independent.
    have hgram : Matrix.gram ℂ v = loewnerMatrix (n := n) f y := by
      ext i j
      simpa [Matrix.gram_apply, loewnerMatrix] using (hv i j)
    have hv_li : LinearIndependent ℂ v := by
      have hpos : (Matrix.gram ℂ v).PosDef := by simpa [hgram] using hL
      exact Matrix.linearIndependent_of_posDef_gram (𝕜 := ℂ) (v := v) hpos
    have hv_sp' : (⊤ : Submodule ℂ H) ≤ Submodule.span ℂ (Set.range v) := by
      simp [hv_span]
    let b : Module.Basis (Fin (n + 1)) ℂ H := Module.Basis.mk hv_li hv_sp'
    have hb : ∀ i : Fin (n + 1), b i = v i := by
      intro i
      simp [b]
    -- First record the key inner-product symmetry for the prescribed values on `v i`
    -- (for `i ≠ 0`).
    have inner_prescribed_symm :
        ∀ {i j : Fin (n + 1)}, i ≠ 0 → j ≠ 0 →
          inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j) =
            inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
      intro i j hi hj
      rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
      have hyi0 : y i ≠ 0 := hyne0 i hi
      have hyj0 : y j ≠ 0 := hyne0 j hj
      have hyi0C : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi0
      have hyj0C : (y j : ℂ) ≠ 0 := by exact_mod_cast hyj0
      -- Expand both sides using the Gram equalities.
      have hLij : inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ) := hv i j
      have hL0j : inner (𝕜 := ℂ) φ (v j) = (loewnerKernel f (y 0) (y j) : ℂ) := by
        simpa [φ] using hv 0 j
      have hLi0 : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) (y 0) : ℂ) := by
        simpa [φ] using hv i 0
      have hL00 : inner (𝕜 := ℂ) φ φ = (loewnerKernel f (y 0) (y 0) : ℂ) := by
        simpa [φ] using hv 0 0
      -- Rewrite `y 0 = 0` on kernel entries.
      have hy0' : y 0 = 0 := hy0
      -- Reduce to the real kernel identity `koranyi_identity` (and `loewnerKernel_swap`
      -- for `x = y`).
      have hKoranyi :
          (loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) =
            (loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) := by
        by_cases hij : i = j
        · subst hij
          -- When `i = j`, this is just the symmetry
          -- `loewnerKernel f 0 (y i) = loewnerKernel f (y i) 0`.
          have hs : loewnerKernel f 0 (y i) = loewnerKernel f (y i) 0 := by
            simpa using (loewnerKernel_swap (f := f) 0 (y i))
          simp [hs, div_eq_mul_inv, sub_eq_add_neg]
        · have hyij : y i ≠ y j := by
            intro h
            exact hij (hyinj h)
          simpa [hy0'] using
            (koranyi_identity (f := f) (x := y i) (y := y j) hyi0 hyj0 hyij)
      -- Convert `hKoranyi` to the complex inner-product equality.
      -- All kernel values are real, so scalar conjugations are harmless.
      have hKoranyiC :
          ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) =
            ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
        exact_mod_cast hKoranyi
      -- Finish by rewriting inner products into kernel entries.
      -- We keep this `simp` focused to avoid elaboration blowups.
      calc
        inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j)
            = (1 / (y i : ℂ)) * (inner (𝕜 := ℂ) (v i - φ) (v j)) := by
                simp [inner_smul_left]
        _ =
            (1 / (y i : ℂ)) *
              (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) φ (v j)) := by
              simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
        _ =
            (1 / (y i : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) - (loewnerKernel f 0 (y j) : ℂ)) := by
              simp [hLij, hL0j, hy0', sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
              simpa using hKoranyiC
        _ =
            (1 / (y j : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) - (loewnerKernel f (y i) 0 : ℂ)) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ =
            (1 / (y j : ℂ)) *
              (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) (v i) φ) := by
              simp [hLij, hLi0, hy0', φ, sub_eq_add_neg]
        _ = (1 / (y j : ℂ)) * inner (𝕜 := ℂ) (v i) (v j - φ) := by
              simp [inner_sub_right]
        _ = inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
              rw [inner_smul_right]
    -- Define the codimension-one subspace `K` spanned by the `v i` with `i ≠ 0`.
    let ι₁ : Type := { i : Fin (n + 1) // i ≠ 0 }
    let v₁ : ι₁ → H := fun i => v i.1
    let K : Submodule ℂ H := Submodule.span ℂ (Set.range v₁)
    letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
    letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
        (@SeminormedAddCommGroup.toPseudoMetricSpace K
          (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
      FiniteDimensional.complete ℂ K
    have hv₁_mem : ∀ i : ι₁, v₁ i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
    have hv₁_li : LinearIndependent ℂ v₁ :=
      hv_li.comp (fun i : ι₁ => (i : Fin (n + 1))) Subtype.coe_injective
    let vK : ι₁ → K := fun i => ⟨v₁ i, hv₁_mem i⟩
    have hvK_li : LinearIndependent ℂ vK := by
      -- `K.subtype ∘ vK = v₁`.
      have hcomp : LinearIndependent ℂ (K.subtype ∘ vK) := by
        simpa [vK, v₁] using hv₁_li
      exact LinearIndependent.of_comp K.subtype hcomp
    have hvK_span : Submodule.span ℂ (Set.range vK) = ⊤ := by
      -- This is tautological: `K` is the span of the same generators.
      simpa [vK, K, v₁] using
        (Submodule.span_range_subtype_eq_top_iff (R := ℂ) (p := K) (s := v₁) hv₁_mem).2 rfl
    have hvK_sp' : (⊤ : Submodule ℂ K) ≤ Submodule.span ℂ (Set.range vK) := by
      simp [hvK_span]
    let bK : Module.Basis ι₁ ℂ K := Module.Basis.mk hvK_li hvK_sp'
    -- The prescribed values for `A(v i)` when `i ≠ 0`.
    let Agen₁ : ι₁ → H := fun i => (1 / (y i.1 : ℂ)) • (v i.1 - φ)
    -- Define a linear functional on `K` by prescribing its values on the basis `vK`.
    let ℓ : K →ₗ[ℂ] ℂ := (bK.constr ℂ fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i))
    let ℓc : StrongDual ℂ K :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := K) (F' := ℂ)) ℓ
    let wK : K := by
      letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
      letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
          (@SeminormedAddCommGroup.toPseudoMetricSpace K
            (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
        FiniteDimensional.complete ℂ K
      exact (InnerProductSpace.toDual ℂ K).symm ℓc
    let w0_base : H := (wK : H)
    -- Use the orthogonal decomposition `H = K ⊕ Kᗮ` to adjust `w0_base` so that
    -- `⟪w0, v0⟫` is real (needed for symmetry at `(0,0)`).
    haveI : K.HasOrthogonalProjection := by infer_instance
    let u : H := (v 0) - K.starProjection (v 0)
    have huK : ∀ x ∈ K, inner (𝕜 := ℂ) u x = 0 := by
      intro x hx
      -- This is exactly the orthogonality characterization of `K.starProjection`.
      simpa [u] using (K.starProjection_inner_eq_zero (v := v 0) x hx)
    have hu0 : u ≠ 0 := by
      intro hu
      have hv0_mem : v 0 ∈ K := by
        -- `u = v0 - proj v0 = 0` implies `proj v0 = v0`, hence `v0 ∈ K`.
        have : K.starProjection (v 0) = v 0 := by
          have : (v 0) - K.starProjection (v 0) = 0 := by simpa [u] using hu
          exact (sub_eq_zero.mp this).symm
        simpa [K.starProjection_eq_self_iff] using this
      -- But `v 0` is not in the span of the other `v i` by linear independence.
      have hrange : Set.range v₁ = v '' ({0}ᶜ : Set (Fin (n + 1))) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨i.1, ?_, rfl⟩
          simp
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i, ?_⟩, rfl⟩
          simpa using hi
      have hv0_not :
          v 0 ∉ Submodule.span ℂ (v '' ({0}ᶜ : Set (Fin (n + 1)))) := by
        simpa using (hv_li.notMem_span 0)
      have : v 0 ∈ Submodule.span ℂ (v '' ({0}ᶜ : Set (Fin (n + 1)))) := by
        simpa [K, hrange] using hv0_mem
      exact hv0_not this
    have hu_inner : inner (𝕜 := ℂ) u (v 0) = inner (𝕜 := ℂ) u u := by
      -- `v0 = u + proj v0` and `u ⟂ K`, while `proj v0 ∈ K`.
      have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
      calc
        inner (𝕜 := ℂ) u (v 0)
            = inner (𝕜 := ℂ) u (u + K.starProjection (v 0)) := by
                simp [u, sub_add_cancel]
        _ = inner (𝕜 := ℂ) u u + inner (𝕜 := ℂ) u (K.starProjection (v 0)) := by
              simp [inner_add_right]
        _ = inner (𝕜 := ℂ) u u := by
              have : inner (𝕜 := ℂ) u (K.starProjection (v 0)) = 0 := by
                simpa using (huK (K.starProjection (v 0)) hproj_mem)
              simp [this]
    have hu_inner_ne0 : inner (𝕜 := ℂ) u (v 0) ≠ 0 := by
      -- `⟪u,u⟫ ≠ 0` when `u ≠ 0`.
      have huu_ne0 : inner (𝕜 := ℂ) u u ≠ 0 :=
        (inner_self_ne_zero (𝕜 := ℂ) (x := u)).2 hu0
      simpa [hu_inner] using huu_ne0
    -- Normalize `u` so that `⟪u', v0⟫ = 1`.
    let u' : H := (1 / star (inner (𝕜 := ℂ) u (v 0))) • u
    have hu'_inner : inner (𝕜 := ℂ) u' (v 0) = (1 : ℂ) := by
      calc
        inner (𝕜 := ℂ) u' (v 0)
            = star (1 / star (inner (𝕜 := ℂ) u (v 0))) * inner (𝕜 := ℂ) u (v 0) := by
                simp [u', inner_smul_left]
        _ = (1 / inner (𝕜 := ℂ) u (v 0)) * inner (𝕜 := ℂ) u (v 0) := by
              simp
        _ = (1 : ℂ) := by
              field_simp [hu_inner_ne0]
    -- Adjust by a purely imaginary multiple of `u'` to make `⟪w0, v0⟫` real.
    let a : ℂ := inner (𝕜 := ℂ) w0_base (v 0)
    let α : ℂ := (Complex.im a) * Complex.I
    let w0 : H := w0_base + α • u'
    let w : Fin (n + 1) → H :=
      fun i => if h : i = 0 then w0 else (1 / (y i : ℂ)) • (v i - φ)
    let A : H →ₗ[ℂ] H := (b.constr ℂ w)
    have hA_apply' : ∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ) := by
      intro i hi
      have : (A (b i)) = w i := by
        exact b.constr_basis (S := ℂ) (f := w) i
      -- Use `b i = v i` and `i ≠ 0` to simplify `w i`.
      have hbvi : b i = v i := hb i
      simp [hbvi, w, hi] at this
      simpa [hbvi] using this
    have hb0 : b 0 = v 0 := hb 0
    have hAv0 : A (v 0) = w0 := by
      have : A (b 0) = w 0 := by
        exact b.constr_basis (S := ℂ) (f := w) 0
      have : A (b 0) = w0 := by simpa [w] using this
      simpa [hb0] using this
    have h00 : inner (𝕜 := ℂ) (A (v 0)) (v 0) = inner (𝕜 := ℂ) (v 0) (A (v 0)) := by
      have him : (inner (𝕜 := ℂ) w0 (v 0)).im = 0 := by
        simp [w0, a, α, inner_add_left, inner_smul_left, hu'_inner]
      have hstar : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) w0 (v 0) := by
        simpa [Complex.star_def] using (Complex.conj_eq_iff_im).2 him
      have hz : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) (v 0) w0 := by
        simp
      calc
        inner (𝕜 := ℂ) (A (v 0)) (v 0)
            = inner (𝕜 := ℂ) w0 (v 0) := by simp [hAv0]
        _ = star (inner (𝕜 := ℂ) w0 (v 0)) := by simpa using hstar.symm
        _ = inner (𝕜 := ℂ) (v 0) w0 := hz
        _ = inner (𝕜 := ℂ) (v 0) (A (v 0)) := by simp [hAv0]
    have h0j : ∀ j : Fin (n + 1), j ≠ 0 →
        inner (𝕜 := ℂ) (A (v 0)) (v j) = inner (𝕜 := ℂ) (v 0) (A (v j)) := by
      intro j hj0
      have hvj_mem : v j ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨j, hj0⟩, rfl⟩
      let xK : K := ⟨v j, hvj_mem⟩
      have hu'K : inner (𝕜 := ℂ) u' (v j) = 0 := by
        have : inner (𝕜 := ℂ) u (v j) = 0 := huK (v j) hvj_mem
        simp [u', inner_smul_left, this]
      have hw_toDual : inner (𝕜 := ℂ) wK xK = ℓc xK := by
        letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
        letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
            (@SeminormedAddCommGroup.toPseudoMetricSpace K
              (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
          FiniteDimensional.complete ℂ K
        dsimp [wK]
        exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := K) (x := xK) (y := ℓc)
      have hbKj : bK ⟨j, hj0⟩ = vK ⟨j, hj0⟩ := by
        exact Module.Basis.mk_apply (hli := hvK_li) (hsp := hvK_sp') (v := vK) ⟨j, hj0⟩
      have hℓx : ℓ xK = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
        have : ℓ (bK ⟨j, hj0⟩) = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
          simpa [ℓ] using
            (bK.constr_basis (S := ℂ)
              (f := fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i)) ⟨j, hj0⟩)
        -- Rewrite `xK = vK ⟨j,hj0⟩ = bK ⟨j,hj0⟩`.
        simpa [xK, vK, hbKj] using this
      have hw0_base :
          inner (𝕜 := ℂ) w0_base (v j) = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
        -- Convert `inner` in `K` into `inner` in `H`.
        have : inner (𝕜 := ℂ) wK xK = ℓ xK := by
          simpa [ℓc] using hw_toDual
        -- Coerce back to `H` and use `hℓx`.
        have : inner (𝕜 := ℂ) w0_base (v j) = ℓ xK := by
          -- `inner wK xK = inner (↑wK) (↑xK)`.
          simpa [w0_base, xK] using (Submodule.coe_inner K wK xK).symm.trans this
        simp [this, hℓx]
      have hAvj : A (v j) = Agen₁ ⟨j, hj0⟩ := by
        simpa [Agen₁] using hA_apply' j hj0
      calc
        inner (𝕜 := ℂ) (A (v 0)) (v j)
            = inner (𝕜 := ℂ) w0 (v j) := by simp [hAv0]
        _ = inner (𝕜 := ℂ) w0_base (v j) + inner (𝕜 := ℂ) (α • u') (v j) := by
              simp [w0, inner_add_left]
        _ = inner (𝕜 := ℂ) w0_base (v j) := by
              simp [inner_smul_left, hu'K]
        _ = inner (𝕜 := ℂ) (v 0) (A (v j)) := by
              simpa [hAvj] using hw0_base
    have hsymm_on_v :
        ∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (A (v i)) (v j) = inner (𝕜 := ℂ) (v i) (A (v j)) := by
      intro i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          exact h00
        · exact h0j j hj
      · by_cases hj : j = 0
        · subst hj
          -- Take `star` of the `(0,i)` identity.
          have h := h0j i hi
          have h' :
              star (inner (𝕜 := ℂ) (A (v 0)) (v i)) =
                star (inner (𝕜 := ℂ) (v 0) (A (v i))) :=
            congrArg star h
          -- Rewrite via `inner_conj_symm`.
          -- `star ⟪A v0, v_i⟫ = ⟪v_i, A v0⟫` and `star ⟪v0, A v_i⟫ = ⟪A v_i, v0⟫`.
          simpa [inner_conj_symm] using h'.symm
        · -- `i,j ≠ 0`: use the previously established symmetry on prescribed values.
          have hAi : A (v i) = (1 / (y i : ℂ)) • (v i - φ) := hA_apply' i hi
          have hAj : A (v j) = (1 / (y j : ℂ)) • (v j - φ) := hA_apply' j hj
          simpa [hAi, hAj] using inner_prescribed_symm (i := i) (j := j) hi hj
    have hsymm_basis :
        ∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (A (b i)) (b j) = inner (𝕜 := ℂ) (b i) (A (b j)) := by
      intro i j
      simpa [hb i, hb j] using hsymm_on_v i j
    have hsymm : A.IsSymmetric := by
      intro x y
      classical
      -- Expand `x` and `y` as `Finset.univ`-sums in the basis `b` (so that we can use
      -- `map_sum`, `sum_inner`, and `inner_sum` without fighting definitional equalities).
      set sx : Finset (Fin (n + 1)) := Finset.univ
      set sy : Finset (Fin (n + 1)) := Finset.univ
      set fx : Fin (n + 1) → H := fun i => (b.repr x i) • b i
      set fy : Fin (n + 1) → H := fun j => (b.repr y j) • b j
      have hx : x = ∑ i ∈ sx, fx i := by
        -- `b.sum_repr x : (∑ i, fx i) = x`
        simp [sx, fx]
      have hy : y = ∑ j ∈ sy, fy j := by
        simp [sy, fy]
      -- Reduce symmetry to the basis vectors.
      rw [hx, hy]
      -- Push `A` inside the finite sums.
      rw [map_sum (g := A) (f := fx) (s := sx)]
      rw [map_sum (g := A) (f := fy) (s := sy)]
      -- Expand by sesquilinearity and use `hsymm_basis`.
      rw [sum_inner sx (fun i => A (fx i)) (∑ j ∈ sy, fy j)]
      rw [sum_inner sx fx (∑ j ∈ sy, A (fy j))]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [inner_sum sy fy (A (fx i))]
      rw [inner_sum sy (fun j => A (fy j)) (fx i)]
      refine Finset.sum_congr rfl ?_
      intro j hj
      -- Simplify scalars and apply `hsymm_basis` on the basis vectors.
      have hL :
          inner (𝕜 := ℂ) (A (fx i)) (fy j)
            =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (A (b i)) (b j) := by
        dsimp [fx, fy]
        calc
          inner (𝕜 := ℂ) (A ((b.repr x i) • b i)) ((b.repr y j) • b j)
              = inner (𝕜 := ℂ) ((b.repr x i) • A (b i)) ((b.repr y j) • b j) := by
                  simp []
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                inner (𝕜 := ℂ) (A (b i)) ((b.repr y j) • b j) := by
                simp [inner_smul_left]
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                ((b.repr y j) * inner (𝕜 := ℂ) (A (b i)) (b j)) := by
                simp [inner_smul_right]
          _ =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (A (b i)) (b j) := by
                simp [mul_assoc]
      have hR :
          inner (𝕜 := ℂ) (fx i) (A (fy j))
            =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (b i) (A (b j)) := by
        dsimp [fx, fy]
        calc
          inner (𝕜 := ℂ) ((b.repr x i) • b i) (A ((b.repr y j) • b j))
              = inner (𝕜 := ℂ) ((b.repr x i) • b i) ((b.repr y j) • A (b j)) := by
                  simp []
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                inner (𝕜 := ℂ) (b i) ((b.repr y j) • A (b j)) := by
                simp [inner_smul_left]
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                ((b.repr y j) * inner (𝕜 := ℂ) (b i) (A (b j))) := by
                simp [inner_smul_right]
          _ =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (b i) (A (b j)) := by
                simp [mul_assoc]
      simp [hL, hR, hsymm_basis, mul_assoc]
    refine ⟨A, ?_, hA_apply'⟩
    -- Convert symmetry to self-adjointness.
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint (A := A)).1 hsymm
  rcases hA with ⟨A, hA_sa, hA_apply⟩
  refine ⟨H, instH, instI, instFD, v, φ, A, hv, rfl, hA_sa, hA_apply, ?_, ?_⟩
  · intro i hi
    rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
    have hyi0 : (y i : ℂ) ≠ 0 := by
      exact_mod_cast (hyne0 i hi)
    calc
      v i - (y i : ℂ) • A (v i)
          = v i - (y i : ℂ) • ((1 / (y i : ℂ)) • (v i - φ)) := by
              simp [hA_apply i hi]
      _ = v i - ((y i : ℂ) * (1 / (y i : ℂ))) • (v i - φ) := by
            simp [smul_smul]
      _ = v i - (1 : ℂ) • (v i - φ) := by
            simp [div_eq_mul_inv, hyi0]
      _ = v i - (v i - φ) := by simp
      _ = φ := by
            simp [sub_eq_add_neg, add_comm]
  · intro i hi
    rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
    -- Derive the scalar identity from the `j = 0` Gram entry and the kernel definition.
    have hyi0 : y i ≠ 0 := hyne0 i hi
    have hyi0C : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi0
    have h_inner : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) 0 : ℂ) := by
      simpa [φ, hy0] using hv i 0
    have h_kernel : loewnerKernel f (y i) 0 = (f (y i) - f 0) / (y i) := by
      simpa using (loewnerKernel_zero_right (f := f) (x := y i) hyi0)
    have h_inner' : inner (𝕜 := ℂ) (v i) φ = ((f (y i) - f 0) / (y i) : ℂ) := by
      simpa [h_kernel] using h_inner
    have h_mul :
        (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ = (f (y i) : ℂ) - (f 0 : ℂ) := by
      -- Multiply the `j = 0` Gram identity by `y i` and cancel the denominator.
      have :
          (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ = ((f (y i) - f 0 : ℝ) : ℂ) := by
        -- `ℂ` is commutative, so cancellation works by `simp`.
        simp [h_inner', div_eq_mul_inv, hyi0C, mul_comm]
      simpa [sub_eq_add_neg] using this
    -- Rearrange to the claimed scalar identity.
    calc
      (f (y i) : ℂ) = (f 0 : ℂ) + ((f (y i) : ℂ) - (f 0 : ℂ)) := by
        -- `a + (b - a) = b`.
        symm
        have :
            (f 0 : ℂ) + ((f (y i) : ℂ) - (f 0 : ℂ)) =
              (f 0 : ℂ) + (f (y i) : ℂ) - (f 0 : ℂ) := by
          simp [sub_eq_add_neg, add_assoc]
        simp [this]
      _ = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ := by
        simp [h_mul]

/-!
## PosSemidef version (degenerate Loewner matrix)

The theorem above assumes positive definiteness of the Loewner matrix, which forces linear
independence of the Gram family `v`.  For the hard direction of Löwner's theorem one needs the
semidefinite version, where degeneracies may occur.

The semidefinite version below, `koranyi_finite_construct_posSemidef_of_minor_posDef`, uses
the standard quotient construction (`ker` inclusion + `liftQ`) and assumes that the minor
away from the base point is positive definite.
-/

/-! ### Semidefinite minor-positive construction -/
/-- A semidefinite Loewner matrix with positive nonzero minor still gives the finite model. -/
theorem koranyi_finite_construct_posSemidef_of_minor_posDef
    (hy : pointsHyp (n := n) y)
    (hL : (loewnerMatrix (n := n) f y).PosSemidef)
    (hminor :
      ((loewnerMatrix (n := n) f y).submatrix
          (fun i : { i : Fin (n + 1) // i ≠ 0 } => i.1)
          (fun j : { j : Fin (n + 1) // j ≠ 0 } => j.1)).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        IsSelfAdjoint A ∧
        (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        (∀ i, i ≠ 0 →
          (f (y i) : ℂ) = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ) := by
  classical
  rcases exists_gram_vectors (n := n) (f := f) (y := y) hL with
    ⟨H, instH, instI, instFD, v, hv, hv_span⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  let φ : H := v 0
  -- The codimension-one subspace `K` spanned by the `v i` with `i ≠ 0`.
  let ι₁ : Type := { i : Fin (n + 1) // i ≠ 0 }
  let v₁ : ι₁ → H := fun i => v i.1
  let K : Submodule ℂ H := Submodule.span ℂ (Set.range v₁)
  letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
  letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
      (@SeminormedAddCommGroup.toPseudoMetricSpace K
        (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
    FiniteDimensional.complete ℂ K
  -- We assume the nonzero minor of the Loewner matrix is positive definite, hence the family `v₁`
  -- is linearly independent. This avoids the well-definedness issue in the fully degenerate case.
  have hv₁_li : LinearIndependent ℂ v₁ := by
    have hgram₁ :
        Matrix.gram ℂ v₁ =
          (loewnerMatrix (n := n) f y).submatrix (fun i : ι₁ => i.1) (fun j : ι₁ => j.1) := by
      ext i j
      simpa [Matrix.gram_apply, loewnerMatrix, v₁] using (hv i.1 j.1)
    have hpos : (Matrix.gram ℂ v₁).PosDef := by
      simpa [hgram₁] using hminor
    exact Matrix.linearIndependent_of_posDef_gram (𝕜 := ℂ) (v := v₁) hpos
  -- The prescribed values for `A(v i)` when `i ≠ 0`.
  let Agen₁ : ι₁ → H := fun i => (1 / (y i.1 : ℂ)) • (v i.1 - φ)
  -- Choose `Agen 0` so that the inner-product symmetry can hold.
  -- In the degenerate case `v 0 ∈ K` we define it by linearity from a relation expressing `v 0`
  -- as a linear combination of the generators `v i` (`i ≠ 0`).
  -- In the complementary case we use a Riesz construction on `K` and adjust along `Kᗮ`.
  let Agen0 : H :=
    if hv0 : v 0 ∈ K then
      Finsupp.linearCombination ℂ Agen₁
        (Classical.choose
          ((Finsupp.mem_span_range_iff_exists_finsupp (v := v₁) (x := v 0)).1 hv0))
    else
      -- Riesz construction on `K`: define a functional by prescribing its values on a basis.
      let hv₁_mem : ∀ i : ι₁, v₁ i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
      let vK : ι₁ → K := fun i => ⟨v₁ i, hv₁_mem i⟩
      have hvK_li : LinearIndependent ℂ vK := by
        have hcomp : LinearIndependent ℂ (K.subtype ∘ vK) := by
          simpa [vK, v₁] using hv₁_li
        exact LinearIndependent.of_comp K.subtype hcomp
      have hvK_span : Submodule.span ℂ (Set.range vK) = ⊤ := by
        simpa [vK, K, v₁] using
          (Submodule.span_range_subtype_eq_top_iff (R := ℂ) (p := K) (s := v₁) hv₁_mem).2 rfl
      have hvK_sp' : (⊤ : Submodule ℂ K) ≤ Submodule.span ℂ (Set.range vK) := by
        simp [hvK_span]
      let bK : Module.Basis ι₁ ℂ K := Module.Basis.mk hvK_li hvK_sp'
      let ℓ : K →ₗ[ℂ] ℂ := (bK.constr ℂ fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i))
      let ℓc : StrongDual ℂ K :=
        (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := K) (F' := ℂ)) ℓ
      let wK : K := by
        letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
        letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
            (@SeminormedAddCommGroup.toPseudoMetricSpace K
              (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
          FiniteDimensional.complete ℂ K
        exact (InnerProductSpace.toDual ℂ K).symm ℓc
      let w0_base : H := (wK : H)
      haveI : K.HasOrthogonalProjection := by infer_instance
      -- Orthogonal complement vector `u := v0 - proj_K v0`, nonzero because `v0 ∉ K`.
      let u : H := (v 0) - K.starProjection (v 0)
      have huK : ∀ x ∈ K, inner (𝕜 := ℂ) u x = 0 := by
        intro x hx
        simpa [u] using (K.starProjection_inner_eq_zero (v := v 0) x hx)
      have hu0 : u ≠ 0 := by
        intro hu
        have : v 0 ∈ K := by
          have h' : (v 0) - K.starProjection (v 0) = 0 := by simpa [u] using hu
          have : (v 0) = K.starProjection (v 0) := by simpa using (sub_eq_zero.mp h')
          have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
          -- Avoid `simp` here (it can hit `maxRecDepth`); rewrite the goal directly.
          rw [this]
          exact hproj_mem
        exact hv0 this
      have hu_inner : inner (𝕜 := ℂ) u (v 0) = inner (𝕜 := ℂ) u u := by
        have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
        calc
          inner (𝕜 := ℂ) u (v 0)
              = inner (𝕜 := ℂ) u (u + K.starProjection (v 0)) := by
                  simp [u, sub_add_cancel]
          _ = inner (𝕜 := ℂ) u u + inner (𝕜 := ℂ) u (K.starProjection (v 0)) := by
                simp [inner_add_right]
          _ = inner (𝕜 := ℂ) u u := by
                have : inner (𝕜 := ℂ) u (K.starProjection (v 0)) = 0 := by
                  simpa using (huK (K.starProjection (v 0)) hproj_mem)
                simp [this]
      have hu_inner_ne0 : inner (𝕜 := ℂ) u (v 0) ≠ 0 := by
        have huu_ne0 : inner (𝕜 := ℂ) u u ≠ 0 :=
          (inner_self_ne_zero (𝕜 := ℂ) (x := u)).2 hu0
        simpa [hu_inner] using huu_ne0
      -- Normalize `u` so that `⟪u', v0⟫ = 1`.
      let u' : H := (1 / star (inner (𝕜 := ℂ) u (v 0))) • u
      have hu'_inner : inner (𝕜 := ℂ) u' (v 0) = (1 : ℂ) := by
        calc
          inner (𝕜 := ℂ) u' (v 0)
              = star (1 / star (inner (𝕜 := ℂ) u (v 0))) * inner (𝕜 := ℂ) u (v 0) := by
                    simp [u', inner_smul_left]
          _ = (1 / inner (𝕜 := ℂ) u (v 0)) * inner (𝕜 := ℂ) u (v 0) := by
                simp
          _ = (1 : ℂ) := by
                field_simp [hu_inner_ne0]
      -- Adjust by a purely imaginary multiple of `u'` to make `⟪w0, v0⟫` real.
      let a : ℂ := inner (𝕜 := ℂ) w0_base (v 0)
      let α : ℂ := (Complex.im a) * Complex.I
      let w0 : H := w0_base + α • u'
      w0
  let Agen : Fin (n + 1) → H :=
    fun i => if h : i = 0 then Agen0 else (1 / (y i : ℂ)) • (v i - φ)
  have hsymm :
      ∀ i j : Fin (n + 1),
        inner (𝕜 := ℂ) (Agen i) (v j) = inner (𝕜 := ℂ) (v i) (Agen j) := by
    classical
    -- First record the key symmetry for the prescribed values on `v i` when `i,j ≠ 0`.
    have inner_prescribed_symm :
        ∀ {i j : Fin (n + 1)}, i ≠ 0 → j ≠ 0 →
          inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j) =
            inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
      intro i j hi hj
      rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
      have hyi0 : y i ≠ 0 := hyne0 i hi
      have hyj0 : y j ≠ 0 := hyne0 j hj
      have hyi0C : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi0
      have hyj0C : (y j : ℂ) ≠ 0 := by exact_mod_cast hyj0
      -- Expand both sides using the Gram equalities.
      have hLij : inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ) := hv i j
      have hL0j : inner (𝕜 := ℂ) φ (v j) = (loewnerKernel f (y 0) (y j) : ℂ) := by
        simpa [φ] using hv 0 j
      have hLi0 : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) (y 0) : ℂ) := by
        simpa [φ] using hv i 0
      -- Rewrite `y 0 = 0` on kernel entries.
      have hy0' : y 0 = 0 := hy0
      -- Reduce to the real kernel identity `koranyi_identity` (and `loewnerKernel_swap`
      -- for `i = j`).
      have hKoranyi :
          (loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) =
            (loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) := by
        by_cases hij : i = j
        · subst hij
          have hs : loewnerKernel f 0 (y i) = loewnerKernel f (y i) 0 := by
            simpa using (loewnerKernel_swap (f := f) 0 (y i))
          simp [hs, div_eq_mul_inv, sub_eq_add_neg]
        · have hyij : y i ≠ y j := by
            intro h
            exact hij (hyinj h)
          simpa [hy0'] using
            (koranyi_identity (f := f) (x := y i) (y := y j) hyi0 hyj0 hyij)
      have hKoranyiC :
          ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) =
            ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
        exact_mod_cast hKoranyi
      -- Finish by rewriting inner products into kernel entries.
      calc
        inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j)
            = (1 / (y i : ℂ)) * (inner (𝕜 := ℂ) (v i - φ) (v j)) := by
                simp [inner_smul_left]
        _ =
            (1 / (y i : ℂ)) *
              (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) φ (v j)) := by
              simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
        _ =
            (1 / (y i : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) - (loewnerKernel f 0 (y j) : ℂ)) := by
              simp [hLij, hL0j, hy0', sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
              simpa using hKoranyiC
        _ =
            (1 / (y j : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) - (loewnerKernel f (y i) 0 : ℂ)) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ =
            (1 / (y j : ℂ)) *
              (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) (v i) φ) := by
              simp [hLij, hLi0, hy0', φ, sub_eq_add_neg]
        _ = (1 / (y j : ℂ)) * inner (𝕜 := ℂ) (v i) (v j - φ) := by
              simp [inner_sub_right]
        _ = inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
              simp [inner_smul_right]
    -- The remaining cases use the definition of `Agen0`.
    by_cases hv0 : v 0 ∈ K
    · -- In the degenerate case `v0 ∈ K`, define `Agen0` by linearity from a relation.
      let c : ι₁ →₀ ℂ :=
        Classical.choose ((Finsupp.mem_span_range_iff_exists_finsupp (v := v₁) (x := v 0)).1 hv0)
      have hc : Finsupp.linearCombination ℂ v₁ c = v 0 :=
        Classical.choose_spec
          ((Finsupp.mem_span_range_iff_exists_finsupp (v := v₁) (x := v 0)).1 hv0)
      have hAgen0 : Agen0 = Finsupp.linearCombination ℂ Agen₁ c := by
        simp [Agen0, hv0, c]
      -- Auxiliary lemma: symmetry with `i = 0`, `j ≠ 0`.
      have h0j : ∀ j : Fin (n + 1), j ≠ 0 →
          inner (𝕜 := ℂ) Agen0 (v j) = inner (𝕜 := ℂ) (v 0) (Agen j) := by
        intro j hj0
        have hv0_eq : Finsupp.linearCombination ℂ v₁ c = v 0 := hc
        have hsymm₁ :
            ∀ i : ι₁,
              inner (𝕜 := ℂ) (Agen₁ i) (v j) =
                inner (𝕜 := ℂ) (v i.1) (Agen j) := by
          intro i
          have :
              inner (𝕜 := ℂ) (Agen₁ i) (v j) =
                inner (𝕜 := ℂ) (v i.1) ((1 / (y j : ℂ)) • (v j - φ)) := by
            simpa [Agen₁, Agen, hj0]
              using (inner_prescribed_symm (i := i.1) (j := j) i.2 hj0)
          simpa [Agen₁, Agen, hj0] using this
        have hL :
            inner (𝕜 := ℂ) (Finsupp.linearCombination ℂ Agen₁ c) (v j) =
              inner (𝕜 := ℂ) (Finsupp.linearCombination ℂ v₁ c) (Agen j) := by
          classical
          refine
            Finsupp.induction_linear
              (motive := fun c =>
                inner (𝕜 := ℂ) (Finsupp.linearCombination ℂ Agen₁ c) (v j) =
                  inner (𝕜 := ℂ) (Finsupp.linearCombination ℂ v₁ c) (Agen j))
              c
              (by simp)
              (by
                intro c₁ c₂ hc₁ hc₂
                simp [map_add, inner_add_left, hc₁, hc₂])
              (by
                intro a r
                calc
                  inner (𝕜 := ℂ)
                      (Finsupp.linearCombination ℂ Agen₁ (Finsupp.single a r)) (v j)
                      = inner (𝕜 := ℂ) (r • Agen₁ a) (v j) := by
                          simp
                  _ = conj r * inner (𝕜 := ℂ) (Agen₁ a) (v j) := by
                        simp [inner_smul_left]
                  _ = conj r * inner (𝕜 := ℂ) (v₁ a) (Agen j) := by
                      simpa [v₁] using congrArg (fun z => conj r * z) (hsymm₁ a)
                  _ = inner (𝕜 := ℂ) (r • v₁ a) (Agen j) := by
                        simp [inner_smul_left]
                  _ =
                      inner (𝕜 := ℂ)
                        (Finsupp.linearCombination ℂ v₁ (Finsupp.single a r)) (Agen j) := by
                        simp)
        simpa [hAgen0, hv0_eq] using hL
      have h00 :
          inner (𝕜 := ℂ) Agen0 (v 0) = inner (𝕜 := ℂ) (v 0) Agen0 := by
        have hv0_eq : Finsupp.linearCombination ℂ v₁ c = v 0 := hc
        calc
          inner (𝕜 := ℂ) Agen0 (v 0)
              = inner (𝕜 := ℂ) Agen0 (Finsupp.linearCombination ℂ v₁ c) := by
                    simp [hv0_eq]
          _ = inner (𝕜 := ℂ) (v 0) (Finsupp.linearCombination ℂ Agen₁ c) := by
                classical
                refine
                  Finsupp.induction_linear
                    (motive := fun c =>
                      inner (𝕜 := ℂ) Agen0 (Finsupp.linearCombination ℂ v₁ c) =
                        inner (𝕜 := ℂ) (v 0) (Finsupp.linearCombination ℂ Agen₁ c))
                    c
                    (by simp)
                    (by
                      intro c₁ c₂ hc₁ hc₂
                      simp [map_add, inner_add_right, hc₁, hc₂])
                    (by
                      intro a r
                      have ha0 : (a.1 : Fin (n + 1)) ≠ 0 := a.2
                      have h0a :
                          inner (𝕜 := ℂ) Agen0 (v a.1) =
                            inner (𝕜 := ℂ) (v 0) (Agen a.1) :=
                        h0j a.1 ha0
                      have hAgen : Agen a.1 = Agen₁ a := by
                        simp [Agen, Agen₁, a.2]
                      have h0a' :
                          inner (𝕜 := ℂ) Agen0 (v₁ a) =
                            inner (𝕜 := ℂ) (v 0) (Agen₁ a) := by
                        simpa [v₁, hAgen] using h0a
                      calc
                        inner (𝕜 := ℂ) Agen0
                            (Finsupp.linearCombination ℂ v₁ (Finsupp.single a r))
                            = inner (𝕜 := ℂ) Agen0 (r • v₁ a) := by simp
                        _ = r * inner (𝕜 := ℂ) Agen0 (v₁ a) := by simp [inner_smul_right]
                        _ = r * inner (𝕜 := ℂ) (v 0) (Agen₁ a) := by simp [h0a']
                        _ = inner (𝕜 := ℂ) (v 0) (r • Agen₁ a) := by
                              simp [inner_smul_right]
                        _ =
                            inner (𝕜 := ℂ) (v 0)
                              (Finsupp.linearCombination ℂ Agen₁ (Finsupp.single a r)) := by
                              simp)
          _ = inner (𝕜 := ℂ) (v 0) Agen0 := by
                simp [hAgen0]
      intro i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          simp [Agen, h00]
        · simpa [Agen, hj] using (h0j j hj)
      · by_cases hj : j = 0
        · subst hj
          have h := h0j i hi
          have h' :
              star (inner (𝕜 := ℂ) Agen0 (v i)) = star (inner (𝕜 := ℂ) (v 0) (Agen i)) :=
            congrArg star h
          simpa [Agen, inner_conj_symm] using h'.symm
        · simpa [Agen, hi, hj] using inner_prescribed_symm (i := i) (j := j) hi hj
    · -- In the complementary case, `Agen0` was built by a Riesz construction plus
      -- a `Kᗮ` adjustment.
      have hAgen0 : Agen0 = Agen0 := rfl
      haveI : K.HasOrthogonalProjection := by infer_instance
      -- Rebuild the ingredients from the `Agen0` definition to obtain the needed identities.
      -- We only need: (0,0) symmetry and (0,j) identities for `j ≠ 0`.
      let hv₁_mem : ∀ i : ι₁, v₁ i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
      let vK : ι₁ → K := fun i => ⟨v₁ i, hv₁_mem i⟩
      have hvK_li : LinearIndependent ℂ vK := by
        have hcomp : LinearIndependent ℂ (K.subtype ∘ vK) := by
          simpa [vK, v₁] using hv₁_li
        exact LinearIndependent.of_comp K.subtype hcomp
      have hvK_span : Submodule.span ℂ (Set.range vK) = ⊤ := by
        simpa [vK, K, v₁] using
          (Submodule.span_range_subtype_eq_top_iff (R := ℂ) (p := K) (s := v₁) hv₁_mem).2 rfl
      have hvK_sp' : (⊤ : Submodule ℂ K) ≤ Submodule.span ℂ (Set.range vK) := by
        simp [hvK_span]
      let bK : Module.Basis ι₁ ℂ K := Module.Basis.mk hvK_li hvK_sp'
      let ℓ : K →ₗ[ℂ] ℂ := (bK.constr ℂ fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i))
      let ℓc : StrongDual ℂ K :=
        (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := K) (F' := ℂ)) ℓ
      let wK : K := by
        letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
        letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
            (@SeminormedAddCommGroup.toPseudoMetricSpace K
              (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
          FiniteDimensional.complete ℂ K
        exact (InnerProductSpace.toDual ℂ K).symm ℓc
      let w0_base : H := (wK : H)
      let u : H := (v 0) - K.starProjection (v 0)
      have huK : ∀ x ∈ K, inner (𝕜 := ℂ) u x = 0 := by
        intro x hx
        simpa [u] using (K.starProjection_inner_eq_zero (v := v 0) x hx)
      have hu0 : u ≠ 0 := by
        intro hu
        have : v 0 ∈ K := by
          have h' : (v 0) - K.starProjection (v 0) = 0 := by simpa [u] using hu
          have : (v 0) = K.starProjection (v 0) := by simpa using (sub_eq_zero.mp h')
          have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
          -- Avoid `simp` here (it can hit `maxRecDepth`); rewrite the goal directly.
          rw [this]
          exact hproj_mem
        exact hv0 this
      have hu_inner : inner (𝕜 := ℂ) u (v 0) = inner (𝕜 := ℂ) u u := by
        have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
        calc
          inner (𝕜 := ℂ) u (v 0)
              = inner (𝕜 := ℂ) u (u + K.starProjection (v 0)) := by
                  simp [u, sub_add_cancel]
          _ = inner (𝕜 := ℂ) u u + inner (𝕜 := ℂ) u (K.starProjection (v 0)) := by
                simp [inner_add_right]
          _ = inner (𝕜 := ℂ) u u := by
                have : inner (𝕜 := ℂ) u (K.starProjection (v 0)) = 0 := by
                  simpa using (huK (K.starProjection (v 0)) hproj_mem)
                simp [this]
      have hu_inner_ne0 : inner (𝕜 := ℂ) u (v 0) ≠ 0 := by
        have huu_ne0 : inner (𝕜 := ℂ) u u ≠ 0 :=
          (inner_self_ne_zero (𝕜 := ℂ) (x := u)).2 hu0
        simpa [hu_inner] using huu_ne0
      let u' : H := (1 / star (inner (𝕜 := ℂ) u (v 0))) • u
      have hu'_inner : inner (𝕜 := ℂ) u' (v 0) = (1 : ℂ) := by
        calc
          inner (𝕜 := ℂ) u' (v 0)
              = star (1 / star (inner (𝕜 := ℂ) u (v 0))) * inner (𝕜 := ℂ) u (v 0) := by
                    simp [u', inner_smul_left]
          _ = (1 / inner (𝕜 := ℂ) u (v 0)) * inner (𝕜 := ℂ) u (v 0) := by
                simp
          _ = (1 : ℂ) := by
                field_simp [hu_inner_ne0]
      let a : ℂ := inner (𝕜 := ℂ) w0_base (v 0)
      let α : ℂ := (Complex.im a) * Complex.I
      let w0 : H := w0_base + α • u'
      have hAgen0' : Agen0 = w0 := by
        simp [Agen0, hv0, vK, bK, ℓ, ℓc, wK, w0_base, u, u', a, α, w0]
      have h00 :
          inner (𝕜 := ℂ) Agen0 (v 0) = inner (𝕜 := ℂ) (v 0) Agen0 := by
        have him : (inner (𝕜 := ℂ) w0 (v 0)).im = 0 := by
          simp [w0, a, α, inner_add_left, inner_smul_left, hu'_inner]
        have hstar : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) w0 (v 0) := by
          simpa [Complex.star_def] using (Complex.conj_eq_iff_im).2 him
        have hz : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) (v 0) w0 := by
          simp
        calc
          inner (𝕜 := ℂ) Agen0 (v 0)
              = inner (𝕜 := ℂ) w0 (v 0) := by simp [hAgen0']
          _ = star (inner (𝕜 := ℂ) w0 (v 0)) := by simpa using hstar.symm
          _ = inner (𝕜 := ℂ) (v 0) w0 := hz
          _ = inner (𝕜 := ℂ) (v 0) Agen0 := by simp [hAgen0']
      have h0j : ∀ j : Fin (n + 1), j ≠ 0 →
          inner (𝕜 := ℂ) Agen0 (v j) = inner (𝕜 := ℂ) (v 0) (Agen j) := by
        intro j hj0
        have hvj_mem : v j ∈ K := by
          refine Submodule.subset_span ?_
          exact ⟨⟨j, hj0⟩, rfl⟩
        let xK : K := ⟨v j, hvj_mem⟩
        have hu'K : inner (𝕜 := ℂ) u' (v j) = 0 := by
          have : inner (𝕜 := ℂ) u (v j) = 0 := huK (v j) hvj_mem
          simp [u', inner_smul_left, this]
        have hw_toDual : inner (𝕜 := ℂ) wK xK = ℓc xK := by
          letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
          letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
              (@SeminormedAddCommGroup.toPseudoMetricSpace K
                (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
            FiniteDimensional.complete ℂ K
          dsimp [wK]
          exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := K) (x := xK) (y := ℓc)
        have hbKj : bK ⟨j, hj0⟩ = vK ⟨j, hj0⟩ := by
          exact Module.Basis.mk_apply (hli := hvK_li) (hsp := hvK_sp') (v := vK) ⟨j, hj0⟩
        have hℓx : ℓ xK = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
          have : ℓ (bK ⟨j, hj0⟩) = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
            simpa [ℓ] using
              (bK.constr_basis (S := ℂ)
                (f := fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i)) ⟨j, hj0⟩)
          simpa [xK, vK, hbKj] using this
        have hw0_base :
            inner (𝕜 := ℂ) w0_base (v j) =
              inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
          have : inner (𝕜 := ℂ) wK xK = ℓ xK := by
            simpa [ℓc] using hw_toDual
          have : inner (𝕜 := ℂ) w0_base (v j) = ℓ xK := by
            simpa [w0_base, xK] using (Submodule.coe_inner K wK xK).symm.trans this
          simp [this, hℓx]
        have hAvj : Agen j = Agen₁ ⟨j, hj0⟩ := by
          simp [Agen, Agen₁, hj0]
        calc
          inner (𝕜 := ℂ) Agen0 (v j)
              = inner (𝕜 := ℂ) w0 (v j) := by simp [hAgen0']
          _ = inner (𝕜 := ℂ) w0_base (v j) + inner (𝕜 := ℂ) (α • u') (v j) := by
                simp [w0, inner_add_left]
          _ = inner (𝕜 := ℂ) w0_base (v j) := by
                simp [inner_smul_left, hu'K]
          _ = inner (𝕜 := ℂ) (v 0) (Agen j) := by
                simpa [hAvj] using hw0_base
      intro i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          simp [Agen, h00]
        · simpa [Agen, hj] using (h0j j hj)
      · by_cases hj : j = 0
        · subst hj
          have h := h0j i hi
          have h' :
              star (inner (𝕜 := ℂ) Agen0 (v i)) =
                star (inner (𝕜 := ℂ) (v 0) (Agen i)) :=
            congrArg star h
          simpa [Agen, inner_conj_symm] using h'.symm
        · simpa [Agen, hi, hj] using inner_prescribed_symm (i := i) (j := j) hi hj
  -- With the symmetry on the generators, we can descend `Agen` along the relations of the `v i`.
  let C : Type := Fin (n + 1) →₀ ℂ
  let lcV : C →ₗ[ℂ] H := Finsupp.linearCombination ℂ v
  let lcW : C →ₗ[ℂ] H := Finsupp.linearCombination ℂ Agen
  have hlcV_surj : Function.Surjective lcV := by
    simpa [lcV] using
      (span_range_eq_top_iff_surjective_finsuppLinearCombination (R := ℂ) (v := v)).1 hv_span
  have hker : LinearMap.ker lcV ≤ LinearMap.ker lcW := by
    intro c hc
    have hc0 : lcV c = 0 := by
      simpa [LinearMap.mem_ker] using hc
    have hz_right : ∀ j : Fin (n + 1), inner (𝕜 := ℂ) (lcW c) (v j) = 0 := by
      intro j
      have :
          inner (𝕜 := ℂ) (lcW c) (v j) =
            inner (𝕜 := ℂ) (lcV c) (Agen j) := by
        classical
        refine
          Finsupp.induction_linear
            (motive := fun c =>
              inner (𝕜 := ℂ) (lcW c) (v j) = inner (𝕜 := ℂ) (lcV c) (Agen j))
            c
            (by simp [lcV, lcW])
            (by
              intro c₁ c₂ hc₁ hc₂
              simp [map_add, inner_add_left, hc₁, hc₂])
            (by
              intro a r
              calc
                inner (𝕜 := ℂ) (lcW (Finsupp.single a r)) (v j)
                    = inner (𝕜 := ℂ) (r • Agen a) (v j) := by
                        have hW : lcW (Finsupp.single a r) = r • Agen a := by
                          dsimp [lcW]
                          exact
                            (Finsupp.linearCombination_single (R := ℂ) (v := Agen)
                              (c := r) (a := a))
                        simp [hW]
                _ = conj r * inner (𝕜 := ℂ) (Agen a) (v j) := by simp [inner_smul_left]
                _ = conj r * inner (𝕜 := ℂ) (v a) (Agen j) := by simp [hsymm a j]
                _ = inner (𝕜 := ℂ) (r • v a) (Agen j) := by simp [inner_smul_left]
                _ = inner (𝕜 := ℂ) (lcV (Finsupp.single a r)) (Agen j) := by
                      have hV : lcV (Finsupp.single a r) = r • v a := by
                        dsimp [lcV]
                        exact
                          (Finsupp.linearCombination_single (R := ℂ) (v := v) (c := r) (a := a))
                      simp [hV])
      calc
        inner (𝕜 := ℂ) (lcW c) (v j) = inner (𝕜 := ℂ) (lcV c) (Agen j) := this
        _ = 0 := by simp [hc0]
    have hz_left : ∀ j : Fin (n + 1), inner (𝕜 := ℂ) (v j) (lcW c) = 0 := by
      intro j
      exact (inner_eq_zero_symm).1 (hz_right j)
    have hz_orth : lcW c ∈ (Submodule.span ℂ (Set.range v))ᗮ := by
      refine (Submodule.mem_orthogonal (K := Submodule.span ℂ (Set.range v)) (v := lcW c)).2 ?_
      intro u hu
      refine Submodule.span_induction (R := ℂ) (s := Set.range v)
        (p := fun u _ => inner (𝕜 := ℂ) u (lcW c) = 0)
        (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hu
      · intro x hx
        rcases hx with ⟨j, rfl⟩
        simpa using hz_left j
      · simp
      · intro x y _ _ hx hy
        simp [inner_add_left, hx, hy]
      · intro a x _ hx
        simp [inner_smul_left, hx]
    have hz_top : lcW c ∈ (⊤ : Submodule ℂ H)ᗮ := by
      simpa [hv_span] using hz_orth
    have hz_bot : lcW c ∈ (⊥ : Submodule ℂ H) := by
      simpa [Submodule.top_orthogonal_eq_bot] using hz_top
    simpa using hz_bot
  let lcWq : (C ⧸ LinearMap.ker lcV) →ₗ[ℂ] H :=
    (LinearMap.ker lcV).liftQ lcW hker
  let e : (C ⧸ LinearMap.ker lcV) ≃ₗ[ℂ] H :=
    lcV.quotKerEquivOfSurjective hlcV_surj
  let A : H →ₗ[ℂ] H := lcWq ∘ₗ e.symm.toLinearMap
  have hA_apply : ∀ i : Fin (n + 1), A (v i) = Agen i := by
    intro i
    have hv_single : lcV (Finsupp.single i (1 : ℂ)) = v i := by
      calc
        lcV (Finsupp.single i (1 : ℂ)) = (1 : ℂ) • v i := by
          dsimp [lcV]
          exact
            (Finsupp.linearCombination_single (R := ℂ) (v := v)
              (c := (1 : ℂ)) (a := i))
        _ = v i := by simp
    have he_single :
        e.symm (lcV (Finsupp.single i (1 : ℂ))) =
          (Submodule.Quotient.mk (Finsupp.single i (1 : ℂ)) :
            C ⧸ LinearMap.ker lcV) := by
      exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := lcV) hlcV_surj
        (x := Finsupp.single i (1 : ℂ))
    calc
      A (v i)
          = lcWq (e.symm (lcV (Finsupp.single i (1 : ℂ)))) := by
              simp [A, hv_single]
      _ = lcWq (Submodule.Quotient.mk (Finsupp.single i (1 : ℂ))) := by
            simp [he_single]
      _ = lcW (Finsupp.single i (1 : ℂ)) := by
            simp [lcWq]
      _ = Agen i := by
            calc
              lcW (Finsupp.single i (1 : ℂ)) = (1 : ℂ) • Agen i := by
                dsimp [lcW]
                exact
                  (Finsupp.linearCombination_single (R := ℂ) (v := Agen)
                    (c := (1 : ℂ)) (a := i))
              _ = Agen i := by simp
  have hA_symm_on_v :
      ∀ i j : Fin (n + 1),
        inner (𝕜 := ℂ) (A (v i)) (v j) = inner (𝕜 := ℂ) (v i) (A (v j)) := by
    intro i j
    simpa [hA_apply] using hsymm i j
  have hA_isSymm : A.IsSymmetric := by
    intro x y
    have hx : x ∈ Submodule.span ℂ (Set.range v) := by
      simp [hv_span]
    have hy' : y ∈ Submodule.span ℂ (Set.range v) := by
      simp [hv_span]
    refine Submodule.span_induction₂ (R := ℂ) (s := Set.range v) (t := Set.range v)
      (p := fun x y _ _ =>
        inner (𝕜 := ℂ) (A x) y = inner (𝕜 := ℂ) x (A y))
      (mem_mem := ?_) (zero_left := ?_) (zero_right := ?_) (add_left := ?_) (add_right := ?_)
      (smul_left := ?_) (smul_right := ?_) hx hy'
    · intro x y hx hy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      simpa using hA_symm_on_v i j
    · intro y _; simp
    · intro x _; simp
    · intro x y z _ _ _ hx hy
      simp [map_add, inner_add_left, hx, hy]
    · intro x y z _ _ _ hx hy
      simp [map_add, inner_add_right, hx, hy]
    · intro r x y _ _ hx
      simp [map_smul, inner_smul_left, hx]
    · intro r x y _ _ hx
      simp [map_smul, inner_smul_right, hx]
  have hA_sa : IsSelfAdjoint A :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint (A := A)).1 hA_isSymm
  refine ⟨H, instH, instI, instFD, v, φ, A, hv, rfl, hA_sa, ?_, ?_, ?_⟩
  · intro i hi
    have : Agen i = (1 / (y i : ℂ)) • (v i - φ) := by
      simp [Agen, hi]
    simp [hA_apply, this]
  · intro i hi
    rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
    have hyi0 : (y i : ℂ) ≠ 0 := by
      exact_mod_cast (hyne0 i hi)
    calc
      v i - (y i : ℂ) • A (v i)
          = v i - (y i : ℂ) • ((1 / (y i : ℂ)) • (v i - φ)) := by
              simp [hA_apply, Agen, hi]
      _ = v i - ((y i : ℂ) * (1 / (y i : ℂ))) • (v i - φ) := by
            simp [smul_smul]
      _ = v i - (1 : ℂ) • (v i - φ) := by
            simp [div_eq_mul_inv, hyi0]
      _ = v i - (v i - φ) := by simp
      _ = φ := by
            simp [sub_eq_add_neg, add_comm]
  · intro i hi
    rcases hy with ⟨hy0, hyinj, hyIoo, hyne0⟩
    have hyi0 : y i ≠ 0 := hyne0 i hi
    have hyi0C : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi0
    have h_inner : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) 0 : ℂ) := by
      simpa [φ, hy0] using hv i 0
    have h_kernel : loewnerKernel f (y i) 0 = (f (y i) - f 0) / (y i) := by
      simpa using (loewnerKernel_zero_right (f := f) (x := y i) hyi0)
    have h_inner' : inner (𝕜 := ℂ) (v i) φ = ((f (y i) - f 0) / (y i) : ℂ) := by
      simpa [h_kernel] using h_inner
    have h_mul :
        (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ = (f (y i) : ℂ) - (f 0 : ℂ) := by
      have :
          (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ = ((f (y i) - f 0 : ℝ) : ℂ) := by
        simp [h_inner', div_eq_mul_inv, hyi0C, mul_comm]
      simpa [sub_eq_add_neg] using this
    calc
      (f (y i) : ℂ) = (f 0 : ℂ) + ((f (y i) : ℂ) - (f 0 : ℂ)) := by
        symm
        have :
            (f 0 : ℂ) + ((f (y i) : ℂ) - (f 0 : ℂ)) =
              (f 0 : ℂ) + (f (y i) : ℂ) - (f 0 : ℂ) := by
          simp [sub_eq_add_neg, add_assoc]
        simp [this]
      _ = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ := by
        simp [h_mul]

end Construction

end

end Quantum.TraceInequality.Loewner
