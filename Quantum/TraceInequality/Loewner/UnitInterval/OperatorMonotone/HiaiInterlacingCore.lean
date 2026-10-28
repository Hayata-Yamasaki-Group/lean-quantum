import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.ScalarConsequences
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 3 Hiai four-point interlacing squeeze

This file contains the Hiai four-point rank-one interlacing comparison, the
resulting scalar slope-core inequalities, and the cross-secant squeeze supplied
by full two-by-two CFC order comparison.
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

/-! ### Four-point interlacing weights and matrices -/

/--
First Hiai interlacing weight for four points `a < c < b < d`.

If `A = diag(a,b)` and `B = A + u u⋆` is chosen so that the eigenvalues of
`B` are `c,d`, then this is `‖u 0‖²`.
-/
def hiaiInterlacingWeight0 (a c b d : ℝ) : ℝ :=
  (d - a) * (c - a) / (b - a)

/--
Second Hiai interlacing weight for four points `a < c < b < d`.

If `A = diag(a,b)` and `B = A + u u⋆` is chosen so that the eigenvalues of
`B` are `c,d`, then this is `‖u 1‖²`.
-/
def hiaiInterlacingWeight1 (a c b d : ℝ) : ℝ :=
  (d - b) * (b - c) / (b - a)

/-- The Hiai interlacing weights are positive for `a < c < b < d`. -/
lemma hiaiInterlacingWeights_pos
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 < hiaiInterlacingWeight0 a c b d ∧
      0 < hiaiInterlacingWeight1 a c b d := by
  have hab : a < b := lt_trans hac hcb
  have had : a < d := lt_trans hab hbd
  constructor
  · exact div_pos (mul_pos (sub_pos.mpr had) (sub_pos.mpr hac))
      (sub_pos.mpr hab)
  · exact div_pos (mul_pos (sub_pos.mpr hbd) (sub_pos.mpr hcb))
      (sub_pos.mpr hab)

/--
Trace identity for the Hiai four-point rank-one interlacing comparison.

It records that `diag(a,b) + u u⋆` with the two named squared weights has trace
`c + d`.
-/
lemma hiaiInterlacingWeights_trace
    {a c b d : ℝ} (hab : a ≠ b) :
    a + b + hiaiInterlacingWeight0 a c b d +
        hiaiInterlacingWeight1 a c b d =
      c + d := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold hiaiInterlacingWeight0 hiaiInterlacingWeight1
  field_simp [hba, hab']
  ring_nf

/--
Determinant identity for the Hiai four-point rank-one interlacing comparison.

It records that the same rank-one perturbation has determinant `c * d`, hence
characteristic roots `c,d` once the off-diagonal product is chosen from these
squared weights.
-/
lemma hiaiInterlacingWeights_det
    {a c b d : ℝ} (hab : a ≠ b) :
    a * b + b * hiaiInterlacingWeight0 a c b d +
        a * hiaiInterlacingWeight1 a c b d =
      c * d := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  unfold hiaiInterlacingWeight0 hiaiInterlacingWeight1
  field_simp [hba, hab']
  ring_nf

/-- The two diagonal nodes used in the Hiai four-point interlacing comparison. -/
def hiaiInterlacingNodes (a b : ℝ) : Fin 2 → ℝ :=
  twoPointNodes a b

/--
The rank-one perturbation vector whose squared moduli are the two Hiai
interlacing weights.
-/
def hiaiInterlacingVector (a c b d : ℝ) : Fin 2 → ℂ :=
  fun i =>
    if i = 0 then
      (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ)
    else
      (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ)

/-- The plain matrix form of the Hiai four-point rank-one comparison. -/
def hiaiInterlacingMatrix (a c b d : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalPerturbation (hiaiInterlacingNodes a b)
    (hiaiInterlacingVector a c b d) 1

/-- The diagonal base matrix in the Hiai four-point comparison. -/
def hiaiInterlacingBase (a b : ℝ) :
    CStarMatrix (Fin 2) (Fin 2) ℂ :=
  cStarDiagonalMatrix (hiaiInterlacingNodes a b)

/--
The Hiai four-point comparison matrix `diag(a,b) + u u⋆`, where the vector
`u` is chosen from the interlacing weights attached to `a < c < b < d`.
-/
def hiaiInterlacingCStarMatrix (a c b d : ℝ) :
    CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix (hiaiInterlacingMatrix a c b d)

/-- The Hiai interlacing matrix lies above its diagonal base point. -/
lemma hiaiInterlacingBase_le_matrix (a c b d : ℝ) :
    hiaiInterlacingBase a b ≤
      hiaiInterlacingCStarMatrix a c b d := by
  simpa [hiaiInterlacingBase, hiaiInterlacingCStarMatrix] using
    (cStarDiagonalMatrix_le_perturbation_of_nonneg
      (hiaiInterlacingNodes a b)
      (hiaiInterlacingVector a c b d)
      (by norm_num : (0 : ℝ) ≤ 1))

/-- The Hiai interlacing vector has the first named squared norm. -/
lemma hiaiInterlacingVector_normSq_zero
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiInterlacingVector a c b d 0 *
        star (hiaiInterlacingVector a c b d 0) =
      (hiaiInterlacingWeight0 a c b d : ℂ) := by
  have hpos := (hiaiInterlacingWeights_pos hac hcb hbd).1
  have hnonneg : 0 ≤ hiaiInterlacingWeight0 a c b d := le_of_lt hpos
  have hreal :
      Real.sqrt (hiaiInterlacingWeight0 a c b d) *
          Real.sqrt (hiaiInterlacingWeight0 a c b d) =
        hiaiInterlacingWeight0 a c b d := by
    simpa [sq] using Real.sq_sqrt hnonneg
  change (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
      star (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) =
    (hiaiInterlacingWeight0 a c b d : ℂ)
  rw [show star (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) =
      (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) by simp]
  exact_mod_cast hreal

/-- The Hiai interlacing vector has the second named squared norm. -/
lemma hiaiInterlacingVector_normSq_one
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiInterlacingVector a c b d 1 *
        star (hiaiInterlacingVector a c b d 1) =
      (hiaiInterlacingWeight1 a c b d : ℂ) := by
  have hpos := (hiaiInterlacingWeights_pos hac hcb hbd).2
  have hnonneg : 0 ≤ hiaiInterlacingWeight1 a c b d := le_of_lt hpos
  have hreal :
      Real.sqrt (hiaiInterlacingWeight1 a c b d) *
          Real.sqrt (hiaiInterlacingWeight1 a c b d) =
        hiaiInterlacingWeight1 a c b d := by
    simpa [sq] using Real.sq_sqrt hnonneg
  change (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
      star (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) =
    (hiaiInterlacingWeight1 a c b d : ℂ)
  rw [show star (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) =
      (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) by simp]
  exact_mod_cast hreal

/-! ### Characteristic roots and spectral containment -/

/--
The Hiai interlacing matrix has characteristic roots `c,d`.  This is the
spectral algebra step behind the four-point CFC comparison.
-/
lemma hiaiInterlacingMatrix_charpoly_eval
    {a c b d t : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (hiaiInterlacingMatrix a c b d).charpoly.eval (t : ℂ) =
      ((t - c) * (t - d) : ℝ) := by
  have hab_lt : a < b := lt_trans hac hcb
  have hab : a ≠ b := ne_of_lt hab_lt
  have htr := hiaiInterlacingWeights_trace (a := a) (c := c) (b := b) (d := d) hab
  have hdet := hiaiInterlacingWeights_det (a := a) (c := c) (b := b) (d := d) hab
  have hpos0 := (hiaiInterlacingWeights_pos hac hcb hbd).1
  have hpos1 := (hiaiInterlacingWeights_pos hac hcb hbd).2
  have hnonneg0 : 0 ≤ hiaiInterlacingWeight0 a c b d := le_of_lt hpos0
  have hnonneg1 : 0 ≤ hiaiInterlacingWeight1 a c b d := le_of_lt hpos1
  have hmul0 :
      (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
          (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) =
        (hiaiInterlacingWeight0 a c b d : ℂ) := by
    have hreal :
        Real.sqrt (hiaiInterlacingWeight0 a c b d) *
            Real.sqrt (hiaiInterlacingWeight0 a c b d) =
          hiaiInterlacingWeight0 a c b d := by
      simpa [sq] using Real.sq_sqrt hnonneg0
    exact_mod_cast hreal
  have hmul1 :
      (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
          (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) =
        (hiaiInterlacingWeight1 a c b d : ℂ) := by
    have hreal :
        Real.sqrt (hiaiInterlacingWeight1 a c b d) *
            Real.sqrt (hiaiInterlacingWeight1 a c b d) =
          hiaiInterlacingWeight1 a c b d := by
      simpa [sq] using Real.sq_sqrt hnonneg1
    exact_mod_cast hreal
  have hcross :
      (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
          (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
          ((Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
            (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ)) =
        (hiaiInterlacingWeight0 a c b d : ℂ) *
          (hiaiInterlacingWeight1 a c b d : ℂ) := by
    calc
      (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
          (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
          ((Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
            (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ))
          =
            ((Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
              (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ)) *
            ((Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ) *
              (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ)) := by
        ring
      _ = (hiaiInterlacingWeight0 a c b d : ℂ) *
          (hiaiInterlacingWeight1 a c b d : ℂ) := by
        rw [hmul0, hmul1]
  have htrC :
      ((a + b + hiaiInterlacingWeight0 a c b d +
          hiaiInterlacingWeight1 a c b d : ℝ) : ℂ) =
        ((c + d : ℝ) : ℂ) := by
    exact_mod_cast htr
  have hdetC :
      ((a * b + b * hiaiInterlacingWeight0 a c b d +
          a * hiaiInterlacingWeight1 a c b d : ℝ) : ℂ) =
        ((c * d : ℝ) : ℂ) := by
    exact_mod_cast hdet
  have hdetC' :
      ((a * b + a * hiaiInterlacingWeight1 a c b d +
          b * hiaiInterlacingWeight0 a c b d : ℝ) : ℂ) =
        ((c * d : ℝ) : ℂ) := by
    have hreorder :
        a * b + a * hiaiInterlacingWeight1 a c b d +
            b * hiaiInterlacingWeight0 a c b d =
          a * b + b * hiaiInterlacingWeight0 a c b d +
            a * hiaiInterlacingWeight1 a c b d := by
      ring
    rw [hreorder]
    exact hdetC
  have htrace :
      (((1 : ℝ) • Matrix.vecMulVec (hiaiInterlacingVector a c b d)
          (star (hiaiInterlacingVector a c b d))).trace) =
        (hiaiInterlacingWeight0 a c b d : ℂ) +
          (hiaiInterlacingWeight1 a c b d : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      hiaiInterlacingVector, Fin.isValue, Pi.star_apply, RCLike.star_def, ite_mul,
      smul_ite, Complex.real_smul, Complex.ofReal_one, one_mul, Fin.sum_univ_two, ↓reduceIte,
      Complex.conj_ofReal, one_ne_zero]
    rw [hmul0, hmul1]
  rw [Matrix.charpoly_fin_two]
  simp only [hiaiInterlacingMatrix, diagonalPerturbation,
    diagonalMatrix, hiaiInterlacingNodes, twoPointNodes, Fin.isValue,
    rankOnePerturbation, Matrix.trace_add, Matrix.trace_diagonal, Fin.sum_univ_two,
    ↓reduceIte, one_ne_zero, map_add, Matrix.det_fin_two, Matrix.add_apply,
    Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.vecMulVec_apply,
    hiaiInterlacingVector, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
    Complex.real_smul, Complex.ofReal_one, one_mul, ne_eq, zero_ne_one, not_false_eq_true,
    Matrix.diagonal_apply_ne, zero_add, map_sub, map_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C, Complex.ofReal_mul, Complex.ofReal_sub]
  rw [htrace, hcross, hmul0, hmul1]
  ring_nf
  calc
    -(↑t * ↑a) - ↑t * ↑b +
              (-(↑t * ↑(hiaiInterlacingWeight0 a c b d)) -
                ↑t * ↑(hiaiInterlacingWeight1 a c b d)) +
            ↑t ^ 2 +
          ↑a * ↑b +
        ↑a * ↑(hiaiInterlacingWeight1 a c b d) +
      ↑b * ↑(hiaiInterlacingWeight0 a c b d)
        =
          (t : ℂ) ^ 2 -
            ((a + b + hiaiInterlacingWeight0 a c b d +
              hiaiInterlacingWeight1 a c b d : ℝ) : ℂ) * (t : ℂ) +
            ((a * b + a * hiaiInterlacingWeight1 a c b d +
              b * hiaiInterlacingWeight0 a c b d : ℝ) : ℂ) := by
        norm_num
        ring_nf
    _ =
          (t : ℂ) ^ 2 - ((c + d : ℝ) : ℂ) * (t : ℂ) +
            ((c * d : ℝ) : ℂ) := by rw [htrC, hdetC']
    _ = -(↑t * ↑c) - ↑t * ↑d + ↑t ^ 2 + ↑c * ↑d := by
      norm_num
      ring_nf

/-- The real spectrum of the Hiai interlacing matrix is contained in `{c,d}`. -/
lemma hiaiInterlacingMatrix_spectrum_subset
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    spectrum ℝ (hiaiInterlacingMatrix a c b d) ⊆
      ({c, d} : Set ℝ) := by
  intro t ht
  have htC : (t : ℂ) ∈ spectrum ℂ (hiaiInterlacingMatrix a c b d) := by
    simpa [Set.mem_preimage] using
      (show t ∈ (algebraMap ℝ ℂ) ⁻¹'
          spectrum ℂ (hiaiInterlacingMatrix a c b d) by
        rwa [spectrum.preimage_algebraMap ℂ])
  have hroot :
      Polynomial.IsRoot
        (hiaiInterlacingMatrix a c b d).charpoly (t : ℂ) :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp htC
  have hpolyC : (((t - c) * (t - d) : ℝ) : ℂ) = 0 := by
    simpa [Polynomial.IsRoot.def,
      hiaiInterlacingMatrix_charpoly_eval
        (a := a) (c := c) (b := b) (d := d) (t := t) hac hcb hbd] using hroot
  have hpolyR : (t - c) * (t - d) = 0 :=
    Complex.ofReal_injective hpolyC
  rcases mul_eq_zero.mp hpolyR with hc0 | hd0
  · left
    exact sub_eq_zero.mp hc0
  · right
    exact sub_eq_zero.mp hd0

/-- CStarMatrix-copy version of the Hiai interlacing spectrum containment. -/
lemma hiaiInterlacingCStarMatrix_spectrum_subset
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    spectrum ℝ (hiaiInterlacingCStarMatrix a c b d) ⊆
      ({c, d} : Set ℝ) := by
  simpa [hiaiInterlacingCStarMatrix] using
    hiaiInterlacingMatrix_spectrum_subset
      (a := a) (c := c) (b := b) (d := d) hac hcb hbd

/-- The real quasispectrum of the Hiai interlacing matrix is finite. -/
lemma hiaiInterlacingCStarMatrix_quasispectrum_finite
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (quasispectrum ℝ (hiaiInterlacingCStarMatrix a c b d)).Finite := by
  have hfinite : ({0, c, d} : Set ℝ).Finite := by simp
  refine hfinite.subset ?_
  intro t ht
  have htq : t = 0 ∨ t ∈ spectrum ℝ (hiaiInterlacingCStarMatrix a c b d) :=
    (mem_quasispectrum_iff
      (a := hiaiInterlacingCStarMatrix a c b d) (x := t)).mp ht
  rcases htq with rfl | hs
  · left
    rfl
  · right
    exact hiaiInterlacingCStarMatrix_spectrum_subset
      (a := a) (c := c) (b := b) (d := d) hac hcb hbd hs

/-- The Hiai interlacing matrix lies in the normalized CFC interval domain. -/
lemma hiaiInterlacingCStarMatrix_mem_domain
    {a c b d : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiInterlacingCStarMatrix a c b d ∈
      cStarFiniteMatrixDomain 2 := by
  refine ⟨?_, ?_⟩
  · simpa [hiaiInterlacingCStarMatrix,
      hiaiInterlacingMatrix] using
      (cStarDiagonalPerturbation_isSelfAdjoint
        (hiaiInterlacingNodes a b)
        (hiaiInterlacingVector a c b d) 1)
  · intro t ht
    have htq : t = 0 ∨
        t ∈ spectrum ℝ (hiaiInterlacingCStarMatrix a c b d) :=
      (mem_quasispectrum_iff
        (a := hiaiInterlacingCStarMatrix a c b d) (x := t)).mp ht
    rcases htq with hzero | hs
    · have ht0 : t = 0 := by simpa using hzero
      simp [ht0]
    · have htcd :=
        hiaiInterlacingCStarMatrix_spectrum_subset
          (a := a) (c := c) (b := b) (d := d) hac hcb hbd hs
      rcases htcd with rfl | rfl
      · exact hc
      · exact hd

/-! ### Affine spectral model for the interlacing matrix -/

/-- Spectral slope of the affine interpolant on the Hiai four-point branches. -/
def hiaiInterlacingSpectralSlope
    (f : ℝ → ℝ) (_a c _b d : ℝ) : ℝ :=
  (f d - f c) / (d - c)

/--
Spectral intercept for the normalized function `t ↦ f t - f 0` on the Hiai
four-point branches.
-/
def hiaiInterlacingSpectralIntercept
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  f c - f 0 - hiaiInterlacingSpectralSlope f a c b d * c

/-- The affine spectral interpolant for the Hiai four-point comparison. -/
def hiaiInterlacingSpectralAffine
    (f : ℝ → ℝ) (a c b d t : ℝ) : ℝ :=
  hiaiInterlacingSpectralSlope f a c b d * t +
    hiaiInterlacingSpectralIntercept f a c b d

/-- The Hiai affine spectral interpolant matches `f - f 0` at `c`. -/
lemma hiaiInterlacingSpectralAffine_c
    (f : ℝ → ℝ) (a c b d : ℝ) :
    hiaiInterlacingSpectralAffine f a c b d c = f c - f 0 := by
  simp [hiaiInterlacingSpectralAffine,
    hiaiInterlacingSpectralIntercept]

/-- The Hiai affine spectral interpolant matches `f - f 0` at `d`. -/
lemma hiaiInterlacingSpectralAffine_d
    (f : ℝ → ℝ) {a c b d : ℝ} (hbd : b < d) (hcb : c < b) :
    hiaiInterlacingSpectralAffine f a c b d d = f d - f 0 := by
  have hcd : c < d := lt_trans hcb hbd
  have hne : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcd)
  unfold hiaiInterlacingSpectralAffine
    hiaiInterlacingSpectralIntercept
    hiaiInterlacingSpectralSlope
  field_simp [hne]
  ring

/--
On the Hiai interlacing matrix, normalized CFC is equal to unital CFC of the
affine spectral interpolant on the two branches `c,d`.
-/
lemma hiaiInterlacingCStarMatrix_cfcₙ_eq_cfc_spectralAffine
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    cfcₙ (fun t : ℝ => f t - f 0)
        (hiaiInterlacingCStarMatrix a c b d) =
      cfc (hiaiInterlacingSpectralAffine f a c b d)
        (hiaiInterlacingCStarMatrix a c b d) := by
  let M : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    hiaiInterlacingCStarMatrix a c b d
  have hnorm_cont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ M) := by
    simpa [M] using
      (hiaiInterlacingCStarMatrix_quasispectrum_finite
        (a := a) (c := c) (b := b) (d := d) hac hcb hbd).continuousOn
        (fun t : ℝ => f t - f 0)
  have hspectrum :
      spectrum ℝ M ⊆ ({c, d} : Set ℝ) := by
    simpa [M] using
      hiaiInterlacingCStarMatrix_spectrum_subset
        (a := a) (c := c) (b := b) (d := d) hac hcb hbd
  have hcongr :
      cfc (fun t : ℝ => f t - f 0) M =
        cfc (hiaiInterlacingSpectralAffine f a c b d) M := by
    apply cfc_congr
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
    rcases ht' with htc | htd
    · simpa [htc] using
        (hiaiInterlacingSpectralAffine_c f a c b d).symm
    · simpa [htd] using
        (hiaiInterlacingSpectralAffine_d f (a := a) (c := c)
          (b := b) (d := d) hbd hcb).symm
  change cfcₙ (fun t : ℝ => f t - f 0) M =
    cfc (hiaiInterlacingSpectralAffine f a c b d) M
  calc
    cfcₙ (fun t : ℝ => f t - f 0) M =
        cfc (fun t : ℝ => f t - f 0) M := by
      exact cfcₙ_eq_cfc (a := M) (hf := hnorm_cont) (hf0 := by simp)
    _ = cfc (hiaiInterlacingSpectralAffine f a c b d) M := hcongr

/-- Unital CFC of the Hiai affine spectral interpolant is an affine matrix expression. -/
lemma hiaiInterlacingCStarMatrix_cfc_spectralAffine_eq
    (f : ℝ → ℝ) (a c b d : ℝ) :
    cfc (hiaiInterlacingSpectralAffine f a c b d)
        (hiaiInterlacingCStarMatrix a c b d) =
      hiaiInterlacingSpectralSlope f a c b d •
          hiaiInterlacingCStarMatrix a c b d +
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
          (hiaiInterlacingSpectralIntercept f a c b d) := by
  let M : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    hiaiInterlacingCStarMatrix a c b d
  have hsa : IsSelfAdjoint M := by
    simpa [M, hiaiInterlacingCStarMatrix,
      hiaiInterlacingMatrix] using
      (cStarDiagonalPerturbation_isSelfAdjoint
        (hiaiInterlacingNodes a b)
        (hiaiInterlacingVector a c b d) 1)
  change cfc
      (fun t : ℝ =>
        hiaiInterlacingSpectralSlope f a c b d * t +
          hiaiInterlacingSpectralIntercept f a c b d) M =
    hiaiInterlacingSpectralSlope f a c b d • M +
      algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
        (hiaiInterlacingSpectralIntercept f a c b d)
  calc
    cfc
        (fun t : ℝ =>
          hiaiInterlacingSpectralSlope f a c b d * t +
            hiaiInterlacingSpectralIntercept f a c b d) M =
        cfc
          (fun t : ℝ =>
            hiaiInterlacingSpectralIntercept f a c b d +
              hiaiInterlacingSpectralSlope f a c b d * t) M := by
      congr 1
      ext t
      ring
    _ =
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (hiaiInterlacingSpectralIntercept f a c b d) +
          cfc (fun t : ℝ => hiaiInterlacingSpectralSlope f a c b d * t)
            M := by
      exact cfc_const_add
        (hiaiInterlacingSpectralIntercept f a c b d)
        (fun t : ℝ => hiaiInterlacingSpectralSlope f a c b d * t)
        M (ha := hsa)
    _ =
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (hiaiInterlacingSpectralIntercept f a c b d) +
          hiaiInterlacingSpectralSlope f a c b d • M := by
      congr 1
      simpa using
        (cfc_const_mul_id (hiaiInterlacingSpectralSlope f a c b d)
          M (ha := hsa))
    _ =
        hiaiInterlacingSpectralSlope f a c b d • M +
          algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (hiaiInterlacingSpectralIntercept f a c b d) := by
      abel

/-- Entrywise spectral formula for the normalized CFC of the Hiai interlacing matrix. -/
theorem hiaiInterlacingCStarMatrix_cfcₙ_entry_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d)
    (i j : Fin 2) :
    (cfcₙ (fun t : ℝ => f t - f 0)
        (hiaiInterlacingCStarMatrix a c b d)) i j =
      (hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          (hiaiInterlacingCStarMatrix a c b d) i j +
        if i = j then
          (hiaiInterlacingSpectralIntercept f a c b d : ℂ)
        else 0 := by
  have hmatrix :
      cfcₙ (fun t : ℝ => f t - f 0)
          (hiaiInterlacingCStarMatrix a c b d) =
        hiaiInterlacingSpectralSlope f a c b d •
            hiaiInterlacingCStarMatrix a c b d +
          algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (hiaiInterlacingSpectralIntercept f a c b d) := by
    rw [hiaiInterlacingCStarMatrix_cfcₙ_eq_cfc_spectralAffine
        f hac hcb hbd]
    exact hiaiInterlacingCStarMatrix_cfc_spectralAffine_eq f a c b d
  have hentry := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M i j) hmatrix
  simpa [Matrix.algebraMap_matrix_apply] using hentry

/-! ### CFC comparison and positivity consequences -/

/--
The full `2×2` CFC order comparison applies to the Hiai four-point
interlacing matrix.
-/
theorem hiaiInterlacingCFCComparison
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    cfcₙ (fun t : ℝ => f t - f 0) (hiaiInterlacingBase a b) ≤
      cfcₙ (fun t : ℝ => f t - f 0)
        (hiaiInterlacingCStarMatrix a c b d) := by
  have hbase :
      hiaiInterlacingBase a b ∈ cStarFiniteMatrixDomain 2 := by
    simpa [hiaiInterlacingBase, hiaiInterlacingNodes] using
      cStarDiagonalMatrix_mem_domain
        (twoPointNodes a b) (twoPointNodes_mem_Ioo ha hb)
  have hmatrix :
      hiaiInterlacingCStarMatrix a c b d ∈
        cStarFiniteMatrixDomain 2 :=
    hiaiInterlacingCStarMatrix_mem_domain hc hd hac hcb hbd
  exact h2 hbase hmatrix
    (hiaiInterlacingBase_le_matrix a c b d)

/-- CFC difference matrix for the Hiai four-point comparison. -/
def hiaiInterlacingCFCDifference
    (f : ℝ → ℝ) (a c b d : ℝ) :
    CStarMatrix (Fin 2) (Fin 2) ℂ :=
  cfcₙ (fun t : ℝ => f t - f 0)
      (hiaiInterlacingCStarMatrix a c b d) -
    cfcₙ (fun t : ℝ => f t - f 0) (hiaiInterlacingBase a b)

/-- The Hiai four-point CFC difference matrix is positive. -/
theorem hiaiInterlacingCFCDifference_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ hiaiInterlacingCFCDifference f a c b d := by
  rw [hiaiInterlacingCFCDifference, sub_nonneg]
  exact hiaiInterlacingCFCComparison h2 ha hb hc hd hac hcb hbd

/--
Quadratic positivity test extracted from the Hiai four-point CFC comparison.
The Hiai squeeze then evaluates these entries spectrally and turns this matrix
positivity into the scalar determinant/Schur inequality
(`hiaiInterlacingCFCDifference_schur_secantCore_nonneg` below).
-/
theorem hiaiInterlacingCFCDifference_quadratic_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (v : Fin 2 → ℂ) :
    0 ≤ star v ⬝ᵥ
      ((CStarMatrix.ofMatrix.symm
          (hiaiInterlacingCFCDifference f a c b d)) *ᵥ v) :=
  cStarMatrix_quadratic_nonneg_of_nonneg
    (hiaiInterlacingCFCDifference_nonneg
      h2 ha hb hc hd hac hcb hbd) v

/--
Determinant positivity of the Hiai four-point CFC difference matrix.

This is the determinant/Schur positivity part of the Hiai squeeze.  The next
scalar step is to substitute the spectral entry formula into this determinant
inequality.
-/
theorem hiaiInterlacingCFCDifference_det_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)).det := by
  exact (cStarMatrix_posSemidef_of_nonneg
    (hiaiInterlacingCFCDifference_nonneg
      h2 ha hb hc hd hac hcb hbd)).det_nonneg

/--
The same determinant positivity written as the explicit `2×2` Schur
expression.
-/
theorem hiaiInterlacingCFCDifference_schur_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤
      (CStarMatrix.ofMatrix.symm
        (hiaiInterlacingCFCDifference f a c b d)) 0 0 *
        (CStarMatrix.ofMatrix.symm
          (hiaiInterlacingCFCDifference f a c b d)) 1 1 -
      (CStarMatrix.ofMatrix.symm
        (hiaiInterlacingCFCDifference f a c b d)) 0 1 *
        (CStarMatrix.ofMatrix.symm
          (hiaiInterlacingCFCDifference f a c b d)) 1 0 := by
  simpa [Matrix.det_fin_two] using
    hiaiInterlacingCFCDifference_det_nonneg
      h2 ha hb hc hd hac hcb hbd

/-! ### Entry formulas for the Hiai difference -/

/-- Entry formula for the diagonal base CFC in the Hiai four-point comparison. -/
lemma hiaiInterlacingBase_cfcₙ_entry_formula
    (f : ℝ → ℝ) {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (i j : Fin 2) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (hiaiInterlacingBase a b)) i j =
        if i = j then
          ((f (hiaiInterlacingNodes a b i) - f 0 : ℝ) : ℂ)
        else 0 := by
  have hab : a ≠ b := ne_of_lt (lt_trans hac hcb)
  simpa [hiaiInterlacingBase, hiaiInterlacingNodes] using
    twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) (x := a) (y := b) hab i j

/-- Off-diagonal coefficient of the Hiai interlacing matrix. -/
def hiaiInterlacingOffdiagCoeff (a c b d : ℝ) : ℂ :=
  (Real.sqrt (hiaiInterlacingWeight0 a c b d) : ℂ) *
    (Real.sqrt (hiaiInterlacingWeight1 a c b d) : ℂ)

/-- Real copy of the Hiai off-diagonal coefficient. -/
def hiaiInterlacingOffdiagCoeffReal (a c b d : ℝ) : ℝ :=
  Real.sqrt (hiaiInterlacingWeight0 a c b d) *
    Real.sqrt (hiaiInterlacingWeight1 a c b d)

/-- The complex off-diagonal coefficient is the real coefficient embedded in `ℂ`. -/
lemma hiaiInterlacingOffdiagCoeff_eq_ofReal
    (a c b d : ℝ) :
    hiaiInterlacingOffdiagCoeff a c b d =
      (hiaiInterlacingOffdiagCoeffReal a c b d : ℂ) := by
  simp [hiaiInterlacingOffdiagCoeff,
    hiaiInterlacingOffdiagCoeffReal]

/-- Entry formula for the Hiai interlacing CStarMatrix. -/
lemma hiaiInterlacingMatrix_entry_formula
    (a c b d : ℝ) (i j : Fin 2) :
    (hiaiInterlacingCStarMatrix a c b d) i j =
      (if i = j then
          (hiaiInterlacingNodes a b i : ℂ)
        else 0) +
        hiaiInterlacingVector a c b d i *
          star (hiaiInterlacingVector a c b d j) := by
  by_cases hij : i = j
  · subst j
    simp [hiaiInterlacingCStarMatrix, hiaiInterlacingMatrix,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, Matrix.vecMulVec_apply]
  · simp [hiaiInterlacingCStarMatrix, hiaiInterlacingMatrix,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, Matrix.vecMulVec_apply, hij]

/-- The first diagonal entry of the Hiai interlacing matrix. -/
lemma hiaiInterlacingMatrix_entry_zero_zero
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (hiaiInterlacingCStarMatrix a c b d) 0 0 =
      (a : ℂ) + (hiaiInterlacingWeight0 a c b d : ℂ) := by
  rw [hiaiInterlacingMatrix_entry_formula]
  rw [hiaiInterlacingVector_normSq_zero hac hcb hbd]
  simp [hiaiInterlacingNodes, twoPointNodes]

/-- The second diagonal entry of the Hiai interlacing matrix. -/
lemma hiaiInterlacingMatrix_entry_one_one
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (hiaiInterlacingCStarMatrix a c b d) 1 1 =
      (b : ℂ) + (hiaiInterlacingWeight1 a c b d : ℂ) := by
  rw [hiaiInterlacingMatrix_entry_formula]
  rw [hiaiInterlacingVector_normSq_one hac hcb hbd]
  simp [hiaiInterlacingNodes, twoPointNodes]

/-- The upper off-diagonal entry of the Hiai interlacing matrix. -/
lemma hiaiInterlacingMatrix_entry_zero_one
    (a c b d : ℝ) :
    (hiaiInterlacingCStarMatrix a c b d) 0 1 =
      hiaiInterlacingOffdiagCoeff a c b d := by
  rw [hiaiInterlacingMatrix_entry_formula]
  simp [hiaiInterlacingOffdiagCoeff,
    hiaiInterlacingVector]

/-- The lower off-diagonal entry of the Hiai interlacing matrix. -/
lemma hiaiInterlacingMatrix_entry_one_zero
    (a c b d : ℝ) :
    (hiaiInterlacingCStarMatrix a c b d) 1 0 =
      hiaiInterlacingOffdiagCoeff a c b d := by
  rw [hiaiInterlacingMatrix_entry_formula]
  simp [hiaiInterlacingOffdiagCoeff,
    hiaiInterlacingVector, mul_comm]

/-- Exact spectral formula for entries of the Hiai CFC difference matrix. -/
theorem hiaiInterlacingCFCDifference_entry_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d)
    (i j : Fin 2) :
    (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)) i j =
      ((hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          (hiaiInterlacingCStarMatrix a c b d) i j +
        if i = j then
          (hiaiInterlacingSpectralIntercept f a c b d : ℂ)
        else 0) -
        (if i = j then
          ((f (hiaiInterlacingNodes a b i) - f 0 : ℝ) : ℂ)
        else 0) := by
  change (hiaiInterlacingCFCDifference f a c b d) i j = _
  rw [hiaiInterlacingCFCDifference]
  rw [show
      (cfcₙ (fun t : ℝ => f t - f 0)
          (hiaiInterlacingCStarMatrix a c b d) -
        cfcₙ (fun t : ℝ => f t - f 0)
          (hiaiInterlacingBase a b)) i j =
        (cfcₙ (fun t : ℝ => f t - f 0)
          (hiaiInterlacingCStarMatrix a c b d)) i j -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (hiaiInterlacingBase a b)) i j by rfl]
  rw [hiaiInterlacingCStarMatrix_cfcₙ_entry_spectralFormula
      f hac hcb hbd i j,
    hiaiInterlacingBase_cfcₙ_entry_formula
      f hac hcb i j]

/-- First diagonal specialization of the Hiai CFC difference entry formula. -/
theorem hiaiInterlacingCFCDifference_diag00_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)) 0 0 =
      (hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          ((a : ℂ) + (hiaiInterlacingWeight0 a c b d : ℂ)) +
        (hiaiInterlacingSpectralIntercept f a c b d : ℂ) -
        ((f a - f 0 : ℝ) : ℂ) := by
  rw [hiaiInterlacingCFCDifference_entry_spectralFormula
    f hac hcb hbd 0 0]
  rw [hiaiInterlacingMatrix_entry_zero_zero hac hcb hbd]
  simp [hiaiInterlacingNodes, twoPointNodes]

/-- Second diagonal specialization of the Hiai CFC difference entry formula. -/
theorem hiaiInterlacingCFCDifference_diag11_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)) 1 1 =
      (hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          ((b : ℂ) + (hiaiInterlacingWeight1 a c b d : ℂ)) +
        (hiaiInterlacingSpectralIntercept f a c b d : ℂ) -
        ((f b - f 0 : ℝ) : ℂ) := by
  rw [hiaiInterlacingCFCDifference_entry_spectralFormula
    f hac hcb hbd 1 1]
  rw [hiaiInterlacingMatrix_entry_one_one hac hcb hbd]
  simp [hiaiInterlacingNodes, twoPointNodes]

/-- Off-diagonal specialization of the Hiai CFC difference entry formula. -/
theorem hiaiInterlacingCFCDifference_offdiag_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)) 0 1 =
      (hiaiInterlacingSpectralSlope f a c b d : ℂ) *
        hiaiInterlacingOffdiagCoeff a c b d := by
  rw [hiaiInterlacingCFCDifference_entry_spectralFormula
    f hac hcb hbd 0 1]
  rw [hiaiInterlacingMatrix_entry_zero_one]
  simp

/-- Lower off-diagonal specialization of the Hiai CFC difference entry formula. -/
theorem hiaiInterlacingCFCDifference_offdiag10_spectralFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    (CStarMatrix.ofMatrix.symm
      (hiaiInterlacingCFCDifference f a c b d)) 1 0 =
      (hiaiInterlacingSpectralSlope f a c b d : ℂ) *
        hiaiInterlacingOffdiagCoeff a c b d := by
  rw [hiaiInterlacingCFCDifference_entry_spectralFormula
    f hac hcb hbd 1 0]
  rw [hiaiInterlacingMatrix_entry_one_zero]
  simp

/-! ### Schur scalar reduction -/

/--
Schur positivity after substituting the Hiai spectral entry formulas.

This is the scalar inequality handed to the final Hiai secant squeeze.
-/
theorem hiaiInterlacingCFCDifference_schur_scalarFormula
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤
      (((hiaiInterlacingSpectralSlope f a c b d : ℂ) *
            ((a : ℂ) + (hiaiInterlacingWeight0 a c b d : ℂ)) +
          (hiaiInterlacingSpectralIntercept f a c b d : ℂ) -
          ((f a - f 0 : ℝ) : ℂ)) *
        ((hiaiInterlacingSpectralSlope f a c b d : ℂ) *
            ((b : ℂ) + (hiaiInterlacingWeight1 a c b d : ℂ)) +
          (hiaiInterlacingSpectralIntercept f a c b d : ℂ) -
          ((f b - f 0 : ℝ) : ℂ)) -
        ((hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          hiaiInterlacingOffdiagCoeff a c b d) *
        ((hiaiInterlacingSpectralSlope f a c b d : ℂ) *
          hiaiInterlacingOffdiagCoeff a c b d)) := by
  have hschur :=
    hiaiInterlacingCFCDifference_schur_nonneg
      h2 ha hb hc hd hac hcb hbd
  rw [hiaiInterlacingCFCDifference_diag00_spectralFormula
      f hac hcb hbd,
    hiaiInterlacingCFCDifference_diag11_spectralFormula
      f hac hcb hbd,
    hiaiInterlacingCFCDifference_offdiag_spectralFormula
      f hac hcb hbd,
    hiaiInterlacingCFCDifference_offdiag10_spectralFormula
      f hac hcb hbd] at hschur
  simpa using hschur

/--
Real scalar expression obtained by substituting the Hiai entry formulas into
Schur positivity.
-/
def hiaiInterlacingSchurScalarExpression
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  (hiaiInterlacingSpectralSlope f a c b d *
      (a + hiaiInterlacingWeight0 a c b d) +
    hiaiInterlacingSpectralIntercept f a c b d -
    (f a - f 0)) *
    (hiaiInterlacingSpectralSlope f a c b d *
        (b + hiaiInterlacingWeight1 a c b d) +
      hiaiInterlacingSpectralIntercept f a c b d -
      (f b - f 0)) -
    (hiaiInterlacingSpectralSlope f a c b d *
      hiaiInterlacingOffdiagCoeffReal a c b d) *
    (hiaiInterlacingSpectralSlope f a c b d *
      hiaiInterlacingOffdiagCoeffReal a c b d)

/-- Real-valued Schur inequality for the Hiai interlacing comparison. -/
theorem hiaiInterlacingCFCDifference_schur_realScalarFormula
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ hiaiInterlacingSchurScalarExpression f a c b d := by
  have hC :=
    hiaiInterlacingCFCDifference_schur_scalarFormula
      h2 ha hb hc hd hac hcb hbd
  have hC' :
      0 ≤
        (hiaiInterlacingSchurScalarExpression f a c b d : ℂ) := by
    simpa [hiaiInterlacingSchurScalarExpression,
      hiaiInterlacingOffdiagCoeff_eq_ofReal] using hC
  exact_mod_cast hC'

/-! ### Secant quotient normal forms -/

/-- First diagonal Hiai weight shifted from the interpolation point `c`. -/
lemma hiaiInterlacingWeight0_shift_formula
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) :
    a + hiaiInterlacingWeight0 a c b d - c =
      (c - a) * (d - b) / (b - a) := by
  have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
  unfold hiaiInterlacingWeight0
  field_simp [hab]
  ring

/-- Second diagonal Hiai weight shifted from the interpolation point `c`. -/
lemma hiaiInterlacingWeight1_shift_formula
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) :
    b + hiaiInterlacingWeight1 a c b d - c =
      (b - c) * (d - a) / (b - a) := by
  have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
  unfold hiaiInterlacingWeight1
  field_simp [hab]
  ring

/-- The square of the real Hiai off-diagonal coefficient is the product of weights. -/
lemma hiaiInterlacingOffdiagCoeffReal_sq
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiInterlacingOffdiagCoeffReal a c b d *
        hiaiInterlacingOffdiagCoeffReal a c b d =
      hiaiInterlacingWeight0 a c b d *
        hiaiInterlacingWeight1 a c b d := by
  have h0 : 0 ≤ hiaiInterlacingWeight0 a c b d :=
    le_of_lt (hiaiInterlacingWeights_pos hac hcb hbd).1
  have h1 : 0 ≤ hiaiInterlacingWeight1 a c b d :=
    le_of_lt (hiaiInterlacingWeights_pos hac hcb hbd).2
  unfold hiaiInterlacingOffdiagCoeffReal
  calc
    Real.sqrt (hiaiInterlacingWeight0 a c b d) *
          Real.sqrt (hiaiInterlacingWeight1 a c b d) *
        (Real.sqrt (hiaiInterlacingWeight0 a c b d) *
          Real.sqrt (hiaiInterlacingWeight1 a c b d))
        =
          (Real.sqrt (hiaiInterlacingWeight0 a c b d) *
            Real.sqrt (hiaiInterlacingWeight0 a c b d)) *
          (Real.sqrt (hiaiInterlacingWeight1 a c b d) *
            Real.sqrt (hiaiInterlacingWeight1 a c b d)) := by
        ring
    _ =
        hiaiInterlacingWeight0 a c b d *
          hiaiInterlacingWeight1 a c b d := by
        have hsq0 :
            Real.sqrt (hiaiInterlacingWeight0 a c b d) *
                Real.sqrt (hiaiInterlacingWeight0 a c b d) =
              hiaiInterlacingWeight0 a c b d := by
          simpa [sq] using Real.sq_sqrt h0
        have hsq1 :
            Real.sqrt (hiaiInterlacingWeight1 a c b d) *
                Real.sqrt (hiaiInterlacingWeight1 a c b d) =
              hiaiInterlacingWeight1 a c b d := by
          simpa [sq] using Real.sq_sqrt h1
        rw [hsq0, hsq1]

/-- The Hiai affine spectral slope is the ordinary secant slope from `c` to `d`. -/
lemma hiaiInterlacingSpectralSlope_eq_slope
    (f : ℝ → ℝ) (a b : ℝ) (c d : ℝ) :
    hiaiInterlacingSpectralSlope f a c b d = slope f c d := by
  simp [hiaiInterlacingSpectralSlope, slope]
  ring

/-- First diagonal Schur factor written in secant quotient form. -/
lemma hiaiInterlacingSchur_diag00_secantFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) :
    hiaiInterlacingSpectralSlope f a c b d *
        (a + hiaiInterlacingWeight0 a c b d) +
      hiaiInterlacingSpectralIntercept f a c b d - (f a - f 0) =
        (c - a) *
          (slope f c a + (d - b) / (b - a) * slope f c d) := by
  have hfa : f c - f a = (c - a) * slope f c a := by
    have hne : a - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt hac)
    simp [slope]
    field_simp [hne]
    ring
  have hshift :=
    hiaiInterlacingWeight0_shift_formula
      (a := a) (c := c) (b := b) (d := d) hac hcb
  rw [hiaiInterlacingSpectralSlope_eq_slope]
  unfold hiaiInterlacingSpectralIntercept
  rw [hiaiInterlacingSpectralSlope_eq_slope]
  calc
    slope f c d * (a + hiaiInterlacingWeight0 a c b d) +
        (f c - f 0 - slope f c d * c) - (f a - f 0)
        =
          slope f c d *
              (a + hiaiInterlacingWeight0 a c b d - c) +
            (f c - f a) := by
          ring
    _ =
          slope f c d * ((c - a) * (d - b) / (b - a)) +
            (c - a) * slope f c a := by
          rw [hshift, hfa]
    _ =
          (c - a) *
            (slope f c a + (d - b) / (b - a) * slope f c d) := by
          ring

/-- Second diagonal Schur factor written in secant quotient form. -/
lemma hiaiInterlacingSchur_diag11_secantFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) :
    hiaiInterlacingSpectralSlope f a c b d *
        (b + hiaiInterlacingWeight1 a c b d) +
      hiaiInterlacingSpectralIntercept f a c b d - (f b - f 0) =
        (b - c) *
          ((d - a) / (b - a) * slope f c d - slope f c b) := by
  have hfb : f c - f b = - (b - c) * slope f c b := by
    have hne : b - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcb)
    simp [slope]
    field_simp [hne]
    ring
  have hshift :=
    hiaiInterlacingWeight1_shift_formula
      (a := a) (c := c) (b := b) (d := d) hac hcb
  rw [hiaiInterlacingSpectralSlope_eq_slope]
  unfold hiaiInterlacingSpectralIntercept
  rw [hiaiInterlacingSpectralSlope_eq_slope]
  calc
    slope f c d * (b + hiaiInterlacingWeight1 a c b d) +
        (f c - f 0 - slope f c d * c) - (f b - f 0)
        =
          slope f c d *
              (b + hiaiInterlacingWeight1 a c b d - c) +
            (f c - f b) := by
          ring
    _ =
          slope f c d * ((b - c) * (d - a) / (b - a)) -
            (b - c) * slope f c b := by
          rw [hshift, hfb]
          ring
    _ =
          (b - c) *
            ((d - a) / (b - a) * slope f c d - slope f c b) := by
          ring

/-- Secant-quotient normal form of the Hiai Schur scalar expression. -/
def hiaiInterlacingSchurSecantExpression
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  ((c - a) * (slope f c a + (d - b) / (b - a) * slope f c d)) *
      ((b - c) * ((d - a) / (b - a) * slope f c d - slope f c b)) -
    (slope f c d * hiaiInterlacingOffdiagCoeffReal a c b d) *
      (slope f c d * hiaiInterlacingOffdiagCoeffReal a c b d)

/-- The Hiai Schur scalar expression is exactly the secant-quotient expression. -/
theorem hiaiInterlacingSchurScalarExpression_secantFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) :
    hiaiInterlacingSchurScalarExpression f a c b d =
      hiaiInterlacingSchurSecantExpression f a c b d := by
  unfold hiaiInterlacingSchurScalarExpression
    hiaiInterlacingSchurSecantExpression
  rw [hiaiInterlacingSchur_diag00_secantFormula f hac hcb,
    hiaiInterlacingSchur_diag11_secantFormula f hac hcb]
  rw [hiaiInterlacingSpectralSlope_eq_slope]

/-- The fully collected scalar core of the Hiai Schur secant expression. -/
def hiaiInterlacingSchurSecantCoreExpression
    (f : ℝ → ℝ) (a c b d : ℝ) : ℝ :=
  (c - a) * (b - c) *
    (((d - a) / (b - a)) * slope f c a * slope f c d -
      slope f c a * slope f c b -
      ((d - b) / (b - a)) * slope f c b * slope f c d)

/--
The Hiai Schur secant expression has a collected core form in which the
off-diagonal square has cancelled the quadratic `slope f c d` term.
-/
theorem hiaiInterlacingSchurSecantExpression_coreFormula
    (f : ℝ → ℝ) {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    hiaiInterlacingSchurSecantExpression f a c b d =
      hiaiInterlacingSchurSecantCoreExpression f a c b d := by
  unfold hiaiInterlacingSchurSecantExpression
    hiaiInterlacingSchurSecantCoreExpression
  have hO :=
    hiaiInterlacingOffdiagCoeffReal_sq
      (a := a) (c := c) (b := b) (d := d) hac hcb hbd
  have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
  let D := slope f c d
  let O := hiaiInterlacingOffdiagCoeffReal a c b d
  let W0 := hiaiInterlacingWeight0 a c b d
  let W1 := hiaiInterlacingWeight1 a c b d
  have hterm : D * O * (D * O) = D * D * (W0 * W1) := by
    have hO' : O * O = W0 * W1 := by
      simpa [O, W0, W1] using hO
    rw [← hO']
    ring
  change
    (c - a) * (slope f c a + (d - b) / (b - a) * D) *
        ((b - c) * ((d - a) / (b - a) * D - slope f c b)) -
      D * O * (D * O) =
    (c - a) * (b - c) *
      (((d - a) / (b - a)) * slope f c a * D -
        slope f c a * slope f c b -
        ((d - b) / (b - a)) * slope f c b * D)
  rw [hterm]
  unfold W0 W1 hiaiInterlacingWeight0 hiaiInterlacingWeight1
  field_simp [hab]
  ring

/--
Four-point Hiai Schur positivity in secant-quotient normal form.

This scalar inequality feeds the downstream conversion to matching one-sided
secant limits.
-/
theorem hiaiInterlacingCFCDifference_schur_secantFormula
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ hiaiInterlacingSchurSecantExpression f a c b d := by
  have hschur :=
    hiaiInterlacingCFCDifference_schur_realScalarFormula
      h2 ha hb hc hd hac hcb hbd
  rwa [hiaiInterlacingSchurScalarExpression_secantFormula f hac hcb] at hschur

/--
Four-point Hiai Schur positivity in the collected secant-core normal form.

This is the exact scalar inequality used by the final common-limit squeeze.
-/
theorem hiaiInterlacingCFCDifference_schur_secantCore_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ hiaiInterlacingSchurSecantCoreExpression f a c b d := by
  have hsec :=
    hiaiInterlacingCFCDifference_schur_secantFormula
      h2 ha hb hc hd hac hcb hbd
  rwa [hiaiInterlacingSchurSecantExpression_coreFormula f hac hcb hbd] at hsec

/--
The same Hiai four-point inequality after dividing by the positive factor
`(c - a) * (b - c)`.
-/
theorem hiaiInterlacingCFCDifference_schur_slopeCore_nonneg
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤
      (((d - a) / (b - a)) * slope f c a * slope f c d -
        slope f c a * slope f c b -
        ((d - b) / (b - a)) * slope f c b * slope f c d) := by
  have hcore :=
    hiaiInterlacingCFCDifference_schur_secantCore_nonneg
      h2 ha hb hc hd hac hcb hbd
  have hpos : 0 < (c - a) * (b - c) :=
    mul_pos (sub_pos.mpr hac) (sub_pos.mpr hcb)
  unfold hiaiInterlacingSchurSecantCoreExpression at hcore
  exact nonneg_of_mul_nonneg_right hcore hpos

/-! ### Slope-core interface on the unit interval -/

/-- Full `2×2` CFC order comparison supplies the scalar Hiai slope-core. -/
theorem hiaiSlopeCoreOnUnitInterval_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B) :
    hiaiSlopeCoreOnUnitInterval f := by
  intro a c b d ha hb hc hd hac hcb hbd
  exact hiaiInterlacingCFCDifference_schur_slopeCore_nonneg
    h2 ha hb hc hd hac hcb hbd

/-! ### Zero-anchor reductions for the slope squeeze -/

/-! ### Asymptotic q-bounds from the Hiai core -/

/-! ### Max-bound form of the slope squeeze -/

/--
The collected four-point Hiai inequality bounds the middle right secant by the
larger of the left and far-right anchor secants, away from the zero-anchor
case.  This is the scalar max-bound used by the final squeeze.
-/
theorem hiaiInterlacing_slopeCore_bound_right
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hden :
      0 <
        slope f c a + ((d - b) / (b - a)) * slope f c d) :
    slope f c b ≤ max (slope f c a) (slope f c d) := by
  let A := slope f c a
  let B := slope f c b
  let D := slope f c d
  let q := (d - b) / (b - a)
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hA : 0 ≤ A := by
    exact MonotoneOn.slope_nonneg hmono hc ha
  have hD : 0 ≤ D := by
    exact MonotoneOn.slope_nonneg hmono hc hd
  have hq : 0 < q := by
    have hnum : 0 < d - b := sub_pos.mpr hbd
    have hden' : 0 < b - a := sub_pos.mpr (lt_trans hac hcb)
    exact div_pos hnum hden'
  have hcore0 :=
    hiaiInterlacingCFCDifference_schur_slopeCore_nonneg
      h2 ha hb hc hd hac hcb hbd
  have hcore :
      0 ≤ (1 + q) * A * D - A * B - q * B * D := by
    have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
    dsimp [A, B, D, q]
    convert hcore0 using 1
    field_simp [hab]
    ring
  simpa [A, B, D, q] using
    hiai_slopeCore_bound_of_posDen hA hD hq hden hcore

/-! ### Full two-by-two CFC slope squeeze -/

/--
If both anchor secants in the Hiai four-point comparison vanish, scalar
monotonicity forces the middle right secant to vanish as well.
-/
lemma twoByTwo_cfc_order_hiai_rightSecant_zeroAnchor
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (_ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hleft : slope f c a = 0) (hright : slope f c d = 0) :
    slope f c b = 0 := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hfa : f a = f c := by
    have hne : a - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt hac)
    rw [slope_def_field] at hleft
    field_simp [hne] at hleft
    have hzero : f a - f c = 0 := by simpa using hleft
    exact sub_eq_zero.mp hzero
  have hfd : f d = f c := by
    have hne : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hcb hbd))
    rw [slope_def_field] at hright
    field_simp [hne] at hright
    have hzero : f d - f c = 0 := by simpa using hright
    exact sub_eq_zero.mp hzero
  have hcfb : f c ≤ f b := hmono hc hb hcb.le
  have hbfc : f b ≤ f c := by
    have hbfd : f b ≤ f d := hmono hb hd hbd.le
    simpa [hfd] using hbfd
  have hfb : f b = f c := le_antisymm hbfc hcfb
  rw [slope_def_field]
  simp [hfb]

/-- Named full-`2×2` CFC-order version of the Hiai right-secant max bound. -/
theorem twoByTwo_cfc_order_hiai_rightSecant_maxBound
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤ max (slope f c a) (slope f c d) :=
  by
    let A := slope f c a
    let D := slope f c d
    let q := (d - b) / (b - a)
    have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
    have hA : 0 ≤ A := by
      exact MonotoneOn.slope_nonneg hmono hc ha
    have hD : 0 ≤ D := by
      exact MonotoneOn.slope_nonneg hmono hc hd
    have hq : 0 < q := by
      have hnum : 0 < d - b := sub_pos.mpr hbd
      have hden' : 0 < b - a := sub_pos.mpr (lt_trans hac hcb)
      exact div_pos hnum hden'
    by_cases hden : 0 < A + q * D
    · exact hiaiInterlacing_slopeCore_bound_right
        h2 ha hb hc hd hac hcb hbd (by simpa [A, D, q] using hden)
    · have hsum_nonneg : 0 ≤ A + q * D := by
        exact add_nonneg hA (mul_nonneg (le_of_lt hq) hD)
      have hsum_zero : A + q * D = 0 := le_antisymm (le_of_not_gt hden) hsum_nonneg
      have hA0 : A = 0 := by
        have hqD_nonneg : 0 ≤ q * D := mul_nonneg (le_of_lt hq) hD
        nlinarith
      have hD0 : D = 0 := by
        have hqD_zero : q * D = 0 := by nlinarith
        exact (mul_eq_zero.mp hqD_zero).resolve_left (ne_of_gt hq)
      have hmid :=
        twoByTwo_cfc_order_hiai_rightSecant_zeroAnchor
          h2 ha hb hc hd hac hcb hbd (by simpa [A] using hA0) (by simpa [D] using hD0)
      simp [hmid, A, D, hA0, hD0]


end

end Quantum.TraceInequality.Loewner
