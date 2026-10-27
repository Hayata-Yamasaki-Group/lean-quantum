import Quantum.TraceInequality.UnitaryBlockMatrix
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.Core
import Quantum.TraceInequality.CompressionInequality.SpectralBounds
import Quantum.TraceInequality.CompressionInequality.RotatedBlockCompression
import Quantum.TraceInequality.CompressionInequality.JuliaUnitary
import Quantum.TraceInequality.CompressionInequality.DefectOperators
import Quantum.TraceInequality.CompressionInequality.ContractionInstances
import Quantum.TraceInequality.CompressionInequality.BlockMatrix
import Quantum.TraceInequality.BlockDiagonal
import Quantum.TraceInequality.BasicTheorems
import Quantum.TraceInequality.Basic
import Quantum.QuantumMechanics.OperatorNotation
import Quantum.TraceInequality.JensenOperatorInequalityFinite

/-!
Finite Jensen inequalities: open-interval version without continuity assumption;
general interval with continuity assumed only at included endpoints
(interior continuity derived); half-line interface as a specialization.
Source: arXiv:2607.05492v1 main.tex:945–955;
Hansen–Pedersen (2003), Jensen's Operator Inequality.
-/
namespace JensenOperatorInequality
open LownerHeinzTheorem
universe u v
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ] [Nontrivial ℋ]

/-- Scalar restriction of localized operator convexity on an order-connected set. -/
theorem convexOn_of_operatorConvexOn_interval {I : Set ℝ} {f : ℝ → ℝ}
    (hI : I.OrdConnected) (hf : OperatorConvexOn (ℋ := ℋ) I f) :
    ConvexOn ℝ I f := by
  refine ⟨hI.convex, ?_⟩
  intro x hxI y hyI a b ha hb hab
  have hb1 : b ≤ 1 := by
    linarith
  have halg_combo (u v r s : ℝ) :
      u • (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) + v • (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) =
        algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r + v * s) := by
    calc
      u • (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) + v • (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) =
          (algebraMap ℝ (ℋ →L[ℂ] ℋ) u) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) +
            (algebraMap ℝ (ℋ →L[ℂ] ℋ) v) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) := by
              rw [Algebra.smul_def, Algebra.smul_def]
      _ = algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r) + algebraMap ℝ (ℋ →L[ℂ] ℋ) (v * s) := by
            simp
      _ = algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r + v * s) := by
            simp
  have hop :
      cfcR (ℋ := ℋ) f
          ((1 - b) • (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) + b • (algebraMap ℝ ((ℋ →L[ℂ] ℋ)) y)) ≤
        (1 - b) • cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) +
          b • cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) y) :=
    hf (A := algebraMap ℝ (ℋ →L[ℂ] ℋ) x) (B := algebraMap ℝ (ℋ →L[ℂ] ℋ) y) (t
        := b)
      (cfc_predicate_algebraMap x) (cfc_predicate_algebraMap y) hb hb1
      ((CFC.spectrum_algebraMap_subset x).trans (Set.singleton_subset_iff.mpr hxI))
      ((CFC.spectrum_algebraMap_subset y).trans (Set.singleton_subset_iff.mpr hyI))
  have hx :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) = algebraMap ℝ ((ℋ →L[ℂ] ℋ)) (f x) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) y) = algebraMap ℝ ((ℋ →L[ℂ] ℋ)) (f y) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hxy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) ((1 - b) * x + b * y)) =
        algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)) := by
    simpa [cfcR, LownerHeinzCore.cfcR] using
      cfc_algebraMap (A := (ℋ →L[ℂ] ℋ)) (((1 - b) * x + b * y)) f
  rw [halg_combo (u := 1 - b) (v := b) (r := x) (s := y), hxy, hx, hy,
    halg_combo (u := 1 - b) (v := b) (r := f x) (s := f y)] at hop
  have hscalar :
      algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)) ≤
        algebraMap ℝ (ℋ →L[ℂ] ℋ) ((1 - b) * f x + b * f y) := by
    simpa [Algebra.smul_def] using hop
  have hspec_le :
      ∀ z ∈ spectrum ℝ (algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y))),
        z ≤ (1 - b) * f x + b * f y := by
    simpa using
      (le_algebraMap_iff_spectrum_le
        (R := ℝ) (A := (ℋ →L[ℂ] ℋ))
        (a := algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)))
        (r := (1 - b) * f x + b * f y)
        (ha := cfc_predicate_algebraMap (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x + b *
            y)))).1 hscalar
  have ha' : a = 1 - b := by
    linarith
  have hscalar' : f ((1 - b) * x + b * y) ≤ (1 - b) * f x + b * f y := by
    obtain ⟨z, hz⟩ :=
      ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ)
        (algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)))
        (cfc_predicate_algebraMap (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x + b * y)))
    have hz_eq : z = f ((1 - b) * x + b * y) := by
      have hz_single :=
        CFC.spectrum_algebraMap_subset (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x
            + b * y)) hz
      simpa using hz_single
    simpa [hz_eq] using hspec_le z hz
  simpa [smul_eq_mul, ha'] using hscalar'

include ℋ in
/-- Uniform localized operator convexity implies continuity in the interior. -/
theorem continuousOn_interior_of_operatorConvexOnAll {I : Set ℝ} {f : ℝ → ℝ}
    (hI : I.OrdConnected) (hf : OperatorConvexOnAll.{u} I f) :
    ContinuousOn f (interior I) :=
  (convexOn_of_operatorConvexOn_interval (ℋ := ℋ) hI (hf (K := ℋ))).continuousOn_interior

/-- The only topological gap after interior continuity is at included endpoints. -/
theorem continuousOn_of_interior_and_endpoints {I : Set ℝ} {f : ℝ → ℝ}
    (hi : ContinuousOn f (interior I))
    (he : ∀ x ∈ I \ interior I, ContinuousWithinAt f I x) :
    ContinuousOn f I := by
  intro x hx
  by_cases hxi : x ∈ interior I
  · exact ((isOpen_interior.continuousOn_iff.mp hi) hxi).continuousWithinAt
  · exact he x ⟨hx, hxi⟩

omit [Nontrivial ℋ] in
/-- Scalar bounds survive a finite contractive column when the bounding interval contains zero. -/
theorem finite_compression_order_bounds {ι : Type v} [Fintype ι]
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (A X : ι → ℋ →L[ℂ] ℋ)
    (hlo : ∀ i, algebraMap ℝ (ℋ →L[ℂ] ℋ) a ≤ A i)
    (hhi : ∀ i, A i ≤ algebraMap ℝ (ℋ →L[ℂ] ℋ) b)
    (hX : ∑ i, star (X i) * X i ≤ 1) :
    algebraMap ℝ (ℋ →L[ℂ] ℋ) a ≤ ∑ i, star (X i) * A i * X i ∧
      ∑ i, star (X i) * A i * X i ≤ algebraMap ℝ (ℋ →L[ℂ] ℋ) b := by
  constructor
  · calc
      algebraMap ℝ (ℋ →L[ℂ] ℋ) a = a • (1 : ℋ →L[ℂ] ℋ) :=
        Algebra.algebraMap_eq_smul_one a
      _ ≤ a • (∑ i, star (X i) * X i) := smul_le_smul_of_nonpos_left hX ha
      _ = ∑ i, a • (star (X i) * X i) := Finset.smul_sum
      _ ≤ ∑ i, star (X i) * A i * X i := by
        apply Finset.sum_le_sum
        intro i _
        simpa [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_assoc]
          using star_left_conjugate_le_conjugate (hlo i) (X i)
  · calc
      ∑ i, star (X i) * A i * X i ≤ ∑ i, b • (star (X i) * X i) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_assoc]
          using star_left_conjugate_le_conjugate (hhi i) (X i)
      _ = b • (∑ i, star (X i) * X i) := Finset.smul_sum.symm
      _ ≤ b • (1 : ℋ →L[ℂ] ℋ) := smul_le_smul_of_nonneg_left hX hb
      _ = algebraMap ℝ (ℋ →L[ℂ] ℋ) b := (Algebra.algebraMap_eq_smul_one b).symm

omit [Nontrivial ℋ] in
/-- Finite contraction compression preserves every order-connected spectral set containing zero.
Compactness is used only for the finite union of the input spectra, not for the interval itself. -/
theorem finite_compression_spectrum_subset {ι : Type v} [Fintype ι] {I : Set ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) (A X : ι → ℋ →L[ℂ] ℋ)
    (hA : ∀ i, IsSelfAdjoint (A i)) (hAs : ∀ i, spectrum ℝ (A i) ⊆ I)
    (hX : ∑ i, star (X i) * X i ≤ 1) :
    IsSelfAdjoint (∑ i, star (X i) * A i * X i) ∧
      spectrum ℝ (∑ i, star (X i) * A i * X i) ⊆ I := by
  classical
  let S : Set ℝ := insert 0 (⋃ i, spectrum ℝ (A i))
  have hS : IsCompact S := (isCompact_iUnion fun i ↦ spectrum.isCompact (A i)).insert 0
  have hS0 : (0 : ℝ) ∈ S := Set.mem_insert _ _
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hSI : S ⊆ I := by
    intro x hx
    rcases hx with rfl | hx
    · exact h0
    · rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact hAs i hi
  have hlow := hS.isLeast_sInf hSne
  have hhigh := hS.isGreatest_sSup hSne
  have hspec (i : ι) : spectrum ℝ (A i) ⊆ S :=
    fun _ hx ↦ Set.mem_insert_of_mem 0 (Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hb := finite_compression_order_bounds (hlow.2 hS0) (hhigh.2 hS0) A X
    (fun i ↦ (algebraMap_le_iff_le_spectrum (hA i)).mpr
      (fun _ hx ↦ hlow.2 (hspec i hx)))
    (fun i ↦ (le_algebraMap_iff_spectrum_le (hA i)).mpr
      (fun _ hx ↦ hhigh.2 (hspec i hx))) hX
  have hsa : IsSelfAdjoint (∑ i, star (X i) * A i * X i) := by
    apply isSelfAdjoint_sum
    intro i _
    simpa using (hA i).conjugate (star (X i))
  refine ⟨hsa, ?_⟩
  intro x hx
  exact hI.out (hSI hlow.1) (hSI hhigh.1)
    ⟨(algebraMap_le_iff_le_spectrum hsa).mp hb.1 x hx,
      (le_algebraMap_iff_spectrum_le hsa).mp hb.2 x hx⟩

namespace IntervalCompression
open HansenPedersen hiding cfcR
open HansenPedersen.ConvexityCharacterization
open scoped HansenPedersen.ConvexityCharacterization.ContractionInstances

private lemma zero_spectrum {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Set ℝ} (h0 : 0 ∈ I) :
    spectrum ℝ (0 : L K) ⊆ I := by
  simpa using (CFC.spectrum_algebraMap_subset (A := L K) (0 : ℝ)).trans
    (Set.singleton_subset_iff.mpr h0)

private lemma diag_spectrum {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Set ℝ} {A B : L K}
    (_hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B)
    (hA : spectrum ℝ A ⊆ I) (hB : spectrum ℝ B ⊆ I) :
    spectrum ℝ (HansenPedersen.Internal.diagMapCLM A B) ⊆ I := by
  have h := AlgHom.spectrum_apply_subset
    ((HansenPedersen.Internal.diagStarAlgHom (K := K) (L' := K)).restrictScalars ℝ) (A, B)
  exact h.trans (by simpa only [Prod.spectrum_eq] using Set.union_subset hA hB)

private lemma compression_spectrum {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Set ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) {A C : L K}
    (hA : IsSelfAdjoint A) (hAs : spectrum ℝ A ⊆ I) (hC : ‖C‖ ≤ 1) :
    spectrum ℝ (star C * A * C) ⊆ I := by
  simpa using (finite_compression_spectrum_subset (ι := Fin 1) hI h0
    (fun _ ↦ A) (fun _ ↦ C) (fun _ ↦ hA) (fun _ ↦ hAs)
    (by simpa using star_mul_self_le_one_of_norm_le_one hC)).2

private lemma diag_cfc {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Set ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f I) {A B : L K} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAs : spectrum ℝ A ⊆ I) (hBs : spectrum ℝ B ⊆ I) :
    cfcR f (HansenPedersen.Internal.diagMapCLM A B) =
      HansenPedersen.Internal.diagMapCLM (cfcR f A) (cfcR f B) :=
  HansenPedersen.cfcR_diagMapCLM_union (hc.mono (Set.union_subset hAs hBs)) hA hB

private lemma unitary_cfc {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {I : Set ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f I) {A : L K} (hA : IsSelfAdjoint A)
    (hAs : spectrum ℝ A ⊆ I) (U : unitary (L K)) :
    cfcR f (star (↑U : L K) * A * (↑U : L K)) =
      star (↑U : L K) * cfcR f A * (↑U : L K) := by
  let φ : L K →⋆ₐ[ℝ] L K := Unitary.conjStarAlgAut ℝ (L K) (star U)
  have hφ : Continuous φ := by
    have hc : Continuous (fun T : L K ↦ star (↑U : L K) * T * (↑U : L K)) := by
      fun_prop
    have heq : (fun T : L K ↦ φ T) =
        (fun T : L K ↦ star (↑U : L K) * T * (↑U : L K)) := by
      funext T
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa only [heq] using hc
  have hm := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hc.mono hAs) (hφ := hφ) (ha := hA) (hφa := hA.map φ)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hm.symm

private lemma star_juliaBlock_mul_diag_mul_juliaBlock
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C E D W Z : L K) (hE : star E = E) (hD : star D = D) :
    star (blockCLM C (-E) D (star C)) * blockCLM W 0 0 Z * blockCLM C (-E) D (star C) =
      blockCLM (star C * W * C + D * Z * D)
        (-(star C * W * E) + D * Z * star C)
        (-(E * W * C) + C * Z * D)
        (E * W * E + C * Z * star C) := by
  rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
  simp [hE, hD, mul_assoc, add_comm]

/-- Sign-flipped Julia-block conjugation of a diagonal block operator
(`V = blockCLM C E D (-(star C))` shape), computed once over atom operators.
The proof uses block multiplication and self-adjointness of the defect blocks. -/
private lemma star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C E D W Z : L K) (hE : star E = E) (hD : star D = D) :
    star (blockCLM C E D (-(star C))) * blockCLM W 0 0 Z * blockCLM C E D (-(star C)) =
      blockCLM (star C * W * C + D * Z * D)
        (star C * W * E - D * Z * star C)
        (E * W * C - C * Z * D)
        (E * W * E + C * Z * star C) := by
  rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
  simp [hE, hD, mul_assoc, sub_eq_add_neg, add_comm]

/-- Midpoint average of two block operators with equal diagonal and opposite
off-diagonal blocks: the off-diagonal parts cancel and the average collapses to
the block-diagonal operator. The proof adds the blocks componentwise, cancels
the off-diagonal sums, and normalizes the diagonal sums by scalar multiplication. -/
private lemma half_smul_add_blockCLM_of_neg
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a b b' c c' d : L K) (hb : b' = -b) (hc : c' = -c) :
    (1 / 2 : ℝ) • (blockCLM a b' c' d + blockCLM a b c d) =
      HansenPedersen.Internal.diagMapCLM a d := by
  subst hb hc
  rw [blockCLM_add, smul_blockCLM]
  have ha2 : (1 / 2 : ℝ) • (a + a) = a := by
    rw [smul_add, ← add_smul]
    norm_num
  have hd2 : (1 / 2 : ℝ) • (d + d) = d := by
    rw [smul_add, ← add_smul]
    norm_num
  rw [neg_add_cancel, neg_add_cancel, smul_zero, ha2, hd2, blockCLM_zero_zero]

/-- Two-sided compression of the real CFC of `0` reduces to a scalar multiple:
`cfcR f 0` is the constant `f 0` times the identity, so `D * cfcR f 0 * D`
collapses to `f 0 • (D * D)`. The proof evaluates the real CFC at zero and rewrites
the scalar algebra map as scalar multiplication. -/
private lemma mul_cfcR_zero_mul {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint]
    (f : ℝ → ℝ) (D : L K) :
    D * cfcR (ℋ := K) f 0 * D = (f 0 : ℝ) • (D * D) := by
  simp [cfcR, Algebra.algebraMap_eq_smul_one]

/-- General-interval Julia dilation. Continuity is explicit at this layer. -/
theorem contraction {I : Set ℝ} {f : ℝ → ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) (hf : ContinuousOn f I)
    (hop : OperatorConvexOnAll.{u} I f) (hf0 : f 0 ≤ 0)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] {A C : L H} (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ I) (hC : ‖C‖ ≤ 1) :
    cfcR f (star C * A * C) ≤ star C * cfcR f A * C := by
  letI : Algebra ℝ (L (WithLp 2 (H × H))) := inferInstance
  letI : NormedSpace ℝ (L (WithLp 2 (H × H))) := inferInstance
  letI : Module ℝ (L (WithLp 2 (H × H))) := inferInstance
  /- Step 1: Build the Julia dilation encoding the contraction as a midpoint problem. -/
  haveI : Nontrivial H := HansenPedersen.nontrivial_of_nontrivial_L
  haveI : Nontrivial (WithLp 2 (H × H)) := inferInstance
  let E : L H := defectLeft C
  let D : L H := defectRight C
  let A0 : L (WithLp 2 (H × H)) := HansenPedersen.Internal.diagMapCLM A 0
  let F0 : L (WithLp 2 (H × H)) :=
    HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0)
  let U0 : L (WithLp 2 (H × H)) := blockCLM C (-E) D (star C)
  let S0 : L (WithLp 2 (H × H)) := blockCLM (1 : L H) 0 0 (- (1 : L H))
  let U : unitary (L (WithLp 2 (H × H))) := ⟨U0, julia_block_mem_unitary (K := H) hC⟩
  let S : unitary (L (WithLp 2 (H × H))) := ⟨S0, signFlip_block_mem_unitary (K := H)⟩
  let V : unitary (L (WithLp 2 (H × H))) := U * S
  let X : L (WithLp 2 (H × H)) := star (↑U : L (WithLp 2 (H × H))) * A0 * (↑U : L _)
  let Y : L (WithLp 2 (H × H)) := star (↑V : L (WithLp 2 (H × H))) * A0 * (↑V : L _)
  let M : L H := star C * A * C
  let N : L H := E * A * E
  let R : L H := star C * cfcR (ℋ := H) f A * C + D * cfcR (ℋ := H) f 0 * D
  let T : L H := E * cfcR (ℋ := H) f A * E + C * cfcR (ℋ := H) f 0 * star C
  have hEstar : star E = E := (defectLeft_selfAdjoint (K := H) C).star_eq
  have hDstar : star D = D := (defectRight_selfAdjoint (K := H) C).star_eq
  have h0self : IsSelfAdjoint (0 : L H) := IsSelfAdjoint.zero _
  /- Step 2: Transfer self-adjointness and spectral control from A to the dilated conjugates. -/
  have hA0self : IsSelfAdjoint A0 := by
    simpa [A0] using HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hA h0self
  have hσA0 : spectrum ℝ A0 ⊆ I := by
    simpa [A0] using diag_spectrum
      (K := H) hA h0self hσA (zero_spectrum h0)
  have hXself : IsSelfAdjoint X := by
    simpa [X, A0, U0, U] using hA0self.map (unitaryConjStarAlgHom U)
  have hYself : IsSelfAdjoint Y := by
    simpa [Y, A0, V] using hA0self.map (unitaryConjStarAlgHom V)
  have hσX : spectrum ℝ X ⊆ I := by
    have hspec : spectrum ℝ X = spectrum ℝ A0 := by
      dsimp [X]
      exact Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A0) (U := U)
    rw [hspec]
    exact hσA0
  have hσY : spectrum ℝ Y ⊆ I := by
    have hspec : spectrum ℝ Y = spectrum ℝ A0 := by
      dsimp [Y]
      exact Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A0) (U := V)
    rw [hspec]
    exact hσA0
  have hConv :
      HOperatorConvexOnInterval (WithLp 2 (H × H)) (I) f :=
    hop (K := WithLp 2 (H × H))
  have hA0block : A0 = blockCLM A 0 0 0 := by
    dsimp [A0]
    exact (blockCLM_zero_zero (K := H) A (0 : L H)).symm
  /- Step 3: Rewrite the conjugates so off-diagonal blocks cancel on averaging. -/
  have hXblock :
      X =
        blockCLM M (-(star C * A * E)) (-(E * A * C)) N := by
    dsimp only [X, U, U0]
    rw [show A0 = blockCLM A 0 0 0 by simpa [blockCLM_zero_zero] using hA0block]
    rw [star_juliaBlock_mul_diag_mul_juliaBlock (K := H) C E D A 0 hEstar hDstar]
    simp [M, N]
  have hVblock :
      (↑V : L (WithLp 2 (H × H))) = blockCLM C E D (- star C) := by
    dsimp [V, U, S, U0, S0]
    rw [blockCLM_mul]
    simp
  have hYblock :
      Y =
        blockCLM M (star C * A * E) (E * A * C) N := by
    dsimp only [Y]
    rw [hVblock]
    rw [show A0 = blockCLM A 0 0 0 by simpa [blockCLM_zero_zero] using hA0block]
    rw [star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock (K := H) C E D A 0 hEstar hDstar]
    simp [M, N]
  have havg :
      (1 / 2 : ℝ) • (X + Y) = HansenPedersen.Internal.diagMapCLM M N := by
    rw [hXblock, hYblock]
    exact half_smul_add_blockCLM_of_neg M _ _ _ _ N rfl rfl
  have hσM : spectrum ℝ M ⊆ I := by
    simpa [M] using compression_spectrum hI h0 hA hσA hC
  have hσN : spectrum ℝ N ⊆ I := by
    have hEnorm : ‖E‖ ≤ 1 := defectLeft_norm_le_one (K := H) hC
    simpa [N, E, hEstar] using compression_spectrum hI h0 hA hσA hEnorm
  have hMself : IsSelfAdjoint M := by
    simpa [M] using star_mul_selfAdjoint_mul (K := H) (T := A) (C := C) hA
  have hNself : IsSelfAdjoint N := by
    simpa [N, E, hEstar] using star_mul_selfAdjoint_mul (K := H) (T := A) (C := E) hA
  /- Step 4: Identify the averaged CFC and the two conjugate CFCs in diagonal form. -/
  have hcfavg :
      cfcR (ℋ := WithLp 2 (H × H)) f ((1 / 2 : ℝ) • (X + Y)) =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f N) := by
    rw [havg]
    simpa using diag_cfc (K := H) hf hMself hNself hσM hσN
  have hcfA0 :
      cfcR (ℋ := WithLp 2 (H × H)) f A0 = F0 := by
    simpa [A0, F0] using diag_cfc (K := H) hf hA h0self
      hσA (zero_spectrum h0)
  have hcfX :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        star (↑U : L (WithLp 2 (H × H))) * F0 * (↑U : L _) := by
    calc
      cfcR (ℋ := WithLp 2 (H × H)) f X =
          star (↑U : L (WithLp 2 (H × H))) *
            cfcR (ℋ := WithLp 2 (H × H)) f A0 * (↑U : L _) := by
            simpa [X] using unitary_cfc (K := WithLp 2 (H × H)) hf hA0self hσA0 U
      _ = star (↑U : L (WithLp 2 (H × H))) * F0 * (↑U : L _) := by rw [hcfA0]
  have hcfY :
      cfcR (ℋ := WithLp 2 (H × H)) f Y =
        star (↑V : L (WithLp 2 (H × H))) * F0 * (↑V : L _) := by
    calc
      cfcR (ℋ := WithLp 2 (H × H)) f Y =
          star (↑V : L (WithLp 2 (H × H))) *
            cfcR (ℋ := WithLp 2 (H × H)) f A0 * (↑V : L _) := by
            simpa [Y] using unitary_cfc (K := WithLp 2 (H × H)) hf hA0self hσA0 V
      _ = star (↑V : L (WithLp 2 (H × H))) * F0 * (↑V : L _) := by rw [hcfA0]
  have hcfXblock :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        blockCLM R
          (-(star C * cfcR (ℋ := H) f A * E) + D * cfcR (ℋ := H) f 0 * star C)
          (-(E * cfcR (ℋ := H) f A * C) + C * cfcR (ℋ := H) f 0 * D)
          T := by
    rw [hcfX]
    dsimp only [F0, U, U0]
    rw [show HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) =
          blockCLM (cfcR (ℋ := H) f A) 0 0 (cfcR (ℋ := H) f 0) by
          simp [blockCLM_zero_zero]]
    rw [star_juliaBlock_mul_diag_mul_juliaBlock (K := H) C E D
      (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) hEstar hDstar]
  have hcfYblock :
      cfcR (ℋ := WithLp 2 (H × H)) f Y =
        blockCLM R
          (star C * cfcR (ℋ := H) f A * E - D * cfcR (ℋ := H) f 0 * star C)
          (E * cfcR (ℋ := H) f A * C - C * cfcR (ℋ := H) f 0 * D)
          T := by
    rw [hcfY, hVblock]
    dsimp only [F0]
    rw [show HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) =
          blockCLM (cfcR (ℋ := H) f A) 0 0 (cfcR (ℋ := H) f 0) by
          simp [blockCLM_zero_zero]]
    rw [star_signedJuliaBlock_mul_diag_mul_signedJuliaBlock (K := H) C E D
      (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f 0) hEstar hDstar]
  have hrhs :
      (1 / 2 : ℝ) •
          (cfcR (ℋ := WithLp 2 (H × H)) f X + cfcR (ℋ := WithLp 2 (H × H)) f Y) =
        HansenPedersen.Internal.diagMapCLM R T := by
    rw [hcfXblock, hcfYblock]
    exact half_smul_add_blockCLM_of_neg R _ _ _ _ T (by abel) (by abel)
  /- Step 5: Apply midpoint convexity on the dilation to obtain a diagonal block inequality. -/
  have hconv :
      cfcR (ℋ := WithLp 2 (H × H)) f ((1 / 2 : ℝ) • (X + Y)) ≤
        (1 / 2 : ℝ) •
          (cfcR (ℋ := WithLp 2 (H × H)) f X + cfcR (ℋ := WithLp 2 (H × H)) f Y) := by
    have h := hConv (t := (1 / 2 : ℝ)) hXself hYself (by norm_num)
      (by norm_num) hσX hσY
    norm_num at h
    simpa only [smul_add] using h
  have hdiag :
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f N) ≤
        HansenPedersen.Internal.diagMapCLM R T := by
    rw [hcfavg, hrhs] at hconv
    exact hconv
  /- Step 6: Read the first diagonal block and discard the f 0 defect term. -/
  have hRself : IsSelfAdjoint R := by
    dsimp [R]
    refine (star_mul_selfAdjoint_mul
      (K := H)
      (T := cfcR (ℋ := H) f A)
      (C := C)
      (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := A))).add ?_
    simpa [D, hDstar] using
      (star_mul_selfAdjoint_mul
        (K := H)
        (T := cfcR (ℋ := H) f 0)
        (C := D)
        (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := 0)))
  have hcfM_le : cfcR (ℋ := H) f M ≤ R := by
    exact diagMapCLM_fst_le_of_le
      (K := H)
      (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := M))
      hRself
      hdiag
  have hcf0_term_nonpos : D * cfcR (ℋ := H) f 0 * D ≤ 0 := by
    calc
      D * cfcR (ℋ := H) f 0 * D = (f 0 : ℝ) • (D * D) :=
        mul_cfcR_zero_mul f D
      _ ≤ (0 : ℝ) • (D * D) := by
        exact smul_le_smul_of_nonneg_right hf0
          (by simpa [D, hDstar] using star_mul_self_nonneg D)
      _ = 0 := by simp
  have hR_le : R ≤ star C * cfcR (ℋ := H) f A * C := by
    simpa [R] using add_le_add_left hcf0_term_nonpos (star C * cfcR (ℋ := H) f A * C)
  exact le_trans hcfM_le hR_le

end IntervalCompression
noncomputable local instance : Algebra ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : NormedSpace ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : Module ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : NonnegSpectrumClass ℝ (HSum ℋ →L[ℂ] HSum ℋ) :=
  inferInstance

omit [Nontrivial ℋ] in
private lemma interval_block_compression (A B X Y : ℋ →L[ℂ] ℋ) :
    star (blockOp X 0 Y 0) * blockDiagonal A B * blockOp X 0 Y 0 =
      blockDiagonal (star X * A * X + star Y * B * Y) 0 := by
  rw [blockOp_star, blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul,
    blockDiagonal_eq_blockOp]
  congr 1 <;> simp [mul_assoc]

omit [Nontrivial ℋ] in
private lemma interval_block_gram (X Y : ℋ →L[ℂ] ℋ) :
    star (blockOp X 0 Y 0) * blockOp X 0 Y 0 =
      blockDiagonal (star X * X + star Y * Y) 0 := by
  have hone : blockDiagonal (1 : ℋ →L[ℂ] ℋ) 1 = 1 :=
    map_one (blockDiagonalHom (ℋ := ℋ))
  simpa [hone] using interval_block_compression (1 : ℋ →L[ℂ] ℋ) 1 X Y

omit [Nontrivial ℋ] in
private lemma interval_block_add (A B : ℋ →L[ℂ] ℋ) :
    blockDiagonal A 0 + blockDiagonal B 0 = blockDiagonal (A + B) 0 := by
  simpa only [blockDiagonalHom_apply, Prod.fst_add, Prod.snd_add, add_zero] using
    (map_add (blockDiagonalHom (ℋ := ℋ)) (A, 0) (B, 0)).symm

omit [Nontrivial ℋ] in
private lemma interval_block_sum {ι : Type v} [Fintype ι] (A : ι → ℋ →L[ℂ] ℋ) :
    ∑ i, blockDiagonal (A i) 0 = blockDiagonal (∑ i, A i) 0 := by
  simpa only [blockDiagonalHom_apply, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_const_zero] using (map_sum (blockDiagonalHom (ℋ := ℋ))
    (fun i ↦ (A i, (0 : ℋ →L[ℂ] ℋ))) Finset.univ).symm

omit [Nontrivial ℋ] in
private lemma interval_zero_spectrum {I : Set ℝ} (h0 : 0 ∈ I) :
    spectrum ℝ (0 : ℋ →L[ℂ] ℋ) ⊆ I := by
  simpa using (CFC.spectrum_algebraMap_subset (A := ℋ →L[ℂ] ℋ) (0 : ℝ)).trans
    (Set.singleton_subset_iff.mpr h0)

omit [Nontrivial ℋ] in
private lemma interval_block_spectrum {I : Set ℝ} {A B : ℋ →L[ℂ] ℋ}
    (hA : spectrum ℝ A ⊆ I) (hB : spectrum ℝ B ⊆ I) :
    spectrum ℝ (blockDiagonal A B) ⊆ I := by
  exact (AlgHom.spectrum_apply_subset (blockDiagonalHom (ℋ := ℋ)) (A, B)).trans
    (by simpa only [Prod.spectrum_eq] using Set.union_subset hA hB)

/-- General-interval binary column Jensen with explicit continuity. -/
theorem jensenColumn_of_opConvexOnAll_continuous {I : Set ℝ} {f : ℝ → ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) (hf : OperatorConvexOnAll.{u} I f)
    (hc : ContinuousOn f I) (hf0 : f 0 ≤ 0)
    (A B X Y : ℋ →L[ℂ] ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAs : spectrum ℝ A ⊆ I) (hBs : spectrum ℝ B ⊆ I)
    (hXY : star X * X + star Y * Y ≤ 1) :
    cfcR f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR f A * X + star Y * cfcR f B * Y := by
  have hsum := finite_compression_spectrum_subset (ι := Fin 2) hI h0
    ![A, B] ![X, Y] (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption) (by simpa [Fin.sum_univ_two] using hXY)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
  have hgram : star (blockOp X 0 Y 0) * blockOp X 0 Y 0 ≤ 1 := by
    rw [interval_block_gram]
    have hone : blockDiagonal (1 : ℋ →L[ℂ] ℋ) 1 = 1 :=
      map_one (blockDiagonalHom (ℋ := ℋ))
    rw [← hone]
    exact blockDiagonal_le_blockDiagonal hXY zero_le_one
  have hnorm : ‖blockOp X 0 Y 0‖ ≤ 1 := by
    have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (star_mul_self_nonneg (blockOp X 0 Y 0))).mpr hgram
    rw [CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg (blockOp X 0 Y 0)]
  have hh := IntervalCompression.contraction hI h0 hc (@hf) hf0
    (blockDiagonal_selfAdjoint hA hB) (interval_block_spectrum hAs hBs) hnorm
  rw [interval_block_compression,
    cfcR_blockDiagonal f _ _ hsum.1 (by simp)
      (hc.mono (Set.union_subset hsum.2 (interval_zero_spectrum h0))),
    cfcR_blockDiagonal f A B hA hB (hc.mono (Set.union_subset hAs hBs)),
    interval_block_compression] at hh
  exact blockDiagonal_le_left hh

/-- Uniform binary contractive-column Jensen on a spectral set. -/
def IntervalBinaryConditionAll (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [Nontrivial K] (A B X Y : K →L[ℂ] K),
    IsSelfAdjoint A → IsSelfAdjoint B → spectrum ℝ A ⊆ I → spectrum ℝ B ⊆ I →
    star X * X + star Y * Y ≤ 1 →
    cfcR f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR f A * X + star Y * cfcR f B * Y

private lemma jensen_fin_of_binary_interval {I : Set ℝ} {f : ℝ → ℝ}
    (hI : I.OrdConnected) (h0 : 0 ∈ I) (hc : ContinuousOn f I) (hf0 : f 0 ≤ 0)
    (hb : IntervalBinaryConditionAll.{u} I f) (n : ℕ) :
    ∀ {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [Nontrivial K] (A X : Fin n → K →L[ℂ] K),
      (∀ i, IsSelfAdjoint (A i)) → (∀ i, spectrum ℝ (A i) ⊆ I) →
      (∑ i, star (X i) * X i ≤ 1) →
      cfcR f (∑ i, star (X i) * A i * X i) ≤
        ∑ i, star (X i) * cfcR f (A i) * X i := by
  induction n using Nat.twoStepInduction with
  | zero =>
      intro K _ _ _ _ A X _ _ _
      simp only [Fin.sum_univ_zero]
      simpa [cfcR, Algebra.algebraMap_eq_smul_one] using
        smul_nonpos_of_nonpos_of_nonneg hf0 (show (0 : K →L[ℂ] K) ≤ 1 from zero_le_one)
  | one =>
      intro K _ _ _ _ A X hA hAs hX
      simpa using (hb (K := K) (A 0) 0 (X 0) 0 (hA 0) (by simp)
        (hAs 0) (interval_zero_spectrum h0) (by simpa using hX))
  | more n _ ih =>
      intro K _ _ _ _ A X hA hAs hX
      let P : Fin (n + 1) → HSum K →L[ℂ] HSum K :=
        Fin.cons (blockDiagonal (A 0) (A 1))
          (fun i ↦ blockDiagonal (A i.succ.succ) 0)
      let V : Fin (n + 1) → HSum K →L[ℂ] HSum K :=
        Fin.cons (blockOp (X 0) 0 (X 1) 0)
          (fun i ↦ blockOp (X i.succ.succ) 0 0 0)
      have hP : ∀ i, IsSelfAdjoint (P i) := by
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact blockDiagonal_selfAdjoint (hA 0) (hA 1)
        · exact blockDiagonal_selfAdjoint (hA j.succ.succ) (by simp)
      have hPs : ∀ i, spectrum ℝ (P i) ⊆ I := by
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact interval_block_spectrum (hAs 0) (hAs 1)
        · exact interval_block_spectrum (hAs j.succ.succ) (interval_zero_spectrum h0)
      have hgram : ∑ i, star (V i) * V i =
          blockDiagonal (∑ i, star (X i) * X i) 0 := by
        simp only [Fin.sum_univ_succ, V, Fin.cons_zero, Fin.cons_succ,
          interval_block_gram, star_zero, mul_zero, add_zero]
        rw [interval_block_sum, interval_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hV : ∑ i, star (V i) * V i ≤ 1 := by
        rw [hgram]
        have hone : blockDiagonal (1 : K →L[ℂ] K) 1 = 1 :=
          map_one (blockDiagonalHom (ℋ := K))
        rw [← hone]
        exact blockDiagonal_le_blockDiagonal hX zero_le_one
      have hcompress : ∑ i, star (V i) * P i * V i =
          blockDiagonal (∑ i, star (X i) * A i * X i) 0 := by
        simp only [Fin.sum_univ_succ, P, V, Fin.cons_zero, Fin.cons_succ,
          interval_block_compression, star_zero, mul_zero, add_zero]
        rw [interval_block_sum, interval_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hcfc (C D : K →L[ℂ] K) (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
          (hCs : spectrum ℝ C ⊆ I) (hDs : spectrum ℝ D ⊆ I) :
          cfcR f (blockDiagonal C D) = blockDiagonal (cfcR f C) (cfcR f D) :=
        cfcR_blockDiagonal f C D hC hD (hc.mono (Set.union_subset hCs hDs))
      have hright : ∑ i, star (V i) * cfcR f (P i) * V i =
          blockDiagonal (∑ i, star (X i) * cfcR f (A i) * X i) 0 := by
        simp only [Fin.sum_univ_succ, P, V, Fin.cons_zero, Fin.cons_succ]
        rw [hcfc _ _ (hA 0) (hA 1) (hAs 0) (hAs 1), interval_block_compression]
        simp_rw [hcfc _ _ (hA _) (by simp) (hAs _) (interval_zero_spectrum h0),
          interval_block_compression]
        simp only [star_zero, zero_mul, mul_zero, add_zero]
        rw [interval_block_sum, interval_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hsum := finite_compression_spectrum_subset hI h0 A X hA hAs hX
      have h := ih P V hP hPs hV
      rw [hcompress, hright,
        hcfc _ _ hsum.1 (by simp) hsum.2 (interval_zero_spectrum h0)] at h
      exact blockDiagonal_le_left h

/-- Finite block packing is independent of the proof of binary Jensen. -/
theorem jensenFinite_of_binary_interval {ι : Type v} [Fintype ι]
    {I : Set ℝ} {f : ℝ → ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    (hc : ContinuousOn f I) (hf0 : f 0 ≤ 0) (hb : IntervalBinaryConditionAll.{u} I f)
    (A X : ι → ℋ →L[ℂ] ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  classical
  let e := (Fintype.equivFin ι).symm
  have h := jensen_fin_of_binary_interval hI h0 hc hf0 (@hb) (Fintype.card ι)
    (fun i ↦ A (e i)) (fun i ↦ X (e i)) (fun i ↦ hA (e i)) (fun i ↦ hAs (e i))
    (by simpa only [e.sum_comp (fun i ↦ star (X i) * X i)] using hX)
  simpa only [e.sum_comp (fun i ↦ star (X i) * A i * X i),
    e.sum_comp (fun i ↦ star (X i) * cfcR f (A i) * X i)] using h

/-- General-interval finite contraction Jensen, with continuity explicit at this layer. -/
theorem jensenFinite_of_opConvexOnAll_continuous {ι : Type v} [Fintype ι]
    {I : Set ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    {f : ℝ → ℝ} (hf : OperatorConvexOnAll.{u} I f)
    (hc : ContinuousOn f I) (hf0 : f 0 ≤ 0)
    (A X : ι → ℋ →L[ℂ] ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  exact jensenFinite_of_binary_interval hI h0 hc hf0
    (jensenColumn_of_opConvexOnAll_continuous hI h0 (@hf) hc hf0) A X hA hAs hX

/-- Finite contractive Jensen on a general interval. Continuity is assumed only at the
endpoints of `I` that belong to `I`; interior continuity is derived from operator
convexity, and open intervals need no continuity assumption
(`jensenFinite_of_opConvexOnAll_of_isOpen`).
Endpoint continuity is an explicit hypothesis of this theorem. -/
theorem jensenFinite_of_opConvexOnAll_of_endpoints {ι : Type v} [Fintype ι]
    {I : Set ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    {f : ℝ → ℝ} (hf : OperatorConvexOnAll.{u} I f) (hf0 : f 0 ≤ 0)
    (he : ∀ x ∈ I \ interior I, ContinuousWithinAt f I x)
    (A X : ι → QuantumState.B ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  exact jensenFinite_of_opConvexOnAll_continuous hI h0 (@hf)
    (continuousOn_of_interior_and_endpoints
      (continuousOn_interior_of_operatorConvexOnAll (ℋ := ℋ) hI (@hf)) he)
    hf0 A X hA hAs hX

/-- Open intervals need no explicit continuity assumption. -/
theorem jensenFinite_of_opConvexOnAll_of_isOpen {ι : Type v} [Fintype ι]
    {I : Set ℝ} (hI : I.OrdConnected) (hopen : IsOpen I) (h0 : 0 ∈ I)
    {f : ℝ → ℝ} (hf : OperatorConvexOnAll.{u} I f) (hf0 : f 0 ≤ 0)
    (A X : ι → QuantumState.B ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  exact jensenFinite_of_opConvexOnAll_of_endpoints hI h0 (@hf) hf0
    (by simp [hopen.interior_eq]) A X hA hAs hX

end JensenOperatorInequality
