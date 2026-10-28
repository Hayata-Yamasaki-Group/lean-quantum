/-
Tensor-power dictionaries for typicality (Gour §8.2): the Hilbert tensor power of an operator
in any basis agrees with the coordinate `matrixTensorPower`, and in an eigenbasis the tensor
power of a density operator is the iid diagonal distribution of its eigenvalues.
-/

import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityFoundationDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesVonNeumann.GSLCore
import Mathlib.Data.Sum.Interval

namespace GourConditionalEntropy

section

open QuantumState GourConditionalEntropy
open Filter Topology
open scoped BigOperators TensorProduct

universe u

set_option autoImplicit false

end

section

open QuantumState GourConditionalEntropy
open Filter Topology
open scoped BigOperators TensorProduct

universe u

set_option autoImplicit false

theorem w42_spectral_probability :
  (∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : {X : L.{u} A // IsDensity.{u} X}),
  (∀ i : Fin (Module.finrank ℂ A), 0 ≤ OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) ∧
  ((∑ i : Fin (Module.finrank ℂ A), OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) = 1) ∧
  (∀ i : Fin (Module.finrank ℂ A), (w42EigenPMF.{u} ρ i).toReal =
    OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) ∧
  (vonNeumannEntropy.{u} ρ.1 = OPT.shannonBits.{0} (w42EigenPMF.{u} ρ))) := by
  intro A _ _ ρ
  have hnonneg : ∀ i, 0 ≤ OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i :=
    ρ.2.1.nonneg_eigenvalues rfl
  have hsum : ∑ i, OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i = 1 := by
    calc
      ∑ i, OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i = (Tr ρ.1).re :=
        (ρ.2.1.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm
      _ = 1 := by rw [ρ.2.2]; rfl
  have hpmf : ∀ i, (w42EigenPMF ρ i).toReal =
      OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i := by
    intro i
    exact ENNReal.toReal_ofReal (hnonneg i)
  refine ⟨hnonneg, hsum, hpmf, ?_⟩
  rw [(w38_vn_spectral_dictionary.{u}).1 ρ,
    OPT.shannonBits_eq_sum_neg_mul_logb]
  simp only [hpmf, neg_mul, Finset.sum_neg_distrib]

end

section

open QuantumState GourConditionalEntropy
open Filter Topology
open scoped BigOperators TensorProduct

universe u

set_option autoImplicit false

private theorem w42c03t_w42t_basis_succ {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (n : ℕ) (x : Fin (n + 1) → Fin (Module.finrank ℂ A)) :
    w42TensorBasis b (n + 1) x =
      b (x 0) ⊗ₜ[ℂ] w42TensorBasis b n (fun j => x j.succ) := by
  change ((b.tensorProduct (w42TensorBasis b n)).reindex _) x = _
  rw [OrthonormalBasis.reindex_apply]
  exact OrthonormalBasis.tensorProduct_apply _ _ _ _

private theorem w42c03t_w42t_entry_succ {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (X : L.{u} A) (n : ℕ) (x y : Fin (n + 1) → Fin (Module.finrank ℂ A)) :
    inner ℂ (w42TensorBasis b (n + 1) x)
      (w42OperatorPower X (n + 1) (w42TensorBasis b (n + 1) y)) =
      inner ℂ (b (x 0)) (X (b (y 0))) *
        inner ℂ (w42TensorBasis b n (fun j => x j.succ))
          (w42OperatorPower X n (w42TensorBasis b n (fun j => y j.succ))) := by
  rw [w42c03t_w42t_basis_succ, w42c03t_w42t_basis_succ]
  change inner ℂ (_ ⊗ₜ[ℂ] _) (TensorProduct.map X (w42OperatorPower X n) _) = _
  rw [TensorProduct.map_tmul, TensorProduct.inner_tmul]

private theorem w42c03t_w42t_entries {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (X : L.{u} A) (n : ℕ) (x y : Fin n → Fin (Module.finrank ℂ A)) :
    inner ℂ (w42TensorBasis b n x) (w42OperatorPower X n (w42TensorBasis b n y)) =
      ∏ j : Fin n, inner ℂ (b (x j)) (X (b (y j))) := by
  induction n with
  | zero =>
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    change inner ℂ (w42TensorBasis b 0 x) (w42TensorBasis b 0 x) = _
    simp
  | succ n ih =>
    rw [w42c03t_w42t_entry_succ, ih, Fin.prod_univ_succ]

private theorem w42c03t_w42t_matrix {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (X : L.{u} A) (n : ℕ) :
    LinearMap.toMatrix (w42TensorBasis b n).toBasis (w42TensorBasis b n).toBasis
        (w42OperatorPower X n) =
      QuantumChannel.matrixTensorPower (LinearMap.toMatrix b.toBasis b.toBasis X) n := by
  ext x y
  simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    QuantumChannel.matrixTensorPower] using w42c03t_w42t_entries b X n x y

private theorem w42c03t_w42t_range {A : Type u} [Qudit.{u} A] [Nontrivial A]
    {n : ℕ} (U : w42TensorSpace A n ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n → Fin (Module.finrank ℂ A)))
    (Y : L.{u} (w42TensorSpace A n)) :
    LinearMap.range (w42CoordinateOperator U Y) =
      (LinearMap.range Y).map U.toLinearEquiv.toLinearMap := by
  simp only [w42CoordinateOperator, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top]

theorem w42_tensor_coordinate_dictionary :
  (∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (X : L.{u} A) (n : ℕ),
  (∃ U : w42TensorSpace.{u} A n ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → Fin (Module.finrank ℂ A)),
    (∀ x : Fin n → Fin (Module.finrank ℂ A), U (w42TensorBasis.{u} b n x) = EuclideanSpace.single x
      1) ∧
    (∀ x y : Fin n → Fin (Module.finrank ℂ A),
      inner ℂ (w42TensorBasis.{u} b n x)
        (w42OperatorPower.{u} X n (w42TensorBasis.{u} b n y)) =
        ∏ j : Fin n, inner ℂ (b (x j)) (X (b (y j)))) ∧
    (Tr.{u} (w42OperatorPower.{u} X n) =
      Matrix.trace (QuantumChannel.matrixTensorPower.{0}
        (LinearMap.toMatrix b.toBasis b.toBasis X) n)) ∧
    (Tr.{0} (w42CoordinateOperator.{u} U (w42OperatorPower.{u} X n)) =
      Tr.{u} (w42OperatorPower.{u} X n)) ∧
    (LinearMap.range (w42CoordinateOperator.{u} U (w42OperatorPower.{u} X n)) =
      (LinearMap.range (w42OperatorPower.{u} X n)).map U.toLinearEquiv.toLinearMap) ∧
    (Module.finrank ℂ (LinearMap.range (w42CoordinateOperator.{u} U
      (w42OperatorPower.{u} X n))) =
      Module.finrank ℂ (LinearMap.range (w42OperatorPower.{u} X n)))) ∧
  (∀ x y : Fin (n + 1) → Fin (Module.finrank ℂ A),
    inner ℂ (w42TensorBasis.{u} b (n + 1) x)
      (w42OperatorPower.{u} X (n + 1) (w42TensorBasis.{u} b (n + 1) y)) =
      inner ℂ (b (x 0)) (X (b (y 0))) *
        inner ℂ (w42TensorBasis.{u} b n (fun j => x j.succ))
          (w42OperatorPower.{u} X n
            (w42TensorBasis.{u} b n (fun j => y j.succ)))) ∧
  (Module.finrank ℂ (w42TensorSpace.{u} A n) = (Module.finrank ℂ A) ^ n) ∧
  (w42OperatorPower.{u} X 0 = 1)) := by
  classical
  intro A _ _ b X n
  refine ⟨?_, w42c03t_w42t_entry_succ b X n, ?_, rfl⟩
  · let U := (w42TensorBasis b n).repr
    refine ⟨U, (w42TensorBasis b n).repr_self, w42c03t_w42t_entries b X n, ?_, ?_, ?_, ?_⟩
    · change LinearMap.trace ℂ _ (w42OperatorPower X n) = _
      rw [LinearMap.trace_eq_matrix_trace ℂ (w42TensorBasis b n).toBasis,
        w42c03t_w42t_matrix]
    · exact LinearMap.trace_conj' (w42OperatorPower X n) U.toLinearEquiv
    · exact w42c03t_w42t_range U (w42OperatorPower X n)
    · rw [w42c03t_w42t_range]
      exact U.toLinearEquiv.finrank_map_eq _
  · rw [Module.finrank_eq_card_basis (w42TensorBasis b n).toBasis]
    simp

end

section

open QuantumState GourConditionalEntropy
open Filter Topology
open scoped BigOperators TensorProduct

universe u

set_option autoImplicit false

private theorem w42c03_diagonal_range
    {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (p : PMF ι)
    (hX : ∀ i, X (b i) = ((p i).toReal : ℂ) • b i) :
    LinearMap.range X = Submodule.span ℂ (b '' {i | 0 < (p i).toReal}) := by
  classical
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [← b.sum_repr v, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, hX]
    by_cases hi : 0 < (p i).toReal
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, hi, rfl⟩))
    · have hz : (p i).toReal = 0 := le_antisymm (le_of_not_gt hi) ENNReal.toReal_nonneg
      simp [hz]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hn : ((p i).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hi)
    refine ⟨((p i).toReal : ℂ)⁻¹ • b i, ?_⟩
    rw [map_smul, hX, smul_smul, inv_mul_cancel₀ hn, one_smul]

private theorem w42c03_diagonal_rank
    {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (p : PMF ι)
    (hX : ∀ i, X (b i) = ((p i).toReal : ℂ) • b i) :
    Module.finrank ℂ (LinearMap.range X) = Fintype.card {i // 0 < (p i).toReal} := by
  classical
  rw [w42c03_diagonal_range b X p hX]
  have hs : b '' {i | 0 < (p i).toReal} =
      Set.range (fun i : {i // 0 < (p i).toReal} => b i) := by
    ext v
    simp
  rw [hs]
  exact finrank_span_eq_card (b.toBasis.linearIndependent.comp _ Subtype.val_injective)

private theorem w42c03_iid_positive_iff {ι : Type} [Fintype ι] (p : PMF ι)
    (n : ℕ) (x : Fin n → ι) :
    0 < (OPT.PMF.iid n p x).toReal ↔ ∀ j, 0 < (p (x j)).toReal := by
  constructor
  · intro hx j
    have hn : ∏ k : Fin n, (p (x k)).toReal ≠ 0 := by
      simpa only [OPT.PMF.iid_apply_toReal, OPT.PMF.realMass] using ne_of_gt hx
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Finset.prod_ne_zero_iff.mp hn j (Finset.mem_univ j)))
  · intro hx
    rw [OPT.PMF.iid_apply_toReal]
    exact Finset.prod_pos (fun j _ => hx j)

private theorem w42c03_iid_positive_card {ι : Type} [Fintype ι] (p : PMF ι) (n : ℕ) :
    Fintype.card {x : Fin n → ι // 0 < (OPT.PMF.iid n p x).toReal} =
      Fintype.card {i // 0 < (p i).toReal} ^ n := by
  classical
  let e := (Equiv.subtypeEquivRight (w42c03_iid_positive_iff p n)).trans
    (Equiv.subtypePiEquivPi (p := fun (_ : Fin n) i => 0 < (p i).toReal))
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_congr e

private theorem w42c03_spectral_apply
    {A : Type u} [Qudit A] [Nontrivial A] (ρ : {X : L A // IsDensity X})
    (hp : ∀ i, (w42EigenPMF ρ i).toReal =
      OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i)
    (i : Fin (Module.finrank ℂ A)) :
    ρ.1 (w42EigenBasis ρ i) = ((w42EigenPMF ρ i).toReal : ℂ) • w42EigenBasis ρ i := by
  rw [hp]
  exact ρ.2.1.isSymmetric.apply_eigenvectorBasis rfl i

private theorem w42c03_tensor_spectral_apply
    {A : Type u} [Qudit A] [Nontrivial A] (ρ : {X : L A // IsDensity X}) (n : ℕ)
    (hp : ∀ i, (w42EigenPMF ρ i).toReal =
      OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i)
    (he : ∀ x y : Fin n → Fin (Module.finrank ℂ A),
      inner ℂ (w42TensorBasis (w42EigenBasis ρ) n x)
        (w42OperatorPower ρ.1 n (w42TensorBasis (w42EigenBasis ρ) n y)) =
        ∏ j : Fin n, inner ℂ (w42EigenBasis ρ (x j)) (ρ.1 (w42EigenBasis ρ (y j))))
    (x : Fin n → Fin (Module.finrank ℂ A)) :
    w42DensityPower ρ n (w42TensorBasis (w42EigenBasis ρ) n x) =
      ((OPT.PMF.iid n (w42EigenPMF ρ) x).toReal : ℂ) •
        w42TensorBasis (w42EigenBasis ρ) n x := by
  classical
  let b := w42TensorBasis (w42EigenBasis ρ) n
  apply b.repr.injective
  apply PiLp.ext
  intro y
  simp only [b.repr_apply_apply, inner_smul_right]
  change inner ℂ (b y) (w42DensityPower ρ n (b x)) =
    ((OPT.PMF.iid n (w42EigenPMF ρ) x).toReal : ℂ) * inner ℂ (b y) (b x)
  rw [b.inner_eq_ite, he]
  simp_rw [w42c03_spectral_apply ρ hp, inner_smul_right, (w42EigenBasis ρ).inner_eq_ite,
    mul_ite, mul_one, mul_zero]
  rw [Fintype.prod_ite_zero]
  simp only [← funext_iff]
  congr 1
  rw [OPT.PMF.iid_apply_toReal, Complex.ofReal_prod]
  rfl

private theorem w42c03_diagonal_isDensity
    {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (p : PMF ι)
    (hX : ∀ i, X (b i) = ((p i).toReal : ℂ) • b i) : IsDensity X := by
  have h : X = PMF.diagonalDensity b p := b.toBasis.ext fun i => by
    exact (hX i).trans (PMF.diagonalDensity_apply b p i).symm
  rw [h]
  exact PMF.diagonalDensity_isDensity b p

theorem w42_tensor_spectral_dictionary :
  ((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : {X : L.{u} A // IsDensity.{u} X}) (n : ℕ),
  (∀ x : Fin n → Fin (Module.finrank ℂ A),
    w42DensityPower.{u} ρ n (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n x) =
      ((OPT.PMF.iid.{0} n (w42EigenPMF.{u} ρ) x).toReal : ℂ) •
        w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n x) ∧
  (IsDensity.{u} (w42DensityPower.{u} ρ n)) ∧
  (Module.finrank ℂ (w42TensorSpace.{u} A n) = (Module.finrank ℂ A) ^ n) ∧
  (w42DensityPower.{u} ρ 0 = 1))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : {X : L.{u} A // IsDensity.{u} X}),
  (∀ i : Fin (Module.finrank ℂ A), 0 ≤ OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) ∧
  ((∑ i : Fin (Module.finrank ℂ A), OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) = 1) ∧
  (∀ i : Fin (Module.finrank ℂ A), (w42EigenPMF.{u} ρ i).toReal =
    OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2 i) ∧
  (vonNeumannEntropy.{u} ρ.1 = OPT.shannonBits.{0} (w42EigenPMF.{u} ρ)))) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : {X : L.{u} A // IsDensity.{u} X}) (n : ℕ),
  (LinearMap.range (w42DensityPower.{u} ρ n) =
    Submodule.span ℂ
      ((w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n) ''
        (w41Event.{0} (fun x : Fin n → Fin (Module.finrank ℂ A) =>
          0 < (OPT.PMF.iid.{0} n (w42EigenPMF.{u} ρ) x).toReal) :
          Set (Fin n → Fin (Module.finrank ℂ A))))) ∧
  (Module.finrank ℂ (LinearMap.range (w42DensityPower.{u} ρ n)) =
    (Module.finrank ℂ (LinearMap.range ρ.1)) ^ n)) := by
  classical
  have hd : ∀ {A : Type u} [Qudit A] [Nontrivial A]
      (ρ : {X : L A // IsDensity X}) (n : ℕ)
      (x : Fin n → Fin (Module.finrank ℂ A)),
      w42DensityPower ρ n (w42TensorBasis (w42EigenBasis ρ) n x) =
        ((OPT.PMF.iid n (w42EigenPMF ρ) x).toReal : ℂ) •
          w42TensorBasis (w42EigenBasis ρ) n x := by
    intro A _ _ ρ n
    obtain ⟨U, _, he, _⟩ := (GourConditionalEntropy.w42_tensor_coordinate_dictionary.{u}
      (w42EigenBasis ρ) ρ.1 n).1
    exact w42c03_tensor_spectral_apply ρ n (GourConditionalEntropy.w42_spectral_probability.{u}
      ρ).2.2.1 he
  refine ⟨?_, GourConditionalEntropy.w42_spectral_probability.{u}, ?_⟩
  · intro A _ _ ρ n
    exact ⟨hd ρ n,
      w42c03_diagonal_isDensity (w42TensorBasis (w42EigenBasis ρ) n)
        (w42DensityPower ρ n) (OPT.PMF.iid n (w42EigenPMF ρ)) (hd ρ n),
      (GourConditionalEntropy.w42_tensor_coordinate_dictionary.{u} (w42EigenBasis ρ) ρ.1 n).2.2⟩
  · intro A _ _ ρ n
    constructor
    · simpa [w41Event] using
        w42c03_diagonal_range (w42TensorBasis (w42EigenBasis ρ) n)
          (w42DensityPower ρ n) (OPT.PMF.iid n (w42EigenPMF ρ)) (hd ρ n)
    · rw [w42c03_diagonal_rank (w42TensorBasis (w42EigenBasis ρ) n)
        (w42DensityPower ρ n) (OPT.PMF.iid n (w42EigenPMF ρ)) (hd ρ n),
        w42c03_iid_positive_card,
        w42c03_diagonal_rank (w42EigenBasis ρ) ρ.1 (w42EigenPMF ρ)
          (w42c03_spectral_apply ρ (GourConditionalEntropy.w42_spectral_probability.{u} ρ).2.2.1)]

end

end GourConditionalEntropy
