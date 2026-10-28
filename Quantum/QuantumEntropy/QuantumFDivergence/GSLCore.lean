import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.QuantumEntropy.PetzRenyiSpectralReduction.GSLCore
import Quantum.QuantumEntropy.Gour.PetzQuantumRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.Reduction
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

/-!
# Spectral probability distributions of a pair of density operators

The two finite spectral probability distributions associated with a pair of density operators
(`quantumSpectralP`, `quantumSpectralQ`).  At order one, the KL divergence of these
distributions equals the Umegaki relative entropy, which gives the order-one value of the Petz
quantum Rényi divergence (`petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN`).
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open Module.End Polynomial
open Filter Set
open scoped BigOperators ENNReal NNReal TensorProduct Topology

universe u

/--
**Source.** Gilad Gour, *Resources of the Quantum World*, Eq. (5.68)
(printed page 245).

For density operators \(\rho,\sigma\) on a finite-dimensional complex Hilbert space other than
\(\{0\}\), let \(p_x,q_y\) be their respective eigenvalues and \((a_x)_x,(b_y)_y\) corresponding
eigenbases. The finite probability distribution
\(\widetilde p\in\operatorname{Prob}(m^2)\) is defined by
\[
  \widetilde p_{xy}:=p_x|\langle a_x,b_y\rangle|^2,
\]
where \(m\) is the dimension of the Hilbert space.

**Difference from the source.** The index set \([m]\times[m]\) is represented as the product of
two finite types corresponding to the finite dimension of the Hilbert space.

**Finite-dimensional dependence.** Finite dimensionality is used where the finite probability
distribution on the product is constructed from the two finite eigenbases.
-/
noncomputable abbrev quantumSpectralP
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    PMF (Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :=
  petzSpectralP rho sigma hrho hsigma

/--
**Source.** Gilad Gour, *Resources of the Quantum World*, Eq. (5.68)
(printed page 245).

For density operators \(\rho,\sigma\) on a finite-dimensional complex Hilbert space other than
\(\{0\}\), let \(p_x,q_y\) be their respective eigenvalues and \((a_x)_x,(b_y)_y\) corresponding
eigenbases. The finite probability distribution
\(\widetilde q\in\operatorname{Prob}(m^2)\) is defined by
\[
  \widetilde q_{xy}:=q_y|\langle a_x,b_y\rangle|^2,
\]
where \(m\) is the dimension of the Hilbert space.

**Difference from the source.** The index set \([m]\times[m]\) is represented as the product of
two finite types corresponding to the finite dimension of the Hilbert space.

**Finite-dimensional dependence.** Finite dimensionality is used where the finite probability
distribution on the product is constructed from the two finite eigenbases.
-/
noncomputable abbrev quantumSpectralQ
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    PMF (Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :=
  petzSpectralQ rho sigma hrho hsigma

private noncomputable def qfDensityEigenbasis
    {ℋ : Type u} [Qudit ℋ] (A : QuantumState.L ℋ) (hA : IsDensity A) :
    OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ :=
  hA.1.isSymmetric.eigenvectorBasis rfl

private noncomputable def qfDensityEigenvalue
    {ℋ : Type u} [Qudit ℋ] (A : QuantumState.L ℋ) (hA : IsDensity A) :
    Fin (Module.finrank ℂ ℋ) → ℝ :=
  hA.1.isSymmetric.eigenvalues rfl

private noncomputable def qfSpectralOverlap
    {ℋ : Type u} [Qudit ℋ] (rho sigma : QuantumState.L ℋ)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i j : Fin (Module.finrank ℂ ℋ)) : ℝ :=
  ‖inner ℂ (qfDensityEigenbasis rho hrho i)
    (qfDensityEigenbasis sigma hsigma j)‖ ^ 2

private theorem qfP_apply
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : QuantumState.L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    quantumSpectralP rho sigma hrho hsigma ij = ENNReal.ofReal
      (qfDensityEigenvalue rho hrho ij.1 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) := by
  rw [quantumSpectralP, petzSpectralP]
  rfl

private theorem qfQ_apply
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : QuantumState.L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ)) :
    quantumSpectralQ rho sigma hrho hsigma ij = ENNReal.ofReal
      (qfDensityEigenvalue sigma hsigma ij.2 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2) := by
  rw [quantumSpectralQ, petzSpectralQ]
  rfl

private theorem qfDensityEigenvalue_nonneg
    {ℋ : Type u} [Qudit ℋ] (A : QuantumState.L ℋ) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ ℋ)) :
    0 ≤ qfDensityEigenvalue A hA i :=
  hA.1.nonneg_eigenvalues rfl i

private theorem qfDensity_apply_eigenbasis
    {ℋ : Type u} [Qudit ℋ] (A : QuantumState.L ℋ) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ ℋ)) :
    A (qfDensityEigenbasis A hA i) =
      ((qfDensityEigenvalue A hA i : ℝ) : ℂ) • qfDensityEigenbasis A hA i := by
  simp [qfDensityEigenbasis, qfDensityEigenvalue]

private noncomputable def qfEigenPMass
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H)) : NNReal :=
  ⟨qfDensityEigenvalue rho hrho ij.1 *
    qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2,
    mul_nonneg (qfDensityEigenvalue_nonneg rho hrho ij.1) (sq_nonneg _)⟩

private noncomputable def qfEigenQMass
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H)) : NNReal :=
  ⟨qfDensityEigenvalue sigma hsigma ij.2 *
    qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2,
    mul_nonneg (qfDensityEigenvalue_nonneg sigma hsigma ij.2) (sq_nonneg _)⟩

/-! ## Nonnegative spectral masses -/

private noncomputable def qfSpectralOverlapNN
    {H : Type u} [Qudit H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i j : Fin (Module.finrank ℂ H)) : NNReal :=
  ⟨qfSpectralOverlap rho sigma hrho hsigma i j, sq_nonneg _⟩

private noncomputable def qfDensityEigenvalueNN
    {H : Type u} [Qudit H]
    (A : QuantumState.L H) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ H)) : NNReal :=
  ⟨qfDensityEigenvalue A hA i, qfDensityEigenvalue_nonneg A hA i⟩

private theorem qf_closedPerspective_eigenMass_eq
    {H : Type u} [Qudit H] [Nontrivial H]
    (g : FDivGenerator)
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H)) :
    closedPerspective g (qfEigenPMass rho sigma hrho hsigma ij)
        (qfEigenQMass rho sigma hrho hsigma ij) =
      ((qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 : ℝ) : EReal) *
        closedPerspective g
          (qfDensityEigenvalue rho hrho ij.1).toNNReal
          (qfDensityEigenvalue sigma hsigma ij.2).toNNReal := by
  let w := qfSpectralOverlapNN rho sigma hrho hsigma ij.1 ij.2
  let r := qfDensityEigenvalueNN rho hrho ij.1
  let s := qfDensityEigenvalueNN sigma hsigma ij.2
  have hp : qfEigenPMass rho sigma hrho hsigma ij = w * r := by
    apply NNReal.eq
    simp only [qfEigenPMass, w, r, qfSpectralOverlapNN,
      qfDensityEigenvalueNN, NNReal.coe_mul, NNReal.coe_mk]
    ring
  have hq : qfEigenQMass rho sigma hrho hsigma ij = w * s := by
    apply NNReal.eq
    simp only [qfEigenQMass, w, s, qfSpectralOverlapNN,
      qfDensityEigenvalueNN, NNReal.coe_mul, NNReal.coe_mk]
    ring
  rw [hp, hq, closedPerspective_smul]
  simp only [w, r, s, qfSpectralOverlapNN, qfDensityEigenvalueNN,
    NNReal.coe_mk]
  rw [Real.toNNReal_of_nonneg (qfDensityEigenvalue_nonneg rho hrho ij.1),
    Real.toNNReal_of_nonneg (qfDensityEigenvalue_nonneg sigma hsigma ij.2)]

/-! ## Order one: KL divergence of the spectral distributions -/

private theorem q1EReal_coe_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = (((∑ i ∈ s, f i : ℝ)) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      rw [ih, ← EReal.coe_add]

theorem quantumFMapDensity
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : QuantumChannel.CPTP H K)
    (rho : QuantumState.L H) (hrho : IsDensity rho) :
    IsDensity (E.toFun rho) := by
  constructor
  · exact (LinearMap.nonneg_iff_isPositive _).mp
      (map_nonneg E.toCompletelyPositiveMap
        ((LinearMap.nonneg_iff_isPositive rho).mpr hrho.1))
  · rw [← E.trace_map rho, hrho.2]

noncomputable def petzRenyiOrderOne : PetzRenyiOrder :=
  ⟨1, by norm_num⟩

/-- The eigenbasis used by the spectral form of the Petz divergence. -/
noncomputable abbrev petzRenyiSpectralEigenbasis
    {H : Type u} [Qudit H] (A : QuantumState.L H) (hA : IsDensity A) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  qfDensityEigenbasis A hA

/-- The eigenvalues used by the spectral form of the Petz divergence. -/
noncomputable abbrev petzRenyiSpectralEigenvalue
    {H : Type u} [Qudit H] (A : QuantumState.L H) (hA : IsDensity A) :
    Fin (Module.finrank ℂ H) → ℝ :=
  qfDensityEigenvalue A hA

private theorem q9ClassicalFDivSum_kl_eq_top_of_not_support_subset
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (h : ¬p.support ⊆ q.support) :
    classicalFDivSum klFDivGenerator p q = ⊤ := by
  classical
  obtain ⟨i, hpi, hqi⟩ := Set.not_subset.mp h
  have hp : p i ≠ 0 := (p.mem_support_iff i).1 hpi
  have hq : q i = 0 := (q.apply_eq_zero_iff i).2 hqi
  have hpnn : (p i).toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hp, p.apply_ne_top i⟩
  have hterm :
      closedPerspective klFDivGenerator (p i).toNNReal (q i).toNNReal = ⊤ := by
    rw [show (q i).toNNReal = 0 by simp [hq],
      closedPerspective_zero_right _ _ hpnn]
    exact EReal.coe_mul_top_of_pos (by positivity)
  unfold classicalFDivSum
  rw [Finset.sum_eq_add_sum_diff_singleton i _ (by simp), hterm]
  apply EReal.top_add_of_ne_bot
  apply ne_of_gt
  apply WithBot.sum_lt_bot
  intro j _
  exact closedPerspective_ne_bot klFDivGenerator
    (p j).toNNReal (q j).toNNReal

private theorem q9SpectralOverlap_sum_right
    {H : Type u} [Qudit H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i : Fin (Module.finrank ℂ H)) :
    ∑ j, qfSpectralOverlap rho sigma hrho hsigma i j = 1 := by
  change (∑ j, ‖inner ℂ (qfDensityEigenbasis rho hrho i)
    (qfDensityEigenbasis sigma hsigma j)‖ ^ 2) = 1
  rw [(qfDensityEigenbasis sigma hsigma).sum_sq_norm_inner_left]
  rw [(qfDensityEigenbasis rho hrho).norm_eq_one]
  norm_num

private theorem q9Log_apply_density_eigenbasis
    {H : Type u} [Qudit H] [Nontrivial H]
    (A : QuantumState.L H) (hA : IsDensity A)
    (i : Fin (Module.finrank ℂ H)) :
    CFC.log A (qfDensityEigenbasis A hA i) =
      ((Real.log (qfDensityEigenvalue A hA i) : ℝ) : ℂ) •
        qfDensityEigenbasis A hA i := by
  exact cfc_real_apply_eigenvector_lm
    (IsSelfAdjoint.of_nonneg ((LinearMap.nonneg_iff_isPositive A).mpr hA.1))
    Real.log (qfDensity_apply_eigenbasis A hA i)
    (mem_spectrum_real_of_eigenvector_lm
      ((qfDensityEigenbasis A hA).orthonormal.ne_zero i)
      (qfDensity_apply_eigenbasis A hA i))

private theorem q9Trace_mul_log_self_eq_sum
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho : QuantumState.L H) (hrho : IsDensity rho) :
    (Tr (rho * CFC.log rho)).re =
      ∑ i, qfDensityEigenvalue rho hrho i *
        Real.log (qfDensityEigenvalue rho hrho i) := by
  let b := qfDensityEigenbasis rho hrho
  rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.log rho) b,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, q9Log_apply_density_eigenbasis,
    map_smul, qfDensity_apply_eigenbasis, smul_smul, inner_smul_right]
  simp [b]
  ring

private theorem q9Inner_log_sigma_eq_sum
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (i : Fin (Module.finrank ℂ H)) :
    inner ℂ (qfDensityEigenbasis rho hrho i)
        (CFC.log sigma (qfDensityEigenbasis rho hrho i)) =
      ∑ j, ((Real.log (qfDensityEigenvalue sigma hsigma j) *
        qfSpectralOverlap rho sigma hrho hsigma i j : ℝ) : ℂ) := by
  let brho := qfDensityEigenbasis rho hrho
  let bsigma := qfDensityEigenbasis sigma hsigma
  calc
    inner ℂ (brho i) (CFC.log sigma (brho i)) =
        inner ℂ (brho i)
          (CFC.log sigma (∑ j, inner ℂ (bsigma j) (brho i) • bsigma j)) := by
      rw [bsigma.sum_repr']
    _ = ∑ j, inner ℂ (brho i)
        (CFC.log sigma (inner ℂ (bsigma j) (brho i) • bsigma j)) := by
      rw [map_sum, inner_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, q9Log_apply_density_eigenbasis, smul_smul,
        inner_smul_right]
      rw [show inner ℂ (bsigma j) (brho i) =
          starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) from
        (inner_conj_symm (bsigma j) (brho i)).symm]
      change starRingEnd ℂ (inner ℂ (brho i) (bsigma j)) *
          ((Real.log (qfDensityEigenvalue sigma hsigma j) : ℝ) : ℂ) *
            inner ℂ (brho i) (bsigma j) =
        ((Real.log (qfDensityEigenvalue sigma hsigma j) *
          ‖inner ℂ (brho i) (bsigma j)‖ ^ 2 : ℝ) : ℂ)
      rw [← Complex.normSq_eq_norm_sq, Complex.ofReal_mul,
        Complex.normSq_eq_conj_mul_self]
      ring

private theorem q9Trace_mul_log_cross_eq_sum
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (Tr (rho * CFC.log sigma)).re =
      ∑ i, ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          Real.log (qfDensityEigenvalue sigma hsigma j) := by
  let brho := qfDensityEigenbasis rho hrho
  have hrhoSym : rho.IsSymmetric := hrho.1.isSymmetric
  rw [LinearMap.trace_eq_sum_inner (T := rho * CFC.log sigma) brho,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply]
  rw [show inner ℂ (brho i) (rho (CFC.log sigma (brho i))) =
      inner ℂ (rho (brho i)) (CFC.log sigma (brho i)) from
    (hrhoSym (brho i) (CFC.log sigma (brho i))).symm]
  rw [qfDensity_apply_eigenbasis, inner_smul_left, Complex.conj_ofReal,
    q9Inner_log_sigma_eq_sum rho sigma hrho hsigma i,
    Finset.mul_sum, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The self trace--logarithm term is its spectral eigenvalue sum. -/
theorem petzRenyiTraceMulLogSelf_eq_spectralSum
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho : QuantumState.L H) (hrho : IsDensity rho) :
    (Tr (rho * CFC.log rho)).re =
      ∑ i, petzRenyiSpectralEigenvalue rho hrho i *
        Real.log (petzRenyiSpectralEigenvalue rho hrho i) :=
  q9Trace_mul_log_self_eq_sum rho hrho

private theorem q9ClosedPerspective_kl_spectral_term
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupport : (quantumSpectralP rho sigma hrho hsigma).support ⊆
      (quantumSpectralQ rho sigma hrho hsigma).support)
    (ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H)) :
    closedPerspective klFDivGenerator
        (qfEigenPMass rho sigma hrho hsigma ij)
        (qfEigenQMass rho sigma hrho hsigma ij) =
      ((qfDensityEigenvalue rho hrho ij.1 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 *
          (Real.log (qfDensityEigenvalue rho hrho ij.1) -
            Real.log (qfDensityEigenvalue sigma hsigma ij.2)) : ℝ) : EReal) := by
  rw [qf_closedPerspective_eigenMass_eq]
  let r := qfDensityEigenvalue rho hrho ij.1
  let s := qfDensityEigenvalue sigma hsigma ij.2
  let w := qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2
  have hr0 : 0 ≤ r := qfDensityEigenvalue_nonneg rho hrho ij.1
  have hs0 : 0 ≤ s := qfDensityEigenvalue_nonneg sigma hsigma ij.2
  have hw0 : 0 ≤ w := sq_nonneg _
  by_cases hw : w = 0
  · simp [w, hw]
  have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw)
  by_cases hr : r = 0
  · have hr' : qfDensityEigenvalue rho hrho ij.1 = 0 := by
      simpa only [r] using hr
    simp [hr', closedPerspective, klFDivGenerator]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hp : quantumSpectralP rho sigma hrho hsigma ij ≠ 0 := by
    rw [qfP_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hrpos hwpos
  have hq : quantumSpectralQ rho sigma hrho hsigma ij ≠ 0 :=
    (PMF.mem_support_iff _ _).1
      (hsupport ((PMF.mem_support_iff _ _).2 hp))
  have hswpos : 0 < s * w := by
    rw [qfQ_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hq
    exact hq
  have hspos : 0 < s := pos_of_mul_pos_left hswpos hw0
  have hrnn : r.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hrpos)
  have hsnn : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hspos)
  rw [closedPerspective_of_ne_zero _ _ _ hrnn hsnn]
  simp only [klFDivGenerator, klFDivFunction]
  rw [Real.toNNReal_of_nonneg hr0, Real.toNNReal_of_nonneg hs0]
  rw [← EReal.coe_mul]
  norm_cast
  simp only [NNReal.coe_div, NNReal.coe_mk]
  rw [Real.log_div hr hspos.ne']
  field_simp [hspos.ne']
  ring

private theorem q9DoubleSum_log_r_eq
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    ∑ i, ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          Real.log (qfDensityEigenvalue rho hrho i) =
      ∑ i, qfDensityEigenvalue rho hrho i *
        Real.log (qfDensityEigenvalue rho hrho i) := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          Real.log (qfDensityEigenvalue rho hrho i) =
      ∑ j, (qfDensityEigenvalue rho hrho i *
        Real.log (qfDensityEigenvalue rho hrho i)) *
          qfSpectralOverlap rho sigma hrho hsigma i j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = (qfDensityEigenvalue rho hrho i *
        Real.log (qfDensityEigenvalue rho hrho i)) *
          ∑ j, qfSpectralOverlap rho sigma hrho hsigma i j := by
        rw [Finset.mul_sum]
    _ = _ := by
      rw [q9SpectralOverlap_sum_right rho sigma hrho hsigma i]
      ring

private theorem q9SpectralDoubleSum_eq_umegakiNorm
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (∑ ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H),
      qfDensityEigenvalue rho hrho ij.1 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 *
          (Real.log (qfDensityEigenvalue rho hrho ij.1) -
            Real.log (qfDensityEigenvalue sigma hsigma ij.2))) =
      umegakiNorm rho sigma := by
  have hnum :
      (Tr (rho * (CFC.log rho - CFC.log sigma))).re =
        (Tr (rho * CFC.log rho)).re - (Tr (rho * CFC.log sigma)).re := by
    rw [mul_sub, map_sub, Complex.sub_re]
  unfold umegakiNorm
  rw [hnum, hrho.2]
  simp only [Complex.one_re, div_one]
  rw [q9Trace_mul_log_self_eq_sum rho hrho,
    q9Trace_mul_log_cross_eq_sum rho sigma hrho hsigma,
    Fintype.sum_prod_type]
  calc
    ∑ i, ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          (Real.log (qfDensityEigenvalue rho hrho i) -
            Real.log (qfDensityEigenvalue sigma hsigma j)) =
      (∑ i, ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          Real.log (qfDensityEigenvalue rho hrho i)) -
      ∑ i, ∑ j, qfDensityEigenvalue rho hrho i *
        qfSpectralOverlap rho sigma hrho hsigma i j *
          Real.log (qfDensityEigenvalue sigma hsigma j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
      rw [q9DoubleSum_log_r_eq rho sigma hrho hsigma]

private theorem q9ClassicalFDivSum_kl_eq_umegakiNorm_of_support_subset
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupport : (quantumSpectralP rho sigma hrho hsigma).support ⊆
      (quantumSpectralQ rho sigma hrho hsigma).support) :
    classicalFDivSum klFDivGenerator
        (quantumSpectralP rho sigma hrho hsigma)
        (quantumSpectralQ rho sigma hrho hsigma) =
      ((umegakiNorm rho sigma : ℝ) : EReal) := by
  classical
  unfold classicalFDivSum
  calc
    ∑ ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H),
      closedPerspective klFDivGenerator
        ((quantumSpectralP rho sigma hrho hsigma) ij).toNNReal
        ((quantumSpectralQ rho sigma hrho hsigma) ij).toNNReal =
      ∑ ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H),
        closedPerspective klFDivGenerator
        (qfEigenPMass rho sigma hrho hsigma ij)
        (qfEigenQMass rho sigma hrho hsigma ij) := by
        apply Finset.sum_congr rfl
        intro ij _
        rw [qfP_apply, qfQ_apply]
        simp only [ENNReal.ofReal, ENNReal.toNNReal_coe]
        rw [Real.toNNReal_of_nonneg (show 0 ≤
            qfDensityEigenvalue rho hrho ij.1 *
              qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 from
          mul_nonneg (qfDensityEigenvalue_nonneg rho hrho ij.1) (sq_nonneg _)),
          Real.toNNReal_of_nonneg (show 0 ≤
              qfDensityEigenvalue sigma hsigma ij.2 *
                qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 from
            mul_nonneg (qfDensityEigenvalue_nonneg sigma hsigma ij.2) (sq_nonneg _))]
        rfl
    _ = ∑ ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H),
      ((qfDensityEigenvalue rho hrho ij.1 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 *
          (Real.log (qfDensityEigenvalue rho hrho ij.1) -
            Real.log (qfDensityEigenvalue sigma hsigma ij.2)) : ℝ) : EReal) := by
        apply Finset.sum_congr rfl
        intro ij _
        exact q9ClosedPerspective_kl_spectral_term
          rho sigma hrho hsigma hsupport ij
    _ = ((∑ ij : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ H),
      qfDensityEigenvalue rho hrho ij.1 *
        qfSpectralOverlap rho sigma hrho hsigma ij.1 ij.2 *
          (Real.log (qfDensityEigenvalue rho hrho ij.1) -
            Real.log (qfDensityEigenvalue sigma hsigma ij.2)) : ℝ) : EReal) := by
        exact q1EReal_coe_finset_sum Finset.univ _
    _ = ((umegakiNorm rho sigma : ℝ) : EReal) := by
      exact congrArg (fun x : ℝ => (x : EReal))
        (q9SpectralDoubleSum_eq_umegakiNorm rho sigma hrho hsigma)

private theorem q9ClassicalKLSpectral_eq_umegakiRelEntropyNN
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    ((classicalRelEntropyPMF
        (quantumSpectralP rho sigma hrho hsigma)
        (quantumSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) =
      umegakiRelEntropyNN rho sigma := by
  let p := quantumSpectralP rho sigma hrho hsigma
  let q := quantumSpectralQ rho sigma hrho hsigma
  by_cases hsupp : suppLE rho sigma
  · have hsupport : p.support ⊆ q.support :=
      (petzSpectral_support_subset_iff_suppLE rho sigma hrho hsigma).2 hsupp
    have hsum := q9ClassicalFDivSum_kl_eq_umegakiNorm_of_support_subset
      rho sigma hrho hsigma hsupport
    have hnonneg := classicalFDivSum_nonnegative klFDivGenerator p q
    rw [hsum] at hnonneg
    have hU : 0 ≤ umegakiNorm rho sigma := EReal.coe_nonneg.mp hnonneg
    have hkl : classicalRelEntropyPMF p q = ENNReal.ofReal (umegakiNorm rho sigma) := by
      rw [← classicalFDivPMF_kl]
      unfold classicalFDivPMF
      rw [hsum]
      rfl
    rw [show classicalRelEntropyPMF
        (quantumSpectralP rho sigma hrho hsigma)
        (quantumSpectralQ rho sigma hrho hsigma) =
          classicalRelEntropyPMF p q from rfl, hkl]
    unfold umegakiRelEntropyNN
    simp [hsupp, EReal.coe_ennreal_ofReal, max_eq_left hU]
  · have hnotsupport : ¬p.support ⊆ q.support := by
      intro hsupport
      exact hsupp
        ((petzSpectral_support_subset_iff_suppLE rho sigma hrho hsigma).1 hsupport)
    have hsum := q9ClassicalFDivSum_kl_eq_top_of_not_support_subset p q hnotsupport
    have hkl : classicalRelEntropyPMF p q = ⊤ := by
      rw [← classicalFDivPMF_kl]
      unfold classicalFDivPMF
      rw [hsum]
      rfl
    rw [show classicalRelEntropyPMF
        (quantumSpectralP rho sigma hrho hsigma)
        (quantumSpectralQ rho sigma hrho hsigma) =
          classicalRelEntropyPMF p q from rfl, hkl]
    unfold umegakiRelEntropyNN
    simp [hsupp]

theorem petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumState.L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzQuantumRenyiDivergence petzRenyiOrderOne rho sigma hrho hsigma =
      (((1 / Real.log 2 : ℝ) : EReal) * umegakiRelEntropyNN rho sigma) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hendpoint :=
    (petzRenyiEndpointValues_eq_classicalSpectral rho sigma hrho hsigma).2
  have hnatural := q9ClassicalKLSpectral_eq_umegakiRelEntropyNN
    rho sigma hrho hsigma
  have hscale :
      ((((ENNReal.ofReal (Real.log 2))⁻¹ : ℝ≥0∞) : EReal)) =
        ((1 / Real.log 2 : ℝ) : EReal) := by
    rw [← ENNReal.ofReal_inv_of_pos hlogTwo, EReal.coe_ennreal_ofReal]
    rw [max_eq_left (inv_nonneg.mpr hlogTwo.le)]
    rw [one_div]
  rw [petzQuantumRenyiDivergence]
  simp only [petzRenyiOrderOne, Subtype.coe_mk, one_ne_zero,
    ↓reduceDIte, hendpoint]
  unfold classicalKLDivergenceBitsPMF
  rw [div_eq_mul_inv, EReal.coe_ennreal_mul]
  rw [hnatural, hscale]
  exact mul_comm _ _

end OPT
