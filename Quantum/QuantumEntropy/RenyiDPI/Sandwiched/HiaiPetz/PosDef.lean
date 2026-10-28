import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.TensorQuasi
import Quantum.QuantumMechanics.Channel.Stinespring
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.Haar
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem sandwichedQuasi_le_cptp_pd_hiaiPetz :
∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (E : CPTP H K) {α : ℝ} {ρ σ : L H},
  1 < α → ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
  E.toFun ρ ∈ pdSetLM (ℋ := K) → E.toFun σ ∈ pdSetLM (ℋ := K) →
  (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≤
    (sandwichedQuasi α ρ σ).re := by
  intro H K _ _ _ _ E α ρ σ hα hρ hσ hEρ hEσ
  obtain ⟨F, hF, hF_nontriv, V, hV_iso, hV_eq⟩ :=
    E.exists_isometric_stinespring_dilation
  letI := hF
  letI := hF_nontriv
  have hρ_out :
      traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := K) :=
    hV_eq ρ ▸ hEρ
  have hσ_out :
      traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := K) :=
    hV_eq σ ▸ hEσ
  have h := RenyiDPI.sandwichedQuasi_haar_hiaiPetz V hV_iso hα hρ hσ hρ_out hσ_out
  unfold rightAverage at h
  rw [sandwichedQuasi_tensor_maxmixed_gt hα
    (nonneg_of_pdSetLM hρ_out) (nonneg_of_pdSetLM hσ_out)] at h
  simpa only [← hV_eq ρ, ← hV_eq σ] using h

private lemma quasi_re_pos
    {H : Type u} [Qudit H] [Nontrivial H]
    {α : ℝ} (hα : 0 < α) {ρ σ : L H}
    (hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H)) :
    0 < (sandwichedQuasi α ρ σ).re := by
  have hpos : (0 : L H) ≤ CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
        CFC.rpow σ ((1 - α) / (2 * α))) α := CFC.rpow_nonneg
  have htrace := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  have hnonneg : 0 ≤ (sandwichedQuasi α ρ σ).re := by
    rw [sandwichedQuasi_eq_direct]
    exact (Complex.le_def.mp htrace).1
  exact lt_of_le_of_ne hnonneg
    (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα hρ hσ))

theorem sandwichedMonotoneOnPosDefGt_hiaiPetz :
SandwichedMonotoneOnPosDefGt.{u} := by
  intro H K _ _ _ _ E α ρ σ hα hρ hσ hEρ hEσ
  have hQ := RenyiDPI.sandwichedQuasi_le_cptp_pd_hiaiPetz E hα hρ hσ hEρ hEσ
  have hTr : (Tr (E.toFun ρ)).re = (Tr ρ).re :=
    congrArg Complex.re (E.trace_map ρ).symm
  have hTr_pos : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQ_pos : 0 < (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    quasi_re_pos (lt_trans zero_lt_one hα) hEρ hEσ
  have hlog := Real.log_le_log (div_pos hQ_pos hTr_pos)
    (div_le_div_of_nonneg_right hQ hTr_pos.le)
  unfold sandwichedRenyiDiv
  rw [hTr]
  exact mul_le_mul_of_nonneg_left hlog
    (one_div_nonneg.mpr (sub_nonneg.mpr hα.le))

end RenyiDPI
