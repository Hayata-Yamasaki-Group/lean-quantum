import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupportResiduals

open QuantumState QuantumChannel GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology UniformConvergence
namespace SandwichedRenyiRelativeEntropy.AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Joint CFC continuity on a varying PSD operator, with a locally bounded spectrum. -/
lemma continuousAt_weighted_cfc {A : ℝ × ℝ → B H}
    (hA : ContinuousAt A (1, 1)) (hAnn : ∀ p, 0 ≤ A p) :
    ContinuousAt (fun p : ℝ × ℝ => cfc (weightedScalar p.2) (A p)) (1, 1) := by
  let S := Metric.closedBall (0 : ℝ) (‖A (1, 1)‖ + 1)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hnorm : ∀ᶠ p in 𝓝 ((1 : ℝ), (1 : ℝ)), ‖A p‖ < ‖A (1, 1)‖ + 1 :=
    hA.norm.eventually (eventually_lt_nhds (lt_add_one _))
  have hspec : ∀ᶠ p in 𝓝 ((1 : ℝ), (1 : ℝ)), spectrum ℝ (A p) ⊆ S := by
    filter_upwards [hnorm] with p hp
    exact (spectrum.subset_closedBall_norm (A p)).trans (Metric.closedBall_subset_closedBall hp.le)
  have hfun : Filter.Tendsto
      (fun s : ℝ => UniformOnFun.ofFun {S} (weightedScalar s)) (𝓝 1)
      (𝓝 (UniformOnFun.ofFun {S} (weightedScalar 1))) := by
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro T hT
    obtain rfl := Set.mem_singleton_iff.mp hT
    exact tendstoUniformlyOn_weightedScalar hS
  have hfuns : Filter.Tendsto
      (fun p : ℝ × ℝ => UniformOnFun.ofFun {S} (weightedScalar p.2)) (𝓝 (1, 1))
      (𝓝 (UniformOnFun.ofFun {S} (weightedScalar 1))) :=
    hfun.comp (continuous_snd.tendsto ((1 : ℝ), (1 : ℝ)))
  have hpair := hfuns.prodMk hA
  rw [← nhds_prod_eq] at hpair
  have hmem : ∀ᶠ p in 𝓝 ((1 : ℝ), (1 : ℝ)),
      (UniformOnFun.ofFun {S} (weightedScalar p.2), A p) ∈
        {f | ContinuousOn (UniformOnFun.toFun {S} f) S} ×ˢ
          {a : B H | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ S} := by
    filter_upwards [hspec,
      (continuousAt_snd : ContinuousAt Prod.snd ((1 : ℝ), (1 : ℝ))).eventually
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp hs
    exact ⟨(continuous_weightedScalar hs).continuousOn, IsSelfAdjoint.of_nonneg (hAnn p), hp⟩
  exact (continuousOn_cfc_setProd (A := B H) hS).continuousWithinAt
    hmem.self_of_nhds |>.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hpair, hmem⟩)

/-- C04: weighted trace-log joint continuity for singular rho and PD sigma. -/
lemma weighted_log_joint_continuity {ρ σ : B H} (hρ : 0 ≤ ρ) (hσ : σ ∈ pdSet) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Tr ((CFC.rpow (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ *
        CFC.rpow σ ((1 - p.1) / (2 * p.1))) p.2 *
        CFC.log (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ *
          CFC.rpow σ ((1 - p.1) / (2 * p.1))) : B H) : L H)).re) (1, 1) := by
  let K : ℝ → B H := fun α => CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
    CFC.rpow σ ((1 - α) / (2 * α))
  have hKnn (α : ℝ) : 0 ≤ K α := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hc : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 := by
    apply ContinuousAt.div <;> [fun_prop; fun_prop; norm_num]
  have hp : ContinuousAt (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) 1 :=
    (CFC.continuous_rpow_exponent
      (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ)).continuousAt.comp hc
  have hK : ContinuousAt K 1 := (hp.mul continuousAt_const).mul hp
  have hKfst : ContinuousAt (fun p : ℝ × ℝ => K p.1) (1, 1) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((1 : ℝ), (1 : ℝ))) hK continuousAt_fst
  have hw := continuousAt_weighted_cfc hKfst (fun p => hKnn p.1)
  have ht := QuantumState.continuous_re_trace.continuousAt.comp hw
  apply ht.congr_of_eventuallyEq
  filter_upwards [(continuousAt_snd : ContinuousAt Prod.snd ((1 : ℝ), (1 : ℝ))).eventually
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))] with p hs
  exact congrArg (fun T : B H => (Tr (T : L H)).re)
    (cfc_weightedScalar_eq (hKnn p.1) hs).symm

/-- C05: the quasi-entropy derivative with a possibly singular PSD first input. -/
lemma quasi_derivative_psd_pd {ρ σ : L H} (hρ : 0 ≤ ρ)
    (hσ : σ ∈ pdSetLM) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      (Tr (ρ * (CFC.log ρ - CFC.log σ))).re 1 := by
  exact quasi_derivative_psd_pd_of_joint_continuity hρ hσ
    (weighted_log_joint_continuity (ρ := ρ.toContinuousLinearMap)
      (σ := σ.toContinuousLinearMap) hρ hσ)


end SandwichedRenyiRelativeEntropy.AlphaOneSupport
