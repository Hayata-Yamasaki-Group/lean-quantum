import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.BoundaryContinuity

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem s13_perturbed
    (core : SandwichedMonotoneOnPosDefGt.{u})
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {α : ℝ} {ρ σ : L H}
    (hα : 1 < α) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hE1 : E.toFun (1 : L H) ∈ pdSetLM (ℋ := K))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α
      (E.toFun ρ + (ε : ℂ) • E.toFun 1)
      (E.toFun σ + (ε : ℂ) • E.toFun 1) ≤
    sandwichedRenyiDiv α (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1) := by
  have hmap (X : L H) : E.toFun (X + (ε : ℂ) • 1) =
      E.toFun X + (ε : ℂ) • E.toFun 1 := by
    change E.toLinearMap (X + (ε : ℂ) • 1) =
      E.toLinearMap X + (ε : ℂ) • E.toLinearMap 1
    rw [map_add, map_smul]
  have hEpd {X : L H} (hX : 0 ≤ X) :
      E.toFun (X + (ε : ℂ) • 1) ∈ pdSetLM (ℋ := K) := by
    rw [hmap]
    apply pdSetLM_add_nonneg (map_nonneg E.toCompletelyPositiveMap hX)
    apply (pdSetLM_strictPositivity_certificate _).2
    exact IsStrictlyPositive.smul (RCLike.ofReal_pos.mpr hε)
      ((pdSetLM_strictPositivity_certificate _).1 hE1)
  rw [← hmap ρ, ← hmap σ]
  exact core E hα (nonneg_add_pos_smul_one_pdSetLM hρ hε)
    (nonneg_add_pos_smul_one_pdSetLM hσ hε) (hEpd hρ) (hEpd hσ)

theorem sandwichedRenyiDiv_faithfulApprox_le_of_core :
SandwichedMonotoneOnPosDefGt.{u} →
  ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (E : CPTP H K) {α : ℝ} {ρ σ : L H},
  1 < α → 0 ≤ ρ → 0 ≤ σ → ρ ≠ 0 → SupportLE ρ σ →
  ∀ {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1),
  sandwichedRenyiDiv α
    ((faithfulApprox E lam h0.le h1).toFun ρ)
    ((faithfulApprox E lam h0.le h1).toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  intro core H K _ _ _ _ E α ρ σ hα hρ hσ hρ0 hsupp lam h0 h1
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  let F := faithfulApprox E lam h0.le h1
  have hF1 := faithfulApprox_one_pdSetLM E h0 h1
  have hFρ := faithfulApprox_pdSetLM E h0 h1 hρ hρ0
  have hFσ := faithfulApprox_pdSetLM E h0 h1 hσ hσ0
  have hleft := RenyiDPI.sandwichedRenyiDiv_tendsto_pd_gt hα hFρ hFσ hF1
  have hright := RenyiDPI.sandwichedRenyiDiv_tendsto_support_gt hα hρ hσ hsupp hρ0
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.eventually_of_mem self_mem_nhdsWithin
    (fun ε hε => s13_perturbed core F hα hρ hσ hF1 hε)

end RenyiDPI
