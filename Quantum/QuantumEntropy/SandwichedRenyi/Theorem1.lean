import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Dispatcher.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesStrongSubadditivity
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates


/-!
Theorem 1 with the density-operator hypotheses of the first paper.
Source: arXiv:2607.05492v1, main.tex:1656–1663 (mathematical statement),
1664–1683 (representative code and the distinction from the PD analytic core).
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel

universe u

/-- Representative code for Theorem 1 of the paper.

Source: arXiv:2607.05492v1, main.tex:1656–1663. The paper assumes both
`ρ` and `σ` are density operators and additionally that `σ` is positive
definite. In particular, `ρ` may be singular and no output PD hypothesis
is imposed. The conclusion uses the extended-real divergence; it is a
specialization of the all-order data-processing theorem
`RenyiDPI.sandwichedRenyiDivNN_monotone`.
-/
theorem sandwichedRenyiDivNN_theorem1
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (_hσpd : IsPositiveDefinite σ) :
    sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDivNN α ρ σ := by
  exact RenyiDPI.sandwichedRenyiDivNN_monotone E hα_ge hα_ne1
    ((LinearMap.nonneg_iff_isPositive ρ).2 hρ.1)
    ((LinearMap.nonneg_iff_isPositive σ).2 hσ.1)

/-- The NN divergence agrees with the real analytic definition on PD pairs.
Source: arXiv:2607.05492v1, main.tex:1664–1683 (the bridge between the extended-real and the
real-valued divergences). This identity applies separately to the input and output pairs when all
four operators are positive definite. The only parameter needed here is `0 < α`.
-/
theorem sandwichedRenyiDivNN_eq_real_of_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα : 0 < α) {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    sandwichedRenyiDivNN α ρ σ = (sandwichedRenyiDiv α ρ σ : EReal) := by
  have hsupp := suppLE_of_pdSetLM_right ρ hσ
  have hQ := sandwichedQuasi_re_ne_zero_of_pdSetLM hα hρ hσ
  unfold sandwichedRenyiDivNN
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨_, _, h⟩)
  · exact h hsupp
  · exact hQ h

/-- The real-valued PD analytic core recovered from the Theorem 1 wrapper.
Source: arXiv:2607.05492v1, main.tex:1656–1683. Unlike the NN wrapper,
this corollary explicitly assumes PD inputs and outputs. -/
theorem sandwichedRenyiDiv_theorem1_of_pd
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hρpd : ρ ∈ pdSetLM (ℋ := ℋ)) (hσpd : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρpd : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσpd : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα : 0 < α := by linarith
  have h := sandwichedRenyiDivNN_theorem1 E hα_ge hα_ne1 hρ hσ
    ((pdSetLM_isPositiveDefinite_certificate σ).1 hσpd)
  rw [sandwichedRenyiDivNN_eq_real_of_pd hα hEρpd hEσpd,
    sandwichedRenyiDivNN_eq_real_of_pd hα hρpd hσpd] at h
  exact_mod_cast h

end SandwichedRenyiRelativeEntropy
