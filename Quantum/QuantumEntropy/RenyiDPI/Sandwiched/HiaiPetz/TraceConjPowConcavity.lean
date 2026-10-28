import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.TraceConjPowVariational
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificates

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma s03_pdSetLM_convex {H : Type u} [Qudit H] [Nontrivial H] :
    Convex ℝ (pdSetLM (ℋ := H)) := by
  intro A hA B hB a b ha hb hab
  have hApos := (pdSetLM_strictPositivity_certificate A).mp hA
  have hBpos := (pdSetLM_strictPositivity_certificate B).mp hB
  apply (pdSetLM_strictPositivity_certificate (a • A + b • B)).mpr
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    simpa only [zero_smul, zero_add, hb1, one_smul] using hBpos
  · exact (IsStrictlyPositive.smul (lt_of_le_of_ne ha (Ne.symm ha0)) hApos).add_nonneg
      (smul_nonneg hb hBpos.nonneg)

private lemma s03_traceConjPowVar_jointlyConcave (hLieb : LiebConcavityPD.{u})
    {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (B : L H) :
    JointlyConcaveOn (pdSetLM (ℋ := H)) (pdSetLM (ℋ := H)) (traceConjPowVar p B) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  have h := hLieb hp0 hp1 (star B) hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  have htr : (Tr ((1 - θ) • X₁ + θ • X₂)).re =
      (1 - θ) * (Tr X₁).re + θ * (Tr X₂).re := by
    rw [map_add, Complex.add_re]
    have hr (r : ℝ) (X : L H) : (Tr (r • X)).re = r * (Tr X).re := by
      rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [hr, hr]
  simp only [traceConjPowVar, smul_eq_mul] at h ⊢
  rw [htr]
  nlinarith

theorem traceConjPow_concave_of_lieb :
LiebConcavityPD.{u} →
  ∀ {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ} (B : L H),
  0 < p → p < 1 → IsUnit B →
  ConcaveOn ℝ (pdSetLM (ℋ := H)) (traceConjPow p B) := by
  intro hLieb H _ _ p B hp0 hp1 hB
  have hconv := s03_pdSetLM_convex (H := H)
  refine ⟨hconv, ?_⟩
  intro A₁ hA₁ A₂ hA₂ a b ha hb hab
  obtain ⟨X₁, hX₁, heq₁⟩ := RenyiDPI.exists_traceConjPowVar_eq_pos hp0 hp1 hB hA₁
  obtain ⟨X₂, hX₂, heq₂⟩ := RenyiDPI.exists_traceConjPowVar_eq_pos hp0 hp1 hB hA₂
  have hupper := RenyiDPI.traceConjPowVar_le_pos (B := B) hp0 hp1
    (hconv hA₁ hA₂ ha hb hab) (hconv hX₁ hX₂ ha hb hab)
  have hlower := s03_traceConjPowVar_jointlyConcave hLieb hp0 hp1 B
    hA₁ hA₂ hX₁ hX₂ hb (show b ≤ 1 by linarith)
  have hab' : 1 - b = a := by linarith
  simp only [hab', smul_eq_mul] at hlower
  rw [← heq₁, ← heq₂] at hlower
  simp only [smul_eq_mul]
  apply (mul_le_mul_iff_right₀ hp0).mp
  nlinarith only [hlower, hupper]

end RenyiDPI
