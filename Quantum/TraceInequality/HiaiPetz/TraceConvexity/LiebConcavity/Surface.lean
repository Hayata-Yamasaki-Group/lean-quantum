/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceConvexity.LiebConcavity.Boundary

/-!
# Lieb concavity surface

Top-level assembly of the Lieb concavity of Hiai–Petz Theorem 6.4.

## Main results

* `AndoConvexityRange`: the Ando exponent range for the two powers `(p, q)`.
* `LiebConcavity`: the joint-concavity statement of `supportPowerTrace p q` for exponents
  with `0 ≤ p`, `0 ≤ q`, `p + q ≤ 1`.
* `liebConcavity`: proof of `LiebConcavity`, reducing the general exponents to the scaled
  single-power joint concavity `supportPowerTrace_scaled_jointlyConcave`.

## References

* Hiai, Theorem 6.4.
-/

namespace HiaiPetz
namespace TraceConvexity
open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
noncomputable section MatrixScopedInstances

/-- Source: Hiai, Theorem 6.4. -/
def AndoConvexityRange (p q : ℝ) : Prop :=
  (p ∈ Set.Icc (-1 : ℝ) 0 ∧ q ∈ Set.Icc (-1 : ℝ) 0) ∨
    (p ∈ Set.Icc (-1 : ℝ) 0 ∧ q ∈ Set.Icc (1 - p) 2) ∨
      (q ∈ Set.Icc (-1 : ℝ) 0 ∧ p ∈ Set.Icc (1 - q) 2)

/-- Source: Hiai, Theorem 6.4. -/
def LiebConcavity : Prop :=
  ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
    0 ≤ p →
    0 ≤ q →
    p + q ≤ 1 →
    ∀ {A1 A2 B1 B2 : Mₙ n} {t : ℝ},
      t ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ A1 →
      0 ≤ A2 →
      0 ≤ B1 →
      0 ≤ B2 →
      t * supportPowerTrace p q A1 B1 X +
          (1 - t) * supportPowerTrace p q A2 B2 X ≤
        supportPowerTrace p q (t • A1 + (1 - t) • A2)
          (t • B1 + (1 - t) • B2) X

/-- Source: Hiai, Theorem 6.4. -/
theorem liebConcavity :
    LiebConcavity := by
  intro n p q X hp_nonneg hq_nonneg hpq A1 A2 B1 B2 t ht hA1 hA2 hB1 hB2
  by_cases hp_one : p = 1
  · subst p
    have hq_zero : q = 0 := by
      nlinarith [hq_nonneg, hpq]
    subst q
    have hscaled :=
      supportPowerTrace_scaled_jointlyConcave (p := (1 : ℝ)) (r := (0 : ℝ)) (X := X)
        ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ht hA1 hA2 hB1 hB2
    simpa using hscaled
  · have hp_lt_one : p < 1 := lt_of_le_of_ne (by linarith [hpq, hq_nonneg]) hp_one
    have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp_nonneg, hp_lt_one.le⟩
    have hden_pos : 0 < 1 - p := sub_pos.mpr hp_lt_one
    let r : ℝ := q / (1 - p)
    have hq_le : q ≤ 1 - p := by
      linarith
    have hr_nonneg : 0 ≤ r := by
      exact div_nonneg hq_nonneg hden_pos.le
    have hr_le_one : r ≤ 1 := by
      have hmul : r * (1 - p) ≤ 1 * (1 - p) := by
        dsimp [r]
        rw [div_mul_cancel₀ q (ne_of_gt hden_pos)]
        simpa using hq_le
      exact le_of_mul_le_mul_right hmul hden_pos
    have hq_eq : q = r * (1 - p) := by
      dsimp [r]
      rw [div_mul_cancel₀ q (ne_of_gt hden_pos)]
    have hscaled :=
      supportPowerTrace_scaled_jointlyConcave (p := p) (r := r) (X := X)
        hpIcc ⟨hr_nonneg, hr_le_one⟩ ht hA1 hA2 hB1 hB2
    simpa [hq_eq] using hscaled

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
