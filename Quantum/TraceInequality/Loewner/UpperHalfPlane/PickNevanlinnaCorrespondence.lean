import Quantum.TraceInequality.Loewner.UpperHalfPlane.PickIntervalSupport

/-!
# Hiai's Theorem 2.24 on the upper half-plane

This file provides theorem-facing wrappers that collect the Pick/Nevanlinna
existence, uniqueness, and interval-support equivalence already proved in the
upper-half-plane development.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open scoped UpperHalfPlane Manifold ContDiff

/-- Hiai Theorem 2.24, existence part: Pick functions are exactly those with a
finite-measure Nevanlinna representation.
Theorem 2.24 of [hiai2025]. -/
theorem upperHalfPlanePick_iff_nevanlinnaRep
    {F : ℍ → ℂ} :
    (MDiff F ∧ ∀ z : ℍ, 0 ≤ (F z).im) ↔ Nonempty (NevanlinnaRep F) := by
  constructor
  · rintro ⟨hF, hF_nonneg⟩
    exact ⟨nevanlinnaRep_of_pick hF hF_nonneg⟩
  · rintro ⟨rep⟩
    exact rep.pick_of_rep

/-- Hiai Theorem 2.24, uniqueness part.
Theorem 2.24 of [hiai2025]. -/
theorem nevanlinnaRep_unique
    {F : ℍ → ℂ} (rep₁ rep₂ : NevanlinnaRep F) :
    rep₁ = rep₂ :=
  NevanlinnaRep.unique rep₁ rep₂

/-- Hiai Theorem 2.24, interval-support condition.
Theorem 2.24 of [hiai2025]. -/
theorem memPickInterval_iff_nevanlinnaRepOnComplement
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    MemPickInterval a b F ↔ Nonempty (NevanlinnaRepOnComplement a b F) :=
  (nevanlinnaRepOnComplement_iff_mem_pickInterval rep).symm

/--
Hiai Theorem 2.24, bundled public wrapper.

The interval statement is parameterized by a chosen Nevanlinna representation of
`F`; uniqueness makes the support condition independent of that choice.

Theorem 2.24 of [hiai2025].
-/
theorem upperHalfPlanePick_nevanlinnaRep_support_equiv
    {F : ℍ → ℂ} :
    ((MDiff F ∧ ∀ z : ℍ, 0 ≤ (F z).im) ↔ Nonempty (NevanlinnaRep F)) ∧
      (∀ rep₁ rep₂ : NevanlinnaRep F, rep₁ = rep₂) ∧
        (∀ {a b : ℝ}, a < b →
          ∀ _rep : NevanlinnaRep F,
            MemPickInterval a b F ↔ Nonempty (NevanlinnaRepOnComplement a b F)) := by
  refine ⟨upperHalfPlanePick_iff_nevanlinnaRep, ?_, ?_⟩
  · intro rep₁ rep₂
    exact nevanlinnaRep_unique rep₁ rep₂
  · intro a b _hab rep
    exact memPickInterval_iff_nevanlinnaRepOnComplement rep

end Loewner
end TraceInequality
end Quantum
