import Quantum.QuantumEntropy.Gour.Sandwiched.DualityFoundationsMinimax.GSLCore
import
  Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesStrongTypicalityQuantumDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCore
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Mathlib
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityFoundationDefinitions.GSLCore
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Multinomial
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Subadditive
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein


open QuantumState QuantumChannel GourConditionalEntropy Filter Topology
open scoped TensorProduct BigOperators
universe u

namespace GourResource
/-- Density operators on `A` (positive semidefinite operators of trace one), as a subtype.
Nontriviality of `A` is not part of the type; the central theorems assume it separately. -/
abbrev State (A : Type u) [Qudit.{u} A] := {X : L.{u} A // IsDensity.{u} X}
/-- The `n`-copy space of `A`: the right-associated tensor product of `n` factors of `A`,
ending in the lifted scalars (`Copy A 0` is `ULift ℂ` and `Copy A 1` is `A ⊗ ULift ℂ`). -/
noncomputable abbrev Copy (A : Type u) [Qudit.{u} A] (n : ℕ) : Type u := w42TensorSpace.{u} A n
/-- A family of free-state sets: for each `n`, a set of operators on the `n`-copy space.
The type itself does not require density, closedness or convexity. -/
abbrev Family (A : Type u) [Qudit.{u} A] := (n : ℕ) → Set (L.{u} (Copy.{u} A n))
/-- The `n`-copy tensor power `ρ^{⊗n}` of a state `ρ`, as an operator on the `n`-copy space;
it is again a density operator. -/
noncomputable abbrev pow {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) : L.{u} (Copy.{u} A n) := w42DensityPower.{u} ρ n
noncomputable def act {A : Type u} [Qudit.{u} A] (U : A ≃ₗᵢ[ℂ] A) (X : L.{u} A) : L.{u} A :=
  U.toLinearEquiv.toLinearMap ∘ₗ X ∘ₗ U.symm.toLinearEquiv.toLinearMap
def wordPerm (d n : ℕ) (π : Equiv.Perm (Fin n)) :
    (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun x i := x (π.symm i)
  invFun x i := x (π i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
/-- The action of a permutation `π` of the `n` tensor factors, as a linear isometry of the
`n`-copy space. It is built from an eigenbasis of `ρ`, but it does not depend on `ρ`
(see `GourResource.gsl_t01`). -/
noncomputable def perm {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Copy.{u} A n ≃ₗᵢ[ℂ] Copy.{u} A n :=
  (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n).equiv
    (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n)
    (wordPerm (Module.finrank ℂ A) n π)
noncomputable def twirl {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) (X : L.{u} (Copy.{u} A n)) : L.{u} (Copy.{u} A n) :=
  (1 / (Nat.factorial n : ℝ)) • ∑ π : Equiv.Perm (Fin n), act.{u} (perm.{u} ρ n π) X
/-- The tensor product of an operator on `n` copies and an operator on `m` copies, as an
operator on `n + m` copies through the canonical reassociation of the copy spaces. The
reassociation does not depend on `ρ` (see `GourResource.gsl_t01`). -/
noncomputable def join {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n m : ℕ) (X : L.{u} (Copy.{u} A n))
    (Y : L.{u} (Copy.{u} A m)) : L.{u} (Copy.{u} A (n + m)) :=
  (w44TensorJoin.{u} ρ n m).toLinearEquiv.toLinearMap ∘ₗ TensorProduct.map X Y ∘ₗ
    (w44TensorJoin.{u} ρ n m).symm.toLinearEquiv.toLinearMap
def symmetric {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) (X : L.{u} (Copy.{u} A n)) : Prop :=
  ∀ π : Equiv.Perm (Fin n), act.{u} (perm.{u} ρ n π) X = X
/-- The density-operator condition together with Gour's four conditions on a family of
free-state sets (Gour, §11.3). For every positive number of copies `n`, `F n` consists of
density operators, is closed and convex, and is closed under permutations of the copies;
`F` is closed under tensor products for positive numbers of copies; and `F 1` contains
`pow γ 1` for a positive definite state `γ`. No condition is imposed on `F 0`. -/
def valid {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) : Prop :=
  (∀ n : ℕ, 0 < n → F n ⊆ {X | IsDensity.{u} X}) ∧
  (∀ n : ℕ, 0 < n → IsClosed (F n) ∧ Convex ℝ (F n)) ∧
  (∀ (n : ℕ), 0 < n → ∀ X ∈ F n, ∀ π : Equiv.Perm (Fin n),
    act.{u} (perm.{u} ρ n π) X ∈ F n) ∧
  (∀ (n m : ℕ), 0 < n → 0 < m → ∀ X ∈ F n, ∀ Y ∈ F m,
    join.{u} ρ n m X Y ∈ F (n + m)) ∧
  (∃ γ : State.{u} A, QuantumState.IsPositiveDefinite.{u} γ.1 ∧ pow.{u} γ 1 ∈ F 1)
/-- Effect operators (tests): `0 ≤ M ≤ 1`. -/
def effect {A : Type u} [Qudit.{u} A] (M : L.{u} A) : Prop :=
  M.IsPositive ∧ (1 - M).IsPositive
/-- The real pairing `Re Tr (X M)`. -/
noncomputable def pairing {A : Type u} [Qudit.{u} A] (X M : L.{u} A) : ℝ := (Tr.{u} (X * M)).re
/-- The optimal type-II error `β_ε(ρ‖σ)`: the real infimum of `Re Tr (σ M)` over effects `M`
with `1 - ε ≤ Re Tr (ρ M)`. It is defined for every real `ε`. -/
noncomputable def beta {A : Type u} [Qudit.{u} A] (ρ σ : L.{u} A) (ε : ℝ) : ℝ :=
  sInf {b : ℝ | ∃ M : L.{u} A, effect.{u} M ∧ 1 - ε ≤ pairing.{u} ρ M ∧ b = pairing.{u} σ M}
/-- The hypothesis-testing relative entropy in bits, `-log₂ β_ε(ρ‖σ)`; it is `⊤` when
`β_ε(ρ‖σ) ≤ 0`. -/
noncomputable def dh {A : Type u} [Qudit.{u} A] (ρ σ : L.{u} A) (ε : ℝ) : EReal :=
  OPT.binaryNegLog2 (Real.toNNReal (beta.{u} ρ σ ε))
/-- The Umegaki relative entropy in bits (`umegakiRelEntropyNN` divided by `log 2`); it is
`⊤` if the support of `ρ` is not contained in that of `σ`. -/
noncomputable def du {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : L.{u} A) : EReal :=
  ((1 / Real.log 2 : ℝ) : EReal) * SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ σ
/-- The max-relative entropy in bits, `OPT.OrderedCone.maxRelEntropy ρ σ` (value `⊥` for
`ρ = 0` and positive semidefinite `σ`). It is not
`SandwichedRenyiRelativeEntropy.maxRelEntropyNN`, which uses natural logarithms and gives `0`
at `ρ = 0`. -/
noncomputable def dm {A : Type u} [Qudit.{u} A] (ρ σ : L.{u} A) : EReal :=
  OPT.OrderedCone.maxRelEntropy ρ σ
noncomputable def td {A : Type u} [Qudit.{u} A] (ρ σ : L.{u} A) : ℝ := w40T₁.{u} (ρ - σ) / 2
noncomputable def smoothMax {A : Type u} [Qudit.{u} A]
    (ρ σ : L.{u} A) (ε : ℝ) : EReal :=
  ⨅ (τ : L.{u} A) (_ : IsDensity.{u} τ ∧ td.{u} ρ τ ≤ ε), dm.{u} τ σ
/-- The resource quantity `inf_{σ ∈ F} D(ρ‖σ)` for a divergence `D`; it is `⊤` if `F` is
empty. -/
noncomputable def res {A : Type u} [Qudit.{u} A]
    (D : L.{u} A → L.{u} A → EReal) (ρ : L.{u} A) (F : Set (L.{u} A)) : EReal :=
  ⨅ (σ : L.{u} A) (_ : σ ∈ F), D ρ σ
/-- The rate `(1/n) · a n` of a sequence, set to `0` for `n = 0`. -/
noncomputable def rate (a : ℕ → EReal) (n : ℕ) : EReal :=
  if n = 0 then 0 else ((1 / (n : ℝ) : ℝ) : EReal) * a n
/-- The hypothesis-testing relative entropy rate
`h_n^ε = (1/n) inf_{σ ∈ F n} D_min^ε(ρ^{⊗n}‖σ)` for `n ≥ 1`, and `0` for `n = 0`.
It is defined for every real `ε`; the infimum over an empty set is `⊤`. -/
noncomputable def hRate {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (ε : ℝ) : ℕ → EReal :=
  rate (fun n => res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (F n))
/-- The relative entropy rate `u_n = (1/n) inf_{σ ∈ F n} D(ρ^{⊗n}‖σ)`, with `D` the Umegaki
relative entropy `du` in bits, and `0` for `n = 0`. -/
noncomputable def uRate {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) : ℕ → EReal :=
  rate (fun n => res.{u} du.{u} (pow.{u} ρ n) (F n))
noncomputable def mRate {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (ε : ℝ) : ℕ → EReal :=
  rate (fun n => res.{u} (fun X Y => smoothMax.{u} X Y ε) (pow.{u} ρ n) (F n))
/-- The regularized relative entropy `D^reg(ρ‖F) = inf_{n ≥ 1} u_n` (see `uRate`).
Under `hyValid ρ F` it is also the limit of `u_n` (`GourResource.gsl_c23`). -/
noncomputable def reg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) : EReal :=
  ⨅ n : PNat, uRate.{u} ρ F n
noncomputable def pin {A : Type u} [Qudit.{u} A] (σ X : L.{u} A) : L.{u} A :=
  spectralPinchingLinearMap.{u} σ X
noncomputable def posProj {A : Type u} [Qudit.{u} A]
    (X : L.{u} A) : L.{u} A :=
  (⨆ (a : ℝ) (_ : 0 < a), Module.End.eigenspace X (a : ℂ)).starProjection.toLinearMap
noncomputable def threshold {A : Type u} [Qudit.{u} A]
    (X σ : L.{u} A) (a : ℝ) : L.{u} A :=
  posProj.{u} ((Real.rpow 2 a : ℝ) • σ - X)
noncomputable def seqRate {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (σ : (n : ℕ) → L.{u} (Copy.{u} A n)) : ℕ → EReal :=
  rate (fun n => du.{u} (pow.{u} ρ n) (σ n))
noncomputable def petz {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (α : ℝ) (ρ σ : L.{u} A) : EReal := by
  classical
  exact if hα : 0 ≤ α then
    if hρ : IsDensity.{u} ρ then
      if hσ : IsDensity.{u} σ then OPT.petzQuantumRenyiDivergenceFinite.{u} ⟨α, hα⟩ ρ σ hρ hσ
      else ⊤
    else ⊤
  else ⊤
/-- The sandwiched Rényi divergence of order `α` in bits, as a total function of `α : ℝ`.
For density operators `ρ, σ` it is `gourSandwichedRenyiBits (ENNReal.ofReal α) ρ σ`; since
`ENNReal.ofReal α = 0` for `α ≤ 0`, every order `α < 0` falls into the order-`0` branch, and
the orders `0` and `1` take the Petz–Rényi endpoint values. For `α > 1` it is the standard
sandwiched Rényi divergence. If `ρ` or `σ` is not a density operator, the value is `⊤`. -/
noncomputable def sand {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (α : ℝ) (ρ σ : L.{u} A) : EReal := by
  classical
  exact if hρ : IsDensity.{u} ρ then
    if hσ : IsDensity.{u} σ then
      SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits.{u} (ENNReal.ofReal α) ρ σ hρ hσ
    else ⊤
  else ⊤
noncomputable def renyiReg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (α : ℝ) : EReal :=
  ⨅ n : PNat, rate (fun k => res.{u} (petz.{u} α) (pow.{u} ρ k) (F k)) n
def symFamily {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) : Family.{u} A :=
  fun n => {X | X ∈ F n ∧ symmetric.{u} ρ n X}
noncomputable def blockPower {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (m : ℕ) (σ : L.{u} (Copy.{u} A m)) :
    (k : ℕ) → L.{u} (Copy.{u} A (m * k))
  | 0 => by simpa using (1 : L.{u} (Copy.{u} A 0))
  | k + 1 => by
    simpa only [Nat.mul_succ] using join.{u} ρ (m * k) m (blockPower ρ m σ k) σ
noncomputable def padded {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State.{u} A) (m : ℕ) (σ : L.{u} (Copy.{u} A m)) (n : ℕ) :
    L.{u} (Copy.{u} A n) :=
  cast (congrArg (fun j => L.{u} (Copy.{u} A j))
    (by simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n m))
    (join.{u} ρ (m * (n / m)) (n % m) (blockPower.{u} ρ m σ (n / m)) (pow.{u} γ (n % m)))
noncomputable def symSpace {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) : Submodule ℂ (Copy.{u} A n) :=
  ⨅ π : Equiv.Perm (Fin n), LinearMap.ker ((perm.{u} ρ n π).toLinearEquiv.toLinearMap - 1)
noncomputable def symProj {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) : L.{u} (Copy.{u} A n) :=
  (symSpace.{u} ρ n).starProjection.toLinearMap
noncomputable def entropy {A : Type u} [Qudit.{u} A] (X : L.{u} A) : ℝ :=
  -(Tr.{u} (X * CFC.log X)).re / Real.log 2
noncomputable def hb (ε : ℝ) : ℝ := -ε * Real.logb 2 ε - (1 - ε) * Real.logb 2 (1 - ε)


noncomputable def positivePart {A : Type u} [Qudit.{u} A] (X : L.{u} A) : L.{u} A :=
  (1/2 : ℝ) • (X + CFC.sqrt (star X * X))

abbrev OpSeq (A : Type u) [Qudit.{u} A] := (n : ℕ) → L.{u} (Copy.{u} A n)
/-- The conditions of Hayashi–Yamasaki, Theorem 1: the density-operator condition,
closedness and convexity, closedness under tensor products for positive numbers of copies,
and a positive definite state in `F 1`. Permutation invariance and closedness under partial
traces are not included, and no condition is imposed on `F 0`. -/
def hyValid {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) : Prop :=
  (∀ n : ℕ, 0 < n → F n ⊆ {X | IsDensity.{u} X}) ∧
  (∀ n : ℕ, 0 < n → IsClosed (F n) ∧ Convex ℝ (F n)) ∧
  (∀ n m : ℕ, 0 < n → 0 < m → ∀ X ∈ F n, ∀ Y ∈ F m,
    join.{u} ρ n m X Y ∈ F (n+m)) ∧
  (∃ γ : State.{u} A, IsPositiveDefinite.{u} γ.1 ∧ pow.{u} γ 1 ∈ F 1)
def admissible {A : Type u} [Qudit.{u} A] (F : Family.{u} A) (σ : OpSeq.{u} A) : Prop :=
  ∀ n : ℕ, 0 < n → σ n ∈ F n ∧ IsDensity.{u} (σ n)
def optSeq {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (ε : ℝ) (σ : OpSeq.{u} A) : Prop :=
  admissible.{u} F σ ∧ ∀ n : ℕ, 0 < n →
    dh.{u} (pow.{u} ρ n) (σ n) ε = res.{u} (fun X Y => dh.{u} X Y ε) (pow.{u} ρ n) (F n)
/-- The optimal type-II error of composite testing: the real infimum, over effects `M` with
`1 - ε ≤ Re Tr (ρ M)`, of `sup_{σ ∈ F} Re Tr (σ M)`. -/
noncomputable def betaSet {A : Type u} [Qudit.{u} A]
    (ρ : L.{u} A) (F : Set (L.{u} A)) (ε : ℝ) : ℝ :=
  sInf {b : ℝ | ∃ M : L.{u} A, effect.{u} M ∧ 1-ε ≤ pairing.{u} ρ M ∧
    b = sSup ((fun σ => pairing.{u} σ M) '' F)}
noncomputable def worstBeta {A : Type u} [Qudit.{u} A]
    (ρ : L.{u} A) (F : Set (L.{u} A)) (ε : ℝ) : ℝ :=
  sSup ((fun σ => beta.{u} ρ σ ε) '' F)
/-- The negative logarithm in bits of the composite type-II error `betaSet ρ F ε`, and `⊤`
if that infimum is at most `0` (Hayashi–Yamasaki, Theorem 1 and Lemma 3). The definition
assumes neither density, nonemptiness, closedness and convexity, nor a range of `ε`. -/
noncomputable def dSet {A : Type u} [Qudit.{u} A]
    (ρ : L.{u} A) (F : Set (L.{u} A)) (ε : ℝ) : EReal :=
  OPT.binaryNegLog2 (Real.toNNReal (betaSet.{u} ρ F ε))
noncomputable def mixHY {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State.{u} A) (m : ℕ) (σ : L.{u} (Copy.{u} A m))
    (z : OpSeq.{u} A) (n : ℕ) : L.{u} (Copy.{u} A n) :=
  (1/3 : ℝ) • (z n + padded.{u} ρ γ m σ n + pow.{u} γ n)
noncomputable def cBits (lam : ℝ) (n : ℕ) : ℝ :=
  Real.logb 2 (1/lam) + Real.logb 2 3 / (max n 1 : ℕ)
noncomputable def grid (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (⌈Real.logb 2 x / cBits lam n⌉ : ℤ) * cBits lam n
noncomputable def roundRaw {A : Type u} [Qudit.{u} A]
    (lam : ℝ) (n : ℕ) (X : L.{u} A) : L.{u} A :=
  cfc (fun x : ℝ => Real.rpow 2 (grid lam n x)) X
noncomputable def rounded {A : Type u} [Qudit.{u} A]
    (lam : ℝ) (n : ℕ) (X : L.{u} A) : L.{u} A :=
  ((Tr.{u} (roundRaw.{u} lam n X)).re)⁻¹ • roundRaw.{u} lam n X
noncomputable def testHi {A : Type u} [Qudit.{u} A]
    (X σ : L.{u} A) (a : ℝ) : L.{u} A :=
  1 - posProj.{u} ((Real.rpow 2 a : ℝ) • σ - X)
noncomputable def testMass {A : Type u} [Qudit.{u} A]
    (X σ : L.{u} A) (a : ℝ) : ℝ := pairing.{u} X (testHi.{u} X σ a)
noncomputable def logWeight {A : Type u} [Qudit.{u} A]
    (X σ E : L.{u} A) : ℝ :=
  (Tr.{u} (X * E * (CFC.log X - CFC.log σ))).re / Real.log 2
noncomputable def cap (lam b δ : ℝ) (n : ℕ) : ℝ :=
  max (cBits lam n + cBits lam n / (n : ℝ)) (b+δ)
noncomputable def pairRate {A : Type u} [Qudit.{u} A]
    (X σ : OpSeq.{u} A) (ε : ℝ) : ℕ → EReal :=
  rate (fun n => dh.{u} (X n) (σ n) ε)
noncomputable def entRate {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X σ : OpSeq.{u} A) : ℕ → EReal := rate (fun n => du.{u} (X n) (σ n))

noncomputable def push0 {A : Type u} [Qudit.{u} A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L.{u} A) : L B :=
  U.toLinearEquiv.toLinearMap ∘ₗ X ∘ₗ U.symm.toLinearEquiv.toLinearMap
noncomputable def push {A B : Type u} [Qudit.{u} A] [Qudit.{u} B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L.{u} A) : L.{u} B :=
  U.toLinearEquiv.toLinearMap ∘ₗ X ∘ₗ U.symm.toLinearEquiv.toLinearMap
noncomputable def tensorWord {A : Type u} [Qudit.{u} A] :
    (n : ℕ) → (Fin n → A) → Copy.{u} A n
  | 0, _ => ULift.up 1
  | n+1, x => x 0 ⊗ₜ[ℂ] tensorWord n (fun i => x i.succ)
def blockWord {A : Type u} (m k : ℕ) (x : Fin k → Fin m → A) : Fin (m*k) → A :=
  fun i => let p : Fin k × Fin m := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm m k) i)
    x p.1 p.2

end GourResource
