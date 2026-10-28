import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesClassicalProbabilityDefinitions.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NormNum
import Quantum.QuantumEntropy.PinchingTensorSpectrum.GSLCore
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore


/-!
Hilbert-space tensor powers, eigenbases and eigenvalue PMFs used for typicality.  The tensor unit
is `ULift ℂ`, and the successor is the actual Hilbert tensor product.
-/

open QuantumState
open scoped BigOperators TensorProduct

universe u

namespace GourConditionalEntropy

private noncomputable abbrev w42UnitQudit : Qudit (ULift.{u} ℂ) := by
  letI : InnerProductSpace ℂ (ULift.{u} ℂ) :=
    { inner x y := inner ℂ x.down y.down
      norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) x.down
      conj_inner_symm x y := inner_conj_symm x.down y.down
      add_left x y z := inner_add_left x.down y.down z.down
      smul_left x y c := inner_smul_left x.down y.down c }
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      toFinite := FiniteDimensional.of_injective
        (ULift.moduleEquiv (R := ℂ) (M := ℂ)).toLinearMap
        (ULift.moduleEquiv (R := ℂ) (M := ℂ)).injective }

private noncomputable def w42TensorSystem (A : Type u) [Qudit.{u} A] :
    ℕ → Σ B : Type u, Qudit.{u} B
  | 0 => ⟨ULift.{u} ℂ, w42UnitQudit.{u}⟩
  | n + 1 =>
    let prev := w42TensorSystem A n
    letI := prev.2
    ⟨A ⊗[ℂ] prev.1, inferInstance⟩

/-- Right-associated Hilbert tensor powers, including the lifted scalar unit. -/
noncomputable abbrev w42TensorSpace (A : Type u) [Qudit.{u} A] (n : ℕ) : Type u :=
  (w42TensorSystem.{u} A n).1

noncomputable instance w42TensorSpaceQudit (A : Type u) [Qudit.{u} A] (n : ℕ) :
    Qudit.{u} (w42TensorSpace.{u} A n) := (w42TensorSystem.{u} A n).2

instance w42TensorSpaceNontrivial (A : Type u) [Qudit.{u} A] [Nontrivial A] (n : ℕ) :
    Nontrivial (w42TensorSpace.{u} A n) := by
  induction n with
  | zero => exact inferInstanceAs (Nontrivial (ULift.{u} ℂ))
  | succ n ih =>
    letI := ih
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    change 0 < Module.finrank ℂ (A ⊗[ℂ] w42TensorSpace.{u} A n)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos (Module.finrank_pos (R := ℂ) (M := A))
      (Module.finrank_pos (R := ℂ) (M := w42TensorSpace.{u} A n))

/-- Tensor powers of arbitrary operators; no density hypothesis is built in. -/
noncomputable def w42OperatorPower {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L.{u} A) : (n : ℕ) → L.{u} (w42TensorSpace.{u} A n)
  | 0 => 1
  | n + 1 => TensorProduct.map X (w42OperatorPower X n)

/-- The `n`-fold tensor power of a density operator `ρ`, as an operator; that it is again a
density operator is proved separately. -/
noncomputable abbrev w42DensityPower {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : {X : L.{u} A // IsDensity.{u} X}) (n : ℕ) :=
  w42OperatorPower.{u} ρ.1 n

private def w42WordConsEquiv (m n : ℕ) :
    (Fin m × (Fin n → Fin m)) ≃ (Fin (n + 1) → Fin m) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, fun j => x j.succ)
  left_inv x := by simp
  right_inv x := by ext i; exact Fin.cases rfl (fun _ => rfl) i

/-- Tensor-product basis, reindexed by words using their head and tail. -/
noncomputable def w42TensorBasis {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A) :
    (n : ℕ) → OrthonormalBasis (Fin n → Fin (Module.finrank ℂ A)) ℂ
      (w42TensorSpace.{u} A n)
  | 0 => by
    let b₀ : OrthonormalBasis Unit ℂ (w42TensorSpace.{u} A 0) :=
      (OrthonormalBasis.singleton Unit ℂ).map
        (LinearIsometryEquiv.ulift.{0, 0, u} ℂ ℂ).symm
    exact b₀.reindex (Equiv.ofUnique Unit (Fin 0 → Fin (Module.finrank ℂ A)))
  | n + 1 => (b.tensorProduct (w42TensorBasis b n)).reindex
      (w42WordConsEquiv (Module.finrank ℂ A) n)

/-- Conjugation by an explicit coordinate isometry. -/
noncomputable def w42CoordinateOperator {A : Type u} [Qudit.{u} A] [Nontrivial A]
    {n : ℕ} (U : w42TensorSpace.{u} A n ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n → Fin (Module.finrank ℂ A)))
    (Y : L.{u} (w42TensorSpace.{u} A n)) :
    L.{0} (EuclideanSpace ℂ (Fin n → Fin (Module.finrank ℂ A))) :=
  U.toLinearEquiv.toLinearMap ∘ₗ Y ∘ₗ U.symm.toLinearEquiv.toLinearMap

/-- An orthonormal eigenbasis of `ρ` (`OPT.petzRenyiSpectralEigenbasis`, the basis used for the
Petz–Rényi divergence), with eigenvalues repeated according to multiplicity. -/
noncomputable abbrev w42EigenBasis {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : {X : L.{u} A // IsDensity.{u} X}) :=
  OPT.petzRenyiSpectralEigenbasis.{u} ρ.1 ρ.2

/-- PMF formation uses positivity and trace one, not a typicality result. -/
noncomputable def w42EigenPMF {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : {X : L.{u} A // IsDensity.{u} X}) : PMF.{0} (Fin (Module.finrank ℂ A)) := by
  classical
  let eig :=  OPT.petzRenyiSpectralEigenvalue.{u} ρ.1 ρ.2
  have heig : ∀ i, 0 ≤ eig i := ρ.2.1.nonneg_eigenvalues rfl
  have hsum : ∑ i, eig i = 1 := by
    calc
      ∑ i, eig i = (Tr.{u} ρ.1).re :=
        (ρ.2.1.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm
      _ = 1 := by rw [ρ.2.2]; rfl
  exact PMF.ofFintype (fun i => ENNReal.ofReal (eig i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => heig i), hsum]
    simp)

end GourConditionalEntropy
