import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityFoundationDefinitions.GSLCore
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tensor join for quantum strong typicality

`w44TensorJoin` is the linear isometry equivalence joining the `r`-fold and `k`-fold tensor
spaces into the `(r + k)`-fold tensor space (Gour §8.5.2).  This module keeps the declarations
of the original module that the public development uses.
-/

open QuantumState
open scoped BigOperators TensorProduct

universe u

namespace GourConditionalEntropy

/-- The ONB equivalence associated with concatenation of the two word indices. -/
noncomputable def w44TensorJoin {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : {X : L.{u} A // IsDensity.{u} X}) (r k : ℕ) :
    (w42TensorSpace.{u} A r ⊗[ℂ] w42TensorSpace.{u} A k) ≃ₗᵢ[ℂ]
      w42TensorSpace.{u} A (r + k) :=
  ((w42TensorBasis.{u} (w42EigenBasis.{u} ρ) r).tensorProduct
    (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) k)).equiv
      (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) (r + k)) (Fin.appendEquiv r k)

end GourConditionalEntropy
