/-
The tensor join of eigenbasis words: `w44TensorJoin` sends the tensor product of the basis
vectors of words `x` and `y` to the basis vector of the concatenated word
(`w44_tensor_join_basis`).  This module keeps the declarations of the original module that the
public development uses.
-/

import
  Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesStrongTypicalityQuantumDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityFoundationDefinitions.GSLCore
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fin.Tuple.Sort
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityTensorFoundation.GSLCore
import Mathlib.Data.Sum.Interval

namespace GourConditionalEntropy

section

open GourConditionalEntropy Filter Topology
open scoped BigOperators TensorProduct

universe u


end

section

open GourConditionalEntropy Filter Topology
open scoped BigOperators TensorProduct

universe u


end

section

open GourConditionalEntropy Filter Topology
open scoped BigOperators TensorProduct

universe u


end

section

open GourConditionalEntropy Filter Topology
open QuantumState
open scoped BigOperators TensorProduct

universe u


theorem w44_tensor_join_basis :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A]
  (ρ : {X : L.{u} A // IsDensity.{u} X}) (r k : ℕ)
  (x : Fin r → Fin (Module.finrank ℂ A))
  (y : Fin k → Fin (Module.finrank ℂ A)),
  w44TensorJoin.{u} ρ r k
    ((w42TensorBasis.{u} (w42EigenBasis.{u} ρ) r x) ⊗ₜ[ℂ]
      (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) k y)) =
    w42TensorBasis.{u} (w42EigenBasis.{u} ρ) (r + k) (Fin.append x y))
:= by
  intro A _ _ ρ r k x y
  simpa only [w44TensorJoin, OrthonormalBasis.tensorProduct_apply] using
    (OrthonormalBasis.equiv_apply_basis
      ((w42TensorBasis (w42EigenBasis ρ) r).tensorProduct
        (w42TensorBasis (w42EigenBasis ρ) k))
      (w42TensorBasis (w42EigenBasis ρ) (r + k)) (Fin.appendEquiv r k) (x, y))

end

section

open GourConditionalEntropy Filter Topology
open QuantumState
open scoped BigOperators TensorProduct

universe u


end

section

open GourConditionalEntropy Filter Topology
open QuantumState
open scoped BigOperators TensorProduct

universe u


end

section

open GourConditionalEntropy Filter Topology
open QuantumState
open scoped BigOperators TensorProduct

universe u


end

end GourConditionalEntropy
