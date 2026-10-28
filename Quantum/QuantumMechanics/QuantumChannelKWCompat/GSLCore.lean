import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore

/-! Partial-trace identities on linear and continuous linear operators. -/
namespace QuantumChannel
open QuantumState TensorProduct
universe u v

lemma TrRight_outer_product_compat
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (u v : E ⊗[ℂ] F) :
    TrRight (ℋ₂ := E) (ℋ₃ := F) (outer_product u v) =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) :=
  TrRight_outer_product b u v

end QuantumChannel
